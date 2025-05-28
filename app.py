# -*- coding: utf-8 -*-
import os
import json
import sqlite3
import hashlib
import subprocess
import random
import shutil
from flask import Flask, render_template, request, send_from_directory, abort, url_for, redirect, session, flash
from functools import wraps
import ctypes
from tqdm import tqdm
from werkzeug.security import generate_password_hash, check_password_hash
from flask_login import LoginManager, login_user, login_required, logout_user, current_user, UserMixin
import threading
from datetime import datetime
from flask import jsonify
import time
from uuid import uuid4
from werkzeug.utils import secure_filename
import logging
from logging.handlers import RotatingFileHandler
from apscheduler.schedulers.background import BackgroundScheduler
import re

DB_LOCK = threading.Lock()

app = Flask(__name__)
app.secret_key = "your_secret_key"  # 本番では十分に複雑な値にしてください
app.jinja_env.globals.update(max=max, min=min)

@app.template_filter('datetimeformat')
def datetimeformat(value, fmt='%Y-%m-%d %H:%M:%S'):
    # view_history の viewed_at 等をフォーマットするためのフィルター
    return datetime.fromtimestamp(value).strftime(fmt)

# 設定：複数の動画ディレクトリ+
VIDEO_DIRS = [
   '/Volumes/4TBMobile/doc/doc',
'/Volumes/4TBMobile/doc/docFC',
'/Volumes/4TBMobile/doc/docLi',
   '/Volumes/4TBMobile/media/media',
'/Volumes/4TBMobile/media/meFc',
'/Volumes/4TBMobile/media/meLi'
]
DB_PATH = "local.sqlite"

# アップロード先ディレクトリの選択肢
UPLOAD_DIRS = {
    os.path.basename(d): d
    for d in VIDEO_DIRS
}


ALLOWED_IPS = [
    '127.0.0.1',
    '192.168.2.100',
    '192.168.2.191', # i9-7
    '192.168.2.190', # ipad
    '192.168.2.171',
]

# グローバル変数で進捗を保持
progress_status = {"total": 0, "current": 0}

# グローバルキャッシュ（サムネイルのファイル名をセットで保持）
THUMBNAIL_CACHE = set()

def load_thumbnail_cache():
    global THUMBNAIL_CACHE
    thumb_dir = os.path.join("static", "thumbnails")
    if not os.path.exists(thumb_dir):
        os.makedirs(thumb_dir)
    # 一括取得してキャッシュに格納
    THUMBNAIL_CACHE = set(os.listdir(thumb_dir))
    print("サムネイルキャッシュをロードしました。", THUMBNAIL_CACHE)

# アプリ起動時にキャッシュを読み込む
load_thumbnail_cache()

def get_short_path_name(long_name):
    # Windowsでのみ短いパスを取得する
    if os.name != 'nt':
        return long_name
    # 260文字バッファを用意（通常のMAX_PATH）
    output_buf_size = 260
    output_buf = ctypes.create_unicode_buffer(output_buf_size)
    ret = ctypes.windll.kernel32.GetShortPathNameW(long_name, output_buf, output_buf_size)
    if ret == 0:
        # 失敗した場合は元のパスを返す
        return long_name
    else:
        return output_buf.value

# DB接続
def get_db_connection():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

# DB初期化：favorite カラムを追加
def init_db():
    conn = get_db_connection()
    conn.execute('''    
        CREATE TABLE IF NOT EXISTS video_data (
            video_id TEXT PRIMARY KEY,
            views INTEGER DEFAULT 0,
            tags TEXT DEFAULT '[]'
        )
    ''')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS user_favorites (
            username TEXT,
            video_id TEXT,
            PRIMARY KEY (username, video_id)
        )
    ''')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS video_metadata (
            video_id TEXT PRIMARY KEY,
            full_path TEXT,
            filename TEXT,
            directory TEXT,
            created REAL,
            duration REAL
        )
    ''')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS view_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL,
            video_id TEXT NOT NULL,
            viewed_at REAL NOT NULL
        )
    ''')
    # アップロードバッチとファイル一覧
    conn.execute('''
          CREATE TABLE IF NOT EXISTS upload_batches (
            batch_id TEXT PRIMARY KEY,
            username TEXT NOT NULL,
            directory TEXT NOT NULL,
            count INTEGER NOT NULL,
            timestamp REAL NOT NULL
          )
        ''')
    conn.execute('''
          CREATE TABLE IF NOT EXISTS upload_files (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            batch_id TEXT NOT NULL,
            filename TEXT NOT NULL
          )
    ''')
    conn.commit()
    conn.close()


init_db()  # サーバー起動時にDB初期化

# ログイン必須デコレータ
# def login_required(f):
#     @wraps(f)
#     def decorated_function(*args, **kwargs):
#         if not session.get("logged_in"):
#             flash("ログインしてください。")
#             return redirect(url_for("login", next=request.url))
#         return f(*args, **kwargs)
#     return decorated_function

# カスタムフィルター：秒数をHH:MM:SSまたはMM:SSに変換
@app.template_filter('format_time')
def format_time_filter(seconds):
    try:
        seconds = int(round(float(seconds)))
        m, s = divmod(seconds, 60)
        h, m = divmod(m, 60)
        if h > 0:
            return f"{h:02d}:{m:02d}:{s:02d}"
        else:
            return f"{m:02d}:{s:02d}"
    except Exception:
        return "00:00"

# --- ログ用タイムスタンプをフォーマットする Jinja2 フィルター ---
@app.template_filter('datetimeformat')
def datetimeformat_filter(value, fmt='%Y-%m-%d %H:%M:%S'):
    """UNIX タイムスタンプ（秒）を人間向け日時文字列に変換"""
    try:
        return datetime.fromtimestamp(float(value)).strftime(fmt)
    except Exception:
        return value

# カスタムフィルター：タイトルの省略表示（30文字以上の場合）
@app.template_filter('truncate_title')
def truncate_title(title):
    if len(title) > 30:
        return title[:30] + "…"
    return title

# 動画データ取得（favoriteカラムの存在をチェック）
def get_video_data(video_id):
    conn = get_db_connection()
    cur = conn.execute('SELECT * FROM video_data WHERE video_id = ?', (video_id,))
    row = cur.fetchone()
    conn.close()
    data = {"views": 0, "tags": []}
    if row:
        data["views"] = row["views"]
        data["tags"] = json.loads(row["tags"])
    # Flask-Login の current_user を使用する
    if current_user.is_authenticated:
        username = current_user.id
        conn = get_db_connection()
        cur = conn.execute('SELECT 1 FROM user_favorites WHERE username = ? AND video_id = ?', (username, video_id))
        fav = cur.fetchone()
        conn.close()
        data["favorite"] = bool(fav)
    else:
        data["favorite"] = False
    return data


# 再生回数更新
def increment_video_views(video_id):
    with DB_LOCK:
        conn = get_db_connection()
        try:
            # favorite カラムをなくしたので、tags までだけ INSERT します
            conn.execute('''
                INSERT INTO video_data (video_id, views, tags)
                VALUES (?, 1, ?)
                ON CONFLICT(video_id) DO UPDATE SET views = views + 1
            ''', (video_id, json.dumps([])))
            conn.commit()
            cur = conn.execute('SELECT views FROM video_data WHERE video_id = ?', (video_id,))
            row = cur.fetchone()
            new_views = row["views"] if row else 1
        finally:
            conn.close()
        return new_views

# タグ追加
def add_video_tag(video_id, tag):
    conn = get_db_connection()
    cur = conn.execute('SELECT tags FROM video_data WHERE video_id = ?', (video_id,))
    row = cur.fetchone()
    if row:
        tags = json.loads(row["tags"])
        if tag not in tags:
            tags.append(tag)
            conn.execute('UPDATE video_data SET tags = ? WHERE video_id = ?', (json.dumps(tags), video_id))
    else:
        tags = [tag]
        # favorite 列はなくなったので views, tags だけ
        conn.execute('INSERT INTO video_data (video_id, views, tags) VALUES (?, ?, ?)', 
                     (video_id, 0, json.dumps(tags)))
    conn.commit()
    conn.close()

def unique_filename(directory: str, filename: str) -> str:
    """
    directory 内に filename が存在する場合、
    ファイル名の末尾に（1）（2）…を付けてユニークにする。
    元ファイル名と拡張子はそのまま尊重します。
    """
    base, ext = os.path.splitext(filename)
    candidate = filename
    i = 1
    # 全角括弧（日本語）を使う
    while os.path.exists(os.path.join(directory, candidate)):
        candidate = f"{base}（{i}）{ext}"
        i += 1
    return candidate

# お気に入り切替用ルート
@app.route('/toggle_favorite/<video_id>', methods=['POST'])
@login_required
def toggle_favorite(video_id):
    """
    お気に入りの切り替えを行います。ユーザーごとに user_favorites テーブルを更新します。
    """
    # Flask-Login の current_user.id を使用してユーザーを取得
    username = current_user.id
    conn = get_db_connection()
    # 既存の登録情報を確認
    cur = conn.execute(
        'SELECT 1 FROM user_favorites WHERE username = ? AND video_id = ?',
        (username, video_id)
    )
    row = cur.fetchone()
    if row:
        # 登録済みなら削除
        conn.execute(
            'DELETE FROM user_favorites WHERE username = ? AND video_id = ?',
            (username, video_id)
        )
        flash("お気に入りから削除しました。")
    else:
        # 未登録なら追加
        conn.execute(
            'INSERT INTO user_favorites (username, video_id) VALUES (?, ?)',
            (username, video_id)
        )
        flash("お気に入りに追加しました。")
    conn.commit()
    conn.close()
    # リダイレクトして一覧を再表示
    return redirect(request.referrer or url_for('index'))


# 複数ディレクトリから動画リストを取得（各動画に絶対パス、作成日時、ディレクトリ情報を付与）
def get_video_list():
    conn = get_db_connection()
    cur = conn.execute("SELECT * FROM video_metadata")
    rows = cur.fetchall()
    conn.close()
    videos = []
    for row in rows:
        videos.append({
            "id": row["video_id"],
            "filename": row["filename"],
            "directory": row["directory"],
            "full_path": row["full_path"],
            "created": row["created"],
            "duration": row["duration"],
        })
    return videos




# ffmpegでサムネイル生成
def generate_thumbnail(video_path, thumb_path, time="00:00:01"):
    if not os.path.exists(thumb_path):
        cmd = [
            "ffmpeg", "-ss", time, "-i", video_path,
            "-vframes", "1", "-y", thumb_path
        ]
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        # キャッシュ更新
        global THUMBNAIL_CACHE
        THUMBNAIL_CACHE.add(os.path.basename(thumb_path))
    return thumb_path

# ffprobeで動画の長さ（duration）を取得
def get_video_duration(video_path):
    # Windowsの場合、短いパスに変換してffprobeに渡す
    if os.name == 'nt':
        video_path = get_short_path_name(video_path)
    cmd = [
        "ffprobe", "-v", "error", "-hide_banner", "-show_entries", "format=duration",
        "-of", "default=noprint_wrappers=1:nokey=1", video_path
    ]
    try:
        output = subprocess.check_output(cmd, stderr=subprocess.DEVNULL).decode('utf-8').strip()
        return float(output)
    except Exception as e:
        print(f"ffprobe error: {e}")
        return 0

# 動画を20分割してシーンサムネイル生成
def generate_scene_thumbnails(video_path, video_id, num_scenes=20):
    scenes_dir = os.path.join("static", "scenes")
    os.makedirs(scenes_dir, exist_ok=True)
    duration = get_video_duration(video_path)
    scenes = []
    if duration <= 0:
        return scenes, duration
    for i in range(num_scenes):
        timestamp = duration * i / num_scenes
        thumb_filename = f"{video_id}_scene_{i}.jpg"
        thumb_filepath = os.path.join(scenes_dir, thumb_filename)
        if not os.path.exists(thumb_filepath):
            cmd = [
                "ffmpeg", "-ss", str(timestamp), "-i", video_path,
                "-vframes", "1", "-y", thumb_filepath
            ]
            subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        scenes.append({
            "thumb": thumb_filename,
            "time": timestamp
        })
    return scenes, duration

# TOPページ：動画一覧（検索・ディレクトリフィルター・ページネーション対応）
@app.route('/')
@login_required
def index():
    # 1) メタデータ取得
    all_videos = get_video_list()

    # 2) リクエストパラメータ
    q                = request.args.get("q", "").strip().lower()
    directory_filter = request.args.get("directory", "all")
    sort_by       = request.args.get("sort", "date")
    order            = request.args.get("order", "desc")
    # ★ favorite は '1' が立っていたら True に
    favorite_only    = request.args.get("favorite") == '1'

    videos = all_videos
    # ディレクトリ絞り込み
    if directory_filter != "all":
        videos = [v for v in videos if v["directory"].startswith(directory_filter)]
    # キーワード検索
    if q:
        videos = [v for v in videos if q in v["filename"].lower()]

    # ★ お気に入りのみフィルター
    if favorite_only:
        videos = [v for v in videos if get_video_data(v["id"])["favorite"]]

    # ソート（views, date, duration, filename）
    reverse = (order == "desc")
    if sort_by == "views":
        videos.sort(key=lambda v: get_video_data(v["id"])["views"], reverse=reverse)
    elif sort_by == "date":
        videos.sort(key=lambda v: v["created"], reverse=reverse)
    elif sort_by == "duration":
        videos.sort(key=lambda v: v["duration"], reverse=reverse)
    elif sort_by == "filename":
        videos.sort(key=lambda v: v["filename"].lower(), reverse=reverse)

    # ページネーション...
    per_page = 100
    page     = int(request.args.get("page", 1))
    total    = len(videos)
    start    = (page - 1) * per_page
    end      = start + per_page
    videos_page = videos[start:end]
    total_pages = (total + per_page - 1) // per_page

    # 現在のページの100件のみ、各動画に対してサムネイルの存在チェックとDBデータ取得を実施
    thumb_dir = os.path.join("static", "thumbnails")
    os.makedirs(thumb_dir, exist_ok=True)
    for video in videos_page:
        # サムネイルファイル名は id + ".jpg" とする
        video["thumb"] = video["id"] + ".jpg"
        thumb_path = os.path.join(thumb_dir, video["thumb"])
        if video["thumb"] not in THUMBNAIL_CACHE:
            generate_thumbnail(video["full_path"], thumb_path)
        # DBから再生回数、タグ、お気に入り情報を取得
        data = get_video_data(video["id"])
        video["views"] = data.get("views", 0)
        video["tags"] = data.get("tags", [])
        video["favorite"] = data.get("favorite", False)

    directories = [("all", "すべて")] + [(d, d) for d in VIDEO_DIRS]

    return render_template(
        'index.html',
        videos=videos_page, q=q, sort=sort_by, order=order,
        page=page, total_pages=total_pages,
        directory_filter=directory_filter,
        favorite_only=favorite_only,  # ★ テンプレートへ渡す
        directories=directories
    )

@app.route('/delete_directory/<video_id>', methods=['POST'])
@login_required
def delete_directory(video_id):
    # 対象動画の情報をDBから取得（キャッシュ済みのメタデータを使用）
    videos = get_video_list()
    video = next((v for v in videos if v["id"] == video_id), None)
    if not video:
        flash("動画が見つかりません。")
        return redirect(url_for("index"))
    
    # 削除（移動）対象のディレクトリは、動画が存在するディレクトリ
    directory_to_move = video["directory"]
    
    # 「431960」が含まれているか確認
    if "431960" not in directory_to_move:
        flash("このディレクトリは削除対象ではありません。")
        return redirect(url_for("video_page", video_id=video_id))
    
    # 移動先ベースディレクトリ
    remove_base = r"D:\remove"
    os.makedirs(remove_base, exist_ok=True)
    folder_name = os.path.basename(directory_to_move)
    dest_dir = os.path.join(remove_base, folder_name)
    # 同名ディレクトリが既に存在する場合は、タイムスタンプを付加
    if os.path.exists(dest_dir):
        import time
        dest_dir = os.path.join(remove_base, f"{folder_name}_{int(time.time())}")
    
    try:
        shutil.move(directory_to_move, dest_dir)
        flash(f"ディレクトリ {directory_to_move} を D:\\remove に移動しました。")
    except Exception as e:
        flash(f"ディレクトリの移動に失敗しました: {e}")
        return redirect(url_for("video_page", video_id=video_id))
    
    # DB更新：該当ディレクトリのレコードを削除（更新対象のみ）
    conn = get_db_connection()
    conn.execute("DELETE FROM video_metadata WHERE directory = ?", (directory_to_move,))
    conn.commit()
    conn.close()
    
    return redirect(url_for("index"))


# ゴミ箱
@app.route('/trash')
@login_required
def trash():
    remove_dir = r"D:\remove"
    if not os.path.exists(remove_dir):
        os.makedirs(remove_dir, exist_ok=True)
    items = os.listdir(remove_dir)
    trash_items = []
    for item in items:
        full_path = os.path.join(remove_dir, item)
        trash_items.append({
            "name": item,
            "full_path": full_path,
            "is_dir": os.path.isdir(full_path)
        })
    return render_template('trash.html', trash_items=trash_items)


@app.route('/history')
@login_required
def history():
    conn = get_db_connection()
    rows = conn.execute('''
        SELECT vh.video_id, vh.viewed_at, vm.filename, vm.duration
          FROM view_history vh
          JOIN video_metadata vm ON vh.video_id = vm.video_id
         WHERE vh.username = ?
         ORDER BY vh.viewed_at DESC
         LIMIT 100
    ''', (current_user.id,)).fetchall()
    conn.close()

    history_items = []
    for row in rows:
        history_items.append({
            'id':        row['video_id'],
            'filename':  row['filename'],
            'duration':  row['duration'],
            'viewed_at': datetime.fromtimestamp(row['viewed_at']).strftime('%Y-%m-%d %H:%M:%S'),
            'thumb':     f"{row['video_id']}.jpg"
        })
    return render_template('history.html', history_items=history_items)


# ログイン関連
# @app.route('/login', methods=['GET', 'POST'])
# def login():
#     if request.method == "POST":
#         username = request.form.get("username")
#         password = request.form.get("password")
#         # 簡易認証例：admin/adminpass、実際はユーザー認証の仕組みを整備してください
#         if username == "admin" and password == "adminpass":
#             session["logged_in"] = True
#             session["username"] = username  # ユーザー名をセッションに保存
#             flash("ログイン成功しました。")
#             next_url = request.args.get("next") or url_for("index")
#             return redirect(next_url)
#         else:
#             flash("ユーザー名またはパスワードが正しくありません。")
#     return render_template('login.html')


# @app.route('/logout')
# def logout():
#     session.pop("logged_in", None)
#     flash("ログアウトしました。")
#     return redirect(url_for("login"))

# 動画再生ページ（安全な動画IDを利用）
@app.route('/video/<video_id>')
@login_required
def video_page(video_id):
    all_videos = get_video_list()
    video = next((v for v in all_videos if v["id"] == video_id), None)
    if not video:
        abort(404)
    full_path = video["full_path"]
    new_views = increment_video_views(video_id)

    conn = get_db_connection()
    conn.execute(
        'INSERT INTO view_history (username, video_id, viewed_at) VALUES (?, ?, ?)',
        (current_user.id, video_id, datetime.now().timestamp())
    )
    conn.commit()
    conn.close()

    scenes, duration = generate_scene_thumbnails(full_path, video_id)
    
    # サイドバー：同一ディレクトリ内の動画（自分自身を除く）からランダムに最大12件
    same_dir_videos = [v for v in all_videos if v["directory"] == video["directory"] and v["id"] != video_id]
    if len(same_dir_videos) > 12:
        sidebar_videos = random.sample(same_dir_videos, 12)
    else:
        sidebar_videos = same_dir_videos

    # 各動画のサムネイル生成（キャッシュを利用）
    thumb_dir = os.path.join("static", "thumbnails")
    os.makedirs(thumb_dir, exist_ok=True)
    for v in sidebar_videos:
        thumb_filename = f"{v['id']}.jpg"
        thumb_path = os.path.join(thumb_dir, thumb_filename)
        if thumb_filename not in THUMBNAIL_CACHE:
            generate_thumbnail(v["full_path"], thumb_path)
        v["thumb"] = thumb_filename
        data = get_video_data(v["id"])
        v["views"] = data.get("views", 0)
    
    # 更新した再生回数とDBからのお気に入り状態を反映
    video["views"] = new_views
    video_data = get_video_data(video_id)
    video["favorite"] = video_data.get("favorite", False)
    tags = video_data.get("tags", [])
    
    return render_template('video.html', video=video, scenes=scenes, duration=duration,
                           sidebar_videos=sidebar_videos, tags=tags)


# 動画ファイル配信
@app.route('/serve_video/<video_id>')
@login_required
def serve_video(video_id):
    videos = get_video_list()
    video = next((v for v in videos if v["id"] == video_id), None)
    if not video:
        abort(404)
    return send_from_directory(video["directory"], video["filename"])

# タグ追加
@app.route('/add_tag', methods=['POST'])
@login_required
def add_tag():
    video_id = request.form.get("video_id")
    new_tag = request.form.get("tag")
    if not video_id or not new_tag:
        flash("タグが正しくありません。")
        return redirect(request.referrer or url_for("index"))
    add_video_tag(video_id, new_tag)
    flash("タグを追加しました。")
    return redirect(request.referrer or url_for("index"))

# 動画ファイルの移動用ルート
# 動画ファイルの移動用ルート
@app.route('/move_video/<video_id>', methods=['POST'])
@login_required
def move_video(video_id):
    # ユーザーに表示する移動先（相対表現）
    allowed_destinations = ["doc", "me", "doc/fc", "doc/li", "me/fc", "me/li", "as", "iv"]
    # 相対パスから絶対パスへのマッピング（必要に応じて適宜変更してください）
    destination_mapping = {
        "doc": "D:\\doc",
        "me": "D:\\me",
        "doc/fc": "D:\\doc\\fc",
        "doc/li": "D:\\doc\\li",
        "me/fc": "D:\\me\\fc",
        "me/li": "D:\\me\\li",
        "as": "D:\\as",
        "iv": "D:\\iv"
    }
    destination = request.form.get("destination")
    if destination not in allowed_destinations:
        flash("無効な移動先です。")
        return redirect(url_for("video_page", video_id=video_id))
    videos = get_video_list()
    video = next((v for v in videos if v["id"] == video_id), None)
    if not video:
        flash("動画が見つかりません。")
        return redirect(url_for("index"))
    # マッピングから絶対パスを取得
    dest_dir = os.path.abspath(destination_mapping[destination])
    os.makedirs(dest_dir, exist_ok=True)
    dest_path = os.path.join(dest_dir, video["filename"])
    try:
        shutil.move(video["full_path"], dest_path)
        flash(f"{video['filename']} を {destination}/ に移動しました。")
    except Exception as e:
        flash(f"動画の移動に失敗しました: {e}")
    return redirect(url_for("index"))

# 一括移動／コピー用ルート
@app.route('/bulk_move', methods=['POST'])
@login_required
def bulk_move():
    # ユーザーに表示する移動先（相対表現）
    allowed_destinations = ["doc", "me", "doc/fc", "doc/li", "me/fc", "me/li", "as", "iv"]
    # 相対パスから絶対パスへのマッピング（必要に応じて適宜変更してください）
    destination_mapping = {
        "doc": "D:\\doc",
        "me": "D:\\me",
        "doc/fc": "D:\\doc\\fc",
        "doc/li": "D:\\doc\\li",
        "me/fc": "D:\\me\\fc",
        "me/li": "D:\\me\\li",
        "as": "D:\\as",
        "iv": "D:\\iv"
    }
    destination = request.form.get("destination")
    if destination not in allowed_destinations:
        flash("無効な移動先です。")
        return redirect(url_for("index"))
    
    # 「コピー」モードかどうか。チェックボックスがONなら"on"が送信される
    copy_mode = (request.form.get("copy_mode") == "on")
    
    # 選択された動画ID（複数選択の場合、リストとして送られる）
    selected_videos = request.form.getlist("selected_videos")
    if not selected_videos:
        flash("一括移動対象の動画が選択されていません。")
        return redirect(url_for("index"))
    
    # 動画リストを取得し、video_idをキーにした辞書を作成
    all_videos = get_video_list()
    video_dict = {v["id"]: v for v in all_videos}
    
    # 移動先の絶対パスを取得
    dest_dir = os.path.abspath(destination_mapping[destination])
    os.makedirs(dest_dir, exist_ok=True)
    
    processed_count = 0
    for vid in selected_videos:
        if vid in video_dict:
            video = video_dict[vid]
            dest_path = os.path.join(dest_dir, video["filename"])
            try:
                if copy_mode:
                    shutil.copy2(video["full_path"], dest_path)
                else:
                    shutil.move(video["full_path"], dest_path)
                processed_count += 1
            except Exception as e:
                flash(f"{video['filename']} の処理に失敗しました: {e}")
    
    if copy_mode:
        flash(f"{processed_count} 件の動画を {destination}/ にコピーしました。")
    else:
        flash(f"{processed_count} 件の動画を {destination}/ に移動しました。")
    return redirect(url_for("index"))



# 動画ファイルの削除（移動）
@app.route('/delete_video/<video_id>', methods=['POST'])
@login_required
def delete_video(video_id):
    # 動画情報を取得
    videos = get_video_list()
    video = next((v for v in videos if v["id"] == video_id), None)
    if not video:
        flash("動画が見つかりません。")
        return redirect(url_for("index"))
    
    # 移動元と移動先のパスを設定
    source_path = video["full_path"]
    remove_dir = "D:\\remove"
    dest_path = os.path.join(remove_dir, video["filename"])
    
    # 移動元ファイルの存在確認
    if not os.path.exists(source_path):
        flash(f"元のファイルが見つかりません: {source_path}")
        return redirect(url_for("index"))
    
    # 移動先ディレクトリの作成
    try:
        os.makedirs(remove_dir, exist_ok=True)
    except Exception as e:
        flash(f"移動先ディレクトリの作成に失敗しました: {e}")
        return redirect(url_for("index"))
    
    # 移動処理
    try:
        # 移動先に同名ファイルがある場合は上書き
        if os.path.exists(dest_path):
            os.remove(dest_path)
        
        # ファイルを移動
        shutil.move(source_path, dest_path)
        
        # 成功メッセージ
        flash(f"{video['filename']} を削除しました。（D:\\removeに移動）")
        
        # ここでDBの更新処理を追加することも可能
        # update_video_metadata() など
        
    except Exception as e:
        flash(f"動画の削除に失敗しました: {e}")
    
    return redirect(url_for("index"))

@app.before_request
def restrict_ip():
    if request.remote_addr not in ALLOWED_IPS:
        abort(403)  # 許可されていない場合は403 Forbidden を返す

@app.route('/progress')
@login_required
def progress():
    return progress_status  # JSONで返す場合は jsonify(progress_status) を使うと良い

def update_video_metadata():
    global progress_status
    scanned_videos = []
    
    conn = get_db_connection()
    # DB から既存のディレクトリハッシュを取得
    cur = conn.execute("SELECT directory, hash_value FROM directory_hash")
    stored_hashes = {row["directory"]: row["hash_value"] for row in cur.fetchall()}
    
    # 各 base ディレクトリを走査
    for base_dir in VIDEO_DIRS:
        current_hash = compute_directory_hash(base_dir)
        if base_dir in stored_hashes and stored_hashes[base_dir] == current_hash:
            print(f"ディレクトリ {base_dir} は変更がないため、既存の情報を利用します。")
            # 既存の情報をvideo_metadataテーブルから読み出す
            cur = conn.execute("SELECT * FROM video_metadata WHERE directory LIKE ?", (base_dir + '%',))
            rows = cur.fetchall()
            for row in rows:
                scanned_videos.append({
                    "video_id": row["video_id"],
                    "full_path": row["full_path"],
                    "filename": row["filename"],
                    "directory": row["directory"],
                    "created": row["created"],
                    "duration": row["duration"],
                })
        else:
            print(f"ディレクトリ {base_dir} に変更があります。処理を実行します。")
            # 変更があったディレクトリは、動画ファイルを走査して scanned_videos に追加
            for root, dirs, files in os.walk(base_dir):
                for file in tqdm(files):
                    if file.lower().endswith(('.mp4', '.avi', '.mkv', '.mov', '.m4a')):
                        full_path = os.path.abspath(os.path.join(root, file))
                        video_hash = hashlib.md5(full_path.encode('utf-8')).hexdigest()
                        created = os.path.getctime(full_path)
                        duration = get_video_duration(full_path)
                        scanned_videos.append({
                            "video_id": video_hash,
                            "full_path": full_path,
                            "filename": file,
                            "directory": root,
                            "created": created,
                            "duration": duration,
                        })
            # DB に現在のハッシュを保存（アップサート）
            conn.execute('''
                INSERT INTO directory_hash (directory, hash_value)
                VALUES (?, ?)
                ON CONFLICT(directory) DO UPDATE SET hash_value=excluded.hash_value
            ''', (base_dir, current_hash))
    
    progress_status["total"] = len(scanned_videos)
    progress_status["current"] = 0

    # video_metadata テーブルの更新処理
    cur = conn.execute("SELECT video_id FROM video_metadata")
    existing_ids = {row["video_id"] for row in cur.fetchall()}
    scanned_ids = {video["video_id"] for video in scanned_videos}
    
    # 削除対象：既存レコードでスキャン結果に無いものを削除
    ids_to_delete = existing_ids - scanned_ids
    if ids_to_delete:
        conn.executemany("DELETE FROM video_metadata WHERE video_id = ?", [(vid,) for vid in ids_to_delete])
        print(f"削除対象の動画ID: {ids_to_delete}")

    # スキャン結果を動画メタデータテーブルにアップサート
    for video in scanned_videos:
        conn.execute('''
            INSERT INTO video_metadata (video_id, full_path, filename, directory, created, duration)
            VALUES (?, ?, ?, ?, ?, ?)
            ON CONFLICT(video_id) DO UPDATE SET
                full_path=excluded.full_path,
                filename=excluded.filename,
                directory=excluded.directory,
                created=excluded.created,
                duration=excluded.duration
        ''', (video["video_id"], video["full_path"], video["filename"],
              video["directory"], video["created"], video["duration"]))
        progress_status["current"] += 1

    conn.commit()
    conn.close()
    print("動画メタデータの更新と不要レコードの削除が完了しました。")
    load_thumbnail_cache()


# ユーザー管理テーブルの初期化
def init_users():
    conn = get_db_connection()
    # users テーブルがなければ作成
    conn.execute('''
        CREATE TABLE IF NOT EXISTS users (
            username TEXT PRIMARY KEY,
            password_hash TEXT NOT NULL,
            role TEXT NOT NULL DEFAULT 'user'
        )
    ''')
    # デフォルトの admin ユーザーを挿入（なければ）
    cur = conn.execute("SELECT 1 FROM users WHERE username = ?", ("admin",))
    if not cur.fetchone():
        password_hash = generate_password_hash("adminpass")
        conn.execute(
            "INSERT INTO users (username, password_hash, role) VALUES (?, ?, ?)",
            ("admin", password_hash, "admin")
        )
    conn.commit()
    conn.close()

@app.route('/upload', methods=['GET'])
@login_required
def upload_page():
    # アップロード用フォームを表示
    return render_template('upload.html', upload_dirs=UPLOAD_DIRS)

# POST を受け付けて非同期にアップロードを開始
@app.route('/start_upload', methods=['POST'])
@login_required
def start_upload():
    dest_key = request.form['directory']
    dest_dir = UPLOAD_DIRS.get(dest_key)
    if not dest_dir:
        flash("無効なアップロード先です。")
        return redirect(url_for('upload_page'))

    files = request.files.getlist('videos')
    if not files:
        flash("ファイルを選択してください。")
        return redirect(url_for('upload_page'))

    # --- 1) バッチID とタイムスタンプを用意 ---
    batch_id = str(uuid4())
    ts = time.time()

    conn = get_db_connection()
    # --- 2) upload_batches に書き込み ---
    conn.execute('''
        INSERT INTO upload_batches (batch_id, username, directory, count, timestamp)
          VALUES (?, ?, ?, ?, ?)
    ''', (batch_id, current_user.id, dest_key, len(files), ts))

    # --- 3) ファイルを保存しつつ upload_files に書き込み ---
    for f in files:
        original = f.filename
        save_path = UPLOAD_DIRS[dest_key]
        unique = unique_filename(save_path, original)
        f.save(os.path.join(save_path, unique))

        conn.execute('''
            INSERT INTO upload_files (batch_id, filename)
              VALUES (?, ?)
        ''', (batch_id, unique))

    conn.commit()
    conn.close()

    flash(f"{len(files)} 件のアップロードが完了しました。")
    update_video_metadata()
    # アップロード進捗画面へリダイレクト
    return redirect(url_for('upload_progress'))

# 進捗画面を表示する GET ルート
@app.route('/upload_progress')
@login_required
def upload_progress():
    return render_template('upload_progress.html')

# 現在の進捗を JSON で返す API
@app.route('/upload_status')
@login_required
def upload_status():
    total = session.get('upload_total', 0)
    done  = session.get('upload_done',  0)
    return jsonify(total=total, done=done)

def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not current_user.is_authenticated or current_user.role != 'admin':
            abort(403)
        return f(*args, **kwargs)
    return decorated

# ログ一覧
@app.route('/logs')
@login_required
@admin_required
def logs():
    conn = get_db_connection()
    batches = conn.execute('''
      SELECT batch_id, username, directory, count, timestamp
        FROM upload_batches
       ORDER BY timestamp DESC
    ''').fetchall()
    conn.close()
    return render_template('logs.html', batches=batches)

# ログ詳細（バッチ内のファイル名リスト）
@app.route('/logs/<batch_id>')
@login_required
@admin_required
def log_detail(batch_id):
    conn = get_db_connection()
    batch = conn.execute('''
      SELECT batch_id, username, directory, count, timestamp
        FROM upload_batches WHERE batch_id = ?
    ''', (batch_id,)).fetchone()
    files = conn.execute('''
      SELECT filename FROM upload_files WHERE batch_id = ?
    ''', (batch_id,)).fetchall()
    conn.close()
    if not batch:
        abort(404)
    return render_template('log_detail.html', batch=batch, files=files)

init_users()

login_manager = LoginManager()
login_manager.init_app(app)
login_manager.login_view = "login"  # ログインが必要なときにリダイレクトする先

# ユーザークラス（UserMixin を継承）
class User(UserMixin):
    def __init__(self, username, password_hash, role):
        self.id = username  # Flask-Login は id 属性でユーザーを識別します
        self.password_hash = password_hash
        self.role = role

def get_user(username):
    conn = get_db_connection()
    cur = conn.execute("SELECT * FROM users WHERE username = ?", (username,))
    row = cur.fetchone()
    conn.close()
    if row:
        return User(row["username"], row["password_hash"], row["role"])
    return None

@login_manager.user_loader
def load_user(user_id):
    return get_user(user_id)

@app.route('/register', methods=['GET', 'POST'])
def register():
    if request.method == "POST":
        username = request.form.get("username")
        password = request.form.get("password")
        if not username or not password:
            flash("ユーザー名とパスワードを入力してください。")
            return redirect(url_for("register"))
        if get_user(username):
            flash("そのユーザー名は既に使われています。")
            return redirect(url_for("register"))
        # ユーザー名が 'admin' なら role = 'admin'、それ以外は 'user'
        role = "admin" if username.lower() == "admin" else "user"
        password_hash = generate_password_hash(password)
        conn = get_db_connection()
        conn.execute("INSERT INTO users (username, password_hash, role) VALUES (?, ?, ?)", (username, password_hash, role))
        conn.commit()
        conn.close()
        flash("登録が完了しました。ログインしてください。")
        return redirect(url_for("login"))
    return render_template("register.html")

@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == "POST":
        username = request.form.get("username")
        password = request.form.get("password")
        user = get_user(username)
        if user and check_password_hash(user.password_hash, password):
            login_user(user)
            flash("ログインに成功しました。")
            next_url = request.args.get("next") or url_for("index")
            return redirect(next_url)
        else:
            flash("ユーザー名またはパスワードが正しくありません。")
    return render_template("login.html")


@app.route('/logout')
@login_required
def logout():
    logout_user()
    flash("ログアウトしました。")
    return redirect(url_for("login"))

def init_directory_hash_table():
    conn = get_db_connection()
    conn.execute('''
        CREATE TABLE IF NOT EXISTS directory_hash (
            directory TEXT PRIMARY KEY,
            hash_value TEXT NOT NULL
        )
    ''')
    conn.commit()
    conn.close()

init_directory_hash_table()

import hashlib

def compute_directory_hash(directory):
    """指定したディレクトリ内の対象ファイルのパス、更新日時、サイズからハッシュを計算する"""
    hash_obj = hashlib.md5()
    for root, dirs, files in os.walk(directory):
        # 動画ファイルのみ対象とする
        for file in sorted(files):
            if file.lower().endswith(('.mp4', '.avi', '.mkv', '.mov', '.m4a')):
                full_path = os.path.join(root, file)
                try:
                    stat = os.stat(full_path)
                    # パス、最終更新時刻、ファイルサイズを連結して更新
                    hash_obj.update(full_path.encode('utf-8'))
                    hash_obj.update(str(stat.st_mtime).encode('utf-8'))
                    hash_obj.update(str(stat.st_size).encode('utf-8'))
                except Exception as e:
                    print(f"エラー: {full_path} の情報取得に失敗: {e}")
    return hash_obj.hexdigest()

def reset_video_metadata():
    conn = get_db_connection()
    conn.execute("DELETE FROM video_metadata")
    conn.execute("DELETE FROM directory_hash")
    conn.commit()
    conn.close()
    update_video_metadata()

# reset_video_metadata()


# 起動時に初回実行
update_video_metadata()

# APSchedulerの設定
from apscheduler.schedulers.background import BackgroundScheduler
scheduler = BackgroundScheduler()
scheduler.add_job(func=update_video_metadata, trigger="cron", hour=5, minute=0)
scheduler.start()

# Flask終了時にschedulerも停止するための設定
import atexit
atexit.register(lambda: scheduler.shutdown())


if __name__ == '__main__':
    app.run(host='0.0.0.0', debug=True)
