# -*- coding: utf-8 -*-
import logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

import os
import json
import sqlite3
import hashlib
import subprocess
import random
import shutil
import cv2
import numpy as np
from flask import Flask, render_template, request, send_from_directory, abort, url_for, redirect, session, flash, \
    jsonify
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
import queue
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple

DB_LOCK = threading.Lock()

app = Flask(__name__)

# 設定ファイルの管理
CONFIG_FILE = "config.json"


def load_config():
    """設定ファイルを読み込む"""
    default_config = {
        "app": {
            "secret_key": "your_secret_key_change_in_production",
            "debug": True,
            "host": "0.0.0.0",
            "port": 5000
        },
        "video_directories": [
            "/Volumes/4TBMobile/doc/doc",
            "/Volumes/4TBMobile/doc/docFC",
            "/Volumes/4TBMobile/doc/docLi",
            "/Volumes/4TBMobile/media/media",
            "/Volumes/4TBMobile/media/meFc",
            "/Volumes/4TBMobile/media/meLi"
        ],
        "allowed_ips": [
            "127.0.0.1",
            "192.168.2.100",
            "192.168.2.191",
            "192.168.2.190",
            "192.168.2.171"
        ],
        "database": {
            "path": "local.sqlite"
        },
        "analysis": {
            "scene_thumbnails_count": 20,
            "quality_analysis_enabled": True,
            "auto_analysis_enabled": True,
            "analysis_schedule_hour": 5,
            "analysis_schedule_minute": 0
        },
        "thumbnails": {
            "width": 160,
            "height": 90,
            "main_thumbnail_time": "00:00:01"
        },
        "pagination": {
            "videos_per_page": 100
        },
        "paths": {
            "remove_directory_windows": "D:\\remove",
            "remove_directory_unix": "~/remove",
            "video_library_base": "~/video_library"
        },
        "move_destinations": {
            "doc": {"windows": "D:\\doc", "unix": "~/video_library/doc"},
            "me": {"windows": "D:\\me", "unix": "~/video_library/me"},
            "doc/fc": {"windows": "D:\\doc\\fc", "unix": "~/video_library/doc/fc"},
            "doc/li": {"windows": "D:\\doc\\li", "unix": "~/video_library/doc/li"},
            "me/fc": {"windows": "D:\\me\\fc", "unix": "~/video_library/me/fc"},
            "me/li": {"windows": "D:\\me\\li", "unix": "~/video_library/me/li"},
            "as": {"windows": "D:\\as", "unix": "~/video_library/as"},
            "iv": {"windows": "D:\\iv", "unix": "~/video_library/iv"}
        }
    }

    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                config = json.load(f)
                # デフォルト設定とマージ
                for key, value in default_config.items():
                    if key not in config:
                        config[key] = value
                return config
        except Exception as e:
            print(f"設定ファイル読み込みエラー: {e}")
            print("デフォルト設定を使用します")

    # 設定ファイルが存在しない場合はデフォルト設定で作成
    save_config(default_config)
    return default_config


def save_config(config):
    """設定ファイルを保存"""
    try:
        with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=2, ensure_ascii=False)
        return True
    except Exception as e:
        print(f"設定ファイル保存エラー: {e}")
        return False


def get_platform_path(path_config):
    """プラットフォーム別のパスを取得 - 修正版"""
    # path_configが文字列の場合はそのまま返す
    if isinstance(path_config, str):
        return os.path.expanduser(path_config)
    
    # path_configが辞書の場合はプラットフォームに応じて選択
    if isinstance(path_config, dict):
        if os.name == 'nt':  # Windows
            return os.path.expanduser(path_config.get('windows', path_config.get('unix', '')))
        else:  # Unix/Linux/macOS
            return os.path.expanduser(path_config.get('unix', path_config.get('windows', '')))
    
    # その他の場合は文字列化して返す
    return os.path.expanduser(str(path_config))


# 設定を読み込み
config = load_config()

# Flaskアプリの設定
app.secret_key = config['app']['secret_key']
app.jinja_env.globals.update(max=max, min=min)

# 設定値を変数に展開
VIDEO_DIRS = config['video_directories']
DB_PATH = config['database']['path']
ALLOWED_IPS = config['allowed_ips']

# ディレクトリ設定
UPLOAD_DIRS = {
    os.path.basename(d): d
    for d in VIDEO_DIRS
}

# グローバル変数で進捗を保持
progress_status = {"total": 0, "current": 0}

# グローバルキャッシュ（サムネイルのファイル名をセットで保持）
THUMBNAIL_CACHE = set()


# 動画分析システム
@dataclass
class VideoAnalysisResult:
    """動画分析結果を格納するデータクラス"""
    video_id: str
    file_path: str
    duration: float
    resolution: str
    fps: float
    bitrate: int
    codec: str
    audio_codec: str
    file_size: int
    avg_brightness: float
    contrast_score: float
    sharpness_score: float
    quality_score: float
    auto_tags: List[str]
    has_audio: bool
    file_hash: str
    analyzed_at: datetime


class VideoAnalyzer:
    """動画分析を行うクラス"""

    def __init__(self):
        self.analysis_queue = queue.Queue()
        self.is_running = False
        self.is_paused = False
        self.worker_thread = None
        self.current_analysis = {"video_id": None, "progress": 0, "status": "待機中"}

    def start_background_analysis(self):
        """バックグラウンド分析を開始"""
        if not self.is_running:
            self.is_running = True
            self.worker_thread = threading.Thread(target=self._analysis_worker, daemon=True)
            self.worker_thread.start()
            print("バックグラウンド動画分析を開始しました")

    def stop_background_analysis(self):
        """バックグラウンド分析を停止"""
        self.is_running = False
        if self.worker_thread:
            self.worker_thread.join(timeout=5)
        print("バックグラウンド動画分析を停止しました")

    def add_video_for_analysis(self, video_id: str, file_path: str):
        """分析対象の動画をキューに追加"""
        if not self._is_already_analyzed(video_id):
            self.analysis_queue.put((video_id, file_path))
            print(f"分析キューに追加: {file_path}")

    def get_analysis_status(self):
        """現在の分析状況を取得"""
        return {
            "queue_size": self.analysis_queue.qsize(),
            "current_analysis": self.current_analysis,
            "is_running": self.is_running,
            "is_paused": self.is_paused
        }

    def pause_analysis(self):
        """分析を一時停止"""
        self.is_paused = True
        self.current_analysis["status"] = "一時停止中"
        print("動画分析を一時停止しました")

    def resume_analysis(self):
        """分析を再開"""
        self.is_paused = False
        if self.is_running:
            self.current_analysis["status"] = "分析中" if self.current_analysis["video_id"] else "待機中"
            print("動画分析を再開しました")

    def _analysis_worker(self):
        """バックグラウンド分析のワーカー"""
        while self.is_running:
            try:
                # 一時停止中はスキップ
                if self.is_paused:
                    time.sleep(1)
                    continue

                video_id, file_path = self.analysis_queue.get(timeout=5)

                # 一時停止された場合、キューに戻す
                if self.is_paused:
                    self.analysis_queue.put((video_id, file_path))
                    continue

                self.current_analysis = {
                    "video_id": video_id,
                    "progress": 0,
                    "status": "分析中"
                }

                print(f"分析開始: {file_path}")
                result = self.analyze_video(video_id, file_path)

                if result:
                    self._save_analysis_result(result)
                    print(f"分析完了: {file_path}")
                else:
                    print(f"分析失敗: {file_path}")

                self.current_analysis = {
                    "video_id": None,
                    "progress": 0,
                    "status": "待機中" if not self.is_paused else "一時停止中"
                }

            except queue.Empty:
                continue
            except Exception as e:
                print(f"分析中にエラー: {e}")
                self.current_analysis = {
                    "video_id": None,
                    "progress": 0,
                    "status": "エラー"
                }

    def analyze_video(self, video_id: str, file_path: str) -> Optional[VideoAnalysisResult]:
        """動画の包括的分析を実行"""
        try:
            self.current_analysis["progress"] = 10

            # 基本情報の取得
            basic_info = self._get_basic_info(file_path)
            if not basic_info:
                return None

            self.current_analysis["progress"] = 30

            # ファイルハッシュ計算
            file_hash = self._calculate_file_hash(file_path)

            self.current_analysis["progress"] = 50

            # 品質分析
            quality_info = self._analyze_quality(file_path)

            self.current_analysis["progress"] = 70

            # シーンサムネイル生成（新規追加）
            self._generate_scene_thumbnails(file_path, video_id, basic_info['duration'])

            self.current_analysis["progress"] = 85

            # 自動タグ生成
            auto_tags = self._generate_auto_tags(file_path, basic_info['duration'])

            self.current_analysis["progress"] = 90

            # 結果をまとめる
            result = VideoAnalysisResult(
                video_id=video_id,
                file_path=file_path,
                file_hash=file_hash,
                auto_tags=auto_tags,
                analyzed_at=datetime.now(),
                **basic_info,
                **quality_info
            )

            self.current_analysis["progress"] = 100
            return result

        except Exception as e:
            print(f"動画分析エラー ({file_path}): {e}")
            return None

    def _get_basic_info(self, file_path: str) -> Dict:
        """FFprobeを使用して基本情報を取得"""
        try:
            cmd = [
                'ffprobe', '-v', 'quiet', '-print_format', 'json',
                '-show_format', '-show_streams', file_path
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)

            if result.returncode != 0:
                return None

            data = json.loads(result.stdout)
            format_info = data['format']

            # 動画ストリームを探す
            video_stream = None
            audio_stream = None
            for stream in data['streams']:
                if stream['codec_type'] == 'video' and not video_stream:
                    video_stream = stream
                elif stream['codec_type'] == 'audio' and not audio_stream:
                    audio_stream = stream

            if not video_stream:
                return None

            # フレームレート計算
            fps = 0
            if 'r_frame_rate' in video_stream:
                fps_str = video_stream['r_frame_rate']
                if '/' in fps_str:
                    num, den = fps_str.split('/')
                    if int(den) != 0:
                        fps = int(num) / int(den)

            return {
                'duration': float(format_info.get('duration', 0)),
                'resolution': f"{video_stream.get('width', 0)}x{video_stream.get('height', 0)}",
                'fps': fps,
                'bitrate': int(format_info.get('bit_rate', 0)),
                'codec': video_stream.get('codec_name', 'unknown'),
                'audio_codec': audio_stream.get('codec_name', 'none') if audio_stream else 'none',
                'file_size': int(format_info.get('size', 0)),
                'has_audio': audio_stream is not None,
            }

        except Exception as e:
            print(f"基本情報取得エラー: {e}")
            return None

    def _analyze_quality(self, file_path: str) -> Dict:
        """OpenCVを使用して画質分析"""
        try:
            cap = cv2.VideoCapture(file_path)
            if not cap.isOpened():
                return {'quality_score': 0.0, 'avg_brightness': 0.0, 'contrast_score': 0.0, 'sharpness_score': 0.0}

            # サンプルフレームを取得
            frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
            sample_frames = min(5, max(1, frame_count // 20))  # 最大5フレームサンプル

            brightness_values = []
            contrast_values = []
            sharpness_values = []

            for i in range(sample_frames):
                frame_pos = (frame_count // sample_frames) * i
                cap.set(cv2.CAP_PROP_POS_FRAMES, frame_pos)
                ret, frame = cap.read()

                if not ret:
                    continue

                # グレースケール変換
                gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)

                # 明度計算
                brightness = np.mean(gray)
                brightness_values.append(brightness)

                # コントラスト計算（標準偏差）
                contrast = np.std(gray)
                contrast_values.append(contrast)

                # シャープネス計算（ラプラシアンの分散）
                laplacian = cv2.Laplacian(gray, cv2.CV_64F)
                sharpness = laplacian.var()
                sharpness_values.append(sharpness)

            cap.release()

            if not brightness_values:
                return {'quality_score': 0.0, 'avg_brightness': 0.0, 'contrast_score': 0.0, 'sharpness_score': 0.0}

            avg_brightness = np.mean(brightness_values)
            avg_contrast = np.mean(contrast_values)
            avg_sharpness = np.mean(sharpness_values)

            # 品質スコア計算（0-100）
            quality_score = min(100, max(0, (avg_sharpness / 1000 * 50) + (avg_contrast / 50 * 30) + 20))

            return {
                'avg_brightness': float(avg_brightness),
                'contrast_score': float(avg_contrast),
                'sharpness_score': float(avg_sharpness),
                'quality_score': float(quality_score)
            }

        except Exception as e:
            print(f"品質分析エラー: {e}")
            return {'quality_score': 0.0, 'avg_brightness': 0.0, 'contrast_score': 0.0, 'sharpness_score': 0.0}

    def _calculate_file_hash(self, file_path: str) -> str:
        """ファイルのハッシュを計算（重複検出用）"""
        try:
            hash_md5 = hashlib.md5()
            with open(file_path, "rb") as f:
                # 大きなファイルの場合は先頭と末尾のみサンプリング
                file_size = os.path.getsize(file_path)
                if file_size > 100 * 1024 * 1024:  # 100MB以上
                    # 先頭1MB
                    hash_md5.update(f.read(1024 * 1024))
                    # 末尾1MB
                    f.seek(-1024 * 1024, 2)
                    hash_md5.update(f.read(1024 * 1024))
                    # ファイルサイズも含める
                    hash_md5.update(str(file_size).encode())
                else:
                    for chunk in iter(lambda: f.read(4096), b""):
                        hash_md5.update(chunk)
            return hash_md5.hexdigest()
        except Exception as e:
            print(f"ハッシュ計算エラー: {e}")
            return ""

    def _generate_scene_thumbnails(self, video_path: str, video_id: str, duration: float, num_scenes: int = None):
        """動画を21分割して最初の20枚のシーンサムネイル生成"""
        if num_scenes is None:
            num_scenes = config['analysis']['scene_thumbnails_count']

        scenes_dir = os.path.join("static", "scenes")
        os.makedirs(scenes_dir, exist_ok=True)

        if duration <= 0:
            return

        try:
            # 既存のサムネイルをチェック
            all_exist = True
            for i in range(num_scenes):
                thumb_filename = f"{video_id}_scene_{i}.jpg"
                thumb_filepath = os.path.join(scenes_dir, thumb_filename)
                if not os.path.exists(thumb_filepath):
                    all_exist = False
                    break

            # 全てのサムネイルが既に存在する場合はスキップ
            if all_exist:
                print(f"シーンサムネイル既存: {video_id} ({num_scenes}枚)")
                return

            # 21分割して最初の20枚を生成（最後の1枚は除外）
            total_segments = num_scenes + 1  # 21分割
            thumb_width = config['thumbnails']['width']
            thumb_height = config['thumbnails']['height']

            for i in range(num_scenes):  # 0-19の20枚
                # タイムスタンプ計算：全体を21分割したときの各セグメントの開始点
                timestamp = duration * i / total_segments
                thumb_filename = f"{video_id}_scene_{i}.jpg"
                thumb_filepath = os.path.join(scenes_dir, thumb_filename)

                if not os.path.exists(thumb_filepath):
                    if os.name == 'nt':
                        video_path_safe = get_short_path_name(video_path)
                    else:
                        video_path_safe = video_path

                    cmd = [
                        "ffmpeg", "-ss", str(timestamp), "-i", video_path_safe,
                        "-vframes", "1", "-vf", f"scale={thumb_width}:{thumb_height}", "-y", thumb_filepath
                    ]
                    result = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
                    if result.returncode == 0:
                        print(f"生成: {thumb_filename} at {timestamp:.2f}s")
                    else:
                        print(f"生成失敗: {thumb_filename}")

        except Exception as e:
            print(f"シーンサムネイル生成エラー: {e}")

    def _generate_auto_tags(self, file_path: str, duration: float) -> List[str]:
        """ファイル名と基本情報からタグを自動生成"""
        tags = []
        filename = os.path.basename(file_path).lower()

        # 時間ベースのタグ
        if duration < 60:
            tags.append("ショート")
        elif duration < 600:
            tags.append("短編")
        elif duration < 3600:
            tags.append("中編")
        else:
            tags.append("長編")

        # ファイル名からのキーワード抽出
        keywords = [
            (['sport', 'sports', 'football', 'soccer', 'baseball'], 'スポーツ'),
            (['music', 'song', 'concert', 'live'], '音楽'),
            (['game', 'gaming', 'play'], 'ゲーム'),
            (['movie', 'film', 'cinema'], '映画'),
            (['anime', 'animation'], 'アニメ'),
            (['news', 'report'], 'ニュース'),
            (['tutorial', 'howto', 'guide'], 'チュートリアル'),
            (['vlog', 'daily', 'life'], 'vlog'),
            (['travel', 'trip', 'vacation'], '旅行'),
            (['food', 'cooking', 'recipe'], '料理'),
            (['nature', 'landscape', 'outdoor'], '自然'),
            (['comedy', 'funny', 'humor'], 'コメディ'),
            (['drama', 'story'], 'ドラマ'),
            (['documentary', 'doc'], 'ドキュメンタリー')
        ]

        for keyword_list, tag in keywords:
            if any(keyword in filename for keyword in keyword_list):
                tags.append(tag)

        # 解像度ベースのタグ
        if 'hd' in filename or '720p' in filename:
            tags.append('HD')
        elif 'fhd' in filename or '1080p' in filename:
            tags.append('フルHD')
        elif '4k' in filename or '2160p' in filename:
            tags.append('4K')

        return tags

    def _is_already_analyzed(self, video_id: str) -> bool:
        """既に分析済みかチェック"""
        conn = get_db_connection()
        cursor = conn.execute('SELECT 1 FROM video_analysis WHERE video_id = ?', (video_id,))
        result = cursor.fetchone() is not None
        conn.close()
        return result

    def _save_analysis_result(self, result: VideoAnalysisResult):
        """分析結果をデータベースに保存"""
        with DB_LOCK:
            conn = get_db_connection()
            conn.execute('''
                INSERT OR REPLACE INTO video_analysis (
                    video_id, file_path, duration, resolution, fps, bitrate,
                    codec, audio_codec, file_size, avg_brightness, contrast_score,
                    sharpness_score, quality_score, auto_tags, has_audio,
                    file_hash, analyzed_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                result.video_id, result.file_path, result.duration,
                result.resolution, result.fps, result.bitrate,
                result.codec, result.audio_codec, result.file_size,
                result.avg_brightness, result.contrast_score, result.sharpness_score,
                result.quality_score, json.dumps(result.auto_tags), result.has_audio,
                result.file_hash, result.analyzed_at
            ))
            conn.commit()
            conn.close()


# グローバルアナライザーインスタンス
video_analyzer = VideoAnalyzer()


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


# DB初期化：動画分析テーブルを追加
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
    # 動画分析結果テーブル
    conn.execute('''
        CREATE TABLE IF NOT EXISTS video_analysis (
            video_id TEXT PRIMARY KEY,
            file_path TEXT,
            duration REAL,
            resolution TEXT,
            fps REAL,
            bitrate INTEGER,
            codec TEXT,
            audio_codec TEXT,
            file_size INTEGER,
            avg_brightness REAL,
            contrast_score REAL,
            sharpness_score REAL,
            quality_score REAL,
            auto_tags TEXT,
            has_audio BOOLEAN,
            file_hash TEXT,
            analyzed_at TIMESTAMP
        )
    ''')
    # インデックス作成
    conn.execute('CREATE INDEX IF NOT EXISTS idx_file_hash ON video_analysis(file_hash)')
    conn.execute('CREATE INDEX IF NOT EXISTS idx_quality_score ON video_analysis(quality_score)')
    conn.commit()
    conn.close()


init_db()  # サーバー起動時にDB初期化


# グローバル進捗管理
class DuplicateProgress:
    def __init__(self):
        self.lock = threading.Lock()
        self.current_task = None
        self.progress = 0
        self.total = 0
        self.current_file = ""
        self.status = "idle"  # idle, running, completed, error
        self.error_message = ""
        self.start_time = None
        self.end_time = None
        self.removed_count = 0
        self.error_count = 0
        self.details = []

    def start_task(self, task_name, total_items):
        with self.lock:
            self.current_task = task_name
            self.progress = 0
            self.total = total_items
            self.current_file = ""
            self.status = "running"
            self.error_message = ""
            self.start_time = datetime.now()
            self.end_time = None
            self.removed_count = 0
            self.error_count = 0
            self.details = []

    def update_progress(self, progress, current_file="", detail=""):
        with self.lock:
            self.progress = progress
            self.current_file = current_file
            if detail:
                self.details.append({
                    'time': datetime.now().strftime('%H:%M:%S'),
                    'message': detail
                })
                # 最新50件のみ保持
                if len(self.details) > 50:
                    self.details = self.details[-50:]

    def increment_removed(self):
        with self.lock:
            self.removed_count += 1

    def increment_error(self):
        with self.lock:
            self.error_count += 1

    def complete_task(self, status="completed", error_message=""):
        with self.lock:
            self.status = status
            self.error_message = error_message
            self.end_time = datetime.now()
            self.progress = self.total

    def get_status(self):
        with self.lock:
            elapsed_time = None
            if self.start_time:
                end_time = self.end_time or datetime.now()
                elapsed_time = (end_time - self.start_time).total_seconds()

            return {
                'current_task': self.current_task,
                'progress': self.progress,
                'total': self.total,
                'current_file': self.current_file,
                'status': self.status,
                'error_message': self.error_message,
                'removed_count': self.removed_count,
                'error_count': self.error_count,
                'elapsed_time': elapsed_time,
                'details': self.details[-10:] if self.details else []  # 最新10件
            }

# グローバル進捗インスタンス
duplicate_progress = DuplicateProgress()

# 設定管理ルート
@app.route('/settings')
@login_required
def settings_page():
    """設定管理ページ"""
    return render_template('settings.html', config=config)


@app.route('/settings/save', methods=['POST'])
@login_required
def save_settings():
    """設定を保存"""
    global config, VIDEO_DIRS, DB_PATH, ALLOWED_IPS, UPLOAD_DIRS

    try:
        # フォームデータから設定を更新
        new_config = config.copy()

        # アプリケーション設定
        new_config['app']['secret_key'] = request.form.get('secret_key', config['app']['secret_key'])
        new_config['app']['debug'] = request.form.get('debug') == 'on'
        new_config['app']['host'] = request.form.get('host', config['app']['host'])
        new_config['app']['port'] = int(request.form.get('port', config['app']['port']))

        # 動画ディレクトリ
        video_dirs = request.form.get('video_directories', '').strip()
        if video_dirs:
            new_config['video_directories'] = [d.strip() for d in video_dirs.split('\n') if d.strip()]

        # 許可IP
        allowed_ips = request.form.get('allowed_ips', '').strip()
        if allowed_ips:
            new_config['allowed_ips'] = [ip.strip() for ip in allowed_ips.split('\n') if ip.strip()]

        # データベース設定
        new_config['database']['path'] = request.form.get('database_path', config['database']['path'])

        # 分析設定
        new_config['analysis']['scene_thumbnails_count'] = int(
            request.form.get('scene_thumbnails_count', config['analysis']['scene_thumbnails_count']))
        new_config['analysis']['quality_analysis_enabled'] = request.form.get('quality_analysis_enabled') == 'on'
        new_config['analysis']['auto_analysis_enabled'] = request.form.get('auto_analysis_enabled') == 'on'
        new_config['analysis']['analysis_schedule_hour'] = int(
            request.form.get('analysis_schedule_hour', config['analysis']['analysis_schedule_hour']))
        new_config['analysis']['analysis_schedule_minute'] = int(
            request.form.get('analysis_schedule_minute', config['analysis']['analysis_schedule_minute']))

        # サムネイル設定
        new_config['thumbnails']['width'] = int(request.form.get('thumbnail_width', config['thumbnails']['width']))
        new_config['thumbnails']['height'] = int(request.form.get('thumbnail_height', config['thumbnails']['height']))
        new_config['thumbnails']['main_thumbnail_time'] = request.form.get('main_thumbnail_time',
                                                                           config['thumbnails']['main_thumbnail_time'])

        # ページネーション設定
        new_config['pagination']['videos_per_page'] = int(
            request.form.get('videos_per_page', config['pagination']['videos_per_page']))

        # パス設定
        new_config['paths']['remove_directory_windows'] = request.form.get('remove_directory_windows',
                                                                           config['paths']['remove_directory_windows'])
        new_config['paths']['remove_directory_unix'] = request.form.get('remove_directory_unix',
                                                                        config['paths']['remove_directory_unix'])
        new_config['paths']['video_library_base'] = request.form.get('video_library_base',
                                                                     config['paths']['video_library_base'])

        # 移動先設定
        for dest in new_config['move_destinations']:
            new_config['move_destinations'][dest]['windows'] = request.form.get(f'move_dest_{dest}_windows',
                                                                                new_config['move_destinations'][dest][
                                                                                    'windows'])
            new_config['move_destinations'][dest]['unix'] = request.form.get(f'move_dest_{dest}_unix',
                                                                             new_config['move_destinations'][dest][
                                                                                 'unix'])

        # 設定を保存
        if save_config(new_config):
            # グローバル変数を更新
            config = new_config
            VIDEO_DIRS = config['video_directories']
            DB_PATH = config['database']['path']
            ALLOWED_IPS = config['allowed_ips']
            UPLOAD_DIRS = {os.path.basename(d): d for d in VIDEO_DIRS}

            flash('設定を保存しました。一部の設定はサーバー再起動後に反映されます。', 'success')
        else:
            flash('設定の保存に失敗しました。', 'error')

    except Exception as e:
        flash(f'設定保存中にエラーが発生しました: {str(e)}', 'error')

    return redirect(url_for('settings_page'))


@app.route('/settings/reset', methods=['POST'])
@login_required
def reset_settings():
    """設定をデフォルトにリセット"""
    global config, VIDEO_DIRS, DB_PATH, ALLOWED_IPS, UPLOAD_DIRS

    try:
        # デフォルト設定を再生成
        default_config = {
            "app": {
                "secret_key": "your_secret_key_change_in_production",
                "debug": True,
                "host": "0.0.0.0",
                "port": 5000
            },
            "video_directories": [
                "/Volumes/4TBMobile/doc/doc",
                "/Volumes/4TBMobile/doc/docFC",
                "/Volumes/4TBMobile/doc/docLi",
                "/Volumes/4TBMobile/media/media",
                "/Volumes/4TBMobile/media/meFc",
                "/Volumes/4TBMobile/media/meLi"
            ],
            "allowed_ips": [
                "127.0.0.1",
                "192.168.2.100",
                "192.168.2.191",
                "192.168.2.190",
                "192.168.2.171"
            ],
            "database": {
                "path": "local.sqlite"
            },
            "analysis": {
                "scene_thumbnails_count": 20,
                "quality_analysis_enabled": True,
                "auto_analysis_enabled": True,
                "analysis_schedule_hour": 5,
                "analysis_schedule_minute": 0
            },
            "thumbnails": {
                "width": 160,
                "height": 90,
                "main_thumbnail_time": "00:00:01"
            },
            "pagination": {
                "videos_per_page": 100
            },
            "paths": {
                "remove_directory_windows": "D:\\remove",
                "remove_directory_unix": "~/remove",
                "video_library_base": "~/video_library"
            },
            "move_destinations": {
                "doc": {"windows": "D:\\doc", "unix": "~/video_library/doc"},
                "me": {"windows": "D:\\me", "unix": "~/video_library/me"},
                "doc/fc": {"windows": "D:\\doc\\fc", "unix": "~/video_library/doc/fc"},
                "doc/li": {"windows": "D:\\doc\\li", "unix": "~/video_library/doc/li"},
                "me/fc": {"windows": "D:\\me\\fc", "unix": "~/video_library/me/fc"},
                "me/li": {"windows": "D:\\me\\li", "unix": "~/video_library/me/li"},
                "as": {"windows": "D:\\as", "unix": "~/video_library/as"},
                "iv": {"windows": "D:\\iv", "unix": "~/video_library/iv"}
            }
        }

        if save_config(default_config):
            # グローバル変数を更新
            config = default_config
            VIDEO_DIRS = config['video_directories']
            DB_PATH = config['database']['path']
            ALLOWED_IPS = config['allowed_ips']
            UPLOAD_DIRS = {os.path.basename(d): d for d in VIDEO_DIRS}

            flash('設定をデフォルトにリセットしました。サーバーを再起動してください。', 'success')
        else:
            flash('設定のリセットに失敗しました。', 'error')
    except Exception as e:
        flash(f'設定リセット中にエラーが発生しました: {str(e)}', 'error')

    return redirect(url_for('settings_page'))


@app.route('/analysis')
@login_required
def analysis_dashboard():
    """動画分析ダッシュボード"""
    conn = get_db_connection()

    try:
        # 分析統計を取得
        stats = conn.execute('''
            SELECT 
                COUNT(*) as total_analyzed,
                AVG(quality_score) as avg_quality,
                COUNT(CASE WHEN quality_score < 30 THEN 1 END) as low_quality,
                COUNT(CASE WHEN has_audio = 0 THEN 1 END) as no_audio,
                COUNT(DISTINCT file_hash) as unique_files
            FROM video_analysis
        ''').fetchone()

        # 最近の分析結果
        recent_analysis = conn.execute('''
            SELECT va.*, vm.filename 
            FROM video_analysis va
            LEFT JOIN video_metadata vm ON va.video_id = vm.video_id
            ORDER BY va.analyzed_at DESC 
            LIMIT 10
        ''').fetchall()

        # 品質分布
        quality_distribution = conn.execute('''
            SELECT 
                CASE 
                    WHEN quality_score < 30 THEN '低品質'
                    WHEN quality_score < 60 THEN '普通'
                    WHEN quality_score < 80 THEN '高品質'
                    ELSE '最高品質'
                END as quality_range,
                COUNT(*) as count
            FROM video_analysis
            GROUP BY quality_range
        ''').fetchall()

    except Exception as e:
        print(f"分析ダッシュボードでエラー: {e}")
        stats = None
        recent_analysis = []
        quality_distribution = []
    finally:
        conn.close()

    # 分析状況
    analysis_status = video_analyzer.get_analysis_status()

    return render_template('analysis_dashboard.html',
                           stats=dict(stats) if stats else {},
                           recent_analysis=recent_analysis,
                           quality_distribution=quality_distribution,
                           analysis_status=analysis_status)


@app.route('/analysis/reset', methods=['POST'])
@login_required
def reset_analysis():
    """全ての分析結果をリセット"""
    try:
        with DB_LOCK:
            conn = get_db_connection()

            # 分析データをクリア
            conn.execute('DELETE FROM video_analysis')

            # シーンサムネイルファイルを削除
            scenes_dir = os.path.join("static", "scenes")
            if os.path.exists(scenes_dir):
                import shutil
                shutil.rmtree(scenes_dir)
                os.makedirs(scenes_dir, exist_ok=True)

            conn.commit()
            conn.close()

        flash("全ての分析結果をリセットしました。再分析を開始してください。")

    except Exception as e:
        flash(f"リセット中にエラーが発生しました: {e}")
        print(f"分析リセットエラー: {e}")

    return redirect(url_for('analysis_dashboard'))


@app.route('/analysis/reset_single/<video_id>', methods=['POST'])
@login_required
def reset_single_analysis(video_id):
    """個別動画の分析結果をリセット"""
    try:
        with DB_LOCK:
            conn = get_db_connection()

            # 個別の分析データをクリア
            conn.execute('DELETE FROM video_analysis WHERE video_id = ?', (video_id,))

            # 個別のシーンサムネイルファイルを削除
            scenes_dir = os.path.join("static", "scenes")
            if os.path.exists(scenes_dir):
                for i in range(20):
                    thumb_file = os.path.join(scenes_dir, f"{video_id}_scene_{i}.jpg")
                    if os.path.exists(thumb_file):
                        os.remove(thumb_file)

            conn.commit()
            conn.close()

        # 再分析をキューに追加
        videos = get_video_list()
        video = next((v for v in videos if v["id"] == video_id), None)
        if video:
            video_analyzer.add_video_for_analysis(video_id, video["full_path"])
            flash(f"動画の分析結果をリセットし、再分析をキューに追加しました。")
        else:
            flash("動画が見つかりませんでした。")

    except Exception as e:
        flash(f"リセット中にエラーが発生しました: {e}")
        print(f"個別分析リセットエラー: {e}")

    return redirect(request.referrer or url_for('analysis_dashboard'))


@app.route('/analysis/start', methods=['POST'])
@login_required
def start_analysis():
    """全動画の分析を開始"""
    videos = get_video_list()
    count = 0

    for video in videos:
        video_analyzer.add_video_for_analysis(video['id'], video['full_path'])
        count += 1

    flash(f"{count}件の動画を分析キューに追加しました。")
    return redirect(url_for('analysis_dashboard'))


@app.route('/analysis/pause', methods=['POST'])
@login_required
def pause_analysis():
    """分析を一時停止"""
    video_analyzer.pause_analysis()
    flash("動画分析を一時停止しました。")
    return redirect(url_for('analysis_dashboard'))


@app.route('/analysis/resume', methods=['POST'])
@login_required
def resume_analysis():
    """分析を再開"""
    video_analyzer.resume_analysis()
    flash("動画分析を再開しました。")
    return redirect(url_for('analysis_dashboard'))


@app.route('/analysis/status')
@login_required
def analysis_status():
    """分析状況をJSONで返す"""
    return jsonify(video_analyzer.get_analysis_status())


@app.route('/duplicates')
@login_required
def duplicates_page():
    """重複動画の管理ページ - 改良版"""
    conn = get_db_connection()

    try:
        # ハッシュが同じ動画を検索
        duplicates = conn.execute('''
            SELECT 
                va.file_hash,
                COUNT(*) as count,
                GROUP_CONCAT(va.video_id) as video_ids,
                GROUP_CONCAT(va.file_path) as file_paths,
                GROUP_CONCAT(va.file_size) as file_sizes,
                GROUP_CONCAT(va.quality_score) as quality_scores,
                GROUP_CONCAT(vm.filename) as filenames,
                GROUP_CONCAT(vm.created) as created_dates
            FROM video_analysis va
            LEFT JOIN video_metadata vm ON va.video_id = vm.video_id
            WHERE va.file_hash != '' AND va.file_hash IS NOT NULL
            GROUP BY va.file_hash
            HAVING COUNT(*) > 1
            ORDER BY COUNT(*) DESC, va.file_hash
        ''').fetchall()

        # 重複グループを整理
        duplicate_groups = []
        total_duplicates = 0
        
        for dup in duplicates:
            video_ids = dup['video_ids'].split(',')
            file_paths = dup['file_paths'].split(',')
            file_sizes = [int(s) for s in dup['file_sizes'].split(',') if s]
            quality_scores = [float(s) for s in dup['quality_scores'].split(',') if s]
            filenames = dup['filenames'].split(',')
            created_dates = [float(d) if d else 0 for d in dup['created_dates'].split(',')]

            group = {
                'hash': dup['file_hash'],
                'count': dup['count'],
                'videos': []
            }

            for i in range(len(video_ids)):
                # サムネイル処理
                thumb_filename = f"{video_ids[i]}.jpg"
                thumb_path = os.path.join("static", "thumbnails", thumb_filename)

                if thumb_filename not in THUMBNAIL_CACHE and i < len(file_paths) and os.path.exists(file_paths[i]):
                    try:
                        generate_thumbnail(file_paths[i], thumb_path)
                        THUMBNAIL_CACHE.add(thumb_filename)
                    except Exception as e:
                        print(f"サムネイル生成エラー ({file_paths[i]}): {e}")

                group['videos'].append({
                    'video_id': video_ids[i],
                    'file_path': file_paths[i] if i < len(file_paths) else '',
                    'filename': filenames[i] if i < len(filenames) else '',
                    'file_size': file_sizes[i] if i < len(file_sizes) else 0,
                    'quality_score': quality_scores[i] if i < len(quality_scores) else 0,
                    'created': created_dates[i] if i < len(created_dates) else 0,
                    'thumb': thumb_filename
                })

            # 品質スコア順でソート（高品質が先頭）
            group['videos'].sort(key=lambda x: x['quality_score'], reverse=True)
            duplicate_groups.append(group)
            total_duplicates += dup['count']

    except Exception as e:
        print(f"重複動画取得エラー: {e}")
        duplicate_groups = []
        total_duplicates = 0
    finally:
        conn.close()

    return render_template('duplicates.html', 
                         duplicate_groups=duplicate_groups,
                         total_duplicates=total_duplicates)


@app.template_filter('datetimeformat')
def datetime_format_filter(value, format='%Y-%m-%d %H:%M:%S'):
    """Format a datetime object or string"""
    if value is None:
        return ""

    try:
        # If it's already a datetime object
        if hasattr(value, 'strftime'):
            return value.strftime(format)

        # If it's a string, try to parse it
        if isinstance(value, str):
            # Try ISO format first
            try:
                dt = datetime.fromisoformat(value.replace('Z', '+00:00'))
                return dt.strftime(format)
            except ValueError:
                # Try other common formats
                for fmt in ['%Y-%m-%d %H:%M:%S.%f', '%Y-%m-%d %H:%M:%S', '%Y-%m-%d']:
                    try:
                        dt = datetime.strptime(value, fmt)
                        return dt.strftime(format)
                    except ValueError:
                        continue
                return value  # Return original if can't parse

        # If it's a timestamp (float)
        if isinstance(value, (int, float)):
            dt = datetime.fromtimestamp(value)
            return dt.strftime(format)

        return str(value)
    except Exception as e:
        print(f"Datetime formatting error: {e}")
        return str(value) if value else ""

@app.route('/duplicates/resolve', methods=['POST'])
@login_required
def resolve_duplicates():
    """重複動画の解決 - 直接削除対応版"""
    data = request.get_json()
    keep_video_id = data.get('keep_video_id')
    remove_video_ids = data.get('remove_video_ids', [])
    delete_permanently = data.get('delete_permanently', False)  # 新しいオプション

    if not keep_video_id or not remove_video_ids:
        return jsonify({'success': False, 'message': '無効なパラメータです'})

    # 削除対象の動画情報を取得
    videos = get_video_list()
    video_dict = {v['id']: v for v in videos}

    # 保持する動画が存在するか確認
    if keep_video_id not in video_dict:
        return jsonify({'success': False, 'message': '保持する動画が見つかりません'})

    removed_count = 0
    error_messages = []

    # 進捗開始
    task_name = "完全削除" if delete_permanently else "移動削除"
    duplicate_progress.start_task(f"重複動画{task_name}", len(remove_video_ids))

    # DB_LOCKを使用してトランザクション処理
    with DB_LOCK:
        conn = get_db_connection()
        try:
            # トランザクション開始
            conn.execute('BEGIN')
            
            for index, video_id in enumerate(remove_video_ids):
                duplicate_progress.update_progress(
                    index, 
                    f"処理中: {video_id}", 
                    f"動画 {index + 1}/{len(remove_video_ids)} を処理中"
                )
                
                if video_id in video_dict and video_id != keep_video_id:
                    video = video_dict[video_id]
                    
                    try:
                        if delete_permanently:
                            # 完全削除
                            if os.path.exists(video['full_path']):
                                os.remove(video['full_path'])
                                duplicate_progress.update_progress(
                                    index, 
                                    video['filename'], 
                                    f"ファイル完全削除: {video['filename']}"
                                )
                            else:
                                duplicate_progress.update_progress(
                                    index, 
                                    video['filename'], 
                                    f"ファイルが見つかりません: {video['filename']}"
                                )
                                error_messages.append(f"ファイルが見つかりません: {video['filename']}")
                                duplicate_progress.increment_error()
                                continue
                        else:
                            # 移動削除（既存の処理）
                            if os.name == 'nt':  # Windows
                                remove_dir_config = config['paths']['remove_directory_windows']
                            else:  # macOS/Linux
                                remove_dir_config = config['paths']['remove_directory_unix']
                            
                            remove_dir = os.path.expanduser(remove_dir_config)
                            
                            # ディレクトリが存在しない場合は作成
                            try:
                                os.makedirs(remove_dir, exist_ok=True)
                            except Exception as e:
                                error_messages.append(f"削除ディレクトリ作成失敗 ({remove_dir}): {str(e)}")
                                duplicate_progress.increment_error()
                                continue

                            dest_path = os.path.join(remove_dir, video['filename'])

                            # ファイルが存在するか確認
                            if not os.path.exists(video['full_path']):
                                error_messages.append(f"ファイルが見つかりません: {video['filename']}")
                                duplicate_progress.increment_error()
                                continue

                            # 同名ファイルがある場合は一意な名前を生成
                            if os.path.exists(dest_path):
                                base, ext = os.path.splitext(video['filename'])
                                counter = 1
                                while os.path.exists(dest_path):
                                    dest_path = os.path.join(remove_dir, f"{base}_{counter}{ext}")
                                    counter += 1

                            # ファイルを移動
                            shutil.move(video['full_path'], dest_path)
                            duplicate_progress.update_progress(
                                index, 
                                video['filename'], 
                                f"ファイル移動: {video['filename']} -> {os.path.basename(dest_path)}"
                            )
                        
                        # データベースからも削除
                        conn.execute('DELETE FROM video_metadata WHERE video_id = ?', (video_id,))
                        conn.execute('DELETE FROM video_data WHERE video_id = ?', (video_id,))
                        conn.execute('DELETE FROM video_analysis WHERE video_id = ?', (video_id,))
                        conn.execute('DELETE FROM view_history WHERE video_id = ?', (video_id,))
                        conn.execute('DELETE FROM user_favorites WHERE video_id = ?', (video_id,))

                        # サムネイルファイルも削除
                        thumb_filename = f"{video_id}.jpg"
                        thumb_path = os.path.join("static", "thumbnails", thumb_filename)
                        if os.path.exists(thumb_path):
                            try:
                                os.remove(thumb_path)
                                THUMBNAIL_CACHE.discard(thumb_filename)
                            except Exception as e:
                                print(f"サムネイル削除失敗: {thumb_path}, エラー: {e}")

                        # シーンサムネイルも削除
                        scenes_dir = os.path.join("static", "scenes")
                        scene_count = config.get('analysis', {}).get('scene_thumbnails_count', 20)
                        for i in range(scene_count):
                            scene_file = os.path.join(scenes_dir, f"{video_id}_scene_{i}.jpg")
                            if os.path.exists(scene_file):
                                try:
                                    os.remove(scene_file)
                                except Exception as e:
                                    print(f"シーンサムネイル削除失敗: {scene_file}, エラー: {e}")

                        removed_count += 1
                        duplicate_progress.increment_removed()
                        duplicate_progress.update_progress(
                            index + 1, 
                            video['filename'], 
                            f"削除完了: {video['filename']}"
                        )
                        
                    except Exception as e:
                        error_message = f"{video['filename']}: {str(e)}"
                        error_messages.append(error_message)
                        duplicate_progress.increment_error()
                        duplicate_progress.update_progress(
                            index, 
                            video['filename'], 
                            f"エラー: {video['filename']} - {str(e)}"
                        )

            # トランザクションをコミット
            conn.commit()
            duplicate_progress.update_progress(len(remove_video_ids), "", "データベース更新完了")
            
        except Exception as e:
            # エラーが発生した場合はロールバック
            conn.rollback()
            error_message = f'データベース処理でエラーが発生しました: {str(e)}'
            duplicate_progress.complete_task("error", error_message)
            return jsonify({
                'success': False,
                'message': error_message
            })
        finally:
            conn.close()

    # 進捗完了
    if removed_count > 0:
        duplicate_progress.complete_task("completed")
    else:
        duplicate_progress.complete_task("error", "削除対象が見つかりませんでした")

    # 結果メッセージの作成
    action_type = "完全削除" if delete_permanently else "移動削除"
    if removed_count > 0:
        message = f'{removed_count}件の重複動画を{action_type}しました'
        if error_messages:
            message += f'。エラー: {"; ".join(error_messages[:3])}'
            if len(error_messages) > 3:
                message += f'...他{len(error_messages) - 3}件'
    else:
        if error_messages:
            message = f'{action_type}に失敗しました。エラー: {"; ".join(error_messages[:3])}'
        else:
            message = '削除対象が見つかりませんでした'

    return jsonify({
        'success': removed_count > 0,
        'message': message,
        'removed_count': removed_count,
        'error_count': len(error_messages),
        'delete_type': action_type
    })

@app.route('/duplicates/bulk_resolve', methods=['POST'])
@login_required
def bulk_resolve_duplicates():
    """一括重複解決 - 進捗表示対応版"""
    data = request.get_json()
    strategy = data.get('strategy')
    group_hashes = data.get('group_hashes', [])
    delete_permanently = data.get('delete_permanently', False)

    if not strategy or not group_hashes:
        return jsonify({'success': False, 'message': '無効なパラメータです'})

    def bulk_resolve_background():
        """バックグラウンドで一括解決を実行"""
        try:
            action_type = "完全削除" if delete_permanently else "移動削除"
            duplicate_progress.start_task(f"一括{action_type}", len(group_hashes))

            # 重複グループの取得
            conn = get_db_connection()
            try:
                placeholders = ','.join(['?' for _ in group_hashes])
                query = f'''
                    SELECT 
                        va.file_hash,
                        va.video_id,
                        va.file_path,
                        va.file_size,
                        va.quality_score,
                        vm.filename,
                        vm.created
                    FROM video_analysis va
                    LEFT JOIN video_metadata vm ON va.video_id = vm.video_id
                    WHERE va.file_hash IN ({placeholders}) AND va.file_hash != '' AND va.file_hash IS NOT NULL
                    ORDER BY va.file_hash, vm.created
                '''
                
                duplicates = conn.execute(query, group_hashes).fetchall()
                
            except Exception as e:
                duplicate_progress.complete_task("error", f'データベースエラー: {str(e)}')
                return
            finally:
                conn.close()

            if not duplicates:
                duplicate_progress.complete_task("error", "重複動画が見つかりません")
                return

            # ハッシュ別にグループ化
            groups = {}
            for dup in duplicates:
                hash_value = dup['file_hash']
                if hash_value not in groups:
                    groups[hash_value] = []
                groups[hash_value].append(dict(dup))

            total_removed = 0
            total_kept = 0
            error_messages = []

            # 各グループを処理
            for group_index, (hash_value, videos) in enumerate(groups.items()):
                duplicate_progress.update_progress(
                    group_index, 
                    f"グループ {group_index + 1}/{len(groups)}", 
                    f"グループ {hash_value[:8]}... を処理中"
                )

                if len(videos) < 2:
                    continue

                try:
                    # 戦略に応じて保持する動画を決定
                    keep_video = None
                    
                    if strategy == 'newest':
                        keep_video = max(videos, key=lambda x: x['created'] or 0)
                    elif strategy == 'oldest':
                        keep_video = min(videos, key=lambda x: x['created'] or float('inf'))
                    elif strategy == 'largest':
                        keep_video = max(videos, key=lambda x: x['file_size'] or 0)
                    elif strategy == 'smallest':
                        keep_video = min(videos, key=lambda x: x['file_size'] or float('inf'))
                    elif strategy == 'highest_quality':
                        keep_video = max(videos, key=lambda x: x['quality_score'] or 0)
                    elif strategy == 'lowest_quality':
                        keep_video = min(videos, key=lambda x: x['quality_score'] or float('inf'))

                    if not keep_video:
                        error_messages.append(f"保持する動画を決定できませんでした (hash: {hash_value[:8]}...)")
                        duplicate_progress.increment_error()
                        continue

                    # 削除対象を決定
                    remove_videos = [v for v in videos if v['video_id'] != keep_video['video_id']]
                    
                    if not remove_videos:
                        continue

                    duplicate_progress.update_progress(
                        group_index, 
                        keep_video['filename'], 
                        f"保持: {keep_video['filename']}, 削除: {len(remove_videos)}件"
                    )

                    # 削除処理を実行
                    result_data = {
                        'keep_video_id': keep_video['video_id'],
                        'remove_video_ids': [v['video_id'] for v in remove_videos],
                        'delete_permanently': delete_permanently
                    }

                    # 既存の削除機能を再利用
                    with app.test_request_context(
                        method='POST',
                        json=result_data,
                        headers={'Content-Type': 'application/json'}
                    ):
                        try:
                            from flask import request as flask_request
                            
                            original_get_json = flask_request.get_json
                            flask_request.get_json = lambda: result_data
                            
                            result = resolve_duplicates()
                            result_json = result.get_json()
                            
                            flask_request.get_json = original_get_json
                            
                            if result_json.get('success'):
                                removed_count = result_json.get('removed_count', 0)
                                total_removed += removed_count
                                total_kept += 1
                                duplicate_progress.update_progress(
                                    group_index + 1, 
                                    keep_video['filename'], 
                                    f"グループ完了: {removed_count}件削除"
                                )
                            else:
                                error_msg = f"削除失敗 (hash: {hash_value[:8]}...): {result_json.get('message', '不明なエラー')}"
                                error_messages.append(error_msg)
                                duplicate_progress.increment_error()
                                
                        except Exception as e:
                            error_msg = f"処理エラー (hash: {hash_value[:8]}...): {str(e)}"
                            error_messages.append(error_msg)
                            duplicate_progress.increment_error()

                except Exception as e:
                    error_msg = f"グループ処理エラー (hash: {hash_value[:8]}...): {str(e)}"
                    error_messages.append(error_msg)
                    duplicate_progress.increment_error()

            # 完了
            strategy_names = {
                'newest': '最新ファイルを保持',
                'oldest': '最古ファイルを保持', 
                'largest': '最大サイズを保持',
                'smallest': '最小サイズを保持',
                'highest_quality': '最高品質を保持',
                'lowest_quality': '最低品質を保持'
            }

            final_message = f'{strategy_names.get(strategy, strategy)}戦略で、{total_kept}グループから{total_removed}件の重複動画を{action_type}しました'
            
            if error_messages:
                final_message += f'。エラー: {len(error_messages)}件'

            duplicate_progress.complete_task("completed")
            duplicate_progress.update_progress(
                len(groups), 
                "", 
                final_message
            )

        except Exception as e:
            duplicate_progress.complete_task("error", f"予期しないエラー: {str(e)}")

    # バックグラウンドで実行
    threading.Thread(target=bulk_resolve_background, daemon=True).start()

    return jsonify({
        'success': True,
        'message': 'バックグラウンドで一括解決を開始しました',
        'background': True
    })

@app.route('/duplicates/progress')
@login_required
def get_duplicate_progress():
    """重複削除の進捗状況を取得"""
    return jsonify(duplicate_progress.get_status())


@app.route('/duplicates/cancel', methods=['POST'])
@login_required
def cancel_duplicate_operation():
    """重複削除操作をキャンセル（注意：実行中の処理は停止できません）"""
    duplicate_progress.complete_task("cancelled", "ユーザーによってキャンセルされました")
    return jsonify({'success': True, 'message': 'キャンセルしました'})

@app.route('/video/<video_id>/analysis')
@login_required
def video_analysis_detail(video_id):
    """個別動画の分析詳細"""
    conn = get_db_connection()
    try:
        analysis = conn.execute(
            'SELECT * FROM video_analysis WHERE video_id = ?',
            (video_id,)
        ).fetchone()
    except Exception as e:
        print(f"分析データ取得エラー: {e}")
        analysis = None
    finally:
        conn.close()

    if not analysis:
        flash('分析データが見つかりません。まず動画分析を実行してください。')
        return redirect(url_for('video_page', video_id=video_id))

    # データを辞書に変換し、JSONをパース
    analysis_data = dict(analysis)

    try:
        if analysis_data.get('auto_tags'):
            analysis_data['auto_tags'] = json.loads(analysis_data['auto_tags'])
        else:
            analysis_data['auto_tags'] = []
    except (json.JSONDecodeError, TypeError):
        analysis_data['auto_tags'] = []

    # 日時データの処理
    if analysis_data.get('analyzed_at'):
        try:
            # 文字列の場合は datetime オブジェクトに変換
            if isinstance(analysis_data['analyzed_at'], str):
                from datetime import datetime
                analysis_data['analyzed_at'] = datetime.fromisoformat(
                    analysis_data['analyzed_at'].replace('Z', '+00:00'))
        except Exception as e:
            print(f"日時変換エラー: {e}")
            # 変換できない場合はそのまま残す

    return render_template('video_analysis_detail.html',
                           video_id=video_id,
                           analysis=analysis_data)


# 既存のupdate_video_metadataを修正して分析も実行
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

    # 分析キューに追加
    for video in scanned_videos:
        video_analyzer.add_video_for_analysis(video["video_id"], video["full_path"])

    print("動画メタデータの更新と分析キューへの追加が完了しました。")
    load_thumbnail_cache()


# 既存のコードの続き...

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


# カスタムフィルター：タイトルの省略表示（30文字以上の場合）
@app.template_filter('truncate_title')
def truncate_title(title):
    if len(title) > 30:
        return title[:30] + "…"
    return title


# カスタムフィルター：パスからファイル名を取得
@app.template_filter('basename')
def basename_filter(path):
    try:
        return os.path.basename(path)
    except Exception:
        return path


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
@app.route('/move_video/<video_id>', methods=['POST'])
@login_required
def move_video(video_id):
    # ユーザーに表示する移動先（相対表現）
    allowed_destinations = ["doc", "me", "doc/fc", "doc/li", "me/fc", "me/li", "as", "iv"]

    # macOSとWindowsでパスマッピングを分ける
    if os.name == 'nt':  # Windows
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
    else:  # macOS/Linux
        base_path = os.path.expanduser("~/video_library")
        destination_mapping = {
            "doc": os.path.join(base_path, "doc"),
            "me": os.path.join(base_path, "me"),
            "doc/fc": os.path.join(base_path, "doc", "fc"),
            "doc/li": os.path.join(base_path, "doc", "li"),
            "me/fc": os.path.join(base_path, "me", "fc"),
            "me/li": os.path.join(base_path, "me", "li"),
            "as": os.path.join(base_path, "as"),
            "iv": os.path.join(base_path, "iv")
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


# 動画ファイルの削除（移動）
@app.route('/delete_video/<video_id>', methods=['POST'])
@login_required
def delete_video(video_id):
    """動画ファイルの削除（移動） - 修正版"""
    # 動画情報を取得
    videos = get_video_list()
    video = next((v for v in videos if v["id"] == video_id), None)
    if not video:
        flash("動画が見つかりません。")
        return redirect(url_for("index"))

    # 移動元と移動先のパスを設定
    source_path = video["full_path"]

    # 設定に基づいてパスを決定 - 修正版
    if os.name == 'nt':  # Windows
        remove_dir = os.path.expanduser(config['paths']['remove_directory_windows'])
    else:  # macOS/Linux
        remove_dir = os.path.expanduser(config['paths']['remove_directory_unix'])

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
        flash(f"{video['filename']} を削除しました。（{remove_dir}に移動）")

    except Exception as e:
        flash(f"動画の削除に失敗しました: {e}")

    return redirect(url_for("index"))


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
    if os.name == 'nt':  # Windows
        remove_base = r"D:\remove"
    else:  # macOS/Linux
        remove_base = os.path.expanduser("~/remove")

    os.makedirs(remove_base, exist_ok=True)
    folder_name = os.path.basename(directory_to_move)
    dest_dir = os.path.join(remove_base, folder_name)

    # 同名ディレクトリが既に存在する場合は、タイムスタンプを付加
    if os.path.exists(dest_dir):
        import time
        dest_dir = os.path.join(remove_base, f"{folder_name}_{int(time.time())}")

    try:
        shutil.move(directory_to_move, dest_dir)
        flash(f"ディレクトリ {directory_to_move} を {remove_base} に移動しました。")
    except Exception as e:
        flash(f"ディレクトリの移動に失敗しました: {e}")
        return redirect(url_for("video_page", video_id=video_id))

    # DB更新：該当ディレクトリのレコードを削除（更新対象のみ）
    conn = get_db_connection()
    conn.execute("DELETE FROM video_metadata WHERE directory = ?", (directory_to_move,))
    conn.commit()
    conn.close()

    return redirect(url_for("index"))


# app.pyの視聴履歴ページを修正

@app.route('/history')
@login_required
def history():
    conn = get_db_connection()
    try:
        rows = conn.execute('''
            SELECT vh.video_id, vh.viewed_at, vm.filename, vm.duration, vm.full_path
              FROM view_history vh
              JOIN video_metadata vm ON vh.video_id = vm.video_id
             WHERE vh.username = ?
             ORDER BY vh.viewed_at DESC
             LIMIT 100
        ''', (current_user.id,)).fetchall()
    except Exception as e:
        print(f"履歴取得エラー: {e}")
        rows = []
    finally:
        conn.close()

    history_items = []
    thumb_dir = os.path.join("static", "thumbnails")
    os.makedirs(thumb_dir, exist_ok=True)

    # 統計計算用の変数
    total_duration = 0
    unique_dates = set()

    for row in rows:
        try:
            # サムネイル生成（存在しない場合）
            thumb_filename = f"{row['video_id']}.jpg"
            thumb_path = os.path.join(thumb_dir, thumb_filename)

            if thumb_filename not in THUMBNAIL_CACHE and os.path.exists(row['full_path']):
                try:
                    generate_thumbnail(row['full_path'], thumb_path)
                    THUMBNAIL_CACHE.add(thumb_filename)
                except Exception as e:
                    print(f"サムネイル生成エラー ({row['full_path']}): {e}")

            # 日時のフォーマット
            viewed_datetime = datetime.fromtimestamp(row['viewed_at'])
            viewed_date_str = viewed_datetime.strftime('%Y-%m-%d')

            # 統計用データ収集
            if row['duration']:
                total_duration += row['duration']
            unique_dates.add(viewed_date_str)

            history_items.append({
                'id': row['video_id'],
                'filename': row['filename'] or '不明なファイル',
                'duration': row['duration'] or 0,
                'viewed_at': viewed_datetime.strftime('%Y-%m-%d %H:%M:%S'),
                'viewed_at_iso': viewed_datetime.isoformat(),  # JavaScript用
                'viewed_date': viewed_date_str,  # 日付のみ
                'thumb': thumb_filename,
                'full_path': row['full_path']  # デバッグ用
            })
        except Exception as e:
            print(f"履歴アイテム処理エラー: {e}")
            continue

    # 統計情報を計算
    stats = {
        'total_count': len(history_items),
        'total_duration_minutes': int(total_duration / 60) if total_duration > 0 else 0,
        'unique_days': len(unique_dates)
    }

    print(f"履歴件数: {len(history_items)}")  # デバッグ用
    print(f"統計: {stats}")  # デバッグ用

    return render_template('history.html', history_items=history_items, stats=stats)


# ゴミ箱
@app.route('/upload', methods=['GET'])
@login_required
def upload_page():
    # アップロード用フォームを表示
    return render_template('upload.html', upload_dirs=UPLOAD_DIRS)


# POST を受け付けて非同期にアップロードを開始
# start_upload ルートを修正
@app.route('/start_upload', methods=['POST'])
@login_required
def start_upload():
    # アップロード開始前に分析を一時停止
    if video_analyzer.is_running and not video_analyzer.is_paused:
        video_analyzer.pause_analysis()
        print("アップロード開始: 動画分析を一時停止しました")

    dest_key = request.form['directory']
    dest_dir = UPLOAD_DIRS.get(dest_key)
    if not dest_dir:
        flash("無効なアップロード先です。")
        return redirect(url_for('upload_page'))

    files = request.files.getlist('videos')
    if not files:
        flash("ファイルを選択してください。")
        return redirect(url_for('upload_page'))

    # 新規タグを取得
    new_tags_input = request.form.get('new_tags', '').strip()
    new_tags = []
    if new_tags_input:
        # カンマ区切りでタグを分割し、空白を除去
        new_tags = [tag.strip() for tag in new_tags_input.split(',') if tag.strip()]

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
    uploaded_video_ids = []
    for f in files:
        original = f.filename
        save_path = UPLOAD_DIRS[dest_key]
        unique = unique_filename(save_path, original)
        full_path = os.path.join(save_path, unique)
        f.save(full_path)

        # ビデオIDを生成（アップロード時に）
        video_id = hashlib.md5(full_path.encode('utf-8')).hexdigest()
        uploaded_video_ids.append(video_id)

        conn.execute('''
            INSERT INTO upload_files (batch_id, filename)
              VALUES (?, ?)
        ''', (batch_id, unique))

    conn.commit()
    conn.close()

    # メタデータを更新（新しいファイルをDBに反映）
    update_video_metadata()

    # 新規タグがある場合は、アップロードした動画全てに適用
    if new_tags:
        for video_id in uploaded_video_ids:
            for tag in new_tags:
                add_video_tag(video_id, tag)

        flash(f"{len(files)} 件のアップロードが完了しました。タグ '{', '.join(new_tags)}' を追加しました。")
    else:
        flash(f"{len(files)} 件のアップロードが完了しました。")

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
    done = session.get('upload_done', 0)
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
        conn.execute("INSERT INTO users (username, password_hash, role) VALUES (?, ?, ?)",
                     (username, password_hash, role))
        conn.commit()
        conn.close()
        flash("登録が完了しました。ログインしてください。")
        return redirect(url_for("login"))
    return render_template("register.html")


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


# ゴミ箱
@app.route('/trash')
@login_required
def trash():
    # macOSとWindowsでパスを分ける
    if os.name == 'nt':  # Windows
        remove_dir = r"D:\remove"
    else:  # macOS/Linux
        remove_dir = os.path.expanduser("~/remove")

    if not os.path.exists(remove_dir):
        os.makedirs(remove_dir, exist_ok=True)

    try:
        items = os.listdir(remove_dir)
    except PermissionError:
        flash("ゴミ箱ディレクトリにアクセスできません。")
        items = []

    trash_items = []
    for item in items:
        full_path = os.path.join(remove_dir, item)
        trash_items.append({
            "name": item,
            "full_path": full_path,
            "is_dir": os.path.isdir(full_path)
        })
    return render_template('trash.html', trash_items=trash_items)


@app.before_request
def restrict_ip():
    if request.remote_addr not in ALLOWED_IPS:
        abort(403)  # 許可されていない場合は403 Forbidden を返す


@app.route('/progress')
@login_required
def progress():
    return progress_status  # JSONで返す場合は jsonify(progress_status) を使うと良い


def get_video_data(video_id):
    conn = get_db_connection()
    cur = conn.execute('SELECT * FROM video_data WHERE video_id = ?', (video_id,))
    row = cur.fetchone()
    conn.close()
    data = {"views": 0, "tags": []}
    if row:
        data["views"] = row["views"]
        data["tags"] = json.loads(row["tags"])

    # 分析データも取得
    conn = get_db_connection()
    analysis = conn.execute('SELECT * FROM video_analysis WHERE video_id = ?', (video_id,)).fetchone()
    if analysis:
        data["analysis"] = dict(analysis)
        if analysis["auto_tags"]:
            data["auto_tags"] = json.loads(analysis["auto_tags"])
        else:
            data["auto_tags"] = []
    else:
        data["analysis"] = None
        data["auto_tags"] = []
    conn.close()

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
        conn.execute('INSERT INTO video_data (video_id, views, tags) VALUES (?, ?, ?)',
                     (video_id, 0, json.dumps(tags)))
    conn.commit()
    conn.close()


def unique_filename(directory: str, filename: str) -> str:
    """
    directory 内に filename が存在する場合、
    ファイル名の末尾に（1）（2）…を付けてユニークにする。
    """
    base, ext = os.path.splitext(filename)
    candidate = filename
    i = 1
    while os.path.exists(os.path.join(directory, candidate)):
        candidate = f"{base}（{i}）{ext}"
        i += 1
    return candidate


# お気に入り切替用ルート
@app.route('/toggle_favorite/<video_id>', methods=['POST'])
@login_required
def toggle_favorite(video_id):
    username = current_user.id
    conn = get_db_connection()
    cur = conn.execute(
        'SELECT 1 FROM user_favorites WHERE username = ? AND video_id = ?',
        (username, video_id)
    )
    row = cur.fetchone()
    if row:
        conn.execute(
            'DELETE FROM user_favorites WHERE username = ? AND video_id = ?',
            (username, video_id)
        )
        flash("お気に入りから削除しました。")
    else:
        conn.execute(
            'INSERT INTO user_favorites (username, video_id) VALUES (?, ?)',
            (username, video_id)
        )
        flash("お気に入りに追加しました。")
    conn.commit()
    conn.close()
    return redirect(request.referrer or url_for('index'))


# 複数ディレクトリから動画リストを取得
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
def generate_thumbnail(video_path, thumb_path, time=None):
    if time is None:
        time = config['thumbnails']['main_thumbnail_time']

    if not os.path.exists(thumb_path):
        cmd = [
            "ffmpeg", "-ss", time, "-i", video_path,
            "-vframes", "1", "-y", thumb_path
        ]
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        global THUMBNAIL_CACHE
        THUMBNAIL_CACHE.add(os.path.basename(thumb_path))
    return thumb_path


# ffprobeで動画の長さ（duration）を取得
def get_video_duration(video_path):
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


# 動画を21分割して最初の20枚のシーンサムネイル生成
def generate_scene_thumbnails(video_path, video_id, num_scenes=20):
    scenes_dir = os.path.join("static", "scenes")
    os.makedirs(scenes_dir, exist_ok=True)
    duration = get_video_duration(video_path)
    scenes = []
    if duration <= 0:
        return scenes, duration

    # 既存のサムネイルを全てチェック
    existing_scenes = []
    total_segments = num_scenes + 1  # 21分割
    all_exist = True

    for i in range(num_scenes):  # 0-19の20枚
        thumb_filename = f"{video_id}_scene_{i}.jpg"
        thumb_filepath = os.path.join(scenes_dir, thumb_filename)
        timestamp = duration * i / total_segments

        if os.path.exists(thumb_filepath):
            existing_scenes.append({
                "thumb": thumb_filename,
                "time": timestamp
            })
        else:
            all_exist = False

    # 全てのサムネイルが既に存在する場合はそれを使用
    if all_exist and len(existing_scenes) == num_scenes:
        return existing_scenes, duration

    # サムネイルが不足している場合は生成
    for i in range(num_scenes):  # 0-19の20枚
        timestamp = duration * i / total_segments
        thumb_filename = f"{video_id}_scene_{i}.jpg"
        thumb_filepath = os.path.join(scenes_dir, thumb_filename)

        if not os.path.exists(thumb_filepath):
            if os.name == 'nt':
                video_path_safe = get_short_path_name(video_path)
            else:
                video_path_safe = video_path
            cmd = [
                "ffmpeg", "-ss", str(timestamp), "-i", video_path_safe,
                "-vframes", "1", "-vf", "scale=160:90", "-y", thumb_filepath
            ]
            result = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if result.returncode == 0:
                print(f"生成: {thumb_filename} at {timestamp:.2f}s")

        scenes.append({
            "thumb": thumb_filename,
            "time": timestamp
        })
    return scenes, duration

# TOPページ：動画一覧
@app.route('/')
@login_required
def index():
    all_videos = get_video_list()
    q = request.args.get("q", "").strip().lower()
    directory_filter = request.args.get("directory", "all")
    sort_by = request.args.get("sort", "date")
    order = request.args.get("order", "desc")
    favorite_only = request.args.get("favorite") == '1'

    videos = all_videos
    if directory_filter != "all":
        videos = [v for v in videos if v["directory"].startswith(directory_filter)]
    if q:
        videos = [v for v in videos if q in v["filename"].lower()]
    if favorite_only:
        videos = [v for v in videos if get_video_data(v["id"])["favorite"]]

    reverse = (order == "desc")
    if sort_by == "views":
        videos.sort(key=lambda v: get_video_data(v["id"])["views"], reverse=reverse)
    elif sort_by == "date":
        videos.sort(key=lambda v: v["created"], reverse=reverse)
    elif sort_by == "duration":
        videos.sort(key=lambda v: v["duration"], reverse=reverse)
    elif sort_by == "filename":
        videos.sort(key=lambda v: v["filename"].lower(), reverse=reverse)

    per_page = config['pagination']['videos_per_page']
    page = int(request.args.get("page", 1))
    total = len(videos)
    start = (page - 1) * per_page
    end = start + per_page
    videos_page = videos[start:end]
    total_pages = (total + per_page - 1) // per_page

    thumb_dir = os.path.join("static", "thumbnails")
    os.makedirs(thumb_dir, exist_ok=True)
    for video in videos_page:
        video["thumb"] = video["id"] + ".jpg"
        thumb_path = os.path.join(thumb_dir, video["thumb"])
        if video["thumb"] not in THUMBNAIL_CACHE:
            generate_thumbnail(video["full_path"], thumb_path)
        data = get_video_data(video["id"])
        video["views"] = data.get("views", 0)
        video["tags"] = data.get("tags", [])
        video["favorite"] = data.get("favorite", False)
        video["auto_tags"] = data.get("auto_tags", [])
        video["analysis"] = data.get("analysis")

    directories = [("all", "すべて")] + [(d, d) for d in VIDEO_DIRS]

    return render_template(
        'index.html',
        videos=videos_page, q=q, sort=sort_by, order=order,
        page=page, total_pages=total_pages,
        directory_filter=directory_filter,
        favorite_only=favorite_only,
        directories=directories
    )


# 動画再生ページ
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

    same_dir_videos = [v for v in all_videos if v["directory"] == video["directory"] and v["id"] != video_id]
    if len(same_dir_videos) > 12:
        sidebar_videos = random.sample(same_dir_videos, 12)
    else:
        sidebar_videos = same_dir_videos

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

    video["views"] = new_views
    video_data = get_video_data(video_id)
    video["favorite"] = video_data.get("favorite", False)
    video["analysis"] = video_data.get("analysis")
    video["auto_tags"] = video_data.get("auto_tags", [])
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


# ユーザー管理テーブルの初期化
def init_users():
    conn = get_db_connection()
    conn.execute('''
        CREATE TABLE IF NOT EXISTS users (
            username TEXT PRIMARY KEY,
            password_hash TEXT NOT NULL,
            role TEXT NOT NULL DEFAULT 'user'
        )
    ''')
    cur = conn.execute("SELECT 1 FROM users WHERE username = ?", ("admin",))
    if not cur.fetchone():
        password_hash = generate_password_hash("adminpass")
        conn.execute(
            "INSERT INTO users (username, password_hash, role) VALUES (?, ?, ?)",
            ("admin", password_hash, "admin")
        )
    conn.commit()
    conn.close()


init_users()

login_manager = LoginManager()
login_manager.init_app(app)
login_manager.login_view = "login"


class User(UserMixin):
    def __init__(self, username, password_hash, role):
        self.id = username
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


@app.before_request
def restrict_ip():
    if request.remote_addr not in ALLOWED_IPS:
        abort(403)


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


init_directory_hash_table()
update_video_metadata()

# バックグラウンド分析開始
video_analyzer.start_background_analysis()

# APSchedulerの設定
scheduler = BackgroundScheduler()
scheduler.add_job(
    func=update_video_metadata,
    trigger="cron",
    hour=config['analysis']['analysis_schedule_hour'],
    minute=config['analysis']['analysis_schedule_minute']
)
scheduler.start()

import atexit

atexit.register(lambda: scheduler.shutdown())
atexit.register(lambda: video_analyzer.stop_background_analysis())

if __name__ == '__main__':
    app.run(
        host=config['app']['host'],
        port=config['app']['port'],
        debug=config['app']['debug']
    )