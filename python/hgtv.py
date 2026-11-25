# -*- coding: utf-8 -*-
from __future__ import annotations
import base64
import binascii
import bisect
import hashlib
import json
import os
import lzma
import random
import re
import struct
import tempfile
import concurrent.futures
import threading
import time
from collections.abc import Mapping
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any
from urllib.parse import parse_qs, quote, urlencode, urlparse
import requests
try:
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
except ImportError:
    hashes = None
    Cipher = algorithms = modes = None
try:
    from Crypto.Cipher import AES as CryptoAES
except ImportError:
    CryptoAES = None
try:
    from base.spider import Spider as _BaseSpider
except Exception:
    try:
        import sys as _sys
        _sys.path.append("..")
        from base.spider import Spider as _BaseSpider
    except Exception:
        class _BaseSpider:
            pass

# FongMi/TVBox 的 Chaquopy 环境未必带 cryptography，多数壳只带 pycryptodome。
# 统一入口，避免调用点直接依赖某一个库。
if Cipher is not None:
    AES_BACKEND = "cryptography"
elif CryptoAES is not None:
    AES_BACKEND = "pycryptodome"
else:
    AES_BACKEND = "none"

class _PureAES128:
    """纯 Python AES-128，供无 pycryptodome/cryptography 的壳使用。"""

    _S = (
        99,124,119,123,242,107,111,197,48,1,103,43,254,215,171,118,202,130,201,125,250,89,71,240,
        173,212,162,175,156,164,114,192,183,253,147,38,54,63,247,204,52,165,229,241,113,216,49,21,
        4,199,35,195,24,150,5,154,7,18,128,226,235,39,178,117,9,131,44,26,27,110,90,160,82,59,214,
        179,41,227,47,132,83,209,0,237,32,252,177,91,106,203,190,57,74,76,88,207,208,239,170,251,67,
        77,51,133,69,249,2,127,80,60,159,168,81,163,64,143,146,157,56,245,188,182,218,33,16,255,243,
        210,205,12,19,236,95,151,68,23,196,167,126,61,100,93,25,115,96,129,79,220,34,42,144,136,70,
        238,184,20,222,94,11,219,224,50,58,10,73,6,36,92,194,211,172,98,145,149,228,121,231,200,55,
        109,141,213,78,169,108,86,244,234,101,122,174,8,186,120,37,46,28,166,180,198,232,221,116,31,
        75,189,139,138,112,62,181,102,72,3,246,14,97,53,87,185,134,193,29,158,225,248,152,17,105,
        217,142,148,155,30,135,233,206,85,40,223,140,161,137,13,191,230,66,104,65,153,45,15,176,84,
        187,22
    )
    _RCON = (0x00,0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1B,0x36)

    def __init__(self, key: bytes):
        if len(key) != 16:
            raise ValueError("AES-128 only")
        self._rk = self._expand(key)

    def _expand(self, key: bytes):
        s = self._S
        w = list(key)
        for i in range(4, 44):
            t0, t1, t2, t3 = w[-4], w[-3], w[-2], w[-1]
            if i % 4 == 0:
                t0, t1, t2, t3 = s[t1], s[t2], s[t3], s[t0]
                t0 ^= self._RCON[i // 4]
            base = (i - 4) * 4
            w.extend((w[base] ^ t0, w[base + 1] ^ t1, w[base + 2] ^ t2, w[base + 3] ^ t3))
        return w

    @staticmethod
    def _xtime(a: int) -> int:
        return ((a << 1) ^ 0x1B) & 0xFF if (a & 0x80) else ((a << 1) & 0xFF)

    def encrypt_block(self, block: bytes) -> bytes:
        s = list(block)
        rk = self._rk
        for i in range(16):
            s[i] ^= rk[i]
        for rnd in range(1, 10):
            s = [self._S[b] for b in s]
            s = [s[0], s[5], s[10], s[15], s[4], s[9], s[14], s[3],
                 s[8], s[13], s[2], s[7], s[12], s[1], s[6], s[11]]
            for c in range(4):
                i = c * 4
                a, b, c0, d = s[i], s[i + 1], s[i + 2], s[i + 3]
                t = a ^ b ^ c0 ^ d
                u = a
                a ^= t ^ self._xtime(a ^ b)
                b ^= t ^ self._xtime(b ^ c0)
                c0 ^= t ^ self._xtime(c0 ^ d)
                d ^= t ^ self._xtime(d ^ u)
                s[i], s[i + 1], s[i + 2], s[i + 3] = a, b, c0, d
            off = rnd * 16
            for i in range(16):
                s[i] ^= rk[off + i]
        s = [self._S[b] for b in s]
        s = [s[0], s[5], s[10], s[15], s[4], s[9], s[14], s[3],
             s[8], s[13], s[2], s[7], s[12], s[1], s[6], s[11]]
        for i in range(16):
            s[i] ^= rk[160 + i]
        return bytes(s)

    def decrypt_block(self, block: bytes) -> bytes:
        def mul(a, b):
            p = 0
            for _ in range(8):
                if b & 1:
                    p ^= a
                hi = a & 0x80
                a = (a << 1) & 0xFF
                if hi:
                    a ^= 0x1B
                b >>= 1
            return p

        s = list(block)
        rk = self._rk
        for i in range(16):
            s[i] ^= rk[160 + i]
        for rnd in range(9, 0, -1):
            s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11],
                 s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
            s = [self._SI[b] for b in s]
            off = rnd * 16
            for i in range(16):
                s[i] ^= rk[off + i]
            for c in range(4):
                i = c * 4
                a, b, c0, d = s[i], s[i + 1], s[i + 2], s[i + 3]
                s[i] = mul(a, 0x0E) ^ mul(b, 0x0B) ^ mul(c0, 0x0D) ^ mul(d, 0x09)
                s[i + 1] = mul(a, 0x09) ^ mul(b, 0x0E) ^ mul(c0, 0x0B) ^ mul(d, 0x0D)
                s[i + 2] = mul(a, 0x0D) ^ mul(b, 0x09) ^ mul(c0, 0x0E) ^ mul(d, 0x0B)
                s[i + 3] = mul(a, 0x0B) ^ mul(b, 0x0D) ^ mul(c0, 0x09) ^ mul(d, 0x0E)
        s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11],
             s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
        s = [self._SI[b] for b in s]
        for i in range(16):
            s[i] ^= rk[i]
        return bytes(s)



_PureAES128._SI = tuple({v: i for i, v in enumerate(_PureAES128._S)}[i] for i in range(256))


def _pure_ctr_decrypt(key: bytes, counter: bytes, data: bytes) -> bytes:
    if not data:
        return b""
    if len(counter) < 16:
        counter = counter.ljust(16, b"\0")
    else:
        counter = counter[:16]
    aes = _PureAES128(key)
    ctr = int.from_bytes(counter, "big")
    out = bytearray()
    for offset in range(0, len(data), 16):
        ks = aes.encrypt_block(ctr.to_bytes(16, "big"))
        ctr = (ctr + 1) & ((1 << 128) - 1)
        chunk = data[offset:offset + 16]
        out.extend(c ^ k for c, k in zip(chunk, ks))
    return bytes(out)


def _pure_cbc_decrypt(key: bytes, iv: bytes, data: bytes) -> bytes:
    if not data:
        return b""
    if len(data) % 16:
        data = data[: len(data) - (len(data) % 16)]
    aes = _PureAES128(key)
    prev = (iv[:16] if len(iv) >= 16 else iv).ljust(16, b"\0")
    out = bytearray()
    for i in range(0, len(data), 16):
        block = data[i:i + 16]
        dec = aes.decrypt_block(block)
        out.extend(d ^ p for d, p in zip(dec, prev))
        prev = block
    return bytes(out)


def _aes_ctr_decrypt(key: bytes, counter: bytes, data: bytes) -> bytes:
    if not data:
        return b""
    if AES_BACKEND == "cryptography":
        decryptor = Cipher(algorithms.AES(key), modes.CTR(counter)).decryptor()
        return decryptor.update(data) + decryptor.finalize()
    if AES_BACKEND == "pycryptodome":
        cipher = CryptoAES.new(
            key, CryptoAES.MODE_CTR, nonce=b"", initial_value=counter
        )
        return cipher.decrypt(data)
    return _pure_ctr_decrypt(key, counter, data)


def _aes_cbc_decrypt(key: bytes, iv: bytes, data: bytes) -> bytes:
    if not data:
        return b""
    if AES_BACKEND == "cryptography":
        decryptor = Cipher(algorithms.AES(key), modes.CBC(iv)).decryptor()
        return decryptor.update(data) + decryptor.finalize()
    if AES_BACKEND == "pycryptodome":
        return CryptoAES.new(key, CryptoAES.MODE_CBC, iv).decrypt(data)
    return _pure_cbc_decrypt(key, iv, data)


SITE = "https://hongguoduanju.com"
EPISODE_PREFIX = "hg-episode-v1:"
# 红果每集视频模型按清晰度返回多条独立线路（360/480/540/720/1080），
# 每条带 main_url + backup_url 双 CDN 与独立加密材料。这里把清晰度作为
# TVBox 多线路暴露；内封音/视轨在解密 _rewrite_moov 时天然全部保留。
_HG_QUALITY_LINES = (
    ("2160", "原画"),
    ("1440", "蓝光"),
    ("1080", "超清"),
    ("720",  "高清"),
    ("540",  "标准"),
    ("480",  "流畅"),
    ("360",  "极速"),
)
_QUALITY_LINE_NAME_TO_Q = {
    "原画": "2160", "蓝光": "1440",
    "超清": "1080", "高清": "720", "标准": "540",
    "流畅": "480", "极速": "360", "2160": "2160", "1440": "1440",
    "1080": "1080", "720": "720",
    "540": "540", "480": "480", "360": "360",
}


def _split_episode_token(token: str) -> tuple[str, str]:
    """把 'hg-episode-v1:<q>:<vid>' 解析为 (清晰度, vid)；兼容旧格式 'hg-episode-v1:<vid>'。"""
    body = str(token or "")
    if body.startswith(EPISODE_PREFIX):
        body = body[len(EPISODE_PREFIX):]
    if ":" in body:
        head, tail = body.split(":", 1)
        if head.isdigit():
            return head, tail
    return "1080", body

# 官网搜索 SSR 固定约 10 条且几乎不认 page；用多关键词轮换实现“翻页”
# 注：AI剧/AI漫剧 这套内容类型已按需求移除（与“漫剧”分类逐字重复），故不留 AI 专用关键词。


# ---- 本机解密缓存 + 自动清理 ----
_HG_CACHE_DIR = None
_HG_CACHE_MAX_FILES = 8          # 最多保留集数
_HG_CACHE_MAX_BYTES = 400 * 1024 * 1024  # 总容量约 400MB
_HG_CACHE_MAX_AGE = 6 * 3600     # 超过 6 小时自动删


def _hg_cache_dir() -> str:
    global _HG_CACHE_DIR
    if _HG_CACHE_DIR and os.path.isdir(_HG_CACHE_DIR):
        return _HG_CACHE_DIR
    candidates = []
    # 优先 App 可写缓存目录（OK影视 / FongMi 常见路径）
    for root in (
        "/data/user/0/com.fongmi.android.oktv/cache",
        "/data/data/com.fongmi.android.oktv/cache",
        "/data/user/0/com.fongmi.android.tv/cache",
        "/data/data/com.fongmi.android.tv/cache",
        "/sdcard/Android/data/com.fongmi.android.oktv/cache",
        "/sdcard/Android/data/com.fongmi.android.tv/cache",
        "/sdcard/Download",
    ):
        candidates.append(os.path.join(root, "hg_cenc_cache"))
    try:
        candidates.append(os.path.join(tempfile.gettempdir(), "hg_cenc_cache"))
    except Exception:
        pass
    try:
        candidates.append(os.path.join(os.getcwd(), "hg_cenc_cache"))
    except Exception:
        pass
    for path in candidates:
        try:
            os.makedirs(path, exist_ok=True)
            test = os.path.join(path, ".w")
            with open(test, "wb") as fh:
                fh.write(b"1")
            os.remove(test)
            _HG_CACHE_DIR = path
            return path
        except Exception:
            continue
    _HG_CACHE_DIR = tempfile.mkdtemp(prefix="hg_cenc_")
    return _HG_CACHE_DIR


def _hg_cache_path(vid: str, quality: str) -> str:
    safe = re.sub(r"[^0-9A-Za-z_-]", "", str(vid))[:40]
    q = re.sub(r"[^0-9A-Za-z]", "", str(quality or "q"))[:8]
    return os.path.join(_hg_cache_dir(), "%s_%s.mp4" % (safe, q))


def _hg_cache_list() -> list:
    root = _hg_cache_dir()
    files = []
    try:
        now = time.time()
        for name in os.listdir(root):
            if not name.endswith(".mp4"):
                continue
            fp = os.path.join(root, name)
            if not os.path.isfile(fp):
                continue
            try:
                st = os.stat(fp)
            except Exception:
                continue
            files.append({"path": fp, "size": st.st_size, "mtime": st.st_mtime, "age": now - st.st_mtime})
    except Exception:
        return []
    files.sort(key=lambda x: x["mtime"])  # 旧 -> 新
    return files


def _hg_cache_cleanup(force: bool = False) -> None:
    """按时间 + 数量 + 体积自动清理本机缓存。"""
    try:
        files = _hg_cache_list()
        if not files and not force:
            return
        # 1) 过期删除
        remain = []
        for item in files:
            if item["age"] > _HG_CACHE_MAX_AGE or item["size"] <= 0:
                try:
                    os.remove(item["path"])
                except Exception:
                    pass
            else:
                remain.append(item)
        # 2) 超量删除最旧
        total = sum(x["size"] for x in remain)
        while remain and (len(remain) > _HG_CACHE_MAX_FILES or total > _HG_CACHE_MAX_BYTES):
            old = remain.pop(0)
            try:
                os.remove(old["path"])
            except Exception:
                pass
            total -= old["size"]
        # 3) 清理残留 tmp
        root = _hg_cache_dir()
        for name in os.listdir(root):
            if name.endswith(".tmp") or name == ".w":
                try:
                    os.remove(os.path.join(root, name))
                except Exception:
                    pass
    except Exception:
        pass



def _hg_cached_ok(body: Any) -> bool:
    """旧的整集缓存可能是 bvc2（黑屏有声），吐出去之前先验一下视轨编码。"""
    try:
        if not body:
            return False
        i = bytes(body).find(b"stsd")
        if i < 0:
            return True
        return bytes(body)[i + 16 : i + 20] in _DECODABLE_ENTRIES
    except Exception:
        return True


def _hg_cache_get(vid: str, quality: str) -> bytes | None:
    _hg_cache_cleanup(False)
    path = _hg_cache_path(vid, quality)
    try:
        if os.path.isfile(path) and os.path.getsize(path) > 64:
            # 读时刷新 mtime，避免刚播又被当过期删
            try:
                os.utime(path, None)
            except Exception:
                pass
            with open(path, "rb") as fh:
                return fh.read()
    except Exception:
        return None
    return None


def _hg_cache_put(vid: str, quality: str, data: bytes) -> None:
    if not data or len(data) < 64:
        return
    path = _hg_cache_path(vid, quality)
    try:
        _hg_cache_cleanup(False)
        tmp = path + ".tmp"
        with open(tmp, "wb") as fh:
            fh.write(data)
        os.replace(tmp, path)
        _hg_cache_cleanup(False)
    except Exception:
        try:
            if os.path.exists(path + ".tmp"):
                os.remove(path + ".tmp")
        except Exception:
            pass


def _aes_is_fast() -> bool:
    return AES_BACKEND in ("cryptography", "pycryptodome")


def _http_get_bytes(url: str, headers: dict | None = None, timeout: int = 60) -> bytes:
    h = dict(headers or {})
    r = requests.get(url, headers=h, timeout=timeout)
    r.raise_for_status()
    return r.content


def _probe_content_length(url: str, headers: dict | None = None, timeout: int = 30) -> int:
    h = dict(headers or {})
    try:
        r = requests.head(url, headers=h, timeout=timeout, allow_redirects=True)
        if r.status_code < 400:
            cl = r.headers.get("Content-Length") or r.headers.get("content-length")
            if cl and str(cl).isdigit():
                return int(cl)
    except Exception:
        pass
    try:
        hh = dict(h)
        hh["Range"] = "bytes=0-0"
        r = requests.get(url, headers=hh, timeout=timeout)
        cr = r.headers.get("Content-Range") or r.headers.get("content-range") or ""
        # bytes 0-0/12345
        if "/" in cr:
            total = cr.split("/")[-1].strip()
            if total.isdigit():
                return int(total)
        cl = r.headers.get("Content-Length") or "0"
        if str(cl).isdigit() and int(cl) > 1:
            return int(cl)
    except Exception:
        pass
    return 0


def _download_range(url: str, start: int, end: int, headers: dict | None, timeout: int) -> tuple[int, bytes]:
    h = dict(headers or {})
    h["Range"] = "bytes=%d-%d" % (start, end)
    last_err = None
    for attempt in range(3):
        try:
            r = requests.get(url, headers=h, timeout=timeout)
            if r.status_code not in (200, 206):
                raise RuntimeError("range http %s" % r.status_code)
            data = r.content
            if not data:
                raise RuntimeError("empty range body")
            return start, data
        except Exception as err:
            last_err = err
            try:
                time.sleep(0.25 * (attempt + 1))
            except Exception:
                pass
    raise RuntimeError("range %s-%s failed: %s" % (start, end, last_err))


def _multi_download(url: str, headers: dict | None = None, timeout: int = 90, workers: int = 4) -> bytes:
    """多分片并行下载，失败则回退整文件单线程。"""
    headers = dict(headers or {})
    total = _probe_content_length(url, headers, timeout=min(30, timeout))
    # 太小或未知长度：直接整下
    if total <= 0 or total < 2 * 1024 * 1024:
        return _http_get_bytes(url, headers, timeout=timeout)

    # 分片大小 1~2MB，线程数限制
    workers = max(2, min(int(workers or 4), 6))
    chunk = max(1 * 1024 * 1024, min(2 * 1024 * 1024, total // workers))
    ranges = []
    start = 0
    while start < total:
        end = min(total - 1, start + chunk - 1)
        ranges.append((start, end))
        start = end + 1

    parts: dict[int, bytes] = {}
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            futs = [
                pool.submit(_download_range, url, s, e, headers, timeout)
                for s, e in ranges
            ]
            for fut in concurrent.futures.as_completed(futs):
                s, data = fut.result()
                parts[s] = data
    except Exception:
        # 并行失败回退
        return _http_get_bytes(url, headers, timeout=timeout)

    buf = bytearray()
    for s, e in ranges:
        piece = parts.get(s)
        if piece is None:
            return _http_get_bytes(url, headers, timeout=timeout)
        buf.extend(piece)
    if len(buf) < total * 0.95:
        # 明显不完整
        return _http_get_bytes(url, headers, timeout=timeout)
    return bytes(buf)



_MANJU_KEYWORDS = [
    "漫剧", "动漫短剧", "二次元", "漫画短剧", "国漫短剧", "日漫", "动态漫", "动画剧",
]

# ===== 官方内容类型与分类（取自官方 hongguoduanju.com 的分类路由体系，与 App 同源同 ID）=====
_HG_CONTENT_TYPES = [
    ("comic-drama", "漫剧", [
        ("", "全部"), ("creative", "脑洞"), ("fantasy", "玄幻"), ("drama", "剧情"),
        ("apocalypse", "末世"), ("wealthy-family", "豪门"), ("wonder", "奇幻"),
        ("sci-fi", "科幻"), ("adventure", "冒险"),
    ]),
    ("real-drama", "真人剧", [
        ("", "全部"), ("romance", "爱情"), ("period", "年代"), ("comeback", "逆袭"),
        ("legend", "传奇"), ("growth", "成长"), ("family", "家庭"), ("clan", "家族"),
        ("cute-kids", "萌宝"), ("suspense", "悬疑"), ("thriller", "惊悚"), ("horror", "恐怖"),
        ("supernatural", "志怪"), ("costume", "古装"), ("fantasy", "玄幻"), ("wonder", "奇幻"),
        ("urban", "都市"), ("youth", "青春"), ("comedy", "喜剧"), ("sci-fi", "科幻"),
        ("disaster", "灾难"), ("action-adventure", "动作冒险"), ("war", "战争"),
        ("variety", "综艺"), ("drama", "剧情"),
    ]),
    ("comic", "漫画", [("", "全部")]),
]
_HG_ROUTES = {k: v for k, v in ((a, b) for a, b, _ in _HG_CONTENT_TYPES)}
_HG_ALIAS = {
    "all": "real-drama", "latest": "real-drama", "hot": "real-drama",
    "male": "real-drama", "female": "real-drama", "短剧": "real-drama",
    "manju": "comic-drama", "漫剧": "comic-drama",
}

def _hg_route_of(tid):
    t = str(tid or "").strip()
    if t in _HG_ROUTES:
        return t
    return _HG_ALIAS.get(t, "real-drama")

def _hg_category_page(route, cat, page):
    """官方分类页：/category/{route}/{item}?page=N，数据在 _ROUTER_DATA。"""
    route = _hg_route_of(route)
    path = "/category/" + route
    if cat:
        path += "/" + str(cat)
    sess = requests.Session()
    sess.trust_env = False
    sess.headers.update({"User-Agent": UA, "Referer": SITE + "/"})
    r = sess.get(SITE + path, params={"page": str(max(1, int(page or 1)))}, timeout=25)
    html = r.text or ""
    m = re.search(r"(?:window\.)?_ROUTER_DATA\s*=\s*", html)
    if not m:
        raise HongguoPluginError("分类页没有路由数据")
    v, _ = json.JSONDecoder().raw_decode(html[m.end():])
    p = ((v.get("loaderData") or {}).get("category_$") or {})
    return p

VIDEO_URL = "https://api5-normal-sinfonlineb.fqnovel.com/novel/player/multi_video_model/v1/"
VIDEO_URL_ALT = "https://api5-normal-lf.fqnovel.com/novel/player/multi_video_model/v1/"
# 2026-11-11 实测情报：multi_video_model/v1/ 已停服（任何请求只回空包），
# 同主机生效的是 video_model/v1/，请求体改为顶层 video_id。两套端点并存，自动择优。
VIDEO_URL_SINGLE = "https://api5-normal-sinfonlineb.fqnovel.com/novel/player/video_model/v1/"
VIDEO_URL_SINGLE_ALT = "https://api5-normal-lf.fqnovel.com/novel/player/video_model/v1/"

UA = "Mozilla/5.0 (Linux; Android 12) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36"
APP_UA = "com.phoenix.read/71332 (Linux; U; Android 16; zh_CN; 25053RT47C; Build/BP2A.250605.031.A3; Cronet/TTNetVersion:04657795 2026-01-23 QuicVersion:c67e9834 2025-09-08)"
MEDIA_UA = "com.phoenix.read/71332"




_HTML_FETCH_ATTEMPTS = 3

_HTML_FETCH_BACKOFF_SECONDS = 1.5

_RANGE_FETCH_ATTEMPTS = 3

_RANGE_FETCH_BACKOFF_SECONDS = 0.8

class HongguoPluginError(RuntimeError):
    """带稳定错误码的插件异常：日志、502 响应体、自检都认 code。"""

    def __init__(self, message: str = "", code: str = "", detail: str = ""):
        self.code = code or ""
        self.detail = detail or ""
        self.raw_message = message or ""
        text = ("%s %s" % (code, message)).strip() if code else str(message or "")
        super().__init__(text)


# ======================================================================
# 失效定位层（诊断日志 / HG_E_* 错误码 / 自检）
# ----------------------------------------------------------------------
# 目标：任何一次「取不到播放地址」，事后只看一个文件就能定位到哪一步
#       断、错误码是什么、上游回了什么状态和响应头，不用再靠猜。
# 产物（都在诊断目录里，默认 /sdcard/Download）：
#   hg_diag.log        逐行诊断，单文件 512KB 自动轮转成 hg_diag.log.1
#   hg_last_error.txt  最近一次失败的人读摘要 + 下一步该查什么
#   GET /hg_selfcheck  本机流服务上的自检 JSON（服务起来时可用）
#   GET /hg_diag       本机流服务上的最近失败摘要（纯文本）
#   Spider.action("diag")  返回最近一次失败摘要（壳支持 action 时可用）
# 环境变量：HG_DIAG_DIR / HG_DIAG_PATH 自定义位置；HG_DIAG_QUIET=1 只写文件不打印；
#           HG_NO_PROBE=1 关闭失败后的对照探测。
# ======================================================================
import collections as _hg_collections
import sys as _hg_sys

HG_DIAG_VERSION = "diag-2026-11-16n"   # n: 缓存落盘 hg_cache.json（HG_CACHE_FILE=0 关闭）

_HG_DIAG_LOCK = threading.RLock()
_HG_DIAG_RING = _hg_collections.deque(maxlen=400)
_HG_DIAG_LAST: dict[str, Any] = {}
_HG_DIAG_COUNT: dict[str, int] = {}
_HG_DIAG_PATH = ""
_HG_DIAG_DIR = ""
_HG_DIAG_BYTES = 0
_HG_DIAG_MAX_BYTES = 1024 * 1024
_HG_DIAG_BOOT = time.time()
_HG_DIAG_QUIET = str(os.environ.get("HG_DIAG_QUIET", "") or "").strip() not in ("", "0", "no", "false")
_HG_PROBE_LOCK = threading.Lock()
_HG_PROBE_DONE = False

# 错误码 -> 下一步该查什么。写给人看，直接进 hg_last_error.txt。
_HG_HINTS = {
    "HG_E_SIGN_REJECTED": "服务端回了 HTTP 200 但空响应：签名被网关静默拒绝。对照同一次运行里的 PROBE 行——弹幕接口正常而这里空，说明是 video_model 的签名/风控；两边都空则是签名算法整体过期。",
    "HG_E_HTTP_4XX": "上游直接 4xx：参数/版本号/设备身份不合法，或接口路径已变。看 resp 行的 status 与 head。",
    "HG_E_HTTP_5XX": "上游 5xx 或 CDN 故障：先重试；连续出现即为站点侧异常。",
    "HG_E_NON_JSON": "响应不是 JSON：可能被劫持、拿到 HTML 错误页或 WAF 拦截页。看 resp 行的 ctype/head。",
    "HG_E_MODEL_EMPTY": "有 JSON 但没有 video_model/video_list：端点或请求体版本已变（对照 74332 / 7.4.3.32）。",
    "HG_E_NO_ADDR": "模型里没有播放地址或密钥材料：该集可能下架/付费/地区限制。",
    "HG_E_NO_MOOV": "拿到地址但首片没有 moov：地址不是真 MP4（错误页）或上游文件结构变了。",
    "HG_E_NO_TRACK": "有 moov 但没有视频轨：上游只给了音频或分片结构变了。",
    "HG_E_CODEC": "只有 bytevc2 等壳解不了的编码：换线路，或等直通/备用接口回退。",
    "HG_E_RANGE": "媒体分片请求失败：签名 URL 过期或 CDN 拒绝 Range。",
    "HG_E_TIMEOUT": "网络超时：换网络/DNS；看 ms= 判断是取模型慢还是取分片慢。",
    "HG_E_NET": "连接失败：断网、DNS 或代理拦截。",
    "HG_E_DEVICE": "设备身份不可用：device_register 没返回有效 did/iid，当前在用随机号。",
    "HG_E_BIND": "本机 127.0.0.1 端口全部不可用：壳禁止监听，已回退直链或壳代理。",
    "HG_E_DECRYPT": "解密失败：spade 密钥或 CENC 结构变化。",
    "HG_E_TOKEN": "集 token 里解析不出 vid：detailContent 给的 id 被壳改写过，或线路与集数对不上。",
    "HG_E_NO_ROUTE": "所有播放路由都失败：看前面最近一条 FAIL 行。",
    "HG_E_UNKNOWN": "未归类错误：按 detail 原文判断。",
}

_HG_RETRYABLE_CODES = (
    "HG_E_SIGN_REJECTED", "HG_E_MODEL_EMPTY", "HG_E_TIMEOUT", "HG_E_NET",
    "HG_E_HTTP_5XX", "HG_E_RANGE",
)


def _hg_now() -> str:
    moment = time.time()
    return time.strftime("%m-%d %H:%M:%S", time.localtime(moment)) + ".%03d" % int((moment % 1) * 1000)


def _hg_ms(started: float) -> int:
    try:
        return int((time.time() - started) * 1000)
    except Exception:
        return 0


def _hg_clean(value: Any, limit: int = 300) -> str:
    """日志字段清洗：单行、限长，绝不把换行带进日志。"""
    try:
        text = value if isinstance(value, str) else str(value)
    except Exception:
        text = "?"
    text = text.replace("\r", " ").replace("\n", " ").replace("\t", " ")
    if len(text) > limit:
        text = text[:limit] + "…"
    return text


def _hg_tail(value: Any, keep: int = 4) -> str:
    digits = "".join(ch for ch in str(value or "") if ch.isalnum())
    if not digits:
        return "-"
    return "…" + digits[-keep:]


def _hg_body_snippet(body: Any, limit: int = 160) -> str:
    try:
        raw = bytes(body or b"")
    except Exception:
        return ""
    try:
        return _hg_clean(raw[:limit].decode("utf-8", "replace"), limit)
    except Exception:
        return ""


def _hg_headers_brief(headers: Any) -> str:
    try:
        parts = []
        for key in ("Content-Length", "Content-Type", "Server", "x-tt-logid"):
            value = headers.get(key, "")
            if value:
                parts.append("%s=%s" % (key, _hg_clean(value, 60)))
        if headers.get("Set-Cookie"):
            parts.append("Set-Cookie=y")
        return " ".join(parts)
    except Exception:
        return ""


def _hg_diag_dir() -> str:
    global _HG_DIAG_DIR
    if _HG_DIAG_DIR:
        return _HG_DIAG_DIR
    candidates = []
    env = str(os.environ.get("HG_DIAG_DIR", "") or "").strip()
    if env:
        candidates.append(env)
    candidates.append("/sdcard/Download")
    try:
        candidates.append(_hg_cache_dir())
    except Exception:
        pass
    try:
        candidates.append(tempfile.gettempdir())
    except Exception:
        pass
    try:
        candidates.append(os.getcwd())
    except Exception:
        pass
    for path in candidates:
        try:
            os.makedirs(path, exist_ok=True)
            probe = os.path.join(path, ".hg_diag_w")
            with open(probe, "wb") as fh:
                fh.write(b"1")
            os.remove(probe)
            _HG_DIAG_DIR = path
            return path
        except Exception:
            continue
    _HG_DIAG_DIR = ""
    return ""


def _hg_diag_path() -> str:
    global _HG_DIAG_PATH, _HG_DIAG_BYTES
    if _HG_DIAG_PATH:
        return _HG_DIAG_PATH
    paths = []
    env = str(os.environ.get("HG_DIAG_PATH", "") or "").strip()
    if env:
        paths.append(env)
    folder = _hg_diag_dir()
    if folder:
        paths.append(os.path.join(folder, "hg_diag.log"))
    for path in paths:
        try:
            parent = os.path.dirname(path)
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(path, "ab") as fh:
                fh.write(b"")
            try:
                _HG_DIAG_BYTES = os.path.getsize(path)
            except Exception:
                _HG_DIAG_BYTES = 0
            _HG_DIAG_PATH = path
            break
        except Exception:
            continue
    return _HG_DIAG_PATH


def _hg_diag_append(line: str) -> None:
    global _HG_DIAG_BYTES
    path = _hg_diag_path()
    if not path:
        return
    data = (line + "\n").encode("utf-8", "replace")
    if _HG_DIAG_BYTES + len(data) > _HG_DIAG_MAX_BYTES:
        # 留两份历史：一部多季剧点两下就能写满一份，只留 .1 会把上次的失败记录挤没
        try:
            old2 = path + ".2"
            try:
                if os.path.exists(old2):
                    os.remove(old2)
            except Exception:
                pass
            try:
                if os.path.exists(path + ".1"):
                    os.replace(path + ".1", old2)
            except Exception:
                pass
            os.replace(path, path + ".1")
        except Exception:
            pass
        _HG_DIAG_BYTES = 0
    with open(path, "ab") as fh:
        fh.write(data)
    _HG_DIAG_BYTES += len(data)


def _hc_range(value: Any) -> str:
    return _hg_clean(value, 40)


def _hg_diag(tag: str, msg: str = "", **fields: Any) -> str:
    """写一行诊断：时间 tag 说明 k=v ...。绝不抛异常、绝不带凭据原文。"""
    parts = [_hg_now(), str(tag)]
    if msg:
        parts.append(_hg_clean(msg))
    for key in sorted(fields):
        parts.append("%s=%s" % (key, _hg_clean(fields[key])))
    line = " ".join(part for part in parts if part)
    try:
        with _HG_DIAG_LOCK:
            _HG_DIAG_RING.append(line)
            _hg_diag_append(line)
    except Exception:
        pass
    if not _HG_DIAG_QUIET:
        try:
            print("[红果] " + line)
        except Exception:
            pass
    return line


def _hg_err_code(exc: Any) -> str:
    """把异常归到稳定错误码：日志/502 响应体/自检都只认这套码。"""
    code = str(getattr(exc, "code", "") or "") if exc is not None else ""
    if code:
        return code
    if not isinstance(exc, BaseException):
        return "HG_E_UNKNOWN"
    text = str(exc)
    low = text.lower()
    if isinstance(exc, requests.Timeout) or "timed out" in low or "timeout" in low:
        return "HG_E_TIMEOUT"
    if isinstance(exc, requests.ConnectionError):
        return "HG_E_NET"
    status = getattr(exc, "status_code", None)
    if status is None:
        status = getattr(getattr(exc, "response", None), "status_code", None)
    if isinstance(status, int) and status >= 400:
        return "HG_E_HTTP_4XX" if status < 500 else "HG_E_HTTP_5XX"
    for needle, code_name in (
        ("空响应", "HG_E_SIGN_REJECTED"),
        ("不是 JSON", "HG_E_NON_JSON"),
        ("video_model 为空", "HG_E_MODEL_EMPTY"),
        ("video_model 数据为空", "HG_E_MODEL_EMPTY"),
        ("没有清晰度", "HG_E_MODEL_EMPTY"),
        ("缺少地址或密钥", "HG_E_NO_ADDR"),
        ("没有视轨", "HG_E_NO_TRACK"),
        ("moov", "HG_E_NO_MOOV"),
        ("壳解不了", "HG_E_CODEC"),
        ("媒体分片", "HG_E_RANGE"),
        ("直通上游返回", "HG_E_RANGE"),
        ("CENC", "HG_E_DECRYPT"),
        ("MP4", "HG_E_NO_MOOV"),
        ("密钥", "HG_E_DECRYPT"),
        ("device_id/install_id", "HG_E_DEVICE"),
        ("解密", "HG_E_DECRYPT"),
        ("端口", "HG_E_BIND"),
    ):
        if needle in text:
            return code_name
    return "HG_E_UNKNOWN"


def _hg_retryable(exc: Any) -> bool:
    return _hg_err_code(exc) in _HG_RETRYABLE_CODES


def _hg_hint(code: str) -> str:
    return _HG_HINTS.get(str(code or ""), _HG_HINTS["HG_E_UNKNOWN"])


def _hg_fail(stage: str, exc: Any = None, **fields: Any) -> str:
    """记一次失败：定位行 + 更新最近失败 + 重写 hg_last_error.txt，返回错误码。"""
    error = exc if isinstance(exc, BaseException) else None
    code = _hg_err_code(error)
    detail = _hg_clean(exc if exc is not None else "")
    # str(exc) 里已经带了错误码前缀时不再重复一遍
    if code and detail.startswith(code):
        detail = detail[len(code):].strip()
    try:
        with _HG_DIAG_LOCK:
            _HG_DIAG_LAST.clear()
            _HG_DIAG_LAST.update({
                "ts": _hg_now(),
                "stage": stage,
                "code": code,
                "detail": detail,
                "fields": dict(fields),
            })
            _HG_DIAG_COUNT[code] = _HG_DIAG_COUNT.get(code, 0) + 1
    except Exception:
        pass
    _hg_diag("FAIL", "%s %s %s" % (stage, code, detail), **fields)
    _hg_write_last_error()
    return code


def _hg_last_error_text() -> str:
    """最近一次失败的人读摘要：给 hg_last_error.txt、/hg_diag、action("diag") 共用。"""
    with _HG_DIAG_LOCK:
        last = dict(_HG_DIAG_LAST)
        recent = list(_HG_DIAG_RING)[-12:]
        counts = dict(_HG_DIAG_COUNT)
    lines = [
        "红果取流诊断  %s" % _hg_now(),
        "诊断日志: %s" % (_hg_diag_path() or "（没有可写目录）"),
        "",
    ]
    if not last:
        lines.append("本次进程还没有失败记录。")
    else:
        lines.append("最近一次失败: %s" % last.get("ts", "-"))
        lines.append("阶段: %s" % last.get("stage", "-"))
        lines.append("错误码: %s" % last.get("code", "-"))
        lines.append("详情: %s" % last.get("detail", "-"))
        fields = last.get("fields") or {}
        if isinstance(fields, Mapping) and fields:
            lines.append("上下文: " + " ".join(
                "%s=%s" % (key, _hg_clean(fields[key], 80)) for key in sorted(fields)
            ))
        lines.append("下一步: " + _hg_hint(last.get("code", "")))
    if counts:
        lines.append("本次进程各错误码次数: " + " ".join(
            "%s=%d" % (key, counts[key]) for key in sorted(counts)
        ))
    lines.append("")
    lines.append("---- 最近 %d 条诊断 ----" % len(recent))
    lines.extend(recent)
    return "\n".join(lines) + "\n"


def _hg_write_last_error() -> None:
    try:
        path = _hg_diag_path()
        if not path:
            return
        target = os.path.join(os.path.dirname(path) or ".", "hg_last_error.txt")
        text = _hg_last_error_text()
        with open(target, "w", encoding="utf-8") as fh:
            fh.write(text)
    except Exception:
        pass


def _hg_banner() -> None:
    """启动横幅：把「跑在什么环境、日志写到哪」先钉进日志，免得事后不知道去哪找。"""
    _hg_diag(
        "BOOT", "诊断层 %s 就绪" % HG_DIAG_VERSION,
        diag=_hg_diag_path() or "unwritable",
        py=_hg_sys.version.split()[0],
        aes=AES_BACKEND,
        req=getattr(requests, "__version__", "?"),
        pid=os.getpid(),
    )


def _hg_selfcheck() -> dict:
    """自检快照：环境 + 最近失败 + 计数 + 最近日志，/hg_selfcheck 直接吐这个。"""
    with _HG_DIAG_LOCK:
        last = dict(_HG_DIAG_LAST)
        counts = dict(_HG_DIAG_COUNT)
        recent = list(_HG_DIAG_RING)[-40:]
    info: dict[str, Any] = {
        "diag_version": HG_DIAG_VERSION,
        "diag_path": _hg_diag_path() or "",
        "quiet": bool(_HG_DIAG_QUIET),
        "python": _hg_sys.version.split()[0],
        "aes_backend": AES_BACKEND,
        "requests": getattr(requests, "__version__", "?"),
        "uptime_s": int(time.time() - _HG_DIAG_BOOT),
        "last_error": last,
        "error_counts": counts,
    }
    try:
        info["endpoints"] = {
            "multi": VIDEO_URL,
            "multi_alt": VIDEO_URL_ALT,
            "single": VIDEO_URL_SINGLE,
            "single_alt": VIDEO_URL_SINGLE_ALT,
        }
    except Exception:
        pass
    try:
        info["sign_order"] = list(_sign_modes_ordered())
        info["endpoint_order"] = ["single" if item else "multi" for item in _ep_modes_ordered()]
    except Exception:
        pass
    try:
        with _STREAM_LOCK:
            device = dict(_STREAM_STATE.get("device") or {})
            info["stream"] = {
                "port": int(_STREAM_STATE.get("port") or 0),
                "sessions": len(_STREAM_STATE.get("sessions") or {}),
                "device_registered": bool(device.get("registered")),
                "did": _hg_tail(device.get("device_id", "")),
            }
    except Exception as exc:
        info["stream"] = {"error": _hg_clean(exc, 80)}
    try:
        files = _hg_cache_list()
        info["cache"] = {
            "dir": _hg_cache_dir(),
            "files": len(files),
            "mb": round(sum(item.get("size") or 0 for item in files) / 1048576.0, 1),
        }
    except Exception:
        pass
    try:
        info["danmaku"] = {
            "enabled": bool(_DM_ENABLED),
            "host": _DM_HOST,
            "last_err": _hg_clean(_DM_LAST_ERR, 120),
        }
    except Exception:
        pass
    info["recent"] = recent
    return info


def _hg_contrast_probe(vid: str, config: Mapping[str, Any]) -> None:
    """取模型全失败后做一次对照探测，把「谁坏了」直接写进日志。

    2026-11-16 的未定分叉是「签名被静默拒绝」还是「整体缺登录态/断网」。
    这里用两条独立链路对照，每个进程只做一次、总预算约 10 秒：
      site    官网首页（无签名、无登录）——网络基线
      danmaku 弹幕接口（同一套 x-ladon/x-argus 签名，另一条业务线）
    结论写进 PROBE verdict 行，不用再靠人肉猜。
    """
    global _HG_PROBE_DONE
    if str(os.environ.get("HG_NO_PROBE", "") or "").strip() not in ("", "0", "no", "false"):
        _hg_diag("PROBE", "skipped", reason="HG_NO_PROBE")
        return
    with _HG_PROBE_LOCK:
        if _HG_PROBE_DONE:
            return
        _HG_PROBE_DONE = True
    site_ok = False
    dm_ok = False
    try:
        started = time.time()
        try:
            response = _hg_session().get(SITE + "/", timeout=6)
            site_ok = response.status_code == 200
            _hg_diag("PROBE", "site", status=response.status_code,
                     n=len(response.content or b""), ms=_hg_ms(started))
        except Exception as exc:
            _hg_diag("PROBE", "site", status=0, code=_hg_err_code(exc),
                     detail=exc, ms=_hg_ms(started))
        started = time.time()
        try:
            items, _info, _extra = _dm_page(
                vid, "", 0,
                str(config.get("device_id") or "") if isinstance(config, Mapping) else "",
                str(config.get("install_id") or "") if isinstance(config, Mapping) else "",
            )
            dm_ok = True
            _hg_diag("PROBE", "danmaku", ok=1, n=len(items), ms=_hg_ms(started))
        except Exception as exc:
            _hg_diag("PROBE", "danmaku", ok=0, code=_hg_err_code(exc),
                     detail=exc, ms=_hg_ms(started))
        if site_ok and dm_ok:
            verdict = "网络与签名链路都通，只有 video_model 被拒：签名/风控针对该接口"
            code = "HG_E_SIGN_REJECTED"
        elif not site_ok:
            verdict = "官网首页也不通：网络/DNS/代理问题，与签名无关"
            code = "HG_E_NET"
        else:
            verdict = "官网通但弹幕签名接口也失败：签名算法整体过期或设备身份被拒"
            code = "HG_E_SIGN_REJECTED"
        _hg_diag("PROBE", "verdict", code=code, note=verdict)
    except Exception:
        pass

def _text(value: Any) -> str:
    return str(value or "").strip()

def _first(*values: Any) -> str:
    for value in values:
        if isinstance(value, (list, tuple)):
            result = _first(*value)
        elif isinstance(value, Mapping):
            result = _first(
                value.get("url"),
                value.get("uri"),
                value.get("src"),
                value.get("download_url"),
                value.get("main_url"),
                value.get("backup_url"),
                value.get("backup_url_1"),
                value.get("play_addr"),
                value.get("url_list"),
            )
        else:
            result = _text(value)
        if result:
            return result
    return ""

def _trim_store(store: Any, cap: int = 512, max_age: float = 0.0) -> None:
    """给常驻进程用的字典裁剪：超量就丢最旧的（必要时先丢过期的）。

    影视仓里的 py 进程可能连跑几周不重启，这类"记一下 vid/剧集"的表
    如果没人裁剪，键值对会一直涨——属于典型的长稳隐患。
    dict 保序，所以 next(iter(store)) 拿到的就是最早写入的那个。
    """
    try:
        if not isinstance(store, dict):
            return
        if max_age > 0:
            cutoff = time.time() - max_age
            for key in [k for k, v in store.items() if isinstance(v, (int, float)) and v < cutoff]:
                store.pop(key, None)
        while len(store) > cap:
            try:
                store.pop(next(iter(store)))
            except StopIteration:
                break
    except Exception:
        pass

def _json_response(response: requests.Response, stage: str = "upstream") -> Any:
    """统一读上游响应：先把这次的硬指标写进诊断日志，再判断成不成功。

    2026-11-16 的教训：video_model 回 HTTP 200 + Content-Length: 0 时，旧代码
    只有一句「空响应」，看不出服务端到底回了什么（Server / x-tt-logid / 是否带
    Set-Cookie），排查全靠猜。现在固定一行 resp，并把失败归到 HG_E_* 错误码。
    """
    status = int(getattr(response, "status_code", 0) or 0)
    headers = getattr(response, "headers", None) or {}
    try:
        body = response.content
    except Exception:
        body = b""
    # 弹幕一轮要打 20 次，成功时不刷屏；失败或非弹幕一律留痕。
    if not (stage == "danmaku" and status == 200 and body):
        try:
            _hg_diag(
                "resp", stage,
                status=status,
                n=len(body),
                cl=_hg_clean(headers.get("Content-Length", ""), 20),
                ctype=_hg_clean(headers.get("Content-Type", ""), 60),
                srv=_hg_clean(headers.get("Server", ""), 40),
                logid=_hg_clean(headers.get("x-tt-logid", ""), 40),
                setck=("y" if headers.get("Set-Cookie") else "n"),
                head=("" if len(body) > 400 else _hg_body_snippet(body, 120)),
            )
        except Exception:
            pass
    if status >= 500:
        raise HongguoPluginError(
            "上游 HTTP %d" % status, code="HG_E_HTTP_5XX", detail=_hg_body_snippet(body)
        )
    if status >= 400:
        raise HongguoPluginError(
            "上游 HTTP %d" % status, code="HG_E_HTTP_4XX", detail=_hg_body_snippet(body)
        )
    if not body:
        raise HongguoPluginError(
            "上游取流接口返回空响应（HTTP %s）" % (status or "?"),
            code="HG_E_SIGN_REJECTED",
            detail=_hg_headers_brief(headers),
        )
    try:
        return response.json()
    except ValueError as exc:
        raise HongguoPluginError(
            "上游响应不是 JSON", code="HG_E_NON_JSON", detail=_hg_body_snippet(body)
        ) from exc

def _router_data(html: str) -> dict[str, Any]:
    match = re.search(r"(?:window\.)?_ROUTER_DATA\s*=\s*", html)
    if not match:
        raise HongguoPluginError("页面没有路由数据")
    try:
        value, _ = json.JSONDecoder().raw_decode(html[match.end() :])
    except json.JSONDecodeError as exc:
        raise HongguoPluginError("页面路由数据解析失败") from exc
    if not isinstance(value, dict):
        raise HongguoPluginError("页面路由数据格式错误")
    return value

def _media_url(item: Mapping[str, Any]) -> str:
    return _first(
        item.get("main_url"),
        item.get("backup_url"),
        item.get("backup_url_1"),
        item.get("play_addr"),
        item.get("url"),
    )

def _spade_value(item: Mapping[str, Any]) -> str:
    encrypt_info = item.get("encrypt_info")
    if not isinstance(encrypt_info, Mapping):
        encrypt_info = {}
    return _first(item.get("spade_a"), encrypt_info.get("spade_a"))

def derive_content_key(spade_b64: str) -> bytes:
    raw = _b64(spade_b64)
    if len(raw) < 3:
        raise HongguoPluginError("spade_a 太短")
    v8 = len(raw) - (raw[0] ^ raw[1] ^ raw[2]) + 47
    if v8 <= 0 or 1 + v8 > len(raw):
        v8 = len(raw) - 1
    if v8 < 33:
        raise HongguoPluginError("spade_a 长度异常")
    value = bytearray(raw[1 : 1 + v8])
    va, vb = 85, 246
    for index in range(v8):
        previous = va if index & 1 else vb
        if index & 1:
            va = value[index]
        else:
            vb = value[index]
        value[index] = (-21 - bin(index).count("1") + (previous ^ value[index])) & 0xFF
    try:
        return binascii.unhexlify(bytes(value[1:33]).decode("ascii"))
    except (ValueError, binascii.Error) as exc:
        raise HongguoPluginError("spade_a 密钥材料无效") from exc

def _find_box(data: memoryview, fourcc: bytes, start: int) -> tuple[int, int]:
    for index in range(max(4, start), len(data) - 4):
        if data[index : index + 4] != fourcc:
            continue
        size = struct.unpack(">I", data[index - 4 : index])[0]
        if size == 1 and index + 12 <= len(data):
            size = struct.unpack(">Q", data[index + 4 : index + 12])[0]
        if 8 <= size <= 5_000_000 and index - 4 + size <= len(data):
            return index - 4, size
    return -1, 0

def _box_body(data: memoryview, fourcc: bytes, start: int) -> memoryview | None:
    offset, size = _find_box(data, fourcc, start)
    return data[offset + 8 : offset + size] if offset >= 0 else None

def _parse_track(
    moov: memoryview,
    track_offset: int,
) -> tuple[list[int], list[int], list[int], list[int], int, int] | None:
    if track_offset < 0:
        return None
    stbl_offset, _ = _find_box(moov, b"stbl", track_offset + 8)
    if stbl_offset < 0:
        return None
    stsz = _box_body(moov, b"stsz", stbl_offset)
    stco = _box_body(moov, b"stco", stbl_offset)
    co64 = _box_body(moov, b"co64", stbl_offset)
    stsc = _box_body(moov, b"stsc", stbl_offset)
    saiz = _box_body(moov, b"saiz", stbl_offset)
    saio = _box_body(moov, b"saio", stbl_offset)
    if any(value is None for value in (stsz, stsc, saiz, saio)) or (
        stco is None and co64 is None
    ):
        return None
    assert stsz is not None and stsc is not None
    assert saiz is not None and saio is not None
    default_size = struct.unpack(">I", stsz[4:8])[0]
    sample_count = struct.unpack(">I", stsz[8:12])[0]
    sizes = (
        [default_size] * sample_count
        if default_size
        else [
            struct.unpack(">I", stsz[12 + index * 4 : 16 + index * 4])[0]
            for index in range(sample_count)
        ]
    )
    chunk_table = stco if stco is not None else co64
    assert chunk_table is not None
    chunk_count = struct.unpack(">I", chunk_table[4:8])[0]
    chunk_width = 4 if stco is not None else 8
    offsets = [
        int.from_bytes(
            chunk_table[
                8 + index * chunk_width : 8 + (index + 1) * chunk_width
            ],
            "big",
        )
        for index in range(chunk_count)
    ]
    entry_count = struct.unpack(">I", stsc[4:8])[0]
    entries = [
        (
            struct.unpack(">I", stsc[8 + index * 12 : 12 + index * 12])[0],
            struct.unpack(">I", stsc[12 + index * 12 : 16 + index * 12])[0],
        )
        for index in range(entry_count)
    ]
    chunk_samples = [0] * chunk_count
    for index, (first_chunk, samples_per_chunk) in enumerate(entries):
        end = entries[index + 1][0] - 1 if index + 1 < len(entries) else chunk_count
        for chunk in range(first_chunk - 1, min(end, chunk_count)):
            chunk_samples[chunk] = samples_per_chunk
    saiz_flags = int.from_bytes(saiz[1:4], "big")
    saiz_cursor = 12 if saiz_flags & 1 else 4
    if len(saiz) < saiz_cursor + 5:
        return None
    default_aux_size = saiz[saiz_cursor]
    aux_count = struct.unpack(">I", saiz[saiz_cursor + 1 : saiz_cursor + 5])[0]
    aux_sizes = (
        [default_aux_size] * aux_count
        if default_aux_size
        else [
            int(saiz[saiz_cursor + 5 + index])
            for index in range(aux_count)
            if saiz_cursor + 5 + index < len(saiz)
        ]
    )
    if len(aux_sizes) != aux_count:
        return None
    saio_flags = int.from_bytes(saio[1:4], "big")
    saio_cursor = 12 if saio_flags & 1 else 4
    offset_width = 8 if saio[0] == 1 else 4
    if len(saio) < saio_cursor + 4 + offset_width:
        return None
    entry_count = int.from_bytes(saio[saio_cursor : saio_cursor + 4], "big")
    if entry_count < 1:
        return None
    aux_offset = int.from_bytes(
        saio[saio_cursor + 4 : saio_cursor + 4 + offset_width],
        "big",
    )
    return sizes, offsets, chunk_samples, aux_sizes, aux_offset, sample_count

def _replace_sinf(data: bytearray) -> None:
    # sinf 盒的首个子盒必为 frma（CENC 规范：frma/schm/schi）。
    # 这里校验后再清零，避免把 avcC/hvcC 配置数据里恰好出现的 "sinf" 字节
    # 当成盒来清零，那样会毁掉解码器配置，表现为视轨丢失/只有声音。
    _sinf_children = (b"frma", b"schm", b"schi")
    position = 0
    while True:
        position = data.find(b"sinf", position)
        if position < 0:
            return
        if position >= 4:
            size = struct.unpack(">I", data[position - 4 : position])[0]
            end = position - 4 + size
            child = bytes(data[position + 8 : position + 12])
            if 8 <= size < 50_000 and end <= len(data) and child in _sinf_children:
                data[position : position + 4] = b"free"
                data[position + 4 : end] = b"\x00" * max(0, end - position - 4)
                position = end
                continue
        position += 4

def decrypt_mp4_cenc(data: bytes, content_key: bytes) -> bytes:
    if len(content_key) != 16:
        raise HongguoPluginError("CENC 密钥长度错误")
    result = bytearray(data)
    if len(result) < 16:
        raise HongguoPluginError("MP4 数据过短")
    moov_start, moov_size = _find_box(memoryview(result), b"moov", 0)
    if moov_start < 0 or moov_size < 8:
        raise HongguoPluginError("MP4 moov 越界")
    moov = memoryview(result)[moov_start : moov_start + moov_size]
    tracks: list[int] = []
    track_search = 0
    while True:
        track, track_size = _find_box(moov, b"trak", track_search)
        if track < 0:
            break
        tracks.append(track)
        track_search = track + max(track_size, 8)
    decrypted_samples = 0
    for track in tracks:
        parsed = _parse_track(moov, track)
        if parsed is None:
            continue
        sizes, offsets, chunk_counts, aux_sizes, aux_offset, sample_count = parsed
        aux_size = sum(max(size, 8) for size in aux_sizes)
        if not sample_count or aux_offset < 0 or aux_offset + aux_size > len(result):
            continue
        aux = result[aux_offset : aux_offset + aux_size]
        sample_index = 0
        aux_index = 0
        for chunk_index, chunk_offset in enumerate(offsets):
            current = chunk_offset
            for _ in range(chunk_counts[chunk_index]):
                if sample_index >= sample_count or sample_index >= len(sizes):
                    break
                size = sizes[sample_index]
                if current + size > len(result):
                    raise HongguoPluginError("MP4 样本越界")
                if sample_index >= len(aux_sizes):
                    raise HongguoPluginError("MP4 辅助信息数量不足")
                entry_size = max(aux_sizes[sample_index], 8)
                iv = bytes(aux[aux_index : aux_index + min(entry_size, 8)]).ljust(
                    8, b"\0"
                ) + b"\0" * 8
                result[current : current + size] = _aes_ctr_decrypt(
                    content_key, iv, bytes(result[current : current + size])
                )
                current += size
                sample_index += 1
                aux_index += entry_size
                decrypted_samples += 1
    if not decrypted_samples:
        raise HongguoPluginError("MP4 没有可解密的 CENC 样本")
    moov_buffer = bytearray(result[moov_start : moov_start + moov_size])
    _restore_cenc_codecs(moov_buffer)
    _replace_sinf(moov_buffer)
    result[moov_start : moov_start + moov_size] = moov_buffer
    return bytes(result)

MEDIA_HEADERS = {"User-Agent": MEDIA_UA, "Referer": "https://novel.snssdk.com/"}

_STREAM_PORT_RANGE = (10010, 10030)
# 每块越小，播放器拿到首字节越快：CENC 是整块解密完才吐，1MB 一块在纯 Python
# AES 下要 2~8 秒才出声（真机表现为一直转圈、进度条不动）。128KB 一块首字节不到 1 秒，
# 总吞吐不变（下游按 64KB 连续写）。
_STREAM_CHUNK = 1 << 17
_STREAM_HEAD_PROBE = 1 << 16
_STREAM_TTL_SECONDS = 900
_STREAM_MAX_SESSIONS = 4
_STREAM_INFLIGHT_WAIT = 60
# 建会话（取 video_model + 拉 moov）冷启动约 3~18s；播放器连上来时最多等这么久，
# 超过就带着已有的会话继续，别把响应头拖过播放器的读超时。
_STREAM_WARM_WAIT = 15
_STREAM_STATE: dict[str, Any] = {"port": 0, "server": None, "sessions": {}, "inflight": {}}
_STREAM_LOCK = threading.RLock()


def _toplevel_boxes(buf: bytes) -> list[tuple[int, int, bytes]]:
    boxes: list[tuple[int, int, bytes]] = []
    cursor = 0
    while cursor + 8 <= len(buf):
        size = struct.unpack(">I", buf[cursor : cursor + 4])[0]
        fourcc = bytes(buf[cursor + 4 : cursor + 8])
        if size == 1:
            if cursor + 16 > len(buf):
                break
            size = struct.unpack(">Q", buf[cursor + 8 : cursor + 16])[0]
        if size < 8:
            break
        boxes.append((cursor, size, fourcc))
        cursor += size
    return boxes


_MEDIA_TLS = threading.local()


def _media_session() -> "requests.Session":
    """拉媒体分片用的线程本地 session（keep-alive），省掉每块重新握手。"""
    ses = getattr(_MEDIA_TLS, "s", None)
    if ses is None:
        ses = requests.Session()
        ses.trust_env = False
        ses.headers.update(MEDIA_HEADERS)
        _MEDIA_TLS.s = ses
    return ses


def _range_get(url: str, start: int, end: int) -> tuple[bytes, int]:
    headers = {"Range": "bytes=%d-%d" % (start, end)}
    expected = end - start + 1
    last_error: Exception | None = None
    for attempt in range(_RANGE_FETCH_ATTEMPTS):
        if attempt:
            time.sleep(_RANGE_FETCH_BACKOFF_SECONDS * attempt)
        try:
            response = _media_session().get(url, headers=headers, timeout=60)
        except requests.RequestException as error:
            last_error = error
            continue
        if response.status_code not in (200, 206):
            last_error = HongguoPluginError(
                "媒体分片请求失败 %s" % response.status_code,
                code="HG_E_RANGE",
                detail="range=bytes=%d-%d %s" % (start, end, _hg_headers_brief(response.headers)),
            )
            _hg_diag("range", "非 206", status=response.status_code,
                     range="%d-%d" % (start, end), n=_hg_ms(0),
                     srv=_hg_clean(response.headers.get("Server", ""), 40),
                     head=_hg_body_snippet(response.content, 100))
            continue
        body = response.content
        # 上游偶发返回短包；短于请求长度时重试，避免播放器收到截断数据。
        if not body or (response.status_code == 206 and len(body) < expected):
            last_error = HongguoPluginError(
                "媒体分片长度不足 %d/%d" % (len(body), expected),
                code="HG_E_RANGE",
            )
            _hg_diag("range", "短包", status=response.status_code,
                     got=len(body), want=expected, range="%d-%d" % (start, end))
            continue
        total = 0
        content_range = response.headers.get("Content-Range") or ""
        if "/" in content_range:
            tail = content_range.rsplit("/", 1)[1].strip()
            if tail.isdigit():
                total = int(tail)
        if not total:
            length = response.headers.get("Content-Length") or ""
            total = int(length) if length.isdigit() else 0
        return body, total
    if last_error is None:
        last_error = HongguoPluginError("媒体分片请求失败", code="HG_E_RANGE")
    raise last_error


def _fetch_moov(url: str) -> tuple[int, int, bytes]:
    started = time.time()
    probe, total = _range_get(url, 0, _STREAM_HEAD_PROBE - 1)
    if not total:
        raise HongguoPluginError("媒体总长度未知", code="HG_E_NO_MOOV",
                                 detail="host=%s" % urlparse(url).netloc)
    moov_start = 0
    moov_size = 0
    for offset, size, fourcc in _toplevel_boxes(probe):
        if fourcc == b"moov":
            moov_start = offset
            moov_size = size
            break
    if not moov_size:
        raise HongguoPluginError(
            "未找到 moov 顶层盒", code="HG_E_NO_MOOV",
            detail="host=%s total=%d boxes=%s" % (
                urlparse(url).netloc, total,
                ",".join(item[2].decode("latin-1", "replace") for item in _toplevel_boxes(probe)[:6]),
            ),
        )
    if moov_start + moov_size > total:
        raise HongguoPluginError(
            "moov 越界", code="HG_E_NO_MOOV",
            detail="start=%d size=%d total=%d" % (moov_start, moov_size, total),
        )
    if moov_start + moov_size <= len(probe):
        return total, moov_start, bytes(probe[moov_start : moov_start + moov_size])
    moov, _ = _range_get(url, moov_start, moov_start + moov_size - 1)
    if len(moov) != moov_size:
        raise HongguoPluginError("moov 分片长度不符", code="HG_E_NO_MOOV",
                                 detail="got=%d want=%d" % (len(moov), moov_size))
    _hg_diag("moov", "ok", host=urlparse(url).netloc, total=total,
             start=moov_start, size=moov_size, ms=_hg_ms(started))
    return total, moov_start, moov


# 解码器配置盒 -> 真实 sample entry 四字符码。
# CENC 的 sinf/frma 缺失或无效时，这是判断真实编码最可靠的依据：
# 一律兜底 avc1 会把 HEVC(hvc1) 错标成 H.264，播放器按错编码解视轨，
# 表现为「有声音没画面 / 视轨缺失」——这正是低清晰度线路只有超清能看的原因。
_CONFIG_BOX_TO_FORMAT = (
    (b"hvcC", b"hvc1"),
    (b"hev1C", b"hev1"),
    (b"av1C", b"av01"),
    (b"vpcC", b"vp09"),
    (b"avcC", b"avc1"),
    (b"dvvC", b"dvh1"),
    (b"dvhC", b"dvh1"),
)
_AUDIO_CONFIG_BOX_TO_FORMAT = (
    (b"esds", b"mp4a"),
    (b"opusC", b"Opus"),
    (b"ac-3", b"ac-3"),
    (b"ec-3", b"ec-3"),
)


def _format_from_config_box(blob: bytes, kind: bytes) -> bytes:
    """按 sample entry 内的解码器配置盒推断真实编码，找不到返回空串。"""
    probes = _AUDIO_CONFIG_BOX_TO_FORMAT + _CONFIG_BOX_TO_FORMAT if kind == b"enca" \
        else _CONFIG_BOX_TO_FORMAT + _AUDIO_CONFIG_BOX_TO_FORMAT
    hit_pos, hit_fmt = -1, b""
    for fourcc, fmt in probes:
        pos = blob.find(fourcc)
        # 取最靠前的配置盒：sample entry 内通常只含一个，靠前者更可能是本轨的配置
        if pos >= 0 and (hit_pos < 0 or pos < hit_pos):
            hit_pos, hit_fmt = pos, fmt
    return hit_fmt


def _original_format_near(data: bytearray, entry_pos: int, default: bytes, kind: bytes = b"encv") -> bytes:
    """从 sample entry 后的 sinf/frma 读取原始四字符码（avc1/hvc1/mp4a 等）。
    frma 缺失/无效时回退到配置盒探测，而不是一律兜底 avc1。"""
    blob = bytes(data[entry_pos : min(len(data), entry_pos + 800)])
    idx = 0
    while True:
        pos = blob.find(b"frma", idx)
        if pos < 0:
            break
        if pos + 8 <= len(blob):
            fmt = bytes(blob[pos + 4 : pos + 8])
            if fmt not in (b"", b"\x00\x00\x00\x00", b"encv", b"enca") and all(32 <= c < 127 for c in fmt):
                return fmt
        idx = pos + 4
    probed = _format_from_config_box(blob, kind)
    return probed or default


def _restore_cenc_codecs(data: bytearray) -> None:
    """把 encv/enca 还原为真实编码（frma 优先，其次按 avcC/hvcC 等配置盒判定）。
    避免一律改成 avc1/hvc1 导致非对应编码的视轨解不出画面。"""
    pos = 0
    while True:
        pos = data.find(b"encv", pos)
        if pos < 0:
            break
        data[pos : pos + 4] = _original_format_near(data, pos, b"avc1", b"encv")
        pos += 4
    pos = 0
    while True:
        pos = data.find(b"enca", pos)
        if pos < 0:
            break
        data[pos : pos + 4] = _original_format_near(data, pos, b"mp4a", b"enca")
        pos += 4


def _moov_has_video_track(moov: bytes) -> bool:
    """moov 中是否存在 hdlr='vide' 的轨。用于校验某清晰度是否真的带视轨。"""
    view = memoryview(moov)
    search = 0
    found_trak = False
    while True:
        trak, trak_size = _find_box(view, b"trak", search)
        if trak < 0:
            break
        found_trak = True
        search = trak + max(trak_size, 8)
        hdlr = _box_body(view, b"hdlr", trak + 8)
        if hdlr is not None and len(hdlr) >= 12:
            if bytes(hdlr[8:12]) == b"vide":
                return True
    # 解析不出任何 trak 时不轻易判死刑，交由后续解密流程定夺
    return not found_trak


def _rewrite_moov(moov: bytes) -> bytes:
    result = bytearray(moov)
    _restore_cenc_codecs(result)
    _replace_sinf(result)
    return bytes(result)


def _sample_table(moov: bytes, moov_start: int) -> list[tuple[int, int, bytes]]:
    view = memoryview(moov)
    samples: list[tuple[int, int, bytes]] = []
    track_search = 0
    while True:
        track, track_size = _find_box(view, b"trak", track_search)
        if track < 0:
            break
        track_search = track + max(track_size, 8)
        parsed = _parse_track(view, track)
        if parsed is None:
            continue
        sizes, offsets, chunk_counts, aux_sizes, aux_offset, sample_count = parsed
        aux_length = sum(max(size, 8) for size in aux_sizes)
        aux_local = aux_offset - moov_start
        if aux_local < 0 or aux_local + aux_length > len(moov):
            raise HongguoPluginError("CENC 辅助信息不在 moov 内，无法流式解密")
        aux = moov[aux_local : aux_local + aux_length]
        sample_index = 0
        aux_index = 0
        for chunk_index, chunk_offset in enumerate(offsets):
            current = chunk_offset
            for _ in range(chunk_counts[chunk_index]):
                if sample_index >= sample_count or sample_index >= len(sizes):
                    break
                if sample_index >= len(aux_sizes):
                    raise HongguoPluginError("CENC 辅助信息数量不足")
                entry_size = max(aux_sizes[sample_index], 8)
                initial_vector = bytes(
                    aux[aux_index : aux_index + min(entry_size, 8)]
                ).ljust(8, b"\0") + b"\0" * 8
                samples.append((current, sizes[sample_index], initial_vector))
                current += sizes[sample_index]
                aux_index += entry_size
                sample_index += 1
    if not samples:
        raise HongguoPluginError("moov 中没有可解密的 CENC 样本")
    samples.sort()
    return samples



_HG_Q_TO_QTYPE = {"2160": "0", "1440": "2", "1080": "1", "720": "10", "540": "20", "480": "30", "360": "40"}
_Q_LABEL = {"2160": "原画", "1440": "蓝光", "1080": "超清", "720": "高清", "540": "标准", "480": "流畅", "360": "极速"}
_QTYPE_TO_Q = {"0": "2160", "2": "1440", "1": "1080", "10": "720", "20": "540", "30": "480", "40": "360"}
# 壳里播放器认得的标准视轨四字符码；bvc2（ByteVC2）不在其中，只出声音不出画面
_DECODABLE_ENTRIES = (b"hvc1", b"hev1", b"avc1", b"avc3")


def _hg_entry_is_bytevc2(item: Any) -> bool:
    """单个清晰度条目是不是 ByteVC2（壳解不了，会黑屏只有声音）。"""
    return isinstance(item, Mapping) and "bytevc2" in str(item.get("gear_des_key") or "")


def _hg_is_bytevc2(rows: Any) -> bool:
    try:
        return any(_hg_entry_is_bytevc2(x) for x in (rows or []))
    except Exception:
        return False


_VIDEO_FOURCCS = (b"hvc1", b"hev1", b"hvc2", b"hev2", b"avc1", b"avc3",
                  b"bvc2", b"bv2C", b"av01", b"vp09", b"encv")


def _hg_moov_fourcc(moov: bytes) -> bytes:
    """从 moov 的 stsd 里取视轨 sample entry 四字符码。

    注意 moov 里音轨、视轨各有一个 stsd，谁在前不固定（实测《反向拿捏2》第 8 集
    兜底直链的 moov 是音轨 mp4a 在前）。只认第一个 stsd 会把 hvc1 误判成 mp4a，
    于是明明能播的 hvc1 直链被验成不可播。这里按顺序找第一个「视频类」四字符码。
    """
    first = b""
    i = moov.find(b"stsd")
    pos = 0
    while i >= 0:
        j = i + 4 + 8
        cc = bytes(moov[j + 4 : j + 8])
        if not first:
            first = cc
        if cc in _VIDEO_FOURCCS:
            return cc
        pos = i + 4
        i = moov.find(b"stsd", pos)
    return first


def _hg_plain_candidates(model: Mapping[str, Any], quality: str = "1080", strict: bool = False) -> list:
    """备用接口（codec_type=1）的标准 hvc1 直链候选。

    只收非 bytevc2 且能解出地址的条目；返回 [(url, size), ...]。
    strict=True 时只认这一档自己的清晰度，绝不跨档串用（防止 1080 被换成 720）。
    """
    fb = _fallback_api_value(model.get("fallback_api") if isinstance(model, Mapping) else None)
    if not fb:
        _hg_diag("plain", "模型里没有 fallback_api", q=quality, strict=int(bool(strict)))
        return []
    api = re.sub(r"codec_type=\d+", "codec_type=1", fb)
    if "codec_type=" not in api:
        api = api + ("&" if "?" in api else "?") + "codec_type=1"
    j = None
    last_status = 0
    for _i in range(2):
        try:
            r = requests.get(api, headers={"User-Agent": APP_UA}, timeout=8)
            last_status = r.status_code
            if r.status_code == 200:
                j = r.json()
                if isinstance(j, Mapping):
                    break
            else:
                _hg_diag("plain", "备用接口非 200", n=_i + 1, status=r.status_code,
                         head=_hg_body_snippet(r.content, 100))
        except Exception as exc:
            j = None
            _hg_diag("plain", "备用接口请求失败", n=_i + 1,
                     code=_hg_err_code(exc), detail=exc)
        try:
            time.sleep(0.3)
        except Exception:
            pass
    if not isinstance(j, Mapping):
        _hg_diag("plain", "备用接口没有可用 JSON", q=quality, status=last_status)
        return []
    data = j
    for key in ("video_info", "data"):
        if isinstance(data.get(key), Mapping):
            data = data[key]
    if isinstance(data.get("data"), Mapping):
        data = data["data"]
    raw_list = data.get("video_list") or {}
    items = list(raw_list.values()) if isinstance(raw_list, Mapping) else [x for x in raw_list if isinstance(x, Mapping)]
    if not items:
        _hg_diag("plain", "备用接口 video_list 为空", q=quality)
        return []
    seed = _key_seed_from_model(data)
    first = _HG_Q_TO_QTYPE.get(str(quality), "1")
    if strict:
        order = [first]
    else:
        order = [first] + [q for q in ("0", "2", "1", "10", "20", "30", "40") if q != first]
    out = []
    seen = set()
    for qt in order:
        for it in items:
            if not isinstance(it, Mapping) or _hg_entry_is_bytevc2(it):
                continue
            if str(it.get("quality_type") or "") != qt:
                continue
            raw = _text(it.get("main_url"))
            pick = raw
            if seed and raw and not raw.startswith("http"):
                try:
                    pick = _decrypt_spade_url(raw, seed) or raw
                except Exception:
                    pick = raw
            if not pick.startswith("http") or pick in seen:
                continue
            seen.add(pick)
            out.append((pick, int(it.get("size") or 0)))
    _hg_diag("plain", "候选直链", q=quality, strict=int(bool(strict)), n=len(out))
    return out


def _hg_entry_size(item: Any) -> int:
    """从模型条目里取字节数（video_meta.size 优先，缺了看顶层 size）。"""
    try:
        if not isinstance(item, Mapping):
            return 0
        vm = item.get("video_meta")
        if isinstance(vm, Mapping) and vm.get("size"):
            return int(vm.get("size") or 0)
        return int(item.get("size") or 0)
    except Exception:
        return 0


def _hg_plain_url_session(url: str, size: int = 0) -> Any:
    """上游本就是未加密直链时，验成标准 hvc1/avc1 且中段 206 才返回直通会话。

    站点对部分集数给的是 1:normal（没有 encrypt_info）：这类流不需要解密，
    但同样不能把 bytevc2 或加密壳丢给播放器，所以沿用同一套四字符码 + 视频轨 + 中段校验。
    """
    if not isinstance(url, str) or not url.startswith("http"):
        return None
    try:
        total, _moov_start, moov = _fetch_moov(url)
    except Exception as exc:
        _hg_diag("plain", "直链没有可用 moov", host=urlparse(url).netloc,
                 code=_hg_err_code(exc), detail=exc)
        return None
    fourcc = _hg_moov_fourcc(moov)
    if fourcc not in _DECODABLE_ENTRIES:
        _hg_diag("plain", "直链编码壳不认", host=urlparse(url).netloc,
                 fourcc=fourcc.decode("latin-1", "replace"))
        return None
    if not _moov_has_video_track(moov):
        _hg_diag("plain", "直链没有视频轨", host=urlparse(url).netloc)
        return None
    mid = max((total or size) // 2, 1024)
    try:
        head = requests.get(
            url,
            headers={"Range": "bytes=%d-%d" % (mid, mid + 1023), "User-Agent": MEDIA_UA},
            timeout=8,
        )
        if head.status_code != 206:
            _hg_diag("plain", "直链中段不是 206", status=head.status_code,
                     host=urlparse(url).netloc)
            return None
    except Exception as exc:
        _hg_diag("plain", "直链中段请求失败", code=_hg_err_code(exc), detail=exc)
        return None
    _hg_diag("plain", "直链可用", host=urlparse(url).netloc, total=total or size)
    return _PlainSession(url, total or size)


def _hg_plain_session(model: Mapping[str, Any], quality: str = "1080", strict: bool = True) -> Any:
    """挑一条确认是标准 hvc1/avc1、且能按 Range 取中段（可 seek）的直通流。

    三条候选都验不过就返回 None，交给调用方报错重试，绝不把 bvc2 丢给播放器。
    """
    candidates = _hg_plain_candidates(model, quality, strict)[:3]
    for url, size in candidates:
        sess = _hg_plain_url_session(url, size)
        if sess is not None:
            return sess
    _hg_diag("plain", "没有可用直链", q=quality, strict=int(bool(strict)), tried=len(candidates))
    return None


class _StreamSession:
    """按 Range 逐块拉取加密 MP4，边下边解 CENC，供本地播放器直连。"""

    def __init__(
        self,
        url: str,
        content_key: bytes,
        total: int,
        moov_start: int,
        moov: bytes,
    ) -> None:
        if len(content_key) != 16:
            raise HongguoPluginError("CENC 密钥长度错误")
        self.url = url
        self.content_key = content_key
        self.total = total
        self.moov_start = moov_start
        self.moov_plain = _rewrite_moov(moov)
        self.moov_end = moov_start + len(moov)
        self.samples = _sample_table(moov, moov_start)
        self.offsets = [item[0] for item in self.samples]
        self.created = time.time()

    def expired(self) -> bool:
        return time.time() - self.created > _STREAM_TTL_SECONDS

    def _patch(self, buffer: bytearray, base: int) -> None:
        end = base + len(buffer) - 1
        index = max(bisect.bisect_right(self.offsets, base) - 1, 0)
        while index < len(self.samples):
            offset, size, initial_vector = self.samples[index]
            index += 1
            if offset > end:
                break
            if offset + size <= base:
                continue
            first = max(offset, base)
            last = min(offset + size - 1, end)
            skip = first - offset
            counter = (
                (int.from_bytes(initial_vector, "big") + skip // 16)
                & ((1 << 128) - 1)
            ).to_bytes(16, "big")
            padding = skip % 16
            plain = _aes_ctr_decrypt(
                self.content_key,
                counter,
                b"\0" * padding + bytes(buffer[first - base : last - base + 1]),
            )
            buffer[first - base : last - base + 1] = plain[padding:]
        if base < self.moov_end and end >= self.moov_start:
            first = max(base, self.moov_start)
            last = min(end, self.moov_end - 1)
            buffer[first - base : last - base + 1] = self.moov_plain[
                first - self.moov_start : last - self.moov_start + 1
            ]

    def read_range(self, start: int, end: int) -> bytes:
        raw, _ = _range_get(self.url, start, end)
        if not raw:
            raise HongguoPluginError("媒体分片为空")
        buffer = bytearray(raw)
        self._patch(buffer, start)
        return bytes(buffer)

    def iter_range(self, start: int, end: int):
        cursor = start
        while cursor <= end:
            stop = min(cursor + _STREAM_CHUNK - 1, end)
            block = self.read_range(cursor, stop)
            yield block
            cursor += len(block)


def _fresh_device_pair() -> tuple[str, str]:
    return (
        str(random.randint(10**17, 10**18 - 1)),
        str(random.randint(10**17, 10**18 - 1)),
    )


# ---- 设备身份持久化 ----
# 重启 App 后沿用同一台「已注册设备」，服务端信任随使用累积；
# 每次都换新设备 = 永远零信任，容易撞风控限额（如只能看前几集）。
_DEVICE_FILE = "hg_device.json"


def _device_file_path() -> str:
    try:
        return os.path.join(_hg_cache_dir(), _DEVICE_FILE)
    except Exception:
        return ""


def _load_persisted_device() -> dict[str, str] | None:
    try:
        path = _device_file_path()
        if not path or not os.path.isfile(path):
            return None
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        did = _text(data.get("device_id"))
        iid = _text(data.get("install_id"))
        if did.isdigit() and iid.isdigit() and did != "0" and iid != "0":
            return {"device_id": did, "install_id": iid}
    except Exception:
        pass
    return None


def _persist_device(pair: Mapping[str, Any]) -> None:
    try:
        did = _text(pair.get("device_id"))
        iid = _text(pair.get("install_id"))
        path = _device_file_path()
        if not (did and iid and path):
            return
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump({"device_id": did, "install_id": iid}, fh)
        os.replace(tmp, path)
    except Exception:
        pass


def _is_empty_model_error(err: BaseException) -> bool:
    text = str(err)
    return (
        "video_model 数据为空" in text
        or "video_model 为空" in text
        or "上游响应不是 JSON" in text
        or "返回空响应" in text
        or "播放模型没有清晰度" in text
        or "播放模型缺少地址或密钥材料" in text
    )


def _register_device_pair() -> tuple[str, str] | None:
    try:
        import uuid as _uuid
        openudid = "".join(random.choice("0123456789abcdef") for _ in range(16))
        # 版本号与播放链路（APP_UA / _video_model 参数）保持一致：
        # 同一设备注册时 73532、播放时 71332 的版本矛盾是服务端风控的明显异常点。
        header = {"display_name": "红果免费短剧", "aid": 8662, "app_version": "7.1.3.32", "version_code": 71332, "manifest_version_code": 71332, "update_version_code": 71332, "channel": "update_64", "package": "com.phoenix.read", "app_language": "zh", "os": "Android", "os_version": "16", "os_api": 36, "device_model": "25053RT47C", "device_brand": "Redmi", "device_manufacturer": "Xiaomi", "cpu_abi": "arm64-v8a", "density_dpi": 520, "display_density": "xxhdpi", "resolution": "2772x1280", "language": "zh", "timezone": 8, "access": "wifi", "openudid": openudid, "clientudid": str(_uuid.uuid4()), "cdid": str(_uuid.uuid4()), "region": "CN", "tz_name": "Asia/Shanghai", "tz_offset": 28800, "sim_region": "cn", "device_platform": "android", "not_request_sender": 0, "is_system_app": 0, "sdk_flavor": "china", "rom": "OS2.0", "rom_version": "BP2A.250605.031.A3"}
        body = json.dumps({"magic_tag": "ss_app_log", "header": header, "_gen_time": int(time.time() * 1000)}).encode("utf-8")
        qs = urlencode({"req_id": str(_uuid.uuid4()), "_rticket": int(time.time() * 1000)})
        resp = requests.post(
            "https://log.snssdk.com/service/2/device_register/?" + qs,
            data=body,
            headers={"User-Agent": APP_UA, "Accept": "application/json", "Content-Type": "application/json; charset=utf-8"},
            timeout=20,
        )
        if resp.status_code != 200:
            _hg_diag("device", "register 非 200", status=resp.status_code,
                     head=_hg_body_snippet(resp.content, 120))
            return None
        data = resp.json()
        did = str(data.get("device_id_str") or data.get("device_id") or "")
        iid = str(data.get("install_id_str") or data.get("install_id") or "")
        if did.isdigit() and iid.isdigit() and did != "0" and iid != "0":
            return did, iid
        _hg_diag("device", "register 回包没有有效 did/iid",
                 keys=",".join(list(data.keys())[:8]) if isinstance(data, Mapping) else "-")
    except Exception as exc:
        _hg_diag("device", "register 异常", code=_hg_err_code(exc), detail=exc)
    return None


def _rotate_stream_device() -> dict[str, str]:
    registered = _register_device_pair()
    if registered is not None:
        device_id, install_id = registered
        is_registered = True
        _persist_device({"device_id": device_id, "install_id": install_id})
    else:
        device_id, install_id = _fresh_device_pair()
        is_registered = False
    pair = {"device_id": device_id, "install_id": install_id}
    with _STREAM_LOCK:
        stored = dict(pair)
        stored["registered"] = is_registered
        _STREAM_STATE["device"] = stored
    # 随机号取流必回空体，所以「这一轮用的到底是不是注册号」必须写死进日志。
    _hg_diag("device", "adopt", registered=int(is_registered),
             did=_hg_tail(device_id), iid=_hg_tail(install_id))
    return pair


def _working_device_pair() -> dict[str, str] | None:
    with _STREAM_LOCK:
        pair = _STREAM_STATE.get("device")
    if isinstance(pair, dict) and pair.get("device_id") and pair.get("install_id"):
        return {"device_id": str(pair["device_id"]), "install_id": str(pair["install_id"])}
    # 内存没有（App 刚重启）→ 恢复本机持久化的已注册设备，沿用旧身份而不是重开新号
    persisted = _load_persisted_device()
    if persisted is not None:
        with _STREAM_LOCK:
            stored = dict(persisted)
            stored["registered"] = True
            _STREAM_STATE["device"] = stored
    return persisted


# ===================== 官方 profile 签名（2026-11-24 移植自 hongguo.js） =====================
# hongguo.js 内嵌运行时的官方签名（profile v04.10.03-ml-android）整套纯 Python 转写：
# x-gorgon / x-khronos / x-ladon / x-argus / x-helios / x-medusa + SM3 + third 表 +
# V5 白盒流密码（内嵌 lzma 数据表）。与 Node 原实现 42 组黄金向量（覆盖全部 16 种
# selector 分支、GET/POST）逐字节比对一致。取流与官方取季（plan/v）共用本签名。
_HG_PROFILE_SIGN_BLOB = (
    "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"
)
_HG_PROFILE_NS = {"__name__": "hg_profile_sign"}
exec(compile(lzma.decompress(base64.b64decode(_HG_PROFILE_SIGN_BLOB)).decode("utf-8"),
             "hg_profile_sign", "exec"), _HG_PROFILE_NS)

_HG_PROFILE_QUERY_BASE = {
    "ac": "wifi", "channel": "update_64", "aid": "8662", "app_name": "novelread",
    "version_code": "73932", "version_name": "7.3.9.32", "device_platform": "android",
    "os": "android", "ssmix": "a", "device_type": "25053RT47C", "device_brand": "Redmi",
    "language": "zh", "os_api": "36", "os_version": "16", "manifest_version_code": "73932",
    "resolution": "1280*2772", "dpi": "520", "update_version_code": "73932",
    "host_abi": "arm64-v8a", "dragon_device_type": "phone", "pv_player": "73932",
    "compliance_status": "0", "need_personal_recommend": "1", "player_so_load": "1",
    "is_android_pad_screen": "0",
}


def _hg_profile_canon(params):
    """hongguo.js Ni 的等价实现：encodeURIComponent 后把 !'() 转成大写 %XX（* 保留字面）。"""
    def _enc(value):
        text = quote(str(value if value is not None else ""), safe="!*()")
        return "".join(("%02X" % ord(ch)) if ch in "!'()" else ch for ch in text)
    return "&".join("%s=%s" % (_enc(k), _enc(v)) for k, v in params.items())


_HG_PROFILE_DEVICE_LOCK = threading.Lock()


def _hg_profile_device():
    """profile 签名专用设备：按官方 he 参数（73932 版本）注册，注册/查询版本一致，
    避免与主链路 71332 设备互相干扰。失败时回退主链路设备号。"""
    with _HG_PROFILE_DEVICE_LOCK:
        pair = _STREAM_STATE.get("profile_device")
        if isinstance(pair, dict) and pair.get("device_id") and pair.get("install_id"):
            return {"device_id": str(pair["device_id"]), "install_id": str(pair["install_id"])}
    persisted = None
    try:
        path = os.path.join(_hg_diag_dir() or "/sdcard/Download", "hg_device_profile.json")
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            did = _text(data.get("device_id"))
            iid = _text(data.get("install_id"))
            if did.isdigit() and iid.isdigit() and did != "0" and iid != "0":
                persisted = {"device_id": did, "install_id": iid}
    except Exception:
        persisted = None
    if persisted is not None:
        with _HG_PROFILE_DEVICE_LOCK:
            _STREAM_STATE["profile_device"] = dict(persisted)
        return persisted
    try:
        import uuid as _uuid
        cdid = str(_uuid.uuid4())
        openudid = "".join(random.choice("0123456789abcdef") for _ in range(16))
        header = {"aid": 8662, "app_name": "novelread", "package": "com.phoenix.read",
                  "app_version": "7.3.9.32", "version_code": 73932, "update_version_code": 73932,
                  "manifest_version_code": 73932, "sdk_version": "6.18.0",
                  "device_platform": "android", "os": "Android", "os_version": "16", "os_api": 36,
                  "device_model": "25053RT47C", "device_brand": "Redmi", "device_manufacturer": "Xiaomi",
                  "density_dpi": 520, "display_density": "mdpi", "resolution": "1280x2772",
                  "language": "zh", "timezone": 8, "access": "wifi", "channel": "update_64",
                  "cdid": cdid, "openudid": openudid}
        body = json.dumps({"magic_tag": "ss_app_log", "header": header,
                           "_gen_time": int(time.time() * 1000)}).encode("utf-8")
        resp = requests.post(
            "https://log.snssdk.com/service/2/device_register/?aid=8662&app_name=novelread",
            data=body,
            headers={"User-Agent": APP_UA, "Content-Type": "application/json; charset=utf-8"},
            timeout=15)
        data = resp.json() if resp.status_code == 200 else {}
        d = data.get("data") if isinstance(data.get("data"), dict) else data
        did = str(d.get("device_id_str") or "")
        iid = str(d.get("install_id_str") or "")
        if did.isdigit() and iid.isdigit() and did != "0" and iid != "0":
            pair = {"device_id": did, "install_id": iid}
            try:
                path = os.path.join(_hg_diag_dir() or "/sdcard/Download", "hg_device_profile.json")
                tmp = path + ".tmp"
                with open(tmp, "w", encoding="utf-8") as fh:
                    json.dump(pair, fh)
                os.replace(tmp, path)
            except Exception:
                pass
            with _HG_PROFILE_DEVICE_LOCK:
                _STREAM_STATE["profile_device"] = dict(pair)
            _hg_diag("device", "profile-register", did=_hg_tail(did), iid=_hg_tail(iid))
            return pair
        _hg_diag("device", "profile-register 无效回包",
                 keys=",".join(list(data.keys())[:8]) if isinstance(data, Mapping) else "-")
    except Exception as exc:
        _hg_diag("device", "profile-register 异常", code=_hg_err_code(exc), detail=exc)
    return _working_device_pair()


def _profile_sign_request(endpoint, devices, body):
    """官方 profile 签名取流请求：he 版本参数 + selector 重试（_rticket 毫秒递增）+ 六头。"""
    did = str(devices.get("device_id") or "")
    iid = str(devices.get("install_id") or "")
    params = dict(_HG_PROFILE_QUERY_BASE)
    params.update({"iid": iid, "device_id": did})
    epoch = int(time.time())
    base_ms = int(time.time() * 1000)
    query = None
    ticket = base_ms
    body_text = (body.decode("utf-8", "replace") if isinstance(body, (bytes, bytearray))
                 else (str(body) if body else None))
    for _x in range(32):
        params["_rticket"] = str(base_ms + _x)
        cand = _hg_profile_canon(params)
        if _HG_PROFILE_NS["selector_mod3"]("x?" + cand, body_text, epoch) != 1:
            query, ticket = cand, base_ms + _x
            break
    if query is None:
        params["_rticket"] = str(base_ms + 31)
        query, ticket = _hg_profile_canon(params), base_ms + 31
    url = endpoint + "?" + query
    headers = {
        "User-Agent": APP_UA,
        "Accept": "application/json; charset=utf-8,application/x-protobuf",
        "Content-Type": "application/json; charset=UTF-8",
        "x-xs-from-web": "0",
        "x-ss-req-ticket": str(ticket),
        "x-tt-request-tag": "t=0;n=0",
        "sdk-version": "2",
        "passport-sdk-version": "50561",
        "x-vc-bdturing-sdk-version": "3.7.2.cn",
        "x-ss-stub": hashlib.md5(bytes(body or b"")).hexdigest().upper(),
        "x-tt-dt": "",
    }
    headers.update(_HG_PROFILE_NS["profile_sign_headers"](url, body_text, epoch, did))
    return headers, url


def _hg_profile_get(path, extra, devices, timeout=12):
    """官方 GET 接口（bookapi）profile 签名。返回 dict；异常向上抛。"""
    did = str(devices.get("device_id") or "")
    iid = str(devices.get("install_id") or "")
    params = dict(_HG_PROFILE_QUERY_BASE)
    params.update({"iid": iid, "device_id": did})
    params.update(extra or {})
    epoch = int(time.time())
    base_ms = int(time.time() * 1000)
    query = None
    ticket = base_ms
    for _x in range(32):
        params["_rticket"] = str(base_ms + _x)
        cand = _hg_profile_canon(params)
        if _HG_PROFILE_NS["selector_mod3"]("x?" + cand, None, epoch) != 1:
            query, ticket = cand, base_ms + _x
            break
    if query is None:
        params["_rticket"] = str(base_ms + 31)
        query, ticket = _hg_profile_canon(params), base_ms + 31
    url = "https://reading.snssdk.com" + path + "?" + query
    headers = {
        "User-Agent": APP_UA,
        "Accept": "application/json; charset=utf-8,application/x-protobuf",
        "x-xs-from-web": "0",
        "x-ss-req-ticket": str(ticket),
        "x-tt-request-tag": "t=0;n=0",
        "sdk-version": "2",
        "passport-sdk-version": "50561",
        "x-vc-bdturing-sdk-version": "3.7.2.cn",
        "x-tt-dt": "",
    }
    headers.update(_HG_PROFILE_NS["profile_sign_headers"](url, None, epoch, did))
    resp = requests.get(url, headers=headers, timeout=timeout)
    return resp.json()


def _hg_official_season_rows(sid, devices):
    """官方取季（hongguo.js seriesSeasons 同款）：plan/v 起头 + cell/change/v 翻页，
    返回 [{no, sid, title, cnt, subscribe}]，按季号升序。官方没给分季时返回 []。"""
    sid = str(sid)
    if not re.match(r"^[1-9][0-9]{9,29}$", sid):
        return []
    resp = _hg_profile_get("/reading/bookapi/plan/v",
                           {"scene": 10, "from": "single_col_same_ip_series",
                            "book_id": sid, "filter_ids": sid}, devices)
    if str(resp.get("code")) != "0":
        return []
    cell = None
    for value in (resp.get("data") or []):
        if not isinstance(value, Mapping):
            continue
        rows0 = value.get("video_data")
        if isinstance(rows0, list) and any(
                isinstance(x, Mapping) and _int(x.get("season_index")) > 0 for x in rows0):
            cell = value
            break
    if not cell:
        return []
    rows = {}
    cursors = set()
    for page in range(10):
        for video in (cell.get("video_data") or []):
            if not isinstance(video, Mapping):
                continue
            vid = str(video.get("series_id_str") or video.get("series_id") or "")
            season = _int(video.get("season_index"))
            title = str(video.get("title") or "").strip()
            if not re.match(r"^[1-9][0-9]{9,29}$", vid) or not season or season > 200 or not title:
                continue
            rows[vid] = {"no": season, "sid": vid, "title": title,
                         "cnt": _int(video.get("episode_cnt")),
                         "subscribe": bool(video.get("subscribe_item"))}
        if cell.get("has_more") is not True:
            break
        cursor = {"cell_id": str(cell.get("cell_id_str") or ""),
                  "offset": _int(cell.get("next_offset")),
                  "session_id": str(cell.get("session_id") or ""),
                  "filter_ids": sid}
        key = cursor["cell_id"] + ":" + str(cursor["offset"])
        if not cursor["cell_id"] or not cursor["offset"] or key in cursors or page == 9:
            break
        cursors.add(key)
        nxt = _hg_profile_get("/reading/bookapi/bookmall/cell/change/v", cursor, devices)
        if str(nxt.get("code")) != "0" or not isinstance(nxt.get("data"), Mapping):
            break
        cell = nxt["data"].get("cell_view")
        if not isinstance(cell, Mapping):
            break
    return sorted(rows.values(), key=lambda r: r["no"])


def _hg_official_seasons_merged(sid, budget=9.0):
    """合并季数（官方版，取季方式移植自 hongguo.js）：plan/v 精确拿到这部剧的全部季
    （季号/series_id/集数），再补齐各季详情成 [(季号, sd)]，按季号升序。
    官方只有当前一季或详情补不齐时返回 []，调用方回退到原有的搜索探测合并。"""
    started = time.time()
    pair = _hg_profile_device()
    if not (isinstance(pair, dict) and pair.get("device_id") and pair.get("install_id")):
        return []
    devices = {"device_id": pair["device_id"], "install_id": pair["install_id"]}
    try:
        rows = _hg_official_season_rows(sid, devices)
    except Exception as exc:
        _hg_diag("season", "official-miss", sid=sid, code=_hg_err_code(exc))
        return []
    if not rows:
        return []
    _t_end = time.time() + min(float(budget or 9.0), 9.0)

    def _fetch(no, rid):
        d = _hg_sd(rid)
        return (no, d) if isinstance(d, Mapping) and d.get("vid_list") else None

    merged = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
        futs = [ex.submit(_fetch, r["no"], r["sid"]) for r in rows]
        for fut in futs:
            try:
                r = fut.result(timeout=max(0.5, _t_end - time.time() + 3.0))
            except Exception:
                r = None
            if r:
                merged.append(r)
    if not merged:
        return []
    # 至少要包含当前这一部，否则宁可回退旧逻辑
    if str(sid) not in {str(d.get("series_id") or "") for _, d in merged}:
        d = _hg_sd(sid)
        if not (isinstance(d, Mapping) and d.get("vid_list")):
            return []
        merged.append((1, d))
    merged = sorted(merged, key=lambda t: (t[0] if t[0] else 1))
    _hg_diag("season", "official-ok", sid=sid, seasons=len(merged), ms=_hg_ms(started))
    return merged


_SIGN_LOCK = threading.Lock()
_SIGN_PREF: dict[str, str | None] = {"mode": None}


_SIGN_MODES = ("profile", "hiker_medusa", "hiker", "sixgod")


def _sign_modes_ordered() -> tuple[str, ...]:
    """自适应签名顺序：哪种签名最近一次成功，下次就先试哪种。
    服务端风控策略会随时间翻转（2026-11-10 实测就从只认六神翻成只认海阔），
    固定顺序意味着翻转后每次播放都白挨一次失败请求。
    2026-11-16 实测：multi_video_model 只认「海阔 ladon/argus + x-medusa」
    （纯海阔、六神全套都回 200 空体），所以 hiker_medusa 默认排第一。"""
    with _SIGN_LOCK:
        pref = _SIGN_PREF["mode"]
    if pref in _SIGN_MODES:
        return (pref,) + tuple(mode for mode in _SIGN_MODES if mode != pref)
    return _SIGN_MODES


def _sign_pref_mark(mode: str) -> None:
    with _SIGN_LOCK:
        _SIGN_PREF["mode"] = mode


_EP_PREF: dict[str, bool | None] = {"single": None}


def _ep_modes_ordered() -> tuple[bool, bool]:
    """端点择优：multi_video_model 与 video_model 哪个最近成功就先用哪个。
    2026-11-11：multi_ 已停服只回空包，single 生效；保留双端点自动切换，
    服务端再翻回去也能无感跟上。"""
    with _SIGN_LOCK:
        pref = _EP_PREF["single"]
    if pref is None:
        # 2026-11-24 实测：multi_video_model 连官方 hongguo.js 同款请求都成波回空包，
        # single 端点稳定出流。默认先打 single，命中后由 _ep_pref_mark 记忆。
        return (True, False)
    return (True, False) if pref else (False, True)


def _ep_pref_mark(single: bool) -> None:
    with _SIGN_LOCK:
        _EP_PREF["single"] = single


_VIDEO_MODEL_BUDGET = 9.0     # 一次取播放模型的总时间预算（秒）
_VIDEO_MODEL_MAX_TRIES = 6    # 最多打几次上游（旧版最多 30 次，外层还再乘 3）


def _video_model_rotating(video_id: str, config: Mapping[str, Any]) -> dict[str, Any]:
    """按「签名 × 端点」组合取播放模型，带时间预算，每个组合的结果都进日志。

    2026-11-10/11-16 实测：空体是站点侧成波出现的，且 multi_video_model 只认
    「海阔 ladon/argus + x-medusa」。旧版这里是 5 轮 × 2 端点 × 3 签名（最多 30 次），
    外层 _stream_session 还再重试 3 次，一次点击能打出上百个请求，播放器早超时了，
    日志里也看不出是签名被拒还是端点停服。
    现在：最多 6 次、9 秒，命中即返回；失败留一行汇总 + 一次对照探测。
    """
    last_err: BaseException | None = None
    tried: list = []
    started = time.time()
    deadline = started + _VIDEO_MODEL_BUDGET
    signs = _sign_modes_ordered()
    endpoints = _ep_modes_ordered()
    combos = [(sign_mode, single) for sign_mode in signs for single in endpoints]
    config = dict(config or {})
    for sign_mode, single in combos[:_VIDEO_MODEL_MAX_TRIES]:
        if time.time() > deadline:
            _hg_diag("sign", "预算用尽，停止取模型", tried=len(tried), ms=_hg_ms(started))
            break
        if single:
            endpoint = VIDEO_URL_SINGLE if (len(tried) % 2 == 0) else VIDEO_URL_SINGLE_ALT
        else:
            endpoint = VIDEO_URL if (len(tried) % 2 == 0) else VIDEO_URL_ALT
        combo_started = time.time()
        try:
            model = _video_model(video_id, config, endpoint, sign_mode, single=single)
        except Exception as err:
            last_err = err
            code = _hg_err_code(err)
            tried.append("%s/%s:%s" % ("single" if single else "multi", sign_mode, code))
            _hg_diag(
                "sign", "miss",
                api=("single" if single else "multi"), sign=sign_mode,
                host=urlparse(endpoint).netloc, code=code, ms=_hg_ms(combo_started),
            )
            # 断网/超时与签名、端点无关，继续打同一套组合没有意义。
            if code in ("HG_E_TIMEOUT", "HG_E_NET"):
                break
            continue
        _sign_pref_mark(sign_mode)
        _ep_pref_mark(single)
        _hg_diag("sign", "hit",
                 api=("single" if single else "multi"), sign=sign_mode,
                 ms=_hg_ms(combo_started), tried=len(tried) + 1)
        return model
    summary = "video_model 全部组合失败（%s）" % (",".join(tried) or "未发出请求")
    fallback_err = HongguoPluginError(summary, code="HG_E_MODEL_EMPTY")
    _hg_fail(
        "video_model/all",
        last_err if last_err is not None else fallback_err,
        vid=video_id, tried=len(tried), ms=_hg_ms(started),
    )
    _hg_contrast_probe(video_id, config)
    raise last_err if last_err is not None else fallback_err


# ===== 空体高峰期的后台重试 =====
# 2026-11-10 实测：站点空体是成波来的（18:41~18:43 连续 16 次、跨 80 秒全空），
# 在播放器那一次请求里死等救不回来。失败后挂一个后台线程按秒继续试，
# 一旦拿到非空 JSON 就把会话放进缓存，用户再点一次立刻起播。
_WARM_LOCK = threading.Lock()
_WARM_ACTIVE: set = set()
_WARM_WINDOW = 180.0
_WARM_INTERVAL = 4.0


def _warm_burst(video_id: str, config: Mapping[str, Any], quality: str) -> None:
    key = "%s|%s" % (video_id, quality)
    with _WARM_LOCK:
        if key in _WARM_ACTIVE or len(_WARM_ACTIVE) >= 2:
            return
        _WARM_ACTIVE.add(key)

    def _run() -> None:
        deadline = time.time() + _WARM_WINDOW
        try:
            while time.time() < deadline:
                time.sleep(_WARM_INTERVAL)
                try:
                    _stream_session(video_id, dict(config or {}), quality)
                except Exception:
                    continue
                return
        finally:
            with _WARM_LOCK:
                _WARM_ACTIVE.discard(key)

    try:
        threading.Thread(target=_run, daemon=True, name="hg-warm").start()
    except Exception:
        with _WARM_LOCK:
            _WARM_ACTIVE.discard(key)


def _stream_session(video_id: str, config: Mapping[str, Any], quality: str = "1080",
                    force: bool = False) -> "_StreamSession":
    quality = quality if quality in _QUALITY_LINE_NAME_TO_Q else "1080"
    cache_key = "%s|%s" % (video_id, quality)
    leader = False
    event = None
    if not force:
        with _STREAM_LOCK:
            sessions = _STREAM_STATE["sessions"]
            for key in [key for key, item in sessions.items() if item.expired()]:
                sessions.pop(key, None)
            session = sessions.get(cache_key)
        if session is not None:
            return session
        # 预热线程与播放器可能同时请求同一集；用 in-flight 事件去重，
        # 避免重复拉 video_model 与 moov（冷启动 3~18s，重复会叠加首字节延迟）。
        with _STREAM_LOCK:
            inflight = _STREAM_STATE.setdefault("inflight", {})
            event = inflight.get(cache_key)
            leader = event is None
            if leader:
                event = threading.Event()
                inflight[cache_key] = event
        if not leader:
            event.wait(_STREAM_INFLIGHT_WAIT)
            with _STREAM_LOCK:
                session = _STREAM_STATE["sessions"].get(cache_key)
            if session is not None:
                return session
    last_err = None
    build_started = time.time()
    _hg_diag("session", "build", vid=video_id, q=quality,
             did=_hg_tail(config.get("device_id") if isinstance(config, Mapping) else ""))
    try:
        # 上游偶发抖动（同一集首次 502、重试即通）——冷启动这里做短重试。
        # 只留 2 轮：取模型那层已有 6 次组合，这里再乘 3 只会让播放器干等。
        for _attempt in range(2):
            try:
                model = _video_model_rotating(video_id, config)
                rows = _video_list_from_model(model)
                key_seed = _key_seed_from_model(model) or ""
                # 按模型里真实存在的档位排，按与用户所选档的接近程度降序，绝不跳档乱配。
                # _QTYPE_TO_Q 已覆盖 2160/1440，故 4K/2K 档也能参与排序。
                avail: list = []
                for _row in rows:
                    _q = _QTYPE_TO_Q.get(str(_row.get("quality_type") or "")) if isinstance(_row, Mapping) else None
                    if _q and _q not in avail:
                        avail.append(_q)
                if quality not in avail:
                    avail.insert(0, quality)
                _rank = {q: i for i, q in enumerate(_QUALITY_ORDER)}
                _base = _rank.get(quality, 99)
                avail.sort(key=lambda q: (0 if q == quality else 1, abs(_rank.get(q, 99) - _base)))
                wanted_order = avail
                seen_urls = set()
                reason = "媒体会话创建失败"
                probed = 0

                def _take(sess: Any, want: str) -> Any:
                    """缓存并按档位返回会话；真的降了档就在日志里说清楚。"""
                    try:
                        sess.quality = want
                    except Exception:
                        pass
                    if want != quality:
                        try:
                            print(
                                "[红果] %s 的%s档拿不到壳能解的编码，降到%s档播出"
                                % (video_id, _Q_LABEL.get(quality, quality), _Q_LABEL.get(want, want))
                            )
                        except Exception:
                            pass
                    with _STREAM_LOCK:
                        store = _STREAM_STATE["sessions"]
                        while len(store) >= _STREAM_MAX_SESSIONS:
                            store.pop(next(iter(store)), None)
                        store[cache_key] = sess
                    return sess

                for want in wanted_order:
                    # _select_quality 返回的是这一档实际命中的清晰度（可能低于所选档），
                    # 后面所有判断都要按"实际拿到的档"来走，不能按"想要的档"。
                    _hg_diag("quality", "try", vid=video_id, q=want)
                    actual, item = _select_quality(rows, want)
                    # 这一档是 ByteVC2：只在这一档上要标准 hvc1，不跨档串
                    if _hg_entry_is_bytevc2(item):
                        plain_session = None
                        try:
                            plain_session = _hg_plain_session(model, actual, strict=True)
                        except Exception:
                            plain_session = None
                        if plain_session is not None:
                            return _take(plain_session, actual)
                        reason = "该档只有 bytevc2，同档 hvc1 也没取到 q=%s" % want
                        _hg_diag("quality", "miss", q=want, why=reason)
                        continue
                    # 这一档本来就是标准编码：走解密路，验不过再回同一档取直通
                    raw_url = _media_url(item)
                    spade = _spade_value(item)
                    if not raw_url:
                        reason = reason if reason != "媒体会话创建失败" else "播放模型缺少地址或密钥材料 q=%s" % want
                        _hg_diag("quality", "miss", q=want, why=reason)
                        continue
                    if raw_url in seen_urls:
                        continue
                    seen_urls.add(raw_url)
                    url = raw_url
                    if key_seed:
                        try:
                            url = _decrypt_spade_url(raw_url, key_seed) or raw_url
                        except HongguoPluginError:
                            url = raw_url
                    # 这一档上游没有加密材料（gear_des_key 是 1:normal、无 encrypt_info）：
                    # 本来就是未加密直链，直通转发即可，不能再当成「缺密钥」判失败
                    if not spade:
                        plain_url_session = _hg_plain_url_session(url, _hg_entry_size(item))
                        if plain_url_session is not None:
                            return _take(plain_url_session, actual)
                        reason = "该档未加密但验不过标准编码 q=%s" % want
                        _hg_diag("quality", "miss", q=want, why=reason)
                        continue
                    total = 0
                    moov = b""
                    moov_start = 0
                    try:
                        total, moov_start, moov = _fetch_moov(url)
                    except Exception as exc:
                        total, moov = 0, b""
                        _hg_diag("quality", "moov 失败", q=want,
                                 code=_hg_err_code(exc), detail=exc)
                    if total and _moov_has_video_track(moov):
                        session = _StreamSession(url, derive_content_key(spade), total, moov_start, moov)
                        # 解密后吐给播放器的视轨必须是他认得的编码，bvc2 这种一律不交
                        _sfc = _hg_moov_fourcc(session.moov_plain)
                        if not _sfc or _sfc in _DECODABLE_ENTRIES:
                            return _take(session, actual)
                        reason = "视轨编码 %s 壳解不了 q=%s" % (_sfc.decode("latin-1"), want)
                        _hg_diag("quality", "miss", q=want, why=reason)
                    else:
                        reason = "该清晰度没有视轨 q=%s" % want
                        _hg_diag("quality", "miss", q=want, why=reason)
                    probed += 1
                    plain_session = None
                    try:
                        plain_session = _hg_plain_session(model, actual, strict=True)
                    except Exception:
                        plain_session = None
                    if plain_session is not None:
                        return _take(plain_session, actual)
                    if probed >= 3:
                        break
                # 全部档位走不通：备用接口(fallback_api)直通兜底——那边低清是标准 hvc1，
                # 是壳唯一解得动的编码；此时允许跨档（strict=False），宁可降档也要能播。
                plain_session = None
                try:
                    plain_session = _hg_plain_session(model, quality, strict=False)
                except Exception:
                    plain_session = None
                if plain_session is not None:
                    return _take(plain_session, quality)
                raise HongguoPluginError(reason)
            except Exception as err:
                last_err = err
                code = _hg_err_code(err)
                _hg_diag("session", "attempt", n=_attempt + 1, code=code, detail=err)
                # 签名被拒 / 模型为空 / 缺地址：同一秒内再拿一次还是同样的空包，
                # 交给上层回退与后台重试更划算。
                if code in ("HG_E_SIGN_REJECTED", "HG_E_MODEL_EMPTY", "HG_E_NO_ADDR",
                            "HG_E_TIMEOUT", "HG_E_NET"):
                    break
                try:
                    time.sleep(0.4 * (_attempt + 1))
                except Exception:
                    pass
        if last_err is not None:
            _hg_diag("session", "fail", vid=video_id, q=quality,
                     code=_hg_err_code(last_err), ms=_hg_ms(build_started),
                     detail=last_err)
            raise last_err
        raise HongguoPluginError("媒体会话创建失败", code="HG_E_NO_ROUTE")
    finally:
        if leader and event is not None:
            with _STREAM_LOCK:
                _STREAM_STATE.get("inflight", {}).pop(cache_key, None)
            event.set()


_RANGE_UNSATISFIABLE = "unsatisfiable"

def _parse_range(value: str, total: int) -> Any:
    """解析 Range 头。返回 (start, end)、None（忽略）或 _RANGE_UNSATISFIABLE。"""
    text = (value or "").strip().lower()
    if not text.startswith("bytes="):
        return None
    spec = text[6:].split(",")[0].strip()
    if "-" not in spec:
        return None
    left, right = spec.split("-", 1)
    if not left:
        if not right.isdigit():
            return None
        length = min(int(right), total)
        if not length:
            return _RANGE_UNSATISFIABLE
        return total - length, total - 1
    if not left.isdigit():
        return None
    start = int(left)
    end = int(right) if right.isdigit() else total - 1
    end = min(end, total - 1)
    if start >= total or start > end:
        return _RANGE_UNSATISFIABLE
    return start, end


class _PlainSession:
    """直通会话：上游是标准 hvc1 MP4（未加密），按 Range 原样转发。"""

    def __init__(self, url: str, total: int) -> None:
        self.url = url
        self.total = int(total)
        self.created = time.time()

    def expired(self) -> bool:
        return time.time() - self.created > _STREAM_TTL_SECONDS

    def iter_range(self, start: int, end: int, chunk: int = 512 * 1024):
        position = start
        while position <= end:
            stop = min(end, position + chunk - 1)
            last_error = None
            block = None
            # 轻量重试: 网络抖动就地消化, 避免升级到昂贵的整会话重建
            for attempt in range(3):
                if attempt:
                    time.sleep(0.5 * attempt)
                try:
                    response = requests.get(
                        self.url,
                        headers={
                            "Range": "bytes=%d-%d" % (position, stop),
                            "User-Agent": MEDIA_UA,
                            "Referer": "https://novel.snssdk.com/",
                        },
                        timeout=30,
                        stream=True,
                    )
                except requests.RequestException as error:
                    last_error = error
                    continue
                try:
                    if response.status_code not in (200, 206):
                        raise HongguoPluginError("直通上游返回 %s" % response.status_code)
                    block = b"".join(response.iter_content(64 * 1024))
                    expected = stop - position + 1
                    if response.status_code == 206 and len(block) < expected:
                        raise HongguoPluginError(
                            "直通分片长度不足 %d/%d" % (len(block), expected))
                    last_error = None
                    break
                except (requests.RequestException, HongguoPluginError) as error:
                    last_error = error
                    block = None
                finally:
                    response.close()
            if last_error is not None:
                raise last_error
            if block:
                yield block
            position = stop + 1



class _StreamHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "hg-stream"

    def log_message(self, *args: Any) -> None:
        return None

    def _params(self) -> dict[str, str]:
        parsed = urlparse(self.path)
        query = parse_qs(parsed.query)
        video_id = (query.get("vid") or query.get("id") or [""])[0]
        if not video_id:
            video_id = parsed.path.rsplit("/", 1)[-1].split(".")[0]
        return {
            "vid": video_id if video_id.isdigit() else "",
            "quality": (query.get("q") or ["1080"])[0],
            "device_id": (query.get("did") or [""])[0],
            "install_id": (query.get("iid") or [""])[0],
        }

    def _fail(self, code: int, message: bytes) -> None:
        self.send_response(code)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(message)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.close_connection = True
        try:
            self.wfile.write(message)
        except OSError:
            pass

    def do_HEAD(self) -> None:  # noqa: N802 - 标准库回调命名
        self._serve(body=False)

    def do_GET(self) -> None:  # noqa: N802 - 标准库回调命名
        self._serve(body=True)

    def do_OPTIONS(self) -> None:  # noqa: N802 - 标准库回调命名
        # WebView/网页播放器(如 WebHTV)带 Range 的 fetch 会先发 CORS 预检,
        # 不回应预检请求会被浏览器直接拦截——表现为永远"正在获取播放信息"。
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, HEAD, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Range, Content-Type")
        # Chrome Private Network Access: 公网页面访问 127.0.0.1 必须带此头
        self.send_header("Access-Control-Allow-Private-Network", "true")
        self.send_header("Access-Control-Max-Age", "86400")
        self.send_header("Content-Length", "0")
        self.end_headers()
        self.close_connection = True

    def _serve_danmaku(self, body: bool) -> None:
        """本机弹幕路由：/hg_dm?vid=..&sid=..&fmt=xml|json，/hg_dm_debug 自检。"""
        parsed = urlparse(self.path)
        query = parse_qs(parsed.query)
        vid = (query.get("vid") or query.get("id") or [""])[0]
        sid = (query.get("sid") or [""])[0]
        fmt = ((query.get("fmt") or ["xml"])[0] or "xml").lower()
        did = (query.get("did") or [""])[0]
        iid = (query.get("iid") or [""])[0]
        if not str(vid).isdigit():
            self._fail(400, b"missing vid")
            return
        if not sid:
            sid = _dm_series_of(vid)
        try:
            _DM_HIT[vid] = time.time()
            _trim_store(_DM_HIT, cap=512, max_age=86400)
        except Exception:
            pass
        _prior = _dm_state(vid)
        if not (_prior.get("items") or []) and _prior.get("error"):
            # 上次是失败（多半撞了限流），播放器这次真来要，就再试一次
            state = _dm_get(vid, sid, did, iid, wait=min(_DM_WAIT, 10), force=True)
        else:
            state = _dm_get(vid, sid, did, iid, wait=_DM_WAIT)
        items = state.get("items") or []
        if parsed.path.rstrip("/").endswith("debug"):
            payload = {
                "vid": vid, "sid": sid, "count": len(items),
                "error": state.get("error") or "", "ts": state.get("t") or 0,
                "head": items[:3],
            }
            data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
            ctype = "application/json; charset=utf-8"
        elif fmt == "json":
            data = _dm_to_json(items)
            ctype = "application/json; charset=utf-8"
        else:
            data = _dm_to_xml(vid, items)
            ctype = "application/xml; charset=utf-8"
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Connection", "close")
        self.end_headers()
        if not body:
            return
        try:
            self.wfile.write(data)
        except OSError:
            pass

    def _serve_diag(self, body: bool, route: str) -> None:
        """本机自检面：/hg_selfcheck 出 JSON，/hg_diag 出最近一次失败摘要。"""
        if route.startswith("/hg_selfcheck"):
            data = json.dumps(_hg_selfcheck(), ensure_ascii=False, indent=1).encode("utf-8")
            ctype = "application/json; charset=utf-8"
        else:
            data = _hg_last_error_text().encode("utf-8")
            ctype = "text/plain; charset=utf-8"
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Connection", "close")
        self.end_headers()
        self.close_connection = True
        if not body:
            return
        try:
            self.wfile.write(data)
        except OSError:
            pass

    def _serve(self, body: bool) -> None:
        route = urlparse(self.path).path
        if route.startswith("/hg_dm"):
            self._serve_danmaku(body)
            return
        if route.startswith("/hg_selfcheck") or route.startswith("/hg_diag"):
            self._serve_diag(body, route)
            return
        if not route.endswith(".mp4"):
            self._fail(404, b"not found")
            return
        params = self._params()
        if not params["vid"]:
            self._fail(400, b"missing vid")
            return
        _hg_diag("http", "request", vid=params["vid"], q=params["quality"],
                 range=_hc_range(self.headers.get("Range")))
        try:
            _DM_STREAM_HIT[str(params["vid"])] = time.time()
            _trim_store(_DM_STREAM_HIT, cap=512, max_age=86400)
        except Exception:
            pass
        try:
            session = _stream_session(
                params["vid"],
                {
                    "device_id": params["device_id"],
                    "install_id": params["install_id"],
                },
                params["quality"],
            )
        except Exception as exc:
            # 把真实原因回吐给壳的播放日志，避免只看到一句没头没脑的
            # media session failed 就去猜是源写错了。现在带 HG_E_* 错误码。
            reason = str(exc or "").strip() or exc.__class__.__name__
            code = _hg_fail(
                "stream/session", exc,
                vid=params["vid"], q=params["quality"],
                range=_hc_range(self.headers.get("Range")),
                did=_hg_tail(params["device_id"]),
            )
            # 空体是成波来的：这里快速失败，同时挂后台继续试，用户过 1 分钟再点就命中缓存
            if _is_empty_model_error(exc if isinstance(exc, BaseException) else Exception(str(exc))):
                try:
                    _warm_burst(
                        params["vid"],
                        {"device_id": params["device_id"], "install_id": params["install_id"]},
                        params["quality"],
                    )
                    reason = reason + "（站点正处在空体高峰，后台已在自动重试，过 1 分钟再点一次即可）"
                except Exception:
                    pass
            self.send_response(502)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.send_header("X-HG-Error-Code", code)
            body = ("media session failed: %s: %s" % (code, reason)).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Connection", "close")
            self.end_headers()
            self.close_connection = True
            try:
                self.wfile.write(body)
            except OSError:
                pass
            return
        raw_range = self.headers.get("Range") or ""
        requested = _parse_range(raw_range, session.total)
        if requested is _RANGE_UNSATISFIABLE:
            self.send_response(416)
            self.send_header("Content-Type", "text/plain; charset=utf-8")
            self.send_header("Content-Range", "bytes */%d" % session.total)
            self.send_header("Content-Length", "0")
            self.send_header("Connection", "close")
            self.end_headers()
            self.close_connection = True
            return
        start, end = requested if requested else (0, session.total - 1)
        self.send_response(206 if requested else 200)
        self.send_header("Content-Type", "video/mp4")
        self.send_header("Accept-Ranges", "bytes")
        # CORS: 网页/WebView 播放器的 fetch 需要, 原生播放器会忽略, 无副作用
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Expose-Headers",
                         "Content-Range, Content-Length, Accept-Ranges, Content-Type")
        self.send_header("Content-Length", str(end - start + 1))
        if requested:
            self.send_header(
                "Content-Range",
                "bytes %d-%d/%d" % (start, end, session.total),
            )
        self.end_headers()
        self.close_connection = True
        if not body:
            return
        # 断点续传式喂流: 上游分片失败(签名 URL 过期/网络抖动)时强制重建会话
        # 拿新 URL, 从已发出的字节位置继续, 播放器无感知——根治"播到一半断流"。
        position = start
        rebuilds = 0
        expected_total = session.total
        try:
            while position <= end:
                try:
                    for block in session.iter_range(position, end):
                        self.wfile.write(block)
                        position += len(block)
                except (BrokenPipeError, ConnectionResetError):
                    raise
                except Exception as exc:
                    rebuilds += 1
                    _hg_diag("stream", "rebuild", n=rebuilds, at=position,
                             code=_hg_err_code(exc), detail=exc)
                    if rebuilds > 4:
                        raise
                    try:
                        session = _stream_session(
                            params["vid"],
                            {
                                "device_id": params["device_id"],
                                "install_id": params["install_id"],
                            },
                            params["quality"],
                            force=True,
                        )
                    except Exception:
                        time.sleep(0.6)
                        continue
                    if session.total != expected_total:
                        raise HongguoPluginError("重建会话后媒体长度不一致", code="HG_E_RANGE",
                                                 detail="%d -> %d" % (expected_total, session.total))
        except (BrokenPipeError, ConnectionResetError):
            _hg_diag("stream", "播放器断开", vid=params["vid"], at=position)
            self.close_connection = True
        except Exception as exc:
            _hg_fail("stream/body", exc, vid=params["vid"], q=params["quality"],
                     at=position, rebuilds=rebuilds)
            self.close_connection = True


def _start_stream_server() -> int:
    with _STREAM_LOCK:
        if _STREAM_STATE["port"]:
            return int(_STREAM_STATE["port"])
        last_err = None
        for port in range(_STREAM_PORT_RANGE[0], _STREAM_PORT_RANGE[1]):
            try:
                server = ThreadingHTTPServer(("127.0.0.1", port), _StreamHandler)
            except OSError as exc:
                last_err = exc
                continue
            server.daemon_threads = True
            threading.Thread(target=server.serve_forever, daemon=True).start()
            _STREAM_STATE["port"] = port
            _STREAM_STATE["server"] = server
            _hg_diag("server", "listen", port=port)
            return port
        _hg_fail(
            "server/bind",
            HongguoPluginError(
                "本机端口 %d-%d 全部绑定失败" % _STREAM_PORT_RANGE,
                code="HG_E_BIND", detail=last_err,
            ),
        )
    return 0

def _b64(value: str) -> bytes:
    text = _text(value)
    text += "=" * (-len(text) % 4)
    try:
        return base64.b64decode(text)
    except (ValueError, binascii.Error):
        return base64.urlsafe_b64decode(text)

def _branch_one_bytes() -> bytes:
    if not hasattr(_branch_one_bytes, "value"):
        _branch_one_bytes.value = lzma.decompress(base64.b85decode(_BRANCH_ONE_B85))
    return _branch_one_bytes.value

_BRANCH_ONE_B85 = (
    '{Wp48S^xk9=GL@E0stWa761SMbT8$j;R-wN{#^houf7QIIVU7<Ew*6C3?&vQR7`VixMIZH9HyzSRN)dgt5HsOFl)*@6hSxGmq5aA'
    'QqcTJ>uEXt3ca?@+^++8<`vdWaS1a!^(@3piHN^UDea^utz&m68PwK)la*43U*mNYT~Az3vWRR9M@u9%`>|`oTuVAm{6Xbi7<B{L'
    '+9%}E{{R4tW;N$iTuuPgJ`u;tZ?qE#6f{J&gM{zloCXZoG-hquoMj#I1srY?B&~p9xgbUzb@!5*4S7ma&y#>iUoW)6rJ_BOyLIpL'
    'xODyDEOHDUy)Hr^$hEEodD$hbGrZQIEu8`Tb_H;~Z>VMWKW5~p-hONtZJoi*u&tO=m69!Z>V7E`+W`F%rB6Z`>9J*SJ%Azqgna;j'
    'pyLxZi;ycJaM~j<o%H|7!w`?YyEm7i6pMnWxuw4z`~B6UKR|wY@2gl<iXrJDd{_1*$qp;ibMN}xIL<*Gi$aI_ToO8niDZ|W6uz1!'
    '%)Ofu3qfRq1h1p__0g|vqG(?;aP76#`-*@WsTbSc98!AL83wt_4q^NHqSkY?D&ko53i_{F9n~l_{x^5C{H|fMAIX4f`wb7ERjZ3y'
    '+#;VMHu5P=Jv3&yp^-ASDTXYC%$TxN7n?j-=xsY0676yMQ)eWeYkG3JD<>_>t{HhAIxC^4(?8&VcUx=ux(qrgcIAXU5Yosc?z1$('
    'FqfP|)2$ve(&}uw;(uxdO>E6dMMn^`79eTmC_B=qkOB^y=1A8sQi<MgW~fDdW0t4{^<IjM^J?x<&Z1M)pYO&uEA!yRw?Np_Eoi{o'
    'V9dD%VA6x*g>j#h5;4}+#ILn~##Qh5V8-%l`Cgcy0u7DR!N$07Q0#BWZ9icP<a5UiL*HS#iW;QiR{)ut8&c9ibCtR^s-hvxT<B5I'
    'pZF*<3Mz685I{5Bn03e7@&D%xea0+oBiI=#Ay^38D377%<QuMZ-O*%Tv;8|=X7k@BR9~m7iE|@?x%zlQ3NE968S;+Y@OKTIO1nRQ'
    '%$PlmG26EWG&hsL(A8Kvzr*S5Ay&gwR^Qs5EP|lmJc;6eX{5+3>-W3P^XQYY)|Xa<5v$^`p|naVLW^*4x>oTf$}?2%{6bD};l{wp'
    'UXx&>{O<J~x}|>(!V18p93xBW_5+H#yeu03vRjESLXD$A9{yVQwj)I(NohO>ORrTjPEA{?DAU0dxSX!K7471{McHXwNi-H;o*fS{'
    'A^u%?y|GH!Rj#yLuLt`!o<Kf)Y(ZpN4Tz3<fO`#$DE7bF-%oqDst*3_DWg8nZiEfL0Og$<i9XRgsx?2^G>t{jYLYX|a)tAG>|ahQ'
    '(CvT4r8nG+e1c=US5#<;4qieQKmF}v#Lir5E|do?DhNZDSa32d|8J@+jja&PG#}{s>QAtW@PV$U?q=(1XE9c#V$_wg+bp&V&B)eE'
    'w|E7%&@=fW46%KQT|hx-6(^7@;GSAuQiVAKWj{$=N<Dko+Tu^~&_g4k&tWyT+RiABes%c{2GlZizn~-ml%l&HeCQ7Y89{*{FhFJ$'
    '%A0T5Ok9YTqU!Y`FOD0Vll<93GAUvEw{f##S5Na@_<&-g^C8;XNP;Jns4P4`9G&OuVy9F{ye}9pZXFBGaV{9GqWseFXXDkv-Jtr#'
    'X`v5*<V}u7WzA@LlIItpV&L%Dnu!B`Tlz^fO$|&4Ecr^f5@l|Pk*?l`Q0k`=`(J9}mTP!oxXK|5+g>iFaV|-^t;>U+e*p}pUxsGg'
    'R<;C@A<@#B?1bIdg$yI+yA6AxY23cPa12A79#Fv)!=h0N+GRs0Kg078`}Jx76kkmF2?7`fU$Lt8m3@5>LUp7)McaOF3%leJQMA(V'
    'z#j;PC$N!2YwiDp$FdZE3B6)aNBYUa(TNaoy8X~=byBHab^*nv9%*}Rf54ca_b0AXoR_G3a@6Q#ZFpU^6?~3S9&n|oyDT=y+-aSh'
    'n_@mxq0;KkI{N4=aOj0w-G;T1{5|jUk~rpYu}~n&xeXONR{x@w=wxoIjOh3^cwp6#*_zNzKwGmt%gS9r?F8cMjKT$lB|br+51yB2'
    '=wZV7fy7D{`(29#`6Q#QIa%hm)is>KD_ry#_H*-F*|Z?%Qv8Wrj@X=do{p=*x3Fz@7wS7@0b~~-n@Ufde^yLqtQCm?0O`Da6nn-j'
    'r9Pog2fjAFwY<gel`&!+$DANDLZf`IKhg4BZGPdEYX1n!8rS+gQ7lP{?{KO45vsUu2dS7*+lGbck?L*-g91mpEav%V%JY1;m@7bb'
    '!~8*@(PmIx$hM4)kQD#-N9l_sU8UpQyq;#!2cR64Gr9}3BImqV(P!p6uw?K%E^%~`2F*P-WIQ3uw-kIk4m<8@RYF5W+XhoQx`p6k'
    '+9I#{E}8>IJkyQ%q6436nF9t#Lsz;}b$hp5{_)$_DwZec8D&xJpU4!-(s}b112NIK72XtvrrGX22}y~3_iro{&MnhETA+DaK?Xi('
    'Q0J_&dFeJ5#7fK#kt7e^e@c1D7iOsd7Y$~wsRTJ#qi|^(h#yWd2}FIU8B9IG^z<X74^tO-6ur(^CZ13AW`UFbC{Pe%@)oIN45MqI'
    'PHdq9D!Kbze*P?h!OC)3qiB!l?49WS?)rHvoGtFxap`)w1=tf8AMQ5IfrG3!9*(uQp>&-907)*(j!(qXjiLbP^#}@|w33k4F~`7m'
    'K~fLbR%d?z%hl(M*M#B6)+ez&D3$JDYg5AF2vDMPEE2G;dt-P!gtE!qaJ41%TjxghS@IBUwUEIbBB|AJ4?hq}BLavJ+^|F^sE80o'
    'uLA?B96n!Yic+9jWQ6baLx|+P0BjCKJP6CmKDt5GssWs1oekHG4ifxLAKG`*ebaE=-5kobMB}Pz;R0REqN-x}q3%W$B*jB?E{A%B'
    '2MhzK1%uoumz1tpa`{9cjKqgYo(@1|z(N)PeGvIibln>rkSAlt;@TjZ46mVE-PxOR1;;0DloppysYZl<liKBRKRt?9$YPa;+3T}O'
    'tk(2rC{(dZQ`ym+rqP^|wr0OI>e6G|A!P|?bB1T7wCbzf01t(nEUGrFWjeMlraZ}~O%Xn~3S`Ij?3XhZJj44r^n=^V1+N&4lbxGo'
    '0!x)@u1Oh2G558Kzoz_xRv^@R+Sg`Cz7G*Hrru<u)3M&MHearUo8*q=Tm|q>F#dZW2&@Gr5H7wXs&LAz?4wE7`UwBTRkeMY-w&~x'
    'xYPt=bzf(89ffpeR@daZBH>+i&9AQXz8Ag>QY~)CA!cmHgH<ADaviZ)5dYJuj+}hxlHaonh`lzE$v|TZ2F?t}1iK6w3;xx3i`k5E'
    '3fT8$h)$9gl59pjn9!Wyy(CiSm)fITqjj_HC6bB*xqNUV@F%^;AJG{&N#upHz)q{2eGtJ{3Vt*~?n6mbI5?3tt&&kjlS^Jk`5AKk'
    'stC&F!}ev&(y?w&Bj#pL<xuFqZlgCPdA=?Pv0St5C9@`p^%+}>PV`CM4&WXiAA=p%;HSE^I8hyHb@HbJlKm9(B<&rvxIdWJ!Ra`W'
    'hBT1d#{e#>cz9y9sU9Z>FD5Whu?djyd$z^Ls@m~rs_#3A*V$?hFlmO6p0uz~8wP--L+&#T9-XiXKJ4AQ%8r0jK1b6h*9Wi$-*5_l'
    'O#gg!K%y%um(KnRmO)=2JlcF+X}hP7Gn{v@AW+9!+?D4&s3dzwJ?<}0CzFsHw)I`q@f#x}7%g)SCviR=d%M!Rmu0E64)p8)od~J;'
    '`uAVx3hx(ZmT&ZB5FN_#N-S9Eo!g%GuzQb%boa1Ar5RHkT*|?FDT530rxbxdzA|UYb0wSBm%7Qn@nee@gz=>xU=<{_-qSfw5uiL;'
    'Mw2t@X*I@v5gyeO;Azw^vnq!jZL<eeC#YGoyR%FFGgKx7>CTY%Y{$jEnTUhmlE>vWa&xR^daeIgtPS9t@UxM+5D(jQtQ_K#m>{iU'
    'O?L(Lsk3<&K&Ums!V4(!0{&6z@!u^0I%2ikvMuCv?M%o^RU4iL9Ul=Tq`Qq@Y|gl{oFV~Pg{3!t#0?>Pb^@f|3o+DkcL3`=U&&99'
    'n1ipU;k(6$Nz26d3+X9kD2Xa;);f=qm`iT8!@&Qu*cJ5i_@Hd;W4ON2#^@~rt|oiREpd1zc0fLvL#d((Kta6BI3vAn-V@xZV6?gw'
    'BF+>*#3Zvm$iZ0&*L4xFf>P65Fs@w&+C#wM^s41lRJlT>3OUK+H|^M(l{gmrAm#*VIo*I{)6)`Nzr6!nmw#7l;a=;Tn6ly2vS7=!'
    '4~fE_r9)9&$7RnSmaUHleEM)gsGR)UePI2Z;ewO0?U{4Hj^NSpP?ZKTS1ny~#up6i*JvMIBxfjm6!LI8GWXS)_4~GP0Tc`k@RHlb'
    '?H*yz0Ro+%R`J|{HtsE%xxbx|k*{5o_xZfD-4bteruCah1ep@1vlv6^uCy1}`{fpW42@`+Mu;V?l$yPujd?<|dg(yXnEsC)#1?($'
    'zKI!)WJ{_o-+z`%>g@GCWa}v981h|wyGx=%oNo$4GCZGs6t-$my{R~~VT)-|t0xOmFH*mG*~zgs#tB&P;ZmopQC~^2%k>{0d<p}3'
    'yiuQU#kl%qM@J@o1s$0?AI$+a`tuRJtV4h2xCDaOMA266*nM}E2{;$JcVMOTdlEtNJv@?I-2L%@2q=VCUrysWM}fF%iaD0e+pt)O'
    '8cDVSi$j093_3X&BFLbb<ehj->IwfZ|8hkc56tni&2PBSpf)>hw3C=z-?+kQb#d26(o17askq>W4Pr};0!JE#@sxOF9my2)h<;cb'
    'qT6pG$%k6+f=FhWam9}cQRXZN5wlU$%U1vcZ{jIriu^h(0M*xQrm~b4xv+A)2*h{|*OUZHRs|f|)GEKa&*g~)W2TtT@sp!Yi~Jp6'
    'wj$ze7Qh-nn-d7f*<Tva>4;;Fh?D`p1icS86F*iA9ztj-WD$>79%gsB#1FbG{_>5LsYa?X69@8s3xd{bEr<N~$Y>`6YU0#ux0)++'
    '_%@p1W~Su8mIu&SDyjn!G5Qr|8K|Nb9}JFJojQ+6p^;w+uT6lnyKtZS=3elR)`hl>nFV_s<6^h;+(3*4)YFb;uPh2sE(;xkw=o({'
    'rYtN4S@zdyB7&z_aWQZ;0%0E*48M`@aATEdR@V13+j;5YhV?niH+U<3IVS)kl|v>n;TU6E(jG84m^*Zt2HF%yZ60921r25wAoevU'
    'fmk@6FhGsIlMK1CsV8Jm4?>-}sW4nU_xov}%a{Q;0GBl>+%-!r4`9mrOw6!D_zy3Kwa6^~rCkp^A1C1|-Jv*l9M=p(toY6>j|X}F'
    '&J*W-E$Lo`K*Nd<EoHO-T}2;3saoc$h$~Cga?D2<*&5Hg46wV3^&u}eJhkX|agkeS8;CBK7iTXMl!@!z3#Xf2x*z*nF)B7N^U=Vx'
    'B1}XSW_z$tJhrx*(Dmrr(Zpe6?bMoEU}Hd$5nq02d;8BUsG-9!=<GO0R|^ib3p+0%`}yu_v~J#U1ypv5yk<wJ>O**eB~TiY`XMSO'
    'jw!2tgE@FcbNS9HRi#}gs*>CRWVgjZ+WHLslM%L{zLlX8<O*U*kHTO10bKQ!rz((U%!zunm{*;U4v`f=tki_GYSn_(WA2Q8P=Uk7'
    'YSNM`v$C{T^NR!Hx9ak32Of6EQM^virk&Mt_!gSCwpt|c<Bx7L(PQoVzQ$tp*1$Qn_;wc}g~yzw-duDWuhv`_SQ;@;W)swM@m4Vb'
    'W8AezVn#N9$eYHZ>k>UAErfG>z6II2{1c-NL1G~)I^m>#6?6%=NdcxVnD#ni3uWui)jx9C4=W~kLY|Oe*bewS|N8*!A|#x($!+mR'
    '&gaDU{A&eA&TJ~XwQ`Fl%NrdX4IS10ui2`WfEQ~bHe>|0ky9r;QeKb->WHB`kP<Z+-rb-v6%0~3m7?si`($DP(UgVNbXscA-z7T&'
    'BXqY|qYp+5s?p-tV9KAT`%Lp&5FG+vd$KsO$q>(B+bZ<Ei~zr+3)btP8>-ZV!rzOtPOZt8Tzpn97eQ+wLh9Tl!))xz{-b2}kkE)X'
    'EJG1G<A2Xjg)~Ie>3IPJPD;I6su@*;N(}z!o7+h>cAl{jEcZ2<pFrdhcbK-&I%8!iASA~9B`vDzLN3vW`c883<BT$M^gS3-#&^WI'
    'LaPGGG|E;t&g46)d;@BlL&Y*3TS~FomoxyY%V}Pk=!S-=MV^{`_4HbM-h9Yp8TC*Z1}*{l<!U)PYL@jc@=-i0{QK6{pE8y3AC#bp'
    'l9ydw1bx^a*@@o{E{{lozQxm*zb2_;&9t(7?XIcrpX$(_zxvcvGE?2(4pMG#-_Z%)u7M(X#=t?VqDUmnx$qkPx5p43&eK|G@e;E*'
    'bjQLK!U%%6Tou#CZjwn|W-T|PT}A8LCPa(L@7n%1m>lfCJ3Ne0NKDBGgit}LYoOSmsl1ef0PEllmj*@Js#r6w08Lh9+bSeom$_*!'
    '5|r6Y4Dx}JPapC_RA{VAT|+ZpKEEoA@4)`4S6pmCKGSZTTrRNRB@V7-ucDbG4nM^oJlA)h97s`h>~c&iC{2ig!d1#Ms|2EpI4<pg'
    '5{k+uapUbX&0|$96o+LU(VI+VYjGtVqIV$Uh3`7JiA?nYTAi`>VS+bD+GS(^tdl5+xK6nJ(&b5xU~owi2wxtJwuQfZM9MOwx0S&Y'
    '0M|tBN1P+_SY#BSCCwPqU4kW7U(8c0F&W4nF1xcA91f)B#zz{gL3*#w7izhnq>*o-vc{mLA5QT^YFI*ri12A+GoT(*4sD|;Di3L;'
    'ddvAmG-l-X;ZAVo5xfgM2m#Lip2TfW%kJ?d*tAJDuo;B0EcW}mr$d+~fQI<{!iGQe0|xatE}eU4w=svBpHR<fP(6WoFy&FT8NGV8'
    '(&Q+7Y;%mbwDXyAtMj{#^RRn?x;8cRw3_SKOUhQYa!+q1OWqIlj)JZrOT^1u$Bu;$Y{3nEyc7#(9Oelrup)4yx6w}}2nJRD4O|)s'
    '%rB{_+nfdK5eNdcBW`Z9BIod+IMwsclUxn(!bp2P0C7SD8_EA1q+IBikyuTHEyw!3xuIJaTvfb8c7EPcg_1Q!C~I+Tu`$dQ^{tD8'
    'gUR^F@;|pVI(>9nV9L4ct5-EG*Q2vOh7|QvY@fsu-mx4=)2$W&H%Bv*6Pkqo!X)sGUjZ*w?($clu1BKNR!cvm&l_A4!QaMjH<)|8'
    'n~62K-9(7nUGvuX);0QFvfsj__uhI8O;kdf<L3V*IPRzzDHf|ly5R+Y${!EQG?PpmLmZcy7n{u5$Ua0QuI(2yZsq;qPVdC}peq^0'
    'z<@pjzs`{sAq=EiGu9Zu+w$ZG0ss(;51f8bw)di87Zb5v+Ng67DfaSH=IO^;AYi6tkt^qUHR;7g(k?Vefu`^xoQN4#U)%-JB;8EM'
    'fQT`aG&H`LFoR8qO}2be^6`gmM;n?H_TU9O4M)BE6(zNvxy&tDQKK}R@Gy?a8rvU7vhZ$)+ei#!QQJ+GjyN1|T=)K-%FGHQA}M(+'
    '{CK+xt4R$YYgYPkZ+(JWiO4IwTumqD+v@f?=)w_CvftQMa>TFkgOHe@qOnFRSEJtXUJpu+LXnR*N4v`Q83l2{m1<!7cv4+eKzRpV'
    '2($w<QJ-5OPeQ6Sbs3`oUsgo-SIo}`aMI5R709Et|3kbwyohKtqkky8-SiNU-g&<Xqi5x&!-HhOoNw8lf3gR}HgICxVvi_#kSC9)'
    'wB!Ay+V?oB77Gr3qCQPEpF`s{=+%{~77M(Qz%mS?J$rj8RIJhq*k~4KsnvBFZi)F2=<j9bv;N`cK71xsd^U=)`imfOGvOI6yCL9t'
    'u&`eXa1#S>pvspU*&UREpagCvg(lKkm+jlKin}pFVycXE6L%w(vH&1}baI9hBwpzi>I<c3v>O466<?IPbZQ=$JR~w7xp*k*VFacd'
    'Ev$B@D+QyksU7=6>7L%@%{_50Sj9%@XzeAAOqip=#fq?ykn4q)2(|F|?HnUV5;G%>lG*m}Au;xPFQ4(+j;)-1SD^9BtFjE^O?z}w'
    'uU|!m6Hy#z2M>UblgTLeaF%`8f16wkT><Ui+TSp}e70Y3l6@Zywj0Dv=uQd*K9?KRag-yLHji0#P!`p}>fnKbEb?e@em~s>XttyK'
    ')TceKHQ-~Tnz{k+grpi-x2T;K=yM_^%S`iDEe!1{lj%g!G~tdPIc}F1V7n8}8Nk*~w27SR70RK(##!BZ^@G6-XQEb<XjCmyJeW|2'
    'XX0>9t|3(uBG74aC&5gMh<}|_L8@RrOvt1qn^KyK5@*eAErDMMa|H4mlpeX~;P@EIw^#%8$Fs3W*5yK!O*hzqcb-^@pHmxbYO?i7'
    '&%4x!c>e_}-F<nWRhBR%3=2)xzCHs^{<K7x*m|<326#w9!z`yerW1}xe5UXui?A2ej9YGoX%gTbL03dT!(E(sf>%GGS6Z3v%bqA9'
    '4&dC6(7GuQAaO7{=>r%0nX@Q*tc%Q^bME5x!^o=9e2DXGmRdV?tK*Ze`U*vd^Cc)i6G=%2lu6SA329j44pM323>Q}aW6O}TIN}PJ'
    '(Y^EKmiAHwt}ZeXj;B$)P;W3qGjf*z6K>R6{s4ufaa%$47e&d32a{7%7`^=alj<NPhZ@hrzhw;a#18X!#z3;X>ldOIo_7_`9PMfV'
    '<86~9RK11O2Dr2@VfeqJ)icEr(oVh{jrh*<GEoJ|tt|5^L>o6W7ZNCf8jo-ka?*2<v*ArvW?28ls)^>>c9zWz4|pJ^$coH__5~}='
    'Mj)2(s#paw69f{;*cw2J!qurM{7Qwa!$noN5)<Y#1iWs;q8UC~2obh<a3<t9LyEgExq<yEfT4Mm(C+LE$m6s3$VS9bKkfQ)EW0|@'
    '!lyspCdGd}*}LySa=mo}lm^U7;%hc6_b*`k*A>PTcp)EoZhP@)Myju?zy}cv6x0d0J+gd~7-ByisLI|O>X~<X^2b7+uyX?^w|Qy#'
    'cod8xtTucA9uQ#BEVOLX@^ZZJDym^TA&G^UOd-BN3&jFO%zpa1qAQBQ$2$KwYFL7gnc?1|NCtBU)c5g*+y+O?9GPn%0BPvtEY&Zk'
    'Y906LZ{vwED1*AK5pGUF)e!*f0FPgD(Ecs+F0R<)qqRk)^WcrAhga_e#QaKU7;tDMj0Qi0)yCV!K&A&}V+zYx9w#aTHoOz6Ws^NO'
    'e}@L5x^ldz@k_mQM9=dhSxYFr*K1pdF&=LR3FTQz=m0rD>HCtJRO%=b97P3M=iYoR9501E+f|zhkdjB-ml5ulYLJmy$;X})JU$+3'
    'zyNT=s|&ZPb^&RRoPE7Wytzt^5i^-iyOFQO{2n1MjAr68i#lYjQNZ>4=eooL+zpM&E4Jkv6N6AKqDj9<zDA8vb>hEF2H3f)Ehqph'
    'I$`&19~xp|KthQK>8t|DOAF0Fq&AUnTMuf6Q`n`VsVE(_4L~E!cl}FQDg=W+@HIkucI9Q2%PY>X`q)7P!lf>fPm4&yX5&a%bZKEy'
    'm}FRrxHg!l1$y9y<eVyWWULXlDoC2j#@XxmXGO+0F>Ss$ukj&~twB;p_?hAab<M?AcX8KE2>Q`}9Mgt9Y23OF3A&X_>oGi<n#;$j'
    'BEXenz0@hx%7?+1$S)@(_&&O+g8x<~E>GXT>tUe>LAG~6d7{>2=VA?$j2svmjI9LncaGVXPfjK{J9fDKJ}7Z+(7%Sy;<ZL>Z?g;K'
    '7rYq|cO>Ma^A(!fsLpc`Ov($85(=_aJTcHz>vfvj)8LIb_vkeqBjdiddaQl$Cgs@;xAk@-%pjZ7;VnIFoD7wecc47Pj<RPokEU=w'
    'k{h%I+G>S4z<AO|;h%k8`JLh<>81ELs8~#u1ku8y@4?1EzR}~D^1Xc-^Z2{`=hMlANbzs{o6#@S2T!_-b^~V`zxQ4kKB^mHF*;r*'
    '6Y@H<<CsJa#Oq9;Y*T66-+(OWBOb*~$-hGY(K7#g?h&LUPT{hU3VT6*2i0(+uiRoUs&{rWb7?y8c*ao7<8qnl%F@!3zh{8F`$Gg&'
    'b6*)k5j6>d&y(Wf(Y&q8zyyKBlvy}_Y&I{%!f#$Dgrs}F>QGh*hn2}#WNst6!Q?wz%p0W6njR>>cz6a+No<0vS!G=N!4Y^o+q-*U'
    'yD$@p!i|$I@`{X;v1fX|k5z*J{TaL8RKb)T!vpi_gd$?mOSdG)%3qc4ix46SfP;eZM#Ii((=+We!%sKq3UCXmEEi`{eY;(`rmdqV'
    '9;(y1{6niqWj$+zPeg4?MY__EReO|KGj2}I%NObBmiEKx{CB!o=SIv4ZU2KJOMhs^ZQqbs7obl9^|8){XqaNp+(039&^000Sa^h&'
    '24%u1SGd{X;_&jh|1^|z3t%L-=xP*V!u%w_`$IegUxv>39@ku+aJiCq1DyW6ayl{SLUVR268{cZ7$oh(Yh~pAabC9C3`>B^8i3jw'
    'cgyaT1*d%;V&x2?QGZSpJyN+@7O?W_)zWXN34Eoez%c<|^4mu<_KPoCRvjokm69iJ4ACJ``8J)wK6{|9dL=2{C6~&fSHc!~4x&mH'
    '_m^imaD|EzFcow!V^y|CI~T6}1`sCH{ZqL`LG|rvl7UeLtOOY@id@bc${0dnFCBGw(}}p5kA*qB*?g^Av553SNeW~CO`9#pr~P~q'
    '%2(z1>q&+-X%*JJebW#_MD4<r^+IaE>N8WZk!u)-rsr(5H2#)1>;iC;@*8I^B<*_|q=T2tOtpm+K=Fe3%P2`ymsz;GR59Gb&>srW'
    'k#lwi!x3Q1M?^Q_<cIisHUzTJY$N3z)A9V)KS%uUyAm9`?zuUXoQ8vEg0n7WrlI?l*AF8zz>enuOH=X*9c}(leKhA-qQ;462_!#*'
    'Pe?r;M_4Nwfd6-`X_Fb!6PT-;zt-+O=^Jz`-JR1V@B4I>eR+ho00s6eD;9FgSLqH1wV%@F^$gs>b_zxfvulv|;zIweZ5Vbbca$B6'
    's@#B6JERzQvsUQ5FOrX6>Ta#RVTbm@km0(utG&Ke1hcv4<CvH{mGy&ILfBTA0o8ZZ1yM{x%H^Or5jf6J?=L-8d`Ya2m=(uTGO(Da'
    '+OM)bRzW@xBd(3xkWyM7Sk5&>&zdr8=7AX+Cb8!iUv`?$Cq*}DTOxb>yY`v7Cd1^lBF*GQTHc<l`m>8cuX*^|dmbpr#7tt6J$t`2'
    'h)c&z03gs}>eWqo9~BsDzYw8VZ6t&9<r_cb_PL<iu1K~&p<x4ObUO@n)&_pV((HP8j(!4Ww}-b-@l3#jzoJ^zW)Jo46N+raSUzhe'
    'o4wrTSZg;LJ1h4I{|#Q%(7-J<6D|@$s3p&ODUo<=7_k%O=0@CARS{8;_fY&6rPJsyQsdN=7DTusc*zmfTSW#9-e%EgiE9KQAk5kw'
    'P#)s%h|B`?%7FRrlADbY5i^sEZ?Mf2zcdq{@_fYD`^h=Lb+Tf><b*ta)$~*?$wYK3e83b!e%;JNFx@0zqOzKQZvWwq$BWy6$9API'
    'VZFw%dKnNS5G{^7$afAKLlLTtPwQCM61v<iaU7i84HGLfXsmQlak5RJ43|%i0sgQ!s?GS>oB-kd;m}c>Izd7vAu#xnYZ<?hz~f&_'
    'MO+7}p@|VlWy(`;rl}eCv@HpK9@mUp=M^5uaE0Z4`=_CWa2@hJV<v*B=N%VWl=bFii>TO{a)*YzAsX^Qw(@XZj})i?G07nV$&I;u'
    '%-}gIAIQPL7P;M2&tpL#^K}aqG%oNFJ061=`7vO4x-ZAbJcX|RkE@67);I>}p(7-Ot61m>5`pjRH#8yI+EnmtUM@g1|3oI-8o7kQ'
    'XFxJ3X{~ep;*5O>;?GCGNf3Ik+hbD|lDo}<_L0>GCo1cOkABa4L!<<fmJ!BQ?Hf-8V!dr8IOEP$F}zZBcRVol^D#-;-~Eq0?l>eU'
    'DiRZy@DdfK8_H;A2RBmyBu5ZmFRm|Kh^9CX2Dc?c6B)~b(4p0LX-x-@DseT}jD`^fcOOR9jVk-wZE`NTC<l2ZQJWS7TvShg%Z(*E'
    'r{T;Db4-Z)Wjw`1c%U1gbN9^OAQQkl>?z!~Skzxz2-410{ur4^P<f)v|DZ}t_132kScw^ni-t%9k9XMrWAC*RoMY0gP2|l7wl?CI'
    'fX=R%qA=dXXCFt;2%Z3h9<+nW(5GWU%O+DyU5xND_xM+(3p4ggSuW|atHu^~y)H0&E|IuYsXqh3h}*P;fn&8WyoXi?V)la^6zOKu'
    '0vPp6HamL%z_>17CZsM5cApJR_U{*36Rh0h1qlg3`kuxmj1&4b_-W|F?OQDMg~ISMnec^>kZuYed)n)eYCT;B;t?v6o&>CS{dIJm'
    'h+srIc=rKUx*PB&ReQB1P*m=|g>X^-8n@c_m4^3iHpF~BR2j1EI74nv+CT=J`mNSK0i?*esv~zHAWK1x+Z%Yz5%)Oas!b@;O^G+P'
    'Scz$&p&^ff`xXeMo?%gXzQkm3#=HuMGK?FzmL!C?%B#M|2k{G&_vC)4OZVM28#w-UaR0hi;XXd01qr7u-w6jPmXxv^G669<bmU^g'
    'k+MH?ay-OD9|W;<mF$7y>9cdq_xA7mS@3B-o8AmW1LfQ1--jU<l8po8B(RMIo!<!Fb{Lh&1{Sgq+Uh1dOGN;4W@+k{BojfHpr&UA'
    'oO%t3YNigNl<aCMd9FH7xz7`w_R8vdsng;ID{aN*OoF$jqkTB3IEb2X4@4`kt`e3B+FVzcN>}%nDEQnRap1LS{?U~c4DpUHhY0S6'
    'A25$sj&A}-vlo!^Aj7uuHfJo4AF9&@aQcBJGxwBs1gSWVx_uERU~L*5S%AWc0x{~y*^HAe`tvS8B{lhL!;4_w)`h|Gd}2C3lNnXv'
    'D%j)-sc+g0Yqn=4?L9(NP}4E9ad&rw1)lI%AV*+j7sEtnt4A5pN*{C(Jf&<7xN1};$2>_POQ;>Il&(22NkLQ`Bou-_`OI(4!JWTL'
    'RXZircVC}Jyq>2M4z=*F(Jj?T{Zv>@X{h!2aAq<jyp7FRb2c9oI^0V46t%WfhFk;cd#qtsl+541VDLDia;TeZg(OgpD#k_6MMBC9'
    'VKMoyj--blBNw>I`O+zniuZIe{-amNawhrOslk5blTTIXyeg)+>r|=?Qr<-t!EHSMqlhJI4%Nkm3hZ_Y-<|;Im_2<>Q?cf3YCTp}'
    'xD9UFPR6GR*P6ZhzS25DiP4&TSD<oQpT!6Gs>7Ce$--6qbV_n?RF?+>$8I2x5+}Wy!@D3%z@X%J!!nS-qms$q)YOrjaNG@3F2JeI'
    'B11G89c#!QRdEil3SS2Dcnx1iDNx4pwR7xdP$NK)7b!FPocY>_k@q|ua8R;6)J3Qk0h+YL_iRENH_!Lu9RP3h3_ksx^LPNmXlY!{'
    '7y`-skrRe=0^nqUEM%ZKm{T+YFg+{ama`H$UfOu|Wo}{~Q`BSA6bB`&x3baJSvimiBd(B5ZRC?ntIf;FDi^~|FS~vN;b7}SAjEQE'
    'NTqu30xy1@Wo%8r|4vgb{Yrd0;iN5E6jIh5Rqv4W^h#gT-7@MKFZ93v`_3A;JN=uCYZaY$MbH~=2QSWKOa(W-8el4Rrqrw}0UqvW'
    'P{g<?Bt(*K@H)3PwgsJ2FAd%whMYD`#D{0sxpx!Y>0e+C5|+DNKFUJcasKKjYAptG%7uRTSR<4>lHQWJAhTvl%mRf9J|F2jA1VCT'
    'gN{3cA?R97Pqm#W3xbIEg_2nC;2x1T=Vnp5tTwP{Ju9N9BufCnfhrWLxnbVa>Nbg9{u4TMXk;+<XO)1>SDrjnN^zdI7K@#L(GW}r'
    '1$=l=ni>jyarNmc<82Z4`)X3yy%w^5i0Y*JfayxJ_Qa-04?vh6Fk8s&`+ej56KkW=49@=^@F07CsUMw7*jhgv%4+P~bl*CSz{!U>'
    '0tv<kS^Y)vpjZ06U*eTPN8;lIA4NNo?DdCQvS8?5w3-@;=+Ev%Ll7Ej!x$LO$sz?n@I4~$|0`L`SQ_;kZ5CSY<Kxa0^i9u|s|~Nw'
    '1~5HbpuddQ^Ls>0M2!hDjcBkR`HCnm|M4_Zd35d!3Jl}iy}c@|KWWRIr=Ay^i6q}#uB|s`G+6{D7!;GO>PnRIcm8C2<lYzvT>lJ%'
    'g-Qxx`=^<B{^573Eqcl#pWtT(pe$O5MQlBxkJGtydEiQN5yXoyI~4#ukHZgC6_hqaouEeiEDV^SV}&gd_|Kg2iBR}rqVapm%xvks'
    '+_d?6R;8{Ne?lt&9&8h|bep_%wskas-S03-<Dd#?cRAcX=fQi)-~%&vdi_wzuc=b0-Cn15PCxDt`9i|kR}P(Ix=cz`W-phCNH*|C'
    '$~;?wMTXi1Wr%iOGm&&`tjV30f-9zi!?Rg$!A5>w8HU%ynm-43nYiihePYn9HOx^R;5HPrpPdt^;t*iC0Of7gK}Chl1FPoEOA`_^'
    'm17c>k;23<nRV#)K<e9zZ=+#20%d|kP6k?-Sme<)C;_s546EzYujIh88D_MVwUz6H?>UIcHHbN9-H*(*c5_<;4{9T#v6(WzF3$t;'
    'EYj9-3GTeJBGZiFNKfZ5l*&M>sm0<WfGpwL!Q2|l$&f=h<<)TL9cRRh%(r#<`*CAPYAhKG_Du3T9W0QY!RxRsj@S+GJ=_sC>VdpN'
    'ME!|1EI0i7DC!}j!F=O0{r#|e;TmN9x9#V+$?D?@8kBrC7+}JyX^5r$l(6F_olq+fQsDS`-zif_4dt3f)<beuhGeLPfZo&KLAPMw'
    'M=(g;79BJhMQwx#5*JRT^S8QQv+p)GzL&Q~$>C5IDd)a9lO|(VGa#SQD6ufB>rh;QXVk#)HCD>Bs=K#9oL`T(odYss>huj7K4c1I'
    'y*S~@u!&`zXR-(oQ+u7y{IB+?57IlVH^Qpk*l7x1?*jwq2@A{)T~eLshb|zTAx>`{)%2h~vcMAj&+PCLt~!4zq7UDMO3ZwxhfGB@'
    'uWYsiL7L8yuzEOYXQt?ICri|!tliMAM+#h@$cAQ#foiQnkY?e-cVsf$aJ>5{r4R(9-Fko?JK&q6ghJ{5f+M(2<vkq0iL(e8$KZw('
    '+d%060x0%>f<piGCLK^r?LNFFyU{k&0k7}RgHx^U4*(d^kWnD*SbySY0(izxtv95wcJ)ipKUj<$3$nTvw%y7=hV%U*$>QefYLGM^'
    'T~Umh53Lk870J46*~Ox!KPnxp`iD#S33?+Kd|fdDS8d4&TD4gepnv>~(u@UL>;eZG!iMVaUqBy@YFr+BNO<I7ZmokXvvew4`hH5G'
    '`oZzpURSOpTv_ICs1AbgE`Wf1DO@q?h+k-gy5v-O_BP%pQCb^qb^$_b+afLiAy%tz@i9@W&!~hx(-SSF%@*d|Gvgc~y>a3HhMq)E'
    '-18&ss>uppRbGFzP^<W{&wIK_2*T;BI?3o7odv~EUP_#eg{Kc>Mpiu=4+^?@;m+KYjDRFo{za}^k{a<U9fkam3lZo%1v(+(w_NXp'
    '?{(sHuPZH_hRsv+fNFL*FW9~I9}$tucVNTGvgamlc2R7|Y{ol52_NKx2%v*FVMH;5OYhA?6*bUhj~*-gkG^4-A@b~K8aja1j&rg`'
    'm#+0wCifK|as_}Wj@L>Q>YyGPAK9M43FD((nusW0IT*+ly}1$@8pI+c%49aac^b+PHy0vf4s;zYuri`)+HO7=O($SHgGK3dRS!R_'
    '%tVlLnUq<~?=(hz;QUB1uYz-PLxKWg2M7b(%hVJ7$NV8KhCqc;KFuEdcZcHS^%5v6TF~?Mu6IMhHgd9(KjXk=NecW=DOiM3<tQ5o'
    'w@B<(`RDmcQ(~Lc&twS%Wznhn@XT#+xB|?X{cSx0QGj>LX6^#%xSC?oJM;`w-lm-8DNY)2jd*QOv;_C3oxj2VQYx$4u9HyCMt*02'
    '>TbVw^KT>+txMSW?gE38;peu{7aJ_#Q%Yp$rngee1j#KQm|po#ODOzV7`HwTx>NJ;z5hg_zSvdevUyE20npPlTB&@&hk^WNw;Qe5'
    '9?rlvL%>R=UeauPL_M2r!3r`F6|@5&=Gu>tPE$PPeJ=-ClQm6vYTe<!0exa-Ou%Xn?eCH==^DbO!7Cy!Ph0f^iQF&cYdj8!hEPe;'
    'lY*1z!QTsLiCu4Z@GGL+`=d>RpRm)aX`JLg+H#}d@`Dq(U|J-fo5Lme&^`s)t=@V`o_maG&Zq|AJW@T;h~R>*pEQJ&!{#3HRzo#v'
    'Q85b|&tv;Rj`J#XLXktDIwu`Fvu(>LYz|eSD(*r9X>q{0Qmny<`$-B&K!owrcmk&`P`DTd()hw;9KPkXSn}lU@+72T*+c9X!p!D='
    '$K*OP!Tq}sEX&>);@WJW3uLVyn^jj0GUq(q>++wMq7wGo1gSc5Nk6TpVG<9)^HcKJ@j)q`BCx3XqFFHGj>TThkZd0*!EYiPI?K+n'
    '^rE;EHs}@#vcp7^SOvg(YD93MwOC3jSB;(x*NRlv{hZ{5&_bsiBgNkFK8i=E-gf+Z(K$POGN<eHgH=$yFkJ|zaN5k_MRt%46gO4S'
    '<F<N#^;cT~IKdf@zcFK;G~a~25u#lX81ig1ux>5XS;%%&fAZA4J}r6bGEb6JF8OBL<11D=ql-*c0LTwkH(ZLaU%+KkthH!!Lp`96'
    '#in#0g;9i?%;TtAR9#r0I{8rj)(5EMizbJN)7~u~uMZ^-L2i?IVB3E|jp1F;)aS#nvGCry<vf3Rch`0)faSg+lp^$s4mD!59s<0#'
    '@|e)#yWSAG#hJm;EX4u*aP>svlwdad9&#wZoPW;99cjSie{SuwaOJ_XgZw`6ze^wDH(y^9itJ)CtrOIjX9L{yN2H2kV%ip^uyh22'
    'vu;BwHd$IZ-rBx^yj=t{?jXCwe-??jLwBgB*b%db9Y@}*SBj7EkRQDLR@!#mD-6sY@7^iVIW;@dl8?vS3FM@%O??6{27M%m@@L{q'
    'bJ|-yyxxY5>y{ETUoKIG34YGX_w7}E=tAk&XI<`T(DJ=vEX8SbX@r<6q4+Dw+%H)v9w+lj-{MzzKZ4fu|J%>^wo;3@KKBlmYN=!n'
    'R^G$2EPlIA2wlQU!5)NYp&hm;-pM}VJ$pj^nzg5fYnWxSxD*%zgZ~iHfX*{}-7U&o46emBoDj$b@*7`qi9q%WV3*+6qalokfCVdX'
    '#+;==oWs6^e)Nv2atQuTi#@>N%pL%GJL<PtLx$5_vX+;X#+5Kz;dCVHX4=;*71k^mLXZ6@MuH~Axo2K@u+98{e@h}w6PA1Z{A>Qc'
    '`JevS0ax!p1P9{~B|h?cLL`=GZ@)OUaL<(V^|Xfnx_>uUv<%F0#rBCV`93{2r-o&h>3i8GUjqH;I+>(+U3_5R{^}+60Na*X`#OfQ'
    '?<l<FAZ0uS9XPEt>=|&|Q}~MxI3z@Y228_}eSbC>I{fnsfzaK@q<sk}EO%#7q)l&+O+_rG0cFqN*eroM4D?lU(e9jJc&T^a1OWyT'
    '$~vt^{@-J!e3g<f(3#ZRhO3yj%*>nZHBa|<G$-e*5AtIQ`#+#w$mxl96E<3p@{e<TmNb1sw_HZenAoH%T0{RtOM0t>xD-3Ms26qF'
    ')qD=~o2rYW7^%FwH(Aw`GMUFqMAIQ78>4ITjp=^q?Y7-DZ!vd<lHt1-7}S7yE3EnT(NlWg0;<Qw)r`|ejP{bFpL`+gl?;{`Q`<is'
    '73)<5iwYB806>2UHeW4twMP2!x7EP{`i*Gb=VtdncHYhU(S%x4vA)gWO9cJ>ev_@q^s$@HuelOqzx^%2oc|<7ftbi&#?l#L`H3*1'
    'AmSV3(ov@c+bG@TE8J$gKTUdKMIyL7A!Z{&w;xBRH9YsAdm7<{z_--GVD+Hh7+GvUj!U<KVqhhEImTMKX8F8DpwD<*-_>Y3A!<%b'
    'pW?3UV(64!EP%Yls1FjvudIFch8XVZgLtr0%q~rTvP4kPv)fdAz(dq3OHLuYPmip({U$-D4y|(d{UbKzbc(jT+2Q&jO%3(}l`u|f'
    'f_-c-`b&Fnnwxo~`jTetvI)s6Onu|bxIp?N>o~S^5`aL3%Mf`Y<r^RZ15xwuRk2j&FDkt+sU7YO`H99o6H7Exc-f}-)Y-aefpr|{'
    '8g22E+sOnDBx(vL^x6EqS0lnd@oFEU-*S6HvL1~yaRaL3_V?Mh8JYev0cy3j-6a2rRBBFLEA8jAzDwrYDz!x9gH@nx5aB9o@)D}s'
    'RX^!ov~^^bi)f?21<h4Dkwth)9OvVs=jH&UupwJ59L&VYjM<66)!!>Af%KTD9;V1{EO0)x!;D-Q1kT>!s1W)P=n@Nz?`iU@pYozO'
    'VpN_br9K_$!Pp?$9&_+l_B;n@rJ(S-%-obrSw{1Fwz_!ujwm(4Rpi9rDwUlz{~cy0-v`_X0il0rImnuoBj0lCNeTFXt%s^&#i|HB'
    '!@6v7N+G|~#1riQr0u<b28$fFD+Lv%dke<?R&I+eds`3<H>!@_W%#i7J1IjkRb03f5w%O*!G%0yD9lR$>Y+7;Y7Us~<NL@TZ9;Bd'
    'Y9*16x?#^=Lr@UAO3dE;{(pJK+AT<JbZe=QVio?1)uS6Y_v%FKD@lq0#lik1hBVrkjr#Vk|7%d@8m3yeY0~M6rj|{e<DPY!kVJ`E'
    'IycP3Etdxbm+u-?f2(yOF@->8p;i#>=rQMMb;z_+*MT8HU{V_A)Qi~18YC1+>}OW6c3x+>6+7_YpazZ-K$NxsJjxeLZ~`&$zxE{!'
    'A^Ie=5~$Rt<s7tV(J!Pjuh8K>O6G;P6l5Yc<n3HnCIZoeTT@TcfVV(iWi0OsTdMPZyk}BPR~DtEl&mL_Rg=9OiF*14c5+xZuv`n-'
    'cdwgFEYPX$xM?e`yJaEpflryM_&R38Imep~7lt9@_T0#Uue42e*QXAK@@GY#?(o{pED@(G&w<lXonJ?7xR;)=1d_catqe^_1V7u7'
    'ob8zzlT0#^@FlhDHC&du84=FEp9WOI+_)*S>3%Unf7~3%0%yU<fBj9PZm}O@%<e>xJ2xEL_^JX!pN|<0|C!gh{HMijCoCr-$W@kc'
    'B+Tt<XX^vmPCnK#A9B#!MOv!CBLh}u=1NM@;*wmTHfBjg&py@arKmVd-jKxI6)gk;n7b44qwwGwMB8ZkwaHlnQ>bV5PST0NmdLIS'
    '2JmUE?0V{l1k{**-iJG2gsj~g@+y2+0PvLpYAlHD);P94gSDuV(hIYC8IxhGI)%1Qe{mjP)4mHGC7U)F$nxy>)39taxgoD&DXz$q'
    'Pb;76%2-ufniA5KYZX2rR&U|X_aRC&SR#fF-+k}c(rH0e;5W0}cPIref*yb}$9yP81_jHWq4A7&tOg@A4}66o>2B?BcyD44JgQNY'
    '+#<@RF=sHtBm!&&8y0b}Qj4LNY?k*`-?Pp$8g39{S$-{i{mp~h6A0lRYq1HkvZ-gaDA;M^GVuHGuu<($c*&}I3hok&01*7;tq6mp'
    'EOVB<fC<(kNj-2i*QtnpJPy#dtSC2{a9TqTNk}L1Ijd0I!ys341)T<e;Cx(~XO9z#f+VbYL=5MNCmtHG=fgM8?pU{YfsBAc04QF1'
    'paQNJvA<12N*iknmAAVOrd7|isR@p`vv)c$Grq7%?BLkHPM@xq-I~zd4ZHjy0_dB$q_>#Crf*BK^DQj^AV7bQHHLYNN+vc_f)w!d'
    'CioL*WE~eU+5%7LAH0a2;*sz|Y1DshF{sqDneAZI9CX?=nEwXQe>yHBD2Qp0Ghb*<dHPXF+=8TQMXK*VMJM7N%}4jzGYF-y@~{WQ'
    'z|wEQgEZLr;g`Ta`)h;UG&9mIa`r*wI$-V4&zq5`TZpV5lnAoAMn(JMTiyO6${`%o3leyFVmpu1EAJd$4tG(a<OQ>@0?#B0%&tCE'
    'UErk2-Jt|*$f}k8l-W(kD4eyQnV|-0s(oDmBz2UIi?%V6Au)ROf!?F4Pu7?6qfyDvslVqiDUF}(Q>u|;Z6h6{7e<LIalS<H1xjH0'
    'l)<%Sx8C%<kOc1WJ&qMGty68S6O!>jTh#$-XLg}5!IIiDP>)6pD6fruQPWy?R2>lvnK<3!;d)o_z?;`A3defn5W0?QT!^Eg#3o*?'
    'h*7bB2!FXn#e^51^xzfCr}EbgIo*+qT`#AWEmm<h_d1idl0n>1VvQ(^8{?qyLaZL53e)-wl_#fGC0e=>L3aot4lP7u@C>Z<ZR^p{'
    'F-!YS9+LWQIvt=K3EZiLn5F^0XWpLf54M0rP^dU;#DnwZaaM7v+z_M_sf8#y10Q9Kze!|yoNv*NNVWti-^eOml#L|=r1n=WFlPN}'
    'c;rwi^RSpkx+_!Ohd;<*Yhu_-P#bVU77h+<jeWUF4n;`LI3&YlSut?>Q2dPT#Bb=B*!*{29i!*_hm=(i>UILY)3m(Y=n*lw8-LJW'
    '@EP8kQKnNMBXo`OJkan>WAzT?kQf}r2N6H%CxiwA5khi$S)r(Uq7m@#WtEYf9^dFj78!-=nw6uw!Yl619#A@CPUb#q00d(*FkhXb'
    'N3dAvhvhl6%^QdFe>M*cpi_h9Jr>BGI&R&06Py?HUbm@X4(SHRN6At!XK@m0+k_8;(Uifw$uZ|Ew%k_i`_Q~07o3D+C4v={T)W(I'
    '-TFS++nEkJ!dzrI%_<ynq1Q!^nOdJuVb~6Nm5u2xE)gLHdtm||EaGfJbkPm*t@*lG4`a%rN+RPyk4oe9<5Kky2}ka~E;!KxC>$K='
    'j!48gUC6<5#6NCF4gM`3;Zl#(BuL)dUb6{@SnpXEqYXwJI0qs_lcP$2=%hfln%P4SU=no%QTpM`EivFGgHiYAD?70xS#(q%Jv%!0'
    'xVg;%7Ot_bq5P4IDq-12K@rql$TJ7Y{jctn5+N$^<@%vs^!rn9U<fmh+=8BhXI?`YmalNkId&f<Yy`=dPBUW|asE*Bz5LH`sN3kJ'
    'cX7E5?x$NfHxufSw>kb$^v}I8w>n<(Y+X#khf$dx<`D+(=yeAg|Jg_EOkf4nXuC{#3{+aVY4m#UY0rH*aXkE)Bxpo?jPCni=p@3?'
    'Y=Z1g%Gh5#FLMe`f9a*b`9dG&2MTf6lwdXS(P4`1sT+Gf^v2k4tGFL2Fwsu;+N<fAR=ku05>wy~Z~ugtt^Q<Bz9I)MLGl!buRJqh'
    ';Fg#9d4$4gKv<8Bw#!H;S-q`JqTV}>8Hv)4^nSpLa02aqKmx7FQh`Ilkl2aQ9QD~t`!oQGL7B4RCM)7)FCwiu-F(~3Wk5>K?v#?i'
    'PhG3`5Pq>9lz-Q!R$|2UA-8Osr@y(^0gld*bGa1e)-#GTO=sC_FxYWrb!CrdgTxAfId36?$wkqB*nNChJRIc_$P8*!edLw?NB#m_'
    'IOj9vccR(-q4#lD@gFhW*N_e44jL1z>4U>}#_0epu=tbIme!p><0%H{W3zh=3_JO-NYLtM|Kg^hL+kZ5A(O!9!&3)s{z}mWCj0w*'
    'X*6EJB1##K_3BZ(qJMV*t_?ies?qcaVQCN4grm!KxpP0Mz~9Ja=RnHwWp83l%^&>epGNRVKl&EGhQ5T%;W9#h@Td@Irmx4xYg4cb'
    'o3<)AgQVV-NerpM1ITi4BkcP13}xrm)vHFXmfh!!0*qto`#oH7kmrjI(48{SeW9@&9NUYf+rRf{@8+BvKvjXYl)7m9E}1qz^DB`%'
    '<$awn^^-bvNx$kieD3hj1b$FJUnhUK0iLk}I0?T2FMhFDB5nsH3g98?Q{`u|Rw=1Hlgqz`f6<|Hg<Caj=VkI|ccbunAPjQzj4s~J'
    'TK_Ff$BsiUD>o@#8KUw>+cJv_YsM;tz1nPIZ)`M}`F=)G+i*p7#5L&0Mne$APjX9$2!dTdJMCxN7c?@^Ry;3Pv9r~Ag1*gV8*Y4j'
    'x!(qmMI-N`y%WS)G8G@xGpy-Z;7{r{iQ`fqy}sm1z2gMy^4j+GI>IN}clTxp?BNc)N77w#@z2lK+U(O}_A*75Zpq80tV`id2wW{}'
    ';nT{5_HMwb=|3sNQ_-ZvW0^kh`lM6Mv%I8zm=M3oJ)(*NxN+9tSb9xnGh!kbSf5TybGnlsQ$VCrm+$KjSE{+OBM9@EmjqrMUx}>+'
    '-8c=@sZ{F%0eSJHn_lX-0w)wWnIOkYYo5(~+?dWQ$Xa<XC*s?WtS;g%9<&z!c2y&Li&dV9T=FnuM#6u*&;7Z~pHT_YRe#G=l3BWJ'
    'QZYFAHODnG1cud&BE}tij6O|dB?HGUYs}>MFe15G4CSPj4}nDKlN1^672=LN@o@;5HM?gD05x|XM*f7`CzG)-E>Ap|&MzLZ8-fli'
    'K`y-TgLip(HQlv7meBuimanXZlcp{K+hUsTOqJA_w;<;SRGZ}*TTR3N=rGV9TR2^ds<+61jUk#A%GJ8dg5KVR3J><2f1x2>%hM8J'
    'K2z$a^u8<D5CVCAlCfq-kIergmml>I0M(nQU-$MzFzMymW=c8pPB|2EaDbE87Xh>R5Ry@toauWkT9d`49kxd-mR<&gkO^Gtj}R!Q'
    'FEK|U3xFlqoSEjcGO8>^;;YqZqr-#PVo9*%gC3a?C51Rm-aCVe;shaTv8`=%RHysx2B%2>c_}FubRjAA+4HuNIzw<N<#n~=rD|Tt'
    '&p1X;iUji#jBUr%Dmq`J<X%~VwDYxhV_m3PX75=nl8NuYjWX5QH>N;+36@+DxQ&7y^ID|tP|ECKnIb)(**9cac`EpQvpm}wvg5?~'
    'G^O_Da@}gO8Iz2C?{Q}02C3COVAmlm+6cdN8I2sw_*xc}K{ZBc)DYlCi6Bm??QPvsOT(=@VX0|r1cF}>Up-eboNAe#G0%%<tWzwW'
    'W6dU-2(`PO)1rC;0~N~j?N&HG{Wmx1qZ_)-?iuD7ST!Lm!X0#GVw-eK{GA0%8x(K|adzWMWhLlWKq&oWQw|<?hgAa(flcdKT>UNN'
    '{j=FI9~I+j7;EBBXCN}KKOSqH(V$ZjG-c=n4g&5I9GS3~?!3d_$qd<`<?_Nw#OOgE6UXHx?7j|Rt-l;Czd|DAP+pu<0kPvfKltQ?'
    'YwK-Z$iA4a86@P5{h~4X@#G)l=cf#8`_oo<S=C|kg$*Eu^>W`T>RpC>0M$zsDDo$ajL9KV;$e)%>1Fqn1LCRKqPtS>`n{sn`3PhX'
    'mQCme6?r{%<}O?y%+v?Fmg$=aQr&iNZQ^IV^rdr{nYEAxJBJlh&=syagaFqR$ws<6<f<I(9JVFA2v+e=x$(LXCyqPMZY^S0SDMlN'
    ')xf6n$=yYpus=i)X~h~<{1C5%wp{}2?|SO51~=nD-K^Njlakp#bJrirmz2#Idb-9gNq&`Xx}jd(z5?6LrG(6*>!@D$bD@-0F?f%<'
    '!+~4!ZvIeAH%!b{@;~>!%KOF=z2~T4{AL)iQ|@z%;G+buZ=+Va^kZ?-s?~8PxxaS!?Rah{dvpI<gvNjif%;;&4j`QlTvgK>2T8UM'
    'Mxnlxx(xdoo{+kF{MiSl9ltA|JOJ_N-ocb?lsI-MuM$@+vGN-jP01CY?!dUaTL8B007-GbYvbG@v8?w7e1YSlD5DUw#V+g_Yt|5{'
    '(hTyL)S$|)N^W{=pu*lVI=$OgQFs0|EGWqpaHP&LhdgM#1n$Q_vR)4GPog05BIh?^Cl9HcQu6PyX^EGvd0|USKQGugpaW7f@r3Uc'
    '?$%(6x9G+8F*8$8E5vaR1<>#f3G^n|0W?nfq<ea1X|9(vSl_wsSFBfQe_)cV5pJG_(V;7RUS?Eqc2L#9Faa!blrV7(Q_}}QE3cN+'
    'gdHw|2)RB>UxK9sq%z~0bG>*EJ5jNB!yz}_c3_&6a6FD{D4P(c;50agU;tT7S`z9^oM)Fps(3-oL;6mu8?kTkyQH!;8|ZG?d}1Cy'
    '*&_rjdHQ6&aF2v=S<6@SZ8+;MJq~C>AHD1n)opmIyR`040!+!g^HVx;s&GV(O86#EI^u&5=j7dZ>+2aET@E!vDiCv;LXM)EuKq2#'
    'Ilf`1!FD{%uYv$QRE)Z&M`?K8_4vCeL2$8~DEgm8!Gkl~-d@BXn<0cg`Y*Jw!E&+Mg^1Q3fTUNV;43~s_|2d*y{9B!{sK$Ic7t8b'
    'ErEKcWG{%fFmmH;6OJlxe8^VhMwt|kwD3)H)O-G`PLI=b4firw*@|fy2@x8;1A&Bdx9aa8C|~FS-s)IGou*x+izxC>LRZwsR6M1='
    '^RqN5+j}|T6Any!0P{>~lTFiH(r1Y9AM<C(*(D2PXP~(usR*=^+qM*}*H%qu48FZN1Seri(nVDC8ZIwHf$uYmT*KP%WZFN(2SoDP'
    ';;``l0bA2-EY^kzd7kR<^4yt~&x)-y9(&Zr3-vEW+}h%c5ZYgJ<Es*eR_<n7WQi-9TL((jlOx!6NtBVQ#k_F6ZZ;1f>AaJaIEoMo'
    'Br{?Ht&8m3DxEwk_t2Kq;ADR;tvqEn8{*aG`qm#wwp{&=$|o%e?PSlP8>yz~J2GoU>-uUAfJbUKk%zIfgHFR^J9ld*aER6poV<j!'
    '81gH=<cdVRz_@n#<F5uEssnNV@z5@85N@r?AX64JouwW}pvs|4%*ppou?*k{OW9dAo}M%c(r|q9e4XEt<d8@6=?EnV+)?%AP|Z7u'
    '0l>O9XSjmJc3Hk2ZZUH$)ujeo@O~L5KA+|lv>7Ioa`EHzWEQd}?PkBpcqJ;}2ikhvxDfHzS>uT^6UFxuPaEFh)vMGhl_C&LngPoy'
    'S&J~2e<HmHpa)jdpBaO#efxfj7$8O&5a;EQH1UHRguZ2o{AH#N1IhBaEf&^g7N;EFth(g~NE%y};D5XnX)-IF;F`tw6n*tN_&&?L'
    'SOFsSVi{>FT$>j}A-g5g#z|mJ?sv(z_(KXMH>9SX?|YQMNjAGa3?7s<cX1XD%!m<0B)nRmcX7&F;sZa-_YaSTFhMMt*i%v#M|_Ae'
    'Av@+CWxTA8h{U-+a@YfPo1hO+`SS`MMlAxLPC3>tnPIj1+GoAf^H<VsWb*56slz53VVmp`&Wg?Fg{>5$h|3R2ZJ4v`mcy0~<IY(&'
    '?U>mzC|3$*z9OLqU@${V@*_c0o(j8Qb#AV`fShD^rc1CjyBTiKM#nIlS2ERo1~Xv7HJ6%+=B#<&Md{X&sjJ=5lAXUd@_juCQW_OB'
    'a4nZNS<vtPqQVbzf2|!DON<IQ7F+>bO*AL?R8YCVUI<%ZNQ*g)Lt6vH?DM_+M+u;qN3<K<gkEq>$Og*ftsicv4Z_AI#qI?!Mc=gd'
    '_=s8)7`jE)&`(9yeN6dOuw~nmD1Z2NcrXlFAn6nFT(5ED)Ym!)1}yg5kR;~ZOC8k4feN1CxbkK$2ROd}=_ag`O0Q4--c37|3g8VX'
    'n32v$?z9RxYtz`pqa@ar4GdFz!HUnD>vw+Fwi)&+a;C?2R#Ox}ozdO@GQ+G^L|r>MsAjNozsGbAu0w)#nUa;i%&1q7WV5sihap58'
    '=lHwZt2p^gVacaFos1w?7O<@HP_-F?6B*@eOz2~{q*X&vRUn;-ss?4w1%lMQ?!bqRin7^U6v=Mpv`fFYm1;68a*Q4G6oqn+`LC~C'
    'ETaJazDD1OwjNE0NfM&Qf2c;Q(^<nL=^!0p$HNiUgn~lucf9rsif?<DS;kc<B9Iq>1}wBwx()L&4lS?YvZav5cQ&?GyRZh7N+lEL'
    '`;-qr-m3Na=AbpNRwBKE_y_E(UhnqP-t>H!ql6cz?kGpXo^f_1l*@rG7wK>l-N6FfY1v237Qv5-Iu{#|Ew1VaGi+YIn&N+yqPb=3'
    '86}=3#P2lxdJ9lJ3HPNDm!AVwOB-gzjPT{mA)82d--w*9m^wxyVGxq70tF8cX2bhe9`_Qzh9g~pOcgUh>4|8TdpAg=Tr7x8PbD0F'
    'hF61<WId4oi7Ii2NFbq#LIlifO9<)*TN<8pRg{j2*=S!i=jET%RrhTqFx8sXp;TGee~CZy&#-NB9ptoIIkY_f`ciXBob{fu-2fas'
    'o`a)#48&}l0!z9vIe(*O#RDT68(@iTWD6%EzAQR8t^`5otmt*-V<~$%3r2kD+h@u+t(C<1+1Bqo)!kh~rRQP8R<1>ZdYK@F>5(R1'
    'QB1Q0ssk-ZMh%bK*GJ}QhFTY3C;!JEMR6*P-W0=D!5?XGROPSWk*DZGti*dfFCj%%MVVBTD}E^$1Z9s@q&FUJJ(|75?P@t6-5hda'
    '2a4Vbbj4o+WCHbnaiD)D^fj%UHjh9YwEZPrp|W$?4$X|w(ew)iD~HwhNFqSv$L6W^nM`KUL>YRvIJVpHPfoSey$a5uh0RNqktmkQ'
    'QvTV+?fGU?dG0Z}S>$bH@VIpanZ?@ojRc~-7f~*5g3!#P*G`I$yu8-Rdh=E8TZ+4`IpNrJ@1xc1ktX8_t7bj5e4U=SjL@{&Zm^_W'
    '#6-R#=#eWqAPuDMS;1u>Ed{nI+66w|R3dh()~Pbv$Ux;Z)GRIN=_>kaRf5c;(m-z-V;5F{l1Jdio>qsLC#;B}t~guxIW3DbtuhU?'
    'T+jR3S(UdT!rM!VLgBH~9$vKdX^3lz@&OC>m<wQniQ9fG{LJnM;m7{~vTfcpdu`F*k?HmKIS8^U|4Xv?5D(ft^}nOd7^P0~xQ0SW'
    '>uxa`KS`heFrEBe+&Cch!B(wSi`bcA08q0-RjC6p`TuM)eiU=2%dTDo{s?lXFK?hjl1sF|sp}hiK`A)f^aBl+?il>sJ8`KwyxHJE'
    'Vx!T>V)Y!em{NWlB)nfQ4C^&dbjGD&FEBJa*XYH$WQXH(1u<%*vDO&Wr{6{Pv0wbk8Bwzbn)JP~nk7Nyir@z~lMX%cX<(Wc*v9i('
    'k(=K>SZZ>QbEK7Oj^;}vD3RG$MKiQ8qV2^=3o?RBvGVw^g+^6P1^HZtWGVR)=LTGbu?UU#v;3y_hV|M6pH?%ZUn5tXpb^UXxz4Fs'
    '5vE`_?xX#ln^B5l;)KS>Q%Z{Sh-VzRBPLyj%rtCbu<;F=->IzMwx)!DW5eG4$+ckhNsTD&0|e1*1-*awdyMwIt1J32j<@Xq@h~)P'
    ';P2MqabP3pw^R(hOL3@-*EI=3*VUo}w((}b3a*=g@u!P*i<F}knzWIaKqBue9!6)yy(;%-*g@yfmxCW22Mtq22on2_)_)q|7}s^m'
    '1L;h9mpJ&LXGdL@%!6p#3{3nC$cx)Ffk34o5IhO*3_$^3*Ku4dB5v0@SzQO~ArvFYU1V@Wm#?(_Lk5t5()?>WI_P!6hc5=x2O@VQ'
    'zG}m^S})!w*|%O7Bd;KNYyTow9US?L!M>7rq3O{D&uE|PD01XtQ{r}0yYc>7P;{UC4_ychk$Y_OD>=Xr)iuZ#AyBqH`}Yu|3|Z3r'
    'j$xJiR-RNV^xXKXHz&X5ED1k|K>aZEqPrl<070gqyr@6V(ll9cIfsSI-|uRqeNAL;dPc{fg&1lT=B>|FJvW=|`bJfitY)_80D`BH'
    '3ghX@fAXXtV{x<QZshq&NYDNTKB5PVD9wQK-Km~IVzH@RF9%h7E~m+JrPyJw9fLlOMB?7oCnIkq94?IA=I63<yFIM#glui*`Gvx2'
    'Hy^#vFAkYM)Y3_A3={JgI&CCWE?J&X_{lu?B20eXm*lkbHjV5jRf|O(;iJF>4hUW&N(uPq%oazy=7Ays{f#&@zq5%=f>K5Jhj_|!'
    ';+&ay!%z}d*A~u`JnMi8&&}$bf`BG)5r(<7#d}j|uF8pFqgA$p%1m@uVG|y#^I2k`${3{(Wj%;Ou<rpOcvxn6Bm18JEa60_w7Z?6'
    '7U`a3zv9eg;$WAbT_r&&n&6}+?R;x)nb6G>3WCO;Vo-435GXi;J}O?;7BMNI>XdSoLCp=5_`;iayadJ@<4EE8HDGq0j4&cbe1UXo'
    'ft&a^1iuClwDeg_n;3`W`Q@BWWS)y@%O`Bixdb6{IUo&UK)hv41-M>sqv7k5=x@4BJc^)KHTDXj0BX8ok2W`mh8ut4`Jc7)H%QjV'
    'pF?1qBW3tP#bYI=J^vzqB@)Svf#-clnw#K_2TQ>(C1uXBYZ#T3BXUy-lDL~^&-n_WaKY+QghVsS$Wg+GlfS(h236bpZR{CtwPijw'
    'abx?UN?T%Ysnj{*bUsdri;q?{jX*Dgx5QPOA$4ow|Dt}7ig;bqjIGSvJL1Sje7BLK$$4n`(~H+UL*-ih#3um+uWem21|I#a3XdJ2'
    '8CM;SD>YRn2RZYtzDW<WdYwZ($U-l;zC_9V({DHcn`r2|s1CR0k@&m<D1NO)GHX0b_yP_7KGoB>+`yP;{i;(64xQ2{3K32DB}l=A'
    'm6>iRj;)rAt~ptjtB;K0%w!Ynq%MFP6YJVPeL|z#1e8ayRhVs$ACE)I)@6qa*?u?B=KD+j7wl!v`Ww-r9Eq%4@4d=Jf5y!*-jYWS'
    '(;rH7>DZXoQf6EH7=8j<9Tb=1JpxKrI7nqPlpN2lDnvasHZ@YIYVn!`<H+H-32qdrYq83USbY6NQP&OD<O$2aW-xLU^r?A~&Sssh'
    'hkYbDZ;np15nRg2R_At?3DS%m)b6H=wt|;|C8zsy^ZuhBP9o{IcmsM<NCD=;yXphr;M9*nMR`X~l2-DwSOT_{wutnurbEve(m;8_'
    '=H9%SbH2#nwLhq;N5zrc(gMeJn&`P@ZD8>YCW{A2HC!Sci01+kJ$M$6=XAPW+nZqaha<3>^%>lT$kekUHrmrxd#O`cD?JgNBKtrl'
    'of!0SvlPOAfMUEsCEx5d4sMx-oQDOfKIP2!A#sL?C?11iB)3R^9d47M`_P*p5<2tw)qB%0co(Ny_ZwatA!9W~23uVsM~qIIY&6~A'
    'QtMR1-GYs)&hmb=@_#~YY}~Lk$%MHLU3b_MLoIpAEI$*WEh4TIacq;e=6J>Cm`HiEd;fz~&-{>O?lg!)u#SuTobm{7U_Lu86Hcc1'
    'Nfs17ZJPeWzSp4h5R$z*<%3p%IaYpV5$=lL0FX_fXdm6lUzPl`8f}9dz`JaCEC~*Q%wF_0U8=u|8R6)F!vk|YRE3buzXxXqI{5YF'
    'h)K@gSWL=bR=-{p3*Q1o=*wv@FggYo1_}B-e(yB;GfnpwWKFEN5H65t2CiKyrL5ViNd((~rn0Be+9*LtYhq5eyEADG3mItMPVN;^'
    'kCfja9ub6};jVo_2DRw@06jd|2jT73m(OU^R%Xut+FYObec`vUZaxP8{nv>&l#o^vI@)Wog&P*xPo_D#cD{hU|5kLbnbCH}O-<Wu'
    'Xi^M*I<@`o+l-N5INbbjfYIN>=NdEKQMBcX%ULmyL~gTgPP3`D9FbA_;>8&xhYj-XFcQ8iZ6%OP>!vHMa0z-$`70cmU<^6o92+M9'
    '+!HzUZ%`O^Pp&nG>qn0pKL1eW>XdN#4vlktqSc|+a0VAn;FpJn?0kqt`<((4w4-|92ArB==_Mf_$`%ubD>o@|0<Rx|Fld@*tO&HJ'
    '3r5+NEL+7sjodcWL=ptlF8b#hVl_rcAAEb6k@JIaJL0z@HBAn2E;Ai{OvJ+@Dov_CrPr7{pg@xt-kP{62omewlCRao_?Eu5nGuuk'
    '3zd6K8tE%(>?~pesO50|Mk2s`h*<G5bf?l(=knk+Vmb|5EnwO<V47|A;4<sW6h-Pdh(NR0srFO4tSVM$=yOlXHaJoQe%8jNW#}iX'
    '^-opejxae<<ICh9q3Nhj){qiY=uXbg*KzM2A!#JC^s!-z5s6%(RuW;;?Erz@7SoKtZ`aQ$JG-Ca%mGsCxM;mlU;$RFjkBho$fP2C'
    '_N6T_z`kAesA2t@X+fxHw%_bW*d^vw;7TX-U;ao3C)Ie8#U_4mKrKMMAOAsz5(C&mfjn@U_(!~%-l&ZN{oa7J^0%Xjne2R7omLmf'
    'x^{=Yv1W0E7R0L&aS8U%XpLOn;c@DCqt1pdZlhQe`Vhl=x+dxqB{C<PU?43_gt%6{1{}BYc;jBTtg*j}c0yW8Dbo1jB#q%y&N(wU'
    'zklzIE72Q-&c@*OMTpD3_*H^eJu(#P4VvtR8sKe9<*p(8kA2%DuMF!g;^Qtr&oxN5TrVa5QV<0KBUGCu1@FcVrogFQiv3a~%Tj(Q'
    'S^XQbwp=Kgn0{b+VULnvt5DW0wvuHjhe!+SNqLF9YW3z)G{X|{oy(ANvP&ubNz7#CanDp@w4bzN7H)_SaHU83K@~gI1Y|bIiGzU{'
    '6(ZbHJe}SFU~WEN65YLiDpF3OqO@(XzE2TO1>ivWoxD^JE33&4^~YSuIF&(%HqeDC=(>Y^HhnI<?Oe*x!G1F5W&k<4<;Twt+gx`2'
    '0&A$r>w^Gh>D{r^6^mA|e(?)!30Gc<l?xT<%+_Oq>Il2Q|Dk^v2SGGr>GH<CKQX(IX>O!I!4Me)fa(@2*>+^zitS$ec6$?`>@`+B'
    's+q*v*h`(MblCnuHB9Eo6$r~WSs=0WWyEu4RJVu7U)s)-2b3cQ@v4;R9$=qIktvF59A~3Zt^cWtgPJJ?Eg(%>dlTfZLka(rhej$;'
    'i>fu&giuj^BbMVGBLJ!fHkmm{N9M>sM(JBw*!`F#Lv$K+A{Jam)9t1D5_E_d4B~1?ZwrE=e@}FtT7M<-vmRh4eyv5)ypXY!dyTSs'
    'HQ611@xcT9H5#bX6>vIep=BrEiSRcqVsrW86raE(bLPu?P{-xRl11U?XjmoKQJM|@aNs8G{5K`MhD6V(BeoHA)b`K78n@p9#xjR8'
    'LuEM`tnn>SEjCK^$xwG+-0Vx#8e)KZ@OHEZVe=m`4~Y4~m3t{~r@n)2%ofUi`dm5lF=w(Ws8MnmX-pDcmuUXl4l)8PX@AXb50QK>'
    '7h?8fEzEd{;cUMgjI9jA`H|i4j&#kk{9DRzf&iMAZvs(r5$}D!vN#$>XLIJw(y4t8{92bm28N6fa$R=u3xZq;P4pf;;Ibqgik%6e'
    'HC-QaLrCO@aL8XoUqMmGjQI#GUUwwe?;_!vh6N|05Oci8U9g(pp?<mZdo~dQtaUjzz{ylCp>IS#o_x{h^#ZdA%!aap&jTSbG`XkY'
    'vy+6i$;PgDl2kvSWBeyzsw6jBKME&A)oF@QoitSwHHeH+EJd$?JgxxNU~r}Fdcqe&uKAJhHdl2``;bz<vX@iMF5S`fkPk10XDj+l'
    'dM*PvN1xSVGyTp<-19JT%|2gq*>$;6HGMR$LyEvd+Vy#xU}7zD+te;Pe@ro-cWvoHER0Fl;njlH+bCWGs4g4Pe|omtz3CUhd^UzL'
    'K=HKrsf$`55nc-i%%Kf1w0ww{HhVPWi#<!2_X$1S48EJK7=N5Y4Jz*(A1&iA1~VXR(|-4sx;G4ZP;vb&=>CG*!0LSX(Dq$uB?D_~'
    'B#M4i0ftxcNJDv4ZWJVo@z^Q>T|Oof*ZT%6!Dm~#lDm^i8iU1tAhK0h^~A9u^DI+gXBv_-#Z;M0qMx0hO4=d{9c#rPJvO%#jM4gM'
    'mHsN*d8$bK`S6T%OqZT_!Rzu~{RTm_iNaSzZ*Vx3K@xk$X}o+4zZc_zR`b7A(`=$_EhVG5@;@)%aH@dGpzmM(5K+MMN>U{Hn^50a'
    '>Y_7?Za<HvMWPK_a(Qa%J?v%(o<~H@!+rnAIzj3QoLG4VhkJ13jxt>=s%N{n0|CuFEZz45#LK_>=dj%<S6J9V+Q<f`@Fe(cW0u>0'
    '#(8lEh?i+AVfPIVu20p;#>q)Gc(sj=$TwX5zUQIGl<BactZ@g5Br->Jci6~uewzgx3je0xXvSCw5~1#mctoUZ`3N>&m9?8Ty0&+$'
    'UL&ei4F>zI%ceT+7eO|wl|uqYaF6PCo1E*xswYpCsH(k2=CCMOGQ4~<4dFV6W!{XDirnh$n(M1P-X)p{@i^Rw;OFQ_yHJkUQkGH-'
    'yGjhD&HojK^ZW@WlnrfZt-pp;6<nzBZs(p;p!Lg7*y->w+JF)#R}rHu<TqpBP20lBe?b;;ylygGC~-ts*!r78Lg~htuP^8W?NuSu'
    'C=R;0i2sY^tO&NK#Y8=4em5)co2eWw*r9*p`H1eRR;mfG`n7cbuN(ey30DcN)?H>W^tZ@yZX@1`;C$JJyfkQ9T>2?>g_#aJzxj4T'
    'H8UhjK2`W~SIh=rrQJ#1iBmzB07@O)^H=hCx}<Z3;&_TT9nsJl!tt1<67O4UGxWu_r7g7iVVPj}e28<1-BAkA4n#^ddOcxe(G#+E'
    'L9+K4XXYb5H}}1j$O0HjiY6Za(ddE)s41r_?d|iPW>+O`yMvi0fEULpuxye?Yuf=ZM&9Sd0epP)qKQ(IF&oiq{RE0I;xaYprAuJa'
    'wp=a;zWE$I(CEjHmiyZcL&`K)CWeQfQ>%ZTsAR(cflBe$1qf=>Q^pVdBo@BOKRG-TlQznN9Jh8#yR|H%I`=mj{_{-gn9$os^bNwC'
    'Q->5_^XzwW8p>i|jbV)_352F6{S2ADY$MZ@myhs_*L@t6Y11@S;B2kAPs<W}7welq9~1)Ok8KeeL2~8;t0&y_JT?G?X$3C#w*qhs'
    'D48t|QM*-kte{^9la;23ED2uqT1z`kWMn)~hBHF)tFq!oSi%ZkgDw4Z^}EkXyIc)=wXUB_>0k`zy?PTqu|X2!61zc?z~%kd-yb;g'
    'e5~hUmB1VF&+wO4Zef?PMWSA5F#({`CSLY*?ZsoHDpf91-Y$~c4?wWemU*GLg$|qfrsw?U7sXU!3GZ2V8&BgH+OcR^F(ec-`#aD5'
    'p%&Uft4}I=_D3R)g<p@u{dtB|KDeRp44Dtei$>V<QSC%K9vt>Im?W!^{*FS_J{Xw~jF$c1&2B;v7PQ<#5JJ4hr(iJ})ww&tUI|P6'
    '7v)^v6^ipk53T_wcX6pdhyfpk?ROmxuX>$f<uA9b2enB9dG(TDU-H%zqV)Bfq4+b)b}wn#SV2qypgh#fNsoqXr?sQR`l|1<pB|mN'
    'kGwMLN;c9Jfy>ceX47E?Mff9D)5x^s&N7w-1UOOBDH}DiZ-^$+R;ra%FLa-n_x&Tl$Rne&aRge`L8t}l2f6XCy1{a!YYcS`ad-KQ'
    'ZL$$Yv32a&2^^lUufA3Jw02heA<iN*EVOMiI|L2y3?=31$YPME$&qzRi)JT?*s>i}U-9f8U{B+nb`Bx{{P@{$G6I-(P9I54njWf*'
    '5NCDW)B7AAu=W?_&UTW6Hq;LwSI;v))PYSqTD7$cC1q*vlse((i6j9S-DUJe(gD9PW&($0em*uj0;Y#l|D`gyoVlStFv*Bugw||C'
    '9K)6<zWt!NlcfcuqJdbXx5_{|@<fzwO@#MDC28=}c&E)>Y#sEPwy@;OOFz<FaVJl<Na^+$e$eW5CnEz_1wRZ$5O$}Fj{qFX{%nNz'
    'Jv}kIuo8QHm=%L-Bo7@BwH_|p_ddwbtTc?B)&8|j2l$f6!?Q^D&?dXO4%qsyes$TF%Cb?#<j0o}!0pdqZ_Wtj*W^PmOFt)&U#R%R'
    'X}A)`&xC3IneG6|dJX=Fg~e4R6E;T*V&(G4(gOl~DH5;K%($zr|5cQin4Ml(pGewSjcc4Pbfm#Ww&10~oxchlBkaGqP$if9JVBsb'
    't&1ZC5Y(LJzcnjn&LG{4I}`F%s|l-V5``WOy#-)%4(VM9Vyc>yUDTSzC8p9^9=f_o9ncgO$kV>?M`E&#rtA_tfMVO+HhW*&$Syig'
    'yn6GU-pQKFF0YH%l!m1*FAc6ypqu+`iGX$4a936uw6#GgHd);=-XkP`W`{$oFQ9>}2pYQWdH-I-N9i~W_WV{%4vEFl-UvdH94mBO'
    'KYGVk2}8pFxmWE6T7E+l04E?Bf2lsb<NCXdPZYuZ7@J$`hhQP=!g7zP<P}87EJ^Dq<Y9K{C;F`nS2$D`-P`r3&v*lWCg@rx?MMtc'
    '<Tq#))3T+63T=k{>lxCf$Z*-5(F9VnNh+T{b<+E<rt1v`weCuli@;H=7{5%alLGmE;>VnY)X8P+-6nkmT=^g-15?3k{2R;?q}yv3'
    'MwOr0G{vHV_dG6E{*NY@%_@oPB~s}0cYv#WZLWPGz#JT6*r;tWtv5kwh-*tWB;x6EA~uM{AOTbsZ2oCqm!N&}8(D@j?2w)nQQ)BP'
    'rX7$nEk}SL<b_&ioPqKUotKMhn8V4;_0V@pC9;!QRj@kGVFzLQpvCkH9H+wf3Wvkyw-nM1+kX<4f!>wWd;W4cok=DRb{BM@lqbr`'
    'EXq}%Cv#S$3b?p2H$u6<4D4wg5RWHNQ50?rl5e`y`91w=cZ7BU48+mZ;@M&K*A*{rZnb~`{N9sWs0D;|tf#6@`~|d7Y=?{I-d0ln'
    '0a&%o7j>MbNj)I4G8P$(i7F4mA95OS+T3<(!Dr5{yv8Y0=W(`$eo}J!RVHaAzpIBhzSpZ8zEcBJsZP(@_zX895S2(UH6AK)MtI7j'
    'uFLqthkTz|B&eA{txq@qP)~_tH6b(a$t2_y@WWn#MsCD$3iTBc>fVYQj<PeHNDlPc!pfq-x3st=8)-{3Z<rFsZ+o4Ew}yqb$6PTH'
    'D$#X$KLI|j)=b<(fIZank3q;YjWn_FyUtl5x*3oDjO+3B8UW*4x%Ce_8}_40OW8%Kx#pUtVofMPB>b=jwJ<-qR|woz9LUYjV<Q60'
    'BLb^b+z%E6g5ur~L=#Y$L|U&Cb!*fszvm8avUi5$wVZGW?yAELRS=k`N`tvxlZ@&r_tP>xfusP07rZPKXZdg2KWFzft)Dp#vZpW2'
    'j*3aM{Hyz3kN~uDO$MG+QJL*`COyRr7E(}`2!9-JOceu&tg-FrniY2{9C~{P|6Nn%Z}DW^ylBN#8zsGo-8x^-3aMTL5l)l)**HL('
    'FLS$Yll_eH(?I?w6y(h7sqo&@dRln2yz-Ci6D{7cFVNESd-<8^-PY=b;Ve@2P<Kyml7SKZ)JnWVuFCu|A@dWUc8&Wh0@@viEN%oI'
    '1nE1+?KSot0=;0?^vzp?`8HAFgf#F5l6ZGgzje@#UX{6wcI!t^z{o)`H|~&Z%3^frDJzp{QNVz&>j%DPn*(PjKx_IsD!x^9Yz*?J'
    'goAs;w?3petUc^yTb_!oO~{5)ND(1iIm#UJTOJwQZBJBy+aEZ(dwT?$PKZ-*0C8cT>W9F@M-V%j{|u}kU|%!-+IXkUI#xzJuElZ7'
    '`hEE@KQNU+yh|b61@k9my>4JgtG;Kv)CdKHcig{Co`j}wV&1>mt<MY;c#4PiboBOuFOF(_xxx!Rgsp6Pk`q+cRNq=@0?og|J)>3J'
    'M?}Ka2cruN8%@oJwKZocb{r)*JFO0i4+$_Fq-&)Ty#vfG36Yk#2bCg9n*y6CJbu_<)g3-0Ild11ZK^+1O*(uOKjTmDg=J_@l`Ah6'
    '9x@1>(`&D&@S100&f~zig01{miL}bfDCeu_!x5mQQHY7hhV<xH{ty#p6Z64CP1{XC`Z5r&RbgX!U+D*Xs8O*f+Jxaf@!?+RxmQ1i'
    'mc)EL2E{_{Poc~lh1>f(VhW?$Fus6>vtpX;cx1mKTx}H@hDP{RVar06SF-+;UC+@%Z-tafHU&o5=1=2*jB2{446UMqAQsr_^)-Qx'
    ')y|9mFu<7xiQgB(*Mm6B0*>yVFFAry7}Yy|LN4+)=qiiVSt;BVJ@Hm1g}7+a`d=h?<_@fQo~{dXfjGqy7~@#JYE?fWgmvs+1UAu6'
    'u=B($WsPctS2Spw<i>uc*S{LL#T7ZIMk)1KS}>^_%I?j4OpK!ihBmVxFOLGKi}j;|XkrHY$c!wO1$BpZMvRnj4+6C3^shUyk?N*8'
    '=z}ur!sKCQE22r@risB^?9h!c7duwKIpo$kmuc}NO)J8hne7aV3RGaqUAJJKjvMLJpaQm@rGsw@McI^7s@Pw+9gD`9C>N?e`_s+e'
    'kM4+dE)gDABx?vssHLSXj2O-5$iGG1NDmsVe-c6EA_POwm3!gKe<G?zENnn&z?&aEPmGYVJD5dymo)lp{Bs%6g^%?~`8+xbc&Px>'
    '+xa<{E8SlR-f299*8?(nMun2oIjzOC<rFE*Eaw6QSV+yYB}pI%uM3aOT_M6VH4Q)EwsTF4!&!LY9Z@St+1fwu$%b1e|Le}Fj%$U%'
    'tkOY-vTR*;h?b>F0d-#i2xo812Oy)5-`YZq>#QutTTbUF>jwEcw59Ab=rpm*-DL_H`Xrshi3ARY7r_>=X@tL3mJB{Mub`_6)Lw6l'
    'jp~gu2^9rlE!y=Z0aK3f3{Ha_`SmXT2|eEwd72Rz<`Hr9^fBd~_JJp}CobTZYxbajESga-#!E$J7#N5cNqgt~D#V~iR5VqR6Purx'
    'GKBrOO=%{$8$?LZ#1H7RMoU&Vq)_pv9M+0;V<<R@Sr&b+M_)xjLr7Zst{VT1lrB5uZLTwl%cg1-J-uOqnyjH`sVwT{;Dfv!%txj%'
    'ez%7QrK>elbC_}hrhxEzUO&ivz4Wr?f+5uVH;r<unC`ul`-Y2keF!|UIaOU}R63d;niCQx@wFq8#c>&DdePhp06i!qn1A6%R5KrI'
    'eJf{C6geGsY+kQPrVG;4?>o)fH!N${Pw|}v09KmATQO_wD;Vpv3WDSa#A1~p0}~!dU;*jBVg$feDv;;UH@42#7=7FTY$b!Exs!i+'
    'PdOt;k%EU|TrE_kizVj=fZ-G)KJ3BWg=T5$EtWkIY~QBJJ;0xDwDEx5I6>poyxVg@Hk6$Tx(5Rh%x+sTnyO`fFT?89+((M!9xjWm'
    '1o(MLAYm{d!W<wm%+@_PgQ_Z4CU(fpC&uW`5<!F5|3SW^pjYZZ%s$1KZ7#*4%)wg_f2bKd;opW<(<_XZIL_o)+@7QayTaH=z|X6b'
    '!1wx$XA-_R+(vi>%p{p+t3g?gFg;0o>+a(XjQ3;Dz}1edl!o9hu)2436tmPzzf2*%^3a7ujr8=bHBX_@-DcpZS_BYDaWG_YAGWXP'
    'HDTE{8FMCz1p}MHj$b+wkUvztnyM7Mwsx7(H9Cy5_vZ)}m|E?>S%#t(S*~ZW#nIV<TSZicn_el4ojso&{61h=C`*#f1!q9P)z~7?'
    'j^ybL+rO>C!F>ONMZHFw?)+C?h>_DMX`hPsOi2!{Qr0?Gl8d^_j$Xs(L9~&nN(zD>^NZz`>d0*ChU|l5JHHGxRtu=PNgt^pO>-%I'
    '^(+_0^LXaS!cnJ=(M3>~yiIFa=Y8Ci2x{dljWG|^sdNsn&qH*A?p}0CAFahmC2>nDj~$`cys~a8H0O0EIcqII@>QLjw40C4CU(6g'
    'ieILwM(9RyANj?&X8w!nW(FRNus89N_|r!@)W@D=6CW~K3usE8*+t^fVUHgId2{%UuEM_?1=-WS9!iEPXan)2Qp35{V(J;^#SfbK'
    '7iJFc&ponTpggf7fj!3Yj2OxCT=4rq5)<4rn1x+-1fZ^&gu4B1pzWjUvEF4+xH6MO_$o@EJ?DVlPJ-;uOw_Z=RQBjjwg`ey;%71u'
    'YX+hII(c7T?ADu(qz!T>5ED%HUu4GhJ_Wl>`C&3vg75^YEZaS}5rYu=MSAIFiw*9`lc_%&1~ut1El$P+gnprc0~llsmGbAF6rF^m'
    'e{H+Kp~R!XAxGwxc`BWFg+ew77SN&~U=!`im3Dv&M^371)GAv5v*r{IX=JezaS!*mEL&WL2u2LxYA?dG6*}z(qQh@XNaPnep0j%#'
    'ItF_{he{Qp1oED*zID}X&l&10X*;mLP%5H4J~P3ay484Q54!~z7V8sFy(m|f_p$%jO^!Hh32Wt2*~fNzKTyNw5yII^j7{O63w4nJ'
    'm$LT6kL5)VvjCaM<;e`x<OyK}Os7m(!GhZ4sIjHt;`vyR`fVwsF)%p@quUu{-v(xt0<xK(K{OoNfPa-!gAIdLfogOMn#|6!W410A'
    'Nn|t-hr<I(VS+OOUF|@Bouu2CSEDLK%K=`%s}4JL(Bi<c)KlfRWZJiX%?ZTsHpsyYaOtm2qdtm6V#b_~H)!9h3C#pam}gMFHaA2G'
    'TxF%b`#^<2dUd?O_o!DuB|hB*j$V8c0upBWmE`*f9gKGLe~y*@2=+tXJ-&|=U4jov>@7J3;*c5t1kIoYuB_dBBRg8%#pF}~&M<bZ'
    'j>6hxEHs?Bo4h~xs>pBnhYP)GZmrE~(CHdCAjx@YD2ZLYy3R?6V`nyrPGwxZ@S|$tOm-zuMFs55MJWYwFuENwV(%^v*){)3r$1TC'
    'w^w4q5VEp>OnaM}d{sw1>rer8EVGk@$Ke!@GgL{G-ao1yrKpu^Z<z#e1^0FZPGZ^l$Rr1U=IAeS5md{_B;DHScyJ!?frD;Bwlw@i'
    'wd;yfUQ{r(wnQwe0w3k<4mQs<z+Ia8irJSR&#fD!lGOQzV-~p7B6zRhR+#mvIcmYf^@}%Z&XU5txhuM@@FM^Z+s_r6==*KYq)1m2'
    'j&@&ObNeRW(teN&r^kAR)6mBWvqmOMIH!ePr(SBPU!yiPgYtyiy!7!Vr4E6_5ksbjB>@QL&n-!ae&??YQbk>5>W4Q|k{XDlDoU3u'
    'Y~VP~zoZv4>Km{@FPqr}AsqgL$cg}PtXe$oy8@K2S>{K}k^aTIW&<U15W=6_F?xsOSa@FYtQbJBBBfN(Sld6io0@^A2Z3rCkxk&e'
    'E_vxrd8#G(-{ZaNDyPY?Hvzb35B%EwwP_I8UGj_)ptS0knbY^#Hvgs=<GV7S1>Gyze@Jn=%3QQmpsp~CGKAf#;x4!`NT<~eRkpke'
    'c>;qOw5L{#qD{fOcj*x*&$KRSw;2dIjR?T(l2Pk^s2x&YR2QQ_LR#wMPai!kOio=aeY3I^Y$LB(NqHB`<NnjuZ!&EJj!Gl_m~V1<'
    '*qbu&*Zk{kyomXXNWWr!-}-zjIpjW_h8ewV4HVOn=Q{~+sZ(iewRpIYbnM0Z_IJKLSE}^ro{^MxmgK(r=t5$DgNeoanQ6aqXvn$@'
    'qmsuVGoLJZQ*1655P&hA7wjEsqQ-Xl72Wj)GnWH2!BnbI#3smYag0S6!PU<N1bi*sLA12&YrMt&2`z(BTt%UB=@!lUKk6mfJ-`Qo'
    '6wE(6JMZU;enUK^1_V308UIfoB|8&^CO&gpBJT4K2Cw+>BVvq?f04a^g->+e^1YOk2nm_II6JQ7Z9q@+<4+^w*ee_iuvC2iS2hQO'
    'ahAw_!RenH;#fRTI35Z({y7#ofa$j=J`Awnx&xD$+j3DXR^lja<9f<9zJ!TOyXim%2!ChiyhDp6ALzIrig8d%bXP6~@K+0n5*EpT'
    'mL*F?ZlM(O$}d#M#g$K|6Q`n+mUuPfPDg4*=`t#)tnuI+O(m3NB@SQjhWUl1af|y^Gsp+0q|Qt9dFtyb41T%(u?_%afWqD2vY%ea'
    't;IFlJ5in3C5$=*OFMMjz{9RZ4>lQ=<U|8I9Lu7+E};kNoEiv;J^xOsR?KxAZEHzfNV{P($!P+#TsmL}oT82Ehj(_*SjK)kp-ej?'
    'obZsa*GTG}Jm;ZOh&=}bItBM{GZ*fD?PCNjKnFIEJ~c7#BTN~Ms9Ds9pe@_W$X0=iPXp*C(fl5Pwl0Y&591darbgO#3`tVfGk-8d'
    '+ZPx0G7x)A7sZ>H1CgIX3DTC$c8gGRHqvy+dZnrqNfE#2;ut978$!}uatmU68YEG(+MdEN3-?LF2&=iV-!##jZITzt4GQ_MvLh~f'
    'h&`Vf_U=A|r{O%gA{^3SzP&DpA3y4URBq_9@c8|z004A?z_^snHnG1Yp@dHp#^gNiC-aKa)i*uGe#cML?D)p$<NSZr$?fj~zG<Qq'
    '=cvyqb31lGQi;>I;%O=UP!@P(uUvr@n#WMvZCJDbFw77bq_<&bU1+>sEpz!Jk?!Giq9;2Jsr1vi_pgDSbg%kKOOYy51OiJNpJ1&I'
    'qpO>8r}ZfWhnKZwEsXW@c`#={^du9eCh0stM~I?v0eOKtD@q7ITUE=SeRtM3yAK}}!p?Zb>Wdsl$Nht_8n9SqhGtn=B(ev=Jc$9W'
    'S-6&OgVGlEaSHuF?!Qv^deT&HlH-UScqFC;^1`V%424I_znjcT$nDijrCX2NoMNiN9!#nYzg%#aCl}43<+74-`ilow@au&JuWZGF'
    '0h<`=7>1QH({_@CbojC&=>rd1@NO4WKrEXO>zxCzj1J9I>Fxl?L-k(wE%rk*=PZY5oac%_OX}XWu9C!U>14wFHy}})ka0L8w?`>7'
    'Qn-({As;$yWK1hlgL9t&o3cr7s+EHA-C_Xi<Lp6*@rp02j)rPexYIQ@mrcw(BrkxMDcbPP3s0V3rVGK2GqbI_`mMyRqi1ZcKz_oY'
    '+zcH(^-)?XQOGz@`V>Z+={PO33xQ|Npw1g18aQNXlN43*9EI^Eq5Bx{&o%ebQ?t!8WndF~S3D@>en=5tp2C5ffB2VZcTuZc==4Ss'
    'dvLs!8W-)WJgZaG^YoI#aootxsHQb5lj4Q~gaVy#j2*E|IYz6Nee~kkt?I?Gk(7=3`QXz&QH^6KnAb6A7A<5HH17*p$lqM2jjrHP'
    '5)Af#<ExXbNH#zS=z}d>>`XpWfj4uY<;H-^b9h($#}Re3N@Xb6?}*P5&10V!inykP*`q=CW{GO@E>Bj@B)cn1`M@lPOb3Vu<Kqbn'
    'vmOepyEt=<r6hZ9S3>s*Xi9!1Th5eVj4b5ham7(rk|?cL4WB?49)s+6?}m2Sb?PIp3tNBc6W)t7xlAu2jO;a(BvFC(QB^jLgMB)s'
    '@1L3A(-6df34C9RiC5~%nDf&X{dVd{-ix#CPuED!u4CRX(P$~?DaY_H9sG{WMiBTwY2XrS*NO%$Y68EaEk}_?4=1GCS7pR%P(JZ~'
    '@^>KiZI$gOZovC}wjeNRB@)U_F(%C7&W7yxYH*br20aIwYe)K%KeidLCTXoW<+%9AX`lD|$kVItp~J*BMtrW#sBra*DKw9<=2!Jk'
    '?cN+D*v2p}+F;a-SmU&;DIBZ9`6A7WH9#wlH3%y8jG%I*CCw1U5c)(x(BrN?)*pjX*~h_Jgd>+1t%rI7aF5K$8Um`NeSw@X-<;D%'
    '6$18E0jPTK(kChh6lilRfb(v&2vkw(=+EY*BcC7rr(zIL=nQ0n*tw<217>ZohUu@i??a^sE$_*`!plg_<6_v$HwFxnxdK$DAz0{m'
    '6A&oKq0a_4{6HoUlG*F2?HR^U2M|<OMID%20WGWRr?%(_I<yLWpfLDm1t-rY&S_~GC-4S&xvqegWax~i9x5WzJs5s6%#K??9MH$C'
    'zIc9Y=dbBmksekqVfDRW#UP{#_~5CriY2Um{S@K2Z&fmOugN77j}y+EFqVH^cU;9UXs5#|RKp5N?`-C;^I^=XO#7<5f{(sdFQw6j'
    '*X6M^-sUYeK-?QT9*3U*Keribaf`dJFTq+YPp4nXLn(I)j;>V0ZIPElpxQj5Sa|7v4?)l_#k4srj^6u8_yS#~<`GWi!rPaB(dzYh'
    '9pVV4Ls7C46Ety6=b<)f%;20?pNwqX7Xee5#m^-W(RZW<uE_O2MevO?Pl1kE;Es%knV7&p_{%LTax_R|6~vjQ%d8uUk@)WRn%o_S'
    '(@Q4-rLAuso25RX+20Rj9$R5&{8mWx7KWnZuF;zwejdt<%dgo6_Xo#k4#54V{e+V~b%Wmhxw+|ElpSI5-8g-zv7`Gpf~ST@=0E(!'
    'Vt?HhNJ6`^z=U*qzQPvn(geFxe$Y*YRXLot0RU75lQQFbLp^=4U$~iT7$({VPGvOfQwH!&V#Je(Qeu>}$#WM+a8u&<!2J4+1zw#?'
    'KUZs?&Or33?8&Eu9>ZF>)aS#5SDlQ7dcs}<6hTlffv+6<HC2>Pd3VUAAsP!bsh9T@ka`Ti*P~vg4<u9SHsZ5YmYqSTkAJomRyaky'
    'dplYd1uw4@m#Ak4apIuBepa7-yqBwA8HB8Ib0@5Z<a-2VU1L`5@|N3c6eH#%^c7Ontt1dLeJVm@blH!sqx{f9rLVHxEi4NpIX`1B'
    'LN1GK6*Cco%K`hcfu=QT274`O(Kmk|Vnu{rGw=nEFH&`FD+1T7LX6r^dO_uA_O^qR6*&S)d@4zb24*r-Ad(|G1OzO?)?s+W+e&@e'
    '6xTFwTU`u7Kqp?S8DGKAm{1}W>j!*C+1?u1-OQany&?`|5{?g%R$fUJ(Cm#7aZ8j6hH2Ed@Eq%M^AwF5l0>y9W5&Z|@H_)3+#Mju'
    '@j<E{oZoc(ae4N9jq%yW40UIQX%ljeEdj^=wq>?!cMo)Bv|zD!3j&Ya_)5hl8c>kO+~?quFyq%2?wg3&AStiuR~&%<J`3DfFwW}?'
    '-zyUSeMi1w5m!AoI>^6<<IJoM@`wG#bbKpi+ngHqghEo#WW?wMsoJSqVn4NcdQfb0u>?ybM0iSp0wYWf;f8+cNy^oq+Byfj1!Wo6'
    '_;lpdruG#XD9}PICcTLtU=4^ZmmS|V<8i}Rki<yO65f%N<b}>di-BJmIfxqCl505D!`up6eRas1LQojgrb6^ZP6<&o(hq~O7q-}$'
    'VVp={Iyf)uAk?b&@Uz3_nxYV}maC_F8hwR`Pb?DH=0am^KBeH%R<AZj0GLU)`pkah`JRCx$v~RAz7NxKWkOTYFVmXYdB4o@K(p{='
    'L><?_sP#bje~=m54;BNz8V1QB*FLgjvq$Eb)p4J;*}4}z2LoIEGy(LW+FKSc^nToU`C(PmY#R&>6Rg=FNC|p$2hc$+&{`m&5U__s'
    'ioIovC5m!NBc0mTFH-zMc57`RJ?5wFwk=myhMi&jS*QP<;%~!_R{O?3`3DP1I9UO&pBlwdKBFv8x*-qncoz3?3g@tU;%MdyMZgO8'
    'q|loP>m(`)Vzj=FHuKA%c1s0w-;GcaR)E|p=C`Zu=+(v|VEbS$98~}2rrKOrub&+uHwF3-O1m6yDF@or5MO*xe(^pVI!rhHV=vN9'
    'C0HMM5hKNE4gS(G(+`GT8Rfg~v+)t|KM0)pYy-C>^@t_?POjHxf*Fw-=9{-OpsHm!rg#kat}8Om%Z{FAyJcV7{z|Ah_B#@!Vj7tF'
    'GiWq}e8r9K{sg-NZ;Rn`<-O3PcP4)_-$@R+$T!Sqge=4jypT(=O&yFTusgNij+w)3QrJZmVlbitH1;V_8p299e0w!4z~?6*i}IHU'
    'iS{s|uAJ0~Ek_6sJpqU=vZ@<r?}hwk)~VKj2Qgv}L{cNj5G7m}WAyt^-wYG<p@}5&F-S>vvL<+|g`PNaaPYFnv}B>Yj!5B>x{PJ~'
    'l{9w&*M9S1gVHxHuZu)Nej#STfCt1jUN>x0-_IY{fFR}RG}wPMz7%1(rJp6nD?#XIuN$fy@su`MW#2GsVE%Ju+Q_%(9mRDi?lpb}'
    '<#hD1o=x|r3lnnqIxiK*WDf>uZE+AkhphtHktKZq%jj)<u6gWqR`8Rzx2G*R!#f=5d$-xY1y6xU@BKd$b{YaIKRZFosudmsoczu('
    'VZSO&;z);l@9*jddhj!aysP&=&U@gi4UF3In&bLF^}R>DAzMp64=Lq^?UKU(<eL4e#NY#iB3}M2W&{M8>F}O=9C!|FPp1v3yUt98'
    '2J0hS)P1_vqAu=E9`pw;AG4J>1TI+&;f%sK9Ft_|Lx`<mqdR4WBn(wrM|`X#LfuWr>L!x7d7503GQYt-cWgan=)89tMRISnWQhJ7'
    'zQvhA?NMBib(+>1H>ZSWd_vLY?^NplJnefHxLfLd3J6}%E}%GhAR>D1FGujsEx`Zx6<BfP=1cE3pw5A<L&BV7kZx%AL0gtN3<WU5'
    'U{!E$15AOEtU{vW;;KRlySHil?=(fDNt=(%by#uEQ=r)IQSGB}?vv7=I1^}j+>bX9%Lq_>fxgF5Y}iErW<Vz@+`wmyVKFc7^oRZZ'
    'i>pY&QVhMxcKFvVlY`!damiV-I+@(KYq*h7Tc#=~VXP`J3ctvL>g6RR0J{l(Zt{p^jq7XCq%&>(8RofIWCDX&H4B0Kj);yP>^##1'
    '*h8(M0dXkTGH8gn`K|U@Fh3$Bxa2&aiu5XOU-G1_;Ng>XQdte!ZVh^9UtvWc>7#aG1W9X1_QiYCdRurSY$Rj)^9E~_#Q!D;amg&y'
    ';$gmk)^9twmr%DNTXI7}7sbvzCtt8zAyBdi!^?KEEB;Ri>5(R%8)<LQTF9g@7HIVHCWzlSw*-5W`*h9cK`M}nY5Ra?G%zIT_omf%'
    '2D@}v<gT<;A=M(}!U5pReuX!tALVI~8-@IsGZt1us`M=wg93Vk&q^kPrVQE(>(^@?;WbU3>Y3E+Z&7|^s7E1a$P8Dv*HA*Q?$h*D'
    'a?a<Bv%Uk=Gn2*3@wkDgF-X#D(?_A9BC4mJV#_yx!-tu#N)94-O`yNj@eP_vlFwcIAUc^+hxFegXNbO?ykSamZb|5~rz<i7>qh>G'
    '_K^jtIj%&I>V3T2nhV`jp?fdd4E$J!yM2aVP_D#8$=+IdSpmIjO!0m#f`p=O0-h{AQ+=?~-ahFMk`6m*GECn4`?*rJwj3BhjM++r'
    '_R{zugKqtB?M-;UDp8l(q}M+qR)Xy?Dc-rN8L~!g?C?sB<957uNfUf>I~->R>R0NR&AR;xilk#%Vk=StIaCNGt6YTULKA2o=nJiO'
    '(dn8%wc@S(EDWPMk5Zj<q{jy+js`dgMcEMab%2Jx%b+CPI_vcvksDWZ=?EMzpKmr)P9U$mtKBW$%$954x+2z3eJ4M`-izHBVbaez'
    '#XEQ$(a|PFw)R+CG<b{~kbl00!-8H<hG%CnjZc&2_dGEuH&2s+4Zl1!#8Vstf)+<5RdfP%jH8Id|Hv8%K#!D8Pr0&@VfuN~N0;ik'
    'H2j$E5#Z+NWL|D>@(~9$mv&~M<T`EXHVAF)q5Q5drw3@NDmxBT6Woa9*p(xE>6=AF&Be@i#2!|^0u>XUyy**@laEUNc0%BKxKbx<'
    'r2Ss1Kt`HWn&jQV?Renut`{1_Lq|f&Y9Zhy4*D@B&M@SBNo+tH{C`xV>00{%&{N9kFf);Ev7I4>uK(<$JOn7$5flZmQq&2Pt?X<q'
    'u6d(Wi1uuC$T&dTL;Df%SgF&-8fF?wwWR$*&y>7}+frf>F0Wu=lmyXqkJ-oB6=NgS-aw?Pg?4$)h36-)=APT9(|+MeaD_j-I17^$'
    'X~u$g)7uv$Zw|{`zq9@vY;1Xgdc@=Lq~4xVZzbFk@YlsLL5Y9>vfoO-4ULXbJHJ4OwnNi_+(pX2=ATLET+JL@XEv92Wc){5_2-wC'
    '498E#0t!sarZ`v<HAR{L+MUW`K~AI4hfzUrM#GPHE%Np+U0Uag?{tV^K&OK5I*XU7u;j=DDmK~~Dm$c*F;DIgk?L#@%Gc(}v%933'
    'cPRU`>-J@(OUKf#JGdo|{8$^Y7TTUIDFbofiwly+y+O1VUAEWn>IObe-(0_ZR3pKb?Iny`g4cLZ`}O6<!im&~q$sE!F6cmE*BRYl'
    'mvVfMc&zy8^ew3YzV=z|*~B=PX;iJ3aEdhwQU0@=7@3c1r};ji1OxZoST2nw!^!+~{0?+&n*hG+<qpV*Q`~z${i3eEbN{EJb20|u'
    'm_Z;6oN5tr-1xC;i%6TNUEI=<#}TE!J~K|u{87iJa?>j#you!c1fvB@5Q@jkTr8dxf#E5;vh)ssuW7AO>sOsOo@BPyrB!W0EAs!C'
    'c}&?h*L3;29bf{`w2GnUy-6`+@ItU#ml=6_&uK8H{^F7=Rg<$i)npFT^)#4-aOhUmdL?rXO!>a%OR*MqED~5-t4^Qvy5MIE0u*Ko'
    'd!0V(kniN5W3n14^NlM6_Smt>XD`LB1Nd+dZ_}JpR(y%&>ssrs+VT$C{(hyx3>o_4Mf@hpf#v~)k;0jQM9w38wHxdap!-J`-P4N9'
    '{(G1{;c;pLT00DbK^mX}^HnT^)^IZdy(q$sM?^~BlbFHmwJY<tFTPNw7$?k-vA-14F}&8+nRqq$4fxnGjc9C!VhS(Is`O=Kqdn~('
    '%`8D7j?;)vA@(ToTycsllQoO6PFIJ+#A5*$^GLKsp9jCQrI{K&qF>3P2g%q|0+~4DfKDmZDu9yS;}Ggy4cpDX{g|Y(Bg$NEt&`O`'
    'C~1Fx3Z;3<Iox1w&&6GryH7#hyliC+f9;&g4F-^J3X5HCN&|^``f(c;2k}IsUL)T`;C6OGo=g90@}`ulrmk%`bY`*gIa_$g7s5}X'
    'OC@kfp->besZv-HL`CFNze^OJvxcm<2}sS?#yGA<wcfwdIad8vijn4h*xg2Be#v!|o?yo0dPg(w)=C=SB};)!Cof3=<>XOlQiw~-'
    '*R(nynCmP#Q&1=?Sm|9J^PrSENvT9Qb~J}*em?0%=W`F(@*oSy76!$5S=7tK_oVG?^Upy`lT!*af3Lm_N!1?MFDn%<QJz{s!V|!7'
    'aG`v-NKy+n;j*Vbffs^}f3aN>M+f)KM~fmI$1*rVWhK1?b6c-;kK!VTo!sUuM-T$(+wvsBJ4`iBK@#Ye_L5m0qkwH)7U{9r*jf<k'
    'iAs~T+-pjsE?FF!mz-PkV24?LcRO=Syrd--`p_{YE~w6;mmv~|#PCmz3H9(fCwJs@{lRwB*LigW55&FIeOR-67T*Nu=00R4jpOw<'
    'Zt$-#`3(`qqO~}Wqs~G!Qs6z*U#80KG*bb=N@wvW_tfiz5W2T8D-dLjzDjsr9(bA#bx(R<|80O;!eHX%ECVv*NPq#@OVN3O*J`P9'
    '>ewj{C_4&{zlw?g+2)RtO5zX~GBI7&JjSfcJRyGG-H3^I$-(1iZ#IG9M{F7<MdMB>8B3XDAskKqL>+93qhCAU!p>9Gnb5qXP~?~n'
    'l_Z4nR%u}0(1LYTGbH$>6ts?is^15dR%8Q+N=l0gl85PN5Lwp;G!WkVt9g8o<uKN&AzBC(nIc(;=;bqKNRC#|kKQhlW-8d4!!668'
    'ZJ|dsA&je@OGq&c(!*LfTZ7ok-(nsp0)X~;he9A#$Dhb$*KOL64Q~&T@OR?V6V`<9iB|(t^1)ER?j`vTSa<~Z^4)vj+^Tlk|J)>R'
    ';#SCj{nwu9TetmJ<e&8i5ONy?zi7P@zvlR8zXe}yW;vU)ZWM&1^nR(x9GZ5;?|f1RD#2$`%qd?2XC_)7>7vXl5|J&qFn$F1g8#kx'
    '?P?e1!otbn&Xg&mJT{Vj>_dM(@i@x>uKGN|y2f%3kPWe?sW7z@2#0xRtaJ<CsU{0ekRm8Htalu{Sd)FlOEd0a;N3{f?MPA-4o8ZL'
    '*{LeAF-{#7|8}5|(7ow#&}j0EWc;b&EZ4Z>jYXy8#Vt~@w<g}vMs5-82HfDftmcvSkYkf|`4$E1S^6FnOF@GH%G_t93$$#gzakTa'
    'KU#4X(`w08uPyi3*QP?B-{J(k8(q);l1Wd&c4}98=1asvH|H+gV~2b@^bV!%rnJ?xk=ZjTG&g^v?&q8oTwuQJ0(hx(m~LTZX(yJ@'
    'WEzBW^Q*(><KO+KxeNsHlltE=NnXs+(RcYH#b%78%muhMPpYdVl3Qte;D;7C_}?YVgXEoV)UGt{02~fv$=|Zq&tBy^ZkIbNZV#l9'
    '3tuEHvn`{>L-?U+SGn={jooxT3odQ*^rf>}OSeK@t%?V|FJ{4&HdvyWW&Ft!gH(>~m%=+EA_RPIyfe)-48mG`=!YX>I_++t7QG~?'
    'e7Ad))?=%~KSpp5Q>YwSHkoWGDN)I-uB*DWiw6p1HMs*CUw*D!3?sS@rRWzGzYp;0mUHL+9~6syI4+q@M@HM}5t~wqSE)cBHE{he'
    '$4>$#`R}LzpOj&<+V&AQJBXk$T@8+{YifM!jDCD7X2lEVz@DY<xcLwbc?Dx2^vF~;-R84Q$4a5~zW-2YagcV4zS7PHTht&Qs4QL+'
    '>&<n0WR?IpZ#_SP9mJi#x8W?*QdN-S%53#UtcCj!V#k3}b-ULI5OHOHBfOmDuHm-kxK~~v;WQ0-QQX*&B-9<ZnAdv4v6kIu-Sp%`'
    '&}i86ef7a;ezb{<B{xi?-H=R<Fr$xWxtTeZ90GJXLAH(%jN-2Z^^)U@*W}frL&_RvPB5)KaT$jutmPW)x*Xop*PD*`Tm{R>mqNIl'
    '8l_p~H4T&H6(?5IcAKTstD&O(?W64h`8h<;j~vc$lEX`-q`2?=wpa)WIX{iSE3v48DXRp`q!tpXzT%CRDYr-5!t<N0b7^qShXn?n'
    '`Q|bdF=hZ@e#ZXgTpgHr^gEl^W%aRYyA{JJU?J4C{+bgvLx78y(KiCnL_%TY9Pfb5TtbSzbjsVnaln}Bl<hj`1=g{s-zAb2p#fy)'
    '?gIY%o}|sTbGJb+{EaOKG}KFmNJgOFZH1-~rE!ucP1;`B@kf!|l~tM7etM4B{Gt}mmv)xc59+tS+`=%@qy@<HxpdRd@!H`4_7jbx'
    'N9Cpc>+!M8)fDfsTj-zje5lK<5z#d_j<&&FXG(wJ-fM@ZiTquoyD5`AL3a4#XWZ3tB6Gbi+EfkulW%g;KQGo3x7h~iE3T1x<k>0H'
    'Ht=HSq139tHpvP(mGTzMLf-Bn%63~tyw0+2@3|X;Y^u9(T^Y1>?^}V+?dI@G8AhtZ<qL+BxGVfQKF=B>6?z6i0p_UTFMKuPo`Thn'
    'f?f>K)@d+`_bbwy`YMlT#4iaqURDMNmqxn^kUAB{51-)B#{}&wseZ|_YAB5JTwZAcl&w486(H&CArd_Rkmc8|!9k_}WuwOa6QA`$'
    'sfr_fG2)3EF9udB>N+b|-j^!eN{4&?mKd05dTva<a1}<M;atf8)iRFSipEZ*2k+#u(b>Inhc?`X8Zut?cb{PPi9+y<#l?qI`=5JY'
    'V<p2j3nF#5ZR7U0byYDRR3<)ICq3XN(Q$2yh==jebO7aw+T%ZJ_}I6~uu3d%9+X$ah~q5?>3H+PB<2KYXsOBm?;B_0x;>@g2Z{Vo'
    '^1J4$3a5W*ZUy-tJ&#Ck5#sZLKM>sh4HqdFD*n@&6yw~xAgQTN=qLz7wOYpM0Dyi}$k-vxXZ~hKFZ1PevZ}-zAIvW=<YqIQv~7p9'
    '^?+k*c~6?VL6}NhUdtzed*d0=I@lkn5?-6x9a_sq^KLJ1nRnIan$JAiH0qCbA-f+y4j&m2ntNax|HZ2?Zc4|yn%7#@eZ)i9%{G#9'
    'uTFtgA~wVxK<359p`&J^5^OO37O--MTIe$1%5U-HW3NY7L1WZ<Q5s-VCh053!buANOinQS3;$C6DxDI1>R8Th+(LLBaxh}djk$=x'
    'M{4PLi;}tH_F4<~BaA#fkR(4cHvGKRhGlAToKga&S4ZX36Rr8f5F4VCZrS*=5DI*ftxW5nWAU%>0iU!_Lcw-&V#Kjs`EmTplKL$>'
    'tO}Jeu==wk=dvhi6>0Np2MwG*=_k%p2S$)w2%W~wzCR3Tttp-%@Z?0pZFKYNAv(&)x5I~Ho^tZ+@5HRNvB<rv-g3fZP3Iz@XLZ~m'
    '!vc-Kz#&IDYcX(Hq5tN^?{5fBIQvPCrsDV3#-t-Mz4LILXaV&y8e=Wa>^tDr7?v2ehFc>_J^YU^8qO*26C-@P4$Tz8#c!8v+A*;s'
    '*VGI;{E`X9i9L_7rE*$e=cg@c)UQ)a6MN~`C&8%wzh4fts8XWgKK{xJw*wpuXivcsMXiH2$O>%ve>xj%qEfd!YoEOx@)T;qXhPuS'
    'm*SYjU|;XtGI_t0MgLC>r*e$?L*Kw`C}~-8t|NRrYFsW-jt_CCJKKs+A`n1X4!W&+YukWK?4%*e{`2(goAX%@GELDo`5TOpoH$<c'
    'wVwaiVxE_JR5uiC%0^e0Ej8^iT)^hN0B2i>+8K5!8@Qtp6E`MjTrAz7?v4Z|&rBa^GiJ=+fU2G!m!|z&DfP!u0x$N{;sO(jrKbZo'
    'dFAfPZ)65i?hVhw>gv!7|H{4zmX!&4c{LSK4U>(}#2aVMx;+Mw#bWj4zi6EQFFrF14f4u1KV4X+f;ns|)L@}sP`ZMr6V47CJW>Y5'
    '2Z{iLbu?S0l35hkUu6VTrG5xfTWRB1EM9|)e!Sn~I1Sv*+igmJ8?OV&5>y7fIX~NEs%nWrqJkMV=$QuAZp8oTWvb(-^C#L<;THLa'
    '8*K9qTyd=|Bm&gK4z6oQ-(=LlP*!fuQ6g$=+6jXM(ePulm8DV#9O<<k^F<$}Ftj=vOjZ4jM*=l~=$U<2g}w}whp!DNLU9jItLE{o'
    'y-Hw5+_VT#uYO-Tpn+=zXo-z6nIAYM8A$Fvta#5ye9l!hoJ5Q@2Z*4#f6wB1(f9g4M2y;NHa$ZDkh~|uzeuOS>qg<_KTPmZKue*f'
    'hAbj~wSz)szh>xkydILXnHl3u_ICk|N2T7N8KJ@uHtQcGCFpmtu`MO(3{#)@l8*3XG^@qmz7h<wG9E!t3Hl5~a#lohhAvUP1_=5e'
    'z*kc1hrGitVeFqn8kV0trKcsmGSJFd?G6DT%Ai^4Qc8jlAY&w$!fH(*k;-dZHXXqg^P3f{)j4(qy@WFGxbp-hF!kc)bh+rcNK)Zv'
    'ddo2xaO1?EIta3ZF29i?Ix=~3ReZ1lHrWHUvKL|WDO+!BuC3tLxV==jvng|o9&Y*BNKhd;F~yZq`+4-DBN5@8hvtqU<N8PNf6)t%'
    '<PL*h-k&j%p2JslPOT=boSF;US@W@vUr(OY4pb+)+P5PU?C_zYBozvhd%d*j+vALUfY@&o(miM!V^;hfiP6|mspBMJ8qa1*RHvX?'
    'xXbTeFt_l#u10Mr+yZ8kUIR9UGVC#C#wx57@oN|5^RzIdc*cs@8w|>;X%VI`U|LmnyG-Of`A-<)?U0{%K%6Bx0$eSJQ~~Zs4WOl;'
    '20K3Ol5cPiq5UqC9_q(VyqTa1H9#Dw)!a?t71?%6?hMkZu(c7;N6=oQ$NH<s(rg>2_~Z2jW+cQ(HOyX(Y2`sZS`x~Qi2nb{c+*v2'
    'zJuFOuPPO7Ib<~-yqr#1ZQfMC?!PyzL3YnA2ca~<xyj2C?q?t5*rwPR6aCl=)y=8@4`Q)bd%3nMQv(5oKl-{}NJJEMM?3#n>=m?a'
    '7!rw4qwk+SU@$WG>M{BR-O<%_`g}J@s?6na1c(6zL1Ywd<`DaJ!EBuT2}@1L;-f`JP`z@z@GO4in#=!zvPk?ZrTbidPj-2bAT`Mq'
    'FoFjjUIj&po%;q;<Kl!`*Y{_@6fW%_ufau5{}5&+dCZZkOEH-PrDJZhGA3$jmk4Bzmb{j6FLOOFjcB0epxTX6(PX?hi>A}PjV)5~'
    '_l|$B=d;PAJVFfGB#7`f{-%`_K2&N7%7&u+QizqoCMlPDkonIvg}rB>smccZbdv{Iqdt6rrV;}MljJM<pEhfw*Aq~)y|A1z;T&(J'
    '+B(CNL1Zrfg^GoE-1s3D`anJjETGa4Ae%p0+_9zYTsOS|y)Z}^Tl)uEOV!GL(nTX6_85C5VDy9Iz#hEzbM`2+$(rfFW?(j5<&O0Z'
    '4>~7OEko2xPkl&?*|%%4<%p=x`9)YeiN}<B4dKY&We_QB%dG~SM%jK^uvu$QEX^>VtW8VlZajMm^AO=06^aLsI%8d4!}$YFV#Eq5'
    '#NgA}3B?j_va;C?|D{zcCwdt~7JuTI2+OfX#M-B?Igv7Y^r*()1Qwm;Xw~Dn?9F4-4~Fu^_t8tNY{tRx&UKCROa7T1Bv?83F%o`Z'
    'A7wfGCHSmSJQkwjRs?2cC)J38U&|&BsECL|AWc>9hwt*gFXlA{w8qEv+&tPyqNhIWc@~kc4r<eQ&$a?3Ye0qWt$&7N17zTMhk|Ox'
    '^4kjHfmS#Om?Fna;U#9`Q(Wp79QOBC`96lacvo#4JRcGBG7{(QuQE(AF%rF?oOT5%J-s}*MdbQ5wj21GChHVr{NnpV+EWEa&V3>z'
    'C7F+jZbT%h^37M-ht&>yJFecFpj@(>sseTGjo~O_A&wz`aV=I8?Q!JN8|4I4h+r(C$!1rB$@y0koTiNcDOA2PRn-%@`NHNGO2&)t'
    'Mg{Ei!87_v+r$so>#gPsuHW<%ANTL@OH_{Aa(?+@LSXbq6hg6mb2&VX;A11~{z)vZtu#A~jY7}T-9WtHEO=kHrM4MSmGz@F$YEq*'
    'o_WRFOgOe}WBuM0D4{QLvFvD*171w7ibWz(%cc~KS^A9+P0lGMV2klaz7nuU$v~v0D12gaa~CNFV~2r5>>gJ(*RFfz(p=6C#BgzJ'
    '9$iu7RP#Ly>$c&mK2zh-J<EQ=NF3w%jGz+*A=h2sFCS6@d$K=LX-ejsgGCf`<tgH7iG9M!`X6vPZf*$53)zRaVjVyS7raTE0le#1'
    'UOxLv&r%%ED(^$N{YY0imu6$RIX_`(^{dy_KYOviTP7!JDjXQ=KiBBlasE^D2~I!;EYEskqi)7~DrYlE^^V57FVrUjp5p(ot#)`?'
    'e<CGz{Mv7JjYz<dRM)3=jlOL?X1;iueA6*~a72L@&|dt^YxXS-36+>#D{iYv4cPgB93<h2UN_-zaJH+|-owH*yYo3ZXv~!%uX_oA'
    'f^^tB-W~jIj6RLWs8mJi5%Xe-DFbM5*t+re@Wy@KxK;;!9%3l+p@DOBy?Oavh`Ux5igL|r{lzfcG*q_pnj~TPpDEPG%2#}f=Tfa)'
    'I*PeY6yvNwUyP7@+#y7JPty2vqtXuMS4R_+QzD~U%xivO2e8O;lt$fCl4Z$WdC*@UN^0vnTzI=Ox>Uoz+gZG9l_qbNW7fJhU*lN='
    'F#QJqtdt{w<^P@f>2Rr82FO}=H*eiTt7`=V!yqQexJGXHbuOfi%)HZyaJ?heCh{Rke2Bp!5HU(P(K%>&$dw@NMc_n)wvzQ@0M5zt'
    '9&+zZMkvdqpE$`O-dLkX%cOvQn+Le<zExi`<8@`Ui$9ZPX~A09y9qBvRF=!XM(0fN9BmliQ+?LfXQ#^FN|pVCO7bep{N^o1iWeuO'
    '-w=ZIHR9*da+3~*oSm?rJcTE-)8A5jm=D^7;4rSWmYrb|UZ<gZV5MieSQ9+GTC+N<(vqKo$ARB0bjeL57~Z%4r&oH#Ldel1a_Rjm'
    '&T4GF-UXXFm$C$r8Z0qoGo4*SHRbN_IjYa<EiGQ3i=cD7Q|Bl6{pLs&d#f_MQz^#W)(cJHWVC9g8sfXEw{W2Vse@*ARm11d#^CI6'
    '>-&{9rkBpL-h2~!I$NzzN6lLOmwK!>QHzzNl=9o@_}rhsbs@tRc_g$%Ar&YLy@s8*$H@Ytamz_#K(ES2Tow3nklFEb5P1<La|b%A'
    '3~zG-i0|B+xzAR~3&YXN7Fj!$s2)c+hWu=`rVy;<_67w*mK#~iNM`CA(x7@iU!w*vQHw_i_L>;$+AYxf;-*Tsr#A`;OP2(zMWhP^'
    'Iy?UE8dY*NvE$`y25pR!F|B|3!DT5e76thELu3r-BideiczfZJ>;o*e-Wj=iXSz#8#*A7?y~1g=N<|4JC{5-TE*1y(iThlQHw62h'
    'AR}RIZ&#AmCD_5M&}>C0mJ|*9Ws{et5{`~&rMjP|gg$47;QR}%Y;W<A<LpmRwfc+0%8AFzs_YC7rb0a}JMIXAsAB}S*(HME#D}qD'
    '5d5W6Kd6j~PgEUaF=`$4<ufFp>Bn<57H~D-IkQwyf5shZaJyj{bk&^r6VP6gtKRgYr0m|{YtTz&eT(R~r}Qv{C<a5OROlri26&J|'
    'Zm1phiHyR@eAYjd<A<QF=6#*e_#n)Hq7+lnKtRDMui>H+J;M)wt(UmrK(GgZIM8&&jSmI49poK$_>*MZp`TEk6MC$^QJuQI1OjLr'
    'tmMXNN-T-W5o1BkTRPM*OAUx2I>|Q+MN#O45;CDYF+;nr@#tEPyH;F(4%7(U`tgkrmpwama>^O**gGm0!~e=BIcpMZ5}bnU?F4`8'
    'n?$!dX)=GMo=C^EJ&;Lyhd!hRl}cJj00h%y{-HWM&A|>vyHu*|*eE0dt685d&g>7BpxUj(=kT#|1y!l9gi=}tRrGZyG?)xzQK<T!'
    'O>gMMhB$Q2Z%4S3s6}nP4)be7JONAKjf3m%Bnpg&9b7@tAk)r;@-D=ISTdrJ!MOoK*B0EEA7<=p$Wxz(d6)CT<l?rG+)4c6&S9Tf'
    'ZW~n+bmrYKhr^m8nyar!?z0OKBT-;%V>ANh0Z6?GY1vPzH@Od|By#o3=cDiL<df>dSi&Titmrd|36BR7L2rWPT`F$@$1=+TJBe?s'
    '$0*5O>DXu9fQsWQULca~4g8r!&_xswRT(8%{Rs8!$2mo)t<tf+8uAbj83sPaRlD|&t|DNq#{)PRr>9Q5OI5?a%3)9?DMbJ`=sgh3'
    '+tqP(0-YaHSxecDpXIsLNLtPB=bBAV0r^DhU}mH;Mj&hK<yBSYbxuWxbM89?7W&Yol7{nDa-VlWf##FNu(TZNZzcFh!bA4k)5>JT'
    'axAHazD-0J3;WDWQ&ibO;#7XWW-%{rVGf*y652d53tK=sgKfSMdZ&%48rDQ#H8M3wBm4{O`Ki{oY+;qh7gH_cq@St0bz5k4KicRT'
    'd}f(q0SA7bmQ@rLIp)%_`&L1I5KYGgzcztLC0$+__0v#tCm>J%E6FFO|G=V7g?@t*{HnAN?&>s=shIbLqg_lqUk47ZNa#ChH7r&k'
    's{*5m)v$+HT?e(8UBla@UvNugS65PT>!4eNHlGJOrThurCMRJCZ(^fWa|fx7R6Fv8!iXhJ3oNX$dKe2*mdw+tq-OyN5DZj-Bfop~'
    ')<D%buGHVsuK(VkNxAvj=Sr(DF8JS?wEhlh!;zw%P-riDkhXvD536mWzP!=X^r3uUwvR5++@8YjBMtOHiF*7uc1j%_-T7xGC*S)s'
    'Zl@p({N}2vTS{%sx}__qV3gq5CnqER14rS;<JOD$NXb+tDMU?49vv$SY5|)NA)-TFI1lR$iI+e@%L3KQ6R8^}w6B(7s0E01yAh4w'
    '^C2<)rh-dCj|K8G)h1?dZF|T7WXLpT9Qj2Q7Z?Y}qM%0^WN5Octy2XDeAzpWoG_bZ7uY_rrcVIi3XZED+n)OO)mq=QOSAKxoLpTk'
    'aTDS`Wu5L!(BUUv)4wH7K1#-Z1q4v>2rP^7&pjqX`XjKQuvNIxdz}}L8QdN8rvG}e9Xei>8k*kr6E$Lst3K0)qHaMyh*uk29b9RE'
    '0MO-H07S^tC$cskj|}8H+}=gEMHn<N>VZDt)l<pG!Wb=^PsmqIpw@>Z*2#*x8A`(XJymeKqCqjjTkfdU=OiYGcvvwYqxNIHG`h<T'
    'IC>}0T;7L!oM%=`bC-6~xz-vN+4lk?SfLl?cT!ZuN_-qOlkFuQqKjU~_623qx1w{ywy}(+^Yp0UAc60}53ygxySN&jGbb3c&A|$1'
    '4aGjFp?UKP0cqQu;$<^fJ^7+SYSTp0;C2sLGG$n8bnWul-#8-yMWv}w!Xamw!Vn&A)jL*}eeMB8wI#gIe#`BXiD@ZLZ;kn?w|=s+'
    'YVA=`gnW3U*H1-+0NVoGn=~G$#I)SmLt&{0>)wPw%dY~z&kQk98}o&M%TeD^fNG6x5?i0q+15rQreNw#>`i1+LoL6Y+J9+cs1<et'
    'y~<LzHs0KarLg-Lj@>kK{06S`*F#-ZZ*q56NE9^i-p+%_=2q6FdEgs9YcNXOd-WItHE0}|4mLRzgX0QyJ1@$F)R=nF?gAKr=4=*|'
    'FR+BrbO^gP!hK<&&wyd#Cem|5Bw}4*Se!Evmv%Oq43qSQlD;l{^$Rn7Ls3+ujG3=KFhB2pK|nndlU6O5)a;z*nf#+?Jc|))ivsnE'
    'Q==xe89L`ovs~&+N;7N=dxV?mUboc`Udt*=z-3X>2#gPv^(p6V0F>agElp3d3y2eKrnzWcDH*DSQ-umS@*wolwZ<tLKs$JK!O)CH'
    'EQlhZ-_(U5h!Arr_L#{I7II`$CFki&y*aQkn8Ua!SjDSEn!P$}{_-Q4t*f_=+1s1I3>B|amIzxCowrQhq8;Bvq`V1-kLA3cr|1<Z'
    '9JmV%dX!3$G)ewVwxXDAjoXPYG8zd=@ROE$=?+BXGTA&DO0|pXjH!_jz(QKUa)zsbO0{R|ZpTr>@>G23l{O9Mo3>P9hA=nIGpb7@'
    '!maG&osw-*3^!(l=iq4|Mj=sIf?s)_F|R2GUIgLLFrmVPdShb*i}Udbr4|RjI#3se%%93)wcz>-#d;6zZ+-pc*m0wvnd=mNaFsC}'
    'k*XXqSYcEm>V$Ey+O{_bwO5kP@ZrN^A{M7EdW0!W|8C`AiK&URQKBtMX8zZv)<Ca}>J*0$c`Ym~14ZXml9TJUa^+OU&<Q+B-t5qa'
    '%ns&;bLEOxgxz9$_ODNRkkE{*CjQg+)1d+}UIi!(Yp3>*H!lJKaBu3f1SV`xS%G%y14e^Nxlg96(qRhjY*;I>%n0hhc41Ebs?`IU'
    'U>g`o8MeG@Fl?;wS*m_$`Bua|V=$5%%bl=qh(nl03Fet3lQu}pC@J+;=9>DT1^4moum&N2%kQ9amDD+fW{!scKzhi+X9j$f89`ec'
    'kyFX?AS`-YoDC)+3tZ}?GoAm7F%R$x%I}<_YZNnjXpa%O5Z8l-xS6oi?+3cQRV9sE<D>uMlAp$0)aE;(4(2k#DQjd6Cn_6mQrs<i'
    'szxsA6JmC}(XYNct7_`~CeFsdYY_DQlb`HL3Qj#0h3H5)dH-*;r@AP3JsLE;6i2d|n(m@&)PEzGqdz+#8Pj@${I_huBP9DPAC~x>'
    'XFsQ`LMufBmNW1JmUY(kWQS6qf&En%++fJE5@3)+w=&Ik6<n0$WHdzvmrDsrNE+I1et&e0s3lM4G^NAIzmJ~?@wh^n#M10aw~feE'
    'BsF$^kKEY!viRe1V?)YZMpQ4q9b<I?#rk?}>fbidlo^IdWab-N|1;ZjdYNFs@(Bk2mZgMJm=DJTG<-CLDo5x#{9%0j&c$0*;`0c2'
    'eXt{nnt}c{U_}5T4u&1BlpnsXW9J+zlu^^jVVn5iDL-%ykFDWiLo=1jGk4*iqk!jT6NX*C)vCfX<!$y^r+l5@CNa~Yhng~PDCg{g'
    'zk`iB5Hn<a{3D%<&N)j-M77YH{=JQ@pIjN$vl)&J<qN?FuxD22Yj8}*Y5(aMkY(k%`ig6E^%(!Cj(}OzK$s5O9!d!&jX4qe0B%31'
    '=+VR67l9vynmG_6sd9(+8T*sN?C%{*WdfIPmreV@lf$Qa?|Ag(WvYs~%y=>=e7oQH0)4geb&uX<uf%NG7tJM^Tf{-+jWDwElLzO5'
    'rh@9DD6NWFW$Rvw!vgem??G6U!RWPnKr2`*skS=?W1ElHujO=Zm9duYsO<xT-<J<@it(Bk%**ChyOsh>l~^TQECz3k%gd00z_O<Y'
    'b$nasu64JG49`=TYDAVnVlQLViDtm(P+=`A3h?o~m=@%`|CKQpK5FnRD#?(1Ua{gidco}9?}z5N=@pO=kbQWK^5<$0L_E5rJ&YjA'
    '!vE(0rCL*Ktwqx`s2<BuiXmkX4*(3prPR`w8&HaOCP-{p`NL9w_uaD*nNzQ<7!7bEi@-D<E<dzz7a#96j1FA+ULPYNM80t-R(ba-'
    '#e5Pq)krvg*s|33uw1dUO4SV%6FRZ!f*ryT*DMFq8AvJzEyrEzQeE975=W708s<eWoJbz5HqcZtB+OvT{&(HmCy4>)3T>*p8^DzB'
    'buIk;4Vzl1B<mg_9Vut5@9`rQdoDfx{<DpW{oILNvwFwpZeKwA-t)D%25LYk)je>U8j>$HmP>~w;`)3%xfgwScC_M>a+WtFf(PO#'
    'VJB!~T4-Jf6l~OncLq+X@z(7yy_wVi1N&%n-GRRJOfLCeVI4_Af1+X^?Va0Hndxq)b+4U+u9US3KVo(8AhB$(c6me`?_$w1gI&NL'
    'yP1qn<w~YY4NWC35Yi1;RnpTOalv}+hVQ-iHvkye_w&u<$f!I_yv1dMyamW_;nl~Dn!!mj{gFnp8#z_p#n!ud^9lu3h|*F_M>}^V'
    'F@XgUX5%UH#+rM$fufz{`(xkCE@ySBl73CrtuUXwsWL5C1{1WEX101I5OA6qH0IE3JK`eppH&+LHK;aEhx7smk0X7t@vlb=`;V(T'
    '(J}Z~ngTP^r|LrSF#tU=tgRY_nB4oo<|x9@oxs==5DPKNz|S_2H*L92m-K&qnG=RFnJEg}QF+1a@?7pc{vE=9xwxne{?0fc_0sW7'
    ';my^6-rnW-oO5Y(QY-kdH3mDipDK~|bso5bJLniskNLYjP2W9|$)Q*JrB-Dr_x~TzTMRKc4@e7*kjgzhuQr<VQXUG@hR!{Mn(jf7'
    '<n<9U0?-6Nrm)oqQDw(@(%fdfenF?9+$Y9_pp&*QR@H{4V#(l<nQ7XxN2=(u_i+7iGEUG#r$4=7!l#6n5%a2zqtHU`!U7W$c<^m$'
    'U~U^<M!#dOY3H%r4U8hm(grT)H)B{54TBvjlnEi4RSpMHqOLgkmCbVW6?424P~S99K4+Sj#Joy%V2%QmH(|mK{;<wx^lBdMo}6Ql'
    '9wzN6l4nfDKnpBws7FUN{2^ibw<rsJB80y=B0USi%A?=I9~F<K`|mbTb0H|NaLF-+3ncUyF$YiNC_u$#V*MUu(UE}54z{MLPPR~>'
    'Cm5{(8rdhZN6hIb(Mr{c!u%-)4n=wrYaaIl3l6=#0o^5l%t7ds)S~9ENNoM`iX+@iw$i&Sd4K9Jm0-zq90Gf|!ywZL>BzK~<*s(>'
    'fl*2PGmbB*$C&+ncoWF4ZUlrJbgj>clOeym$S)(*ne}-j<s4n3Y1N7nRss)FS5bK5O^8x$teTwMnO$7iJ@TLDz-}6nX5k(pH!VCE'
    'tItdWI*_}(NV^$}@GVAI_}nU+HAH{@mb7-$=!PSM8m$;L^V?pm!f!X(DV(L1U?r?uT5GWQp7rzKoWhMx(!i}wtD;=c^?hT2{VZ_a'
    'lOp(jnE7X&Ovk_whV?U%$v_Y3CmMAqWP^^&wK3jgRwVZ2u2-aU+bqc67cn-?SGHQ%-(y!me2{Zj1%*8Owd$d8(xl={e5hxMRc1i='
    'BUaOUZgMd7#DW0F!KY1!L18t09yew}M$*xs4wRsihwZAqsp@15;R?MJLReZ_#|8FDS)^*)oGJSw81LpK%P;g28#6r{(iCT7)lghp'
    'acF=2ymTq5u});r&*uyt*7;^tyM!Jg@^u`?_qssob7of;Vi1j}*Q7=`qJCpOmWFZV&elrUYN~KD$(}BUyWjqd&I~nZ1@D)>UmN6a'
    'rR%g!2Wiu&K8*#-@TFtL+k}v$f})K!mi+-#1oS7`VKPsQuhxS%12rC!l-$sSWkWq#K@F@NLL&aAwM#y`t5LBU@FQ`tIs&5zAoZi<'
    'Jycd^03bF)a5A!a`~?YE@Lz)7wsj+JOGuA#>|J+6L3H6N0O4@pMUG~Fl|tnH?^+<%V&Q00!0B$S9>ded9c-iE-wXIzI*#~OZy1C~'
    'jBjHjC>be_MA)<D1s@TH!LkvT6oYZGIdZ#!!n5dwz|ftNv^N2*Mr~*mkJ(&X1OH@%cb!>A4^*>S6N|Mg%4(eXc#3*f<&>Qn{2=m<'
    'xiG-fa~MZp556^Uyj+m>M1Iots+g3#U1Fh^x!WPZ0}E)kv_-KNMM=4ZBLQ1%K53JCJgF*XK9@9_)fmLndzkt7p^$kTr@sL+4XjD<'
    'TgVg~So-e_jaJgZ^}_sd&YQ^z3iBAi%AtV9s4-VM2`UP_m^?nGHKQ}VF}_Eyu$_swiwQ4a&YnoL1cY^nr<!8jAHlQwxUiy}IQLHh'
    'ZFree@Yc}GU~qsXcy$$v93Bw>G@!06zTuvQ5GtXZ$35n60Zq!ZJ=%m~+%N@uMQ%;RV!r(qFL+kt7vnadMA-u#Pwqx@^=5Sq{h6*I'
    'K669J0kZpvQfG@mPE=YS-%@mlL&__X*y&lk2Fsw?b{A9w-kSf+2MMv0yOU-H+c%vDQ(O~$46j&rpMNx$(7199OdAcK4_q<k002vl'
    '*rc|u?<JuCc2P6He3;vRap3o7efNKY75$P@0|VoU9ezWo3c1b)9{(we@P!Tdir{EA0Zyzx={+Id6IVcSKzgq$LyP!o(G>3Kdb1Ji'
    'O07ex-at)iq#_4oVL$6+5FNvTQ?{TDW{}yFfSD}D`1H|o_j6?(F0n6cE6krXh3uRqs~gw**k+WTZ=UHI@m+edH)0XF{|2WK>U(W3'
    'HYdMo?i;o=z1A$M<K`FJ<l^4k+7qcVJdlw%55dT1{AtNh`D(E+3$b~HGaOTBWGMJ%jpx9MJ!d(I6T(KL{;rW|xJF#o^T`Ey+$sv?'
    'Fclhstd$;rl=!T~Gp!DHOQXGSZieK^qynH83X5~6Ym)EaSk1WZH%c2^=oFbLJi-tJY#8J&be^K+C&I(7?)$)m$L|ff=^ix?@L+F$'
    'QWrcpyr77$(oRs_C{%Jr%cb+)KGrOJQq9>AI|e}<BIcJ6%+kU+N!qozcU6=TbZEu}j~G5WjIQNMGYGgS7l%QIxX72Tx2+BHulX;g'
    'UG2=kA>1_Qf!}Iu_-gS@TBIR?sTLtTo=>8t%WY)|+@+4@p3H>DA)wH>8uWlme|vm#y050?#z%1vVH6xXRl*{|A+a^pvH2mSny==8'
    ';{8@z;kn}o={`}7wPfyAWOP$u3z~fq5!VCd_JDE=3V9yzh6s}TG{ztdUK*Z$eBC*x97ufac2!s@SNQSHVnG27D91a&!c7Z_MUwA;'
    'Pjs5DGLO4>-GTIB$LD#c9*J?T_ne7Uu&HD8Pq`syO^5v4m?N_wgMy&t;Y7k>7<OxR@DXf1E7m`fSO?#mWQ96W%oD6WA05>Fy5fG1'
    '^a&cOQgUK)_js@~0bJ4leS>CM_q-df&nvmIy)qgy)jga8H6dq3!DuDu^;W%_u$LPhv0x%teww&jXv9!Xhx~<N-T*f_Jt)Bn23lJA'
    'p}cR774eYekDA|OjfA1B{KBYX6u~Unlf6sg=yu*aNuFYhe<%B<+tJ3ht?BX6bg^=V@{4&#%IgOl)GKM<UP3j7_ONtQ1nJ&l`~P4m'
    'x44lmO1}Hvkk=66tt4c4Jy?KQde`~WlwirI-&q^21#%sakVQpj(81=?m{;`_0s-j8T81HaZV4+#oH!dd!6-dlDt6TA&EZO2^Vcv5'
    'ki5$BC^f=9C1vd0o$_VHmAJs|)oP5T*qF_a;|D7!R2lcn`1Sq&3fSA&VxU>dG<!|A2x8!2gS?Dya=>g~B^!06u&RFHDtSskRd=rH'
    '6exw)cLv(!a&hmbbD67sQ;&R0?hX(l2%ZUvi$sLZaN2w9Os|<5i<!DXHLdAS7A+9W${P=0V3`2AHmzRhI&NH-j}-85Um-aGDs+%T'
    'kxtsCv5B}Ba^*>o_eJb*AUffoF79^^`qDynhiJTv<9JdOg}BP2w^|mL&hPG_{>UhDaq1EQEV2OP8~uQ$v_h(whCZz_h!H+ws>;PG'
    '!@de=q-w_$t2Z<>%BuoL=u2`kZ5|B-h{_JNbu5V@f5jDe0Q%aAQ1o}X2qe6Ttz#lB)TYF*bX2d;$v$PE%k%;V+FL(8QROi5<XNbo'
    'ZSC}jGT%L_7Q3PYup$+~T9&T<99GO48It@YZN*1Hpc>SWKurNU#y&uEXrzzay~3gjbTiZMZc1=U<os0T@#cZk&LCWwgQ^3dFb3))'
    '^m1#ZYGZJxAtQV!PePcLmmpC7+(SNbG-2l5nc$x>-Nn#O`2;~mL~j2lYq(KlctABS%X*#??AAKZeKHfL5FNhz^v2o|wW`YDpAz55'
    'w$t1Z@VC2RoXxR|IVxSLBjMA=`b2pXXB&cEynbkaZ`a+tR4^ivQlCD)2V3Vy55=dk#ZsA>T}={QG^jJ%#SRMK<fR0R2mZ)eXK~8T'
    'C^2vph)%Xz7ux{0CM?0>ZZ6-KET__Mj|h=liLe&OWg6T;I#tz3$TsR<B9liT<Y*{i&_uKwWNd$5VF@7%=gv0A?f?#CM~zFVa~2Uy'
    '<t~#YcOY7ek0+bf#bR3ZZQjvC)M)*I!>7=^iyxzZc+}}x6L^2GFq&H>%xnmRZ~qK)PEj{L**6zBcsbGanWpiACA-`K7aU`qY|QuV'
    '&pT!45Jd*TC_A~sBLy^`&gnIg_+QDs?H&~OFeU~VV4Xyodb?elq*zHosqs3ZA-Gs77H{^3gf(;Bx&U~C4%z_N0s?J-H8FZ=GI@G6'
    's4N6>xh9x2?nCsNNYM(PHG%t*ajhagjk{<+1*2#U^!jQ~Ue@;>FgAk>-bW)aQE`4a9fO9$V0I^^_)-4X$|8IBEYk@icvZriJ0P_d'
    'B<*c;n0DlG=o*6Qo-#Fog~PSN^(fM!j0}781+)iD;hMUAtA;gE1N1WZY8V9i4CN%{$9=dfFq&qL2jjv2b>HH94MFIjXuk^IOWCfE'
    '=ww@Qmblmej^=2l2P@=q0cAgj`Y4s={st9)YGhY@7i_o$>YiVZ$=%gs?@REn)9t+}aO#XzEP<<>OJtmEG!5+{AvIg?=2E8C+SE7a'
    '-#>gg9ZZrLhC`H_J>U8OoU>1CSlIfSH3!(7IifpL>=d?&b}!gb#?Ry0D7j+J`D8n)F4v9r%RQ5RE)%jgCOnb!13*#xm~R0JCmV>#'
    'YUa#NJAy*bnkQMKx!aV6z@^KnTZ0q@k>A5E^)m7nu>A#R%)0p^^8go=65?Hwr?ctV@UAIiX@N%PdHbk#Tj`3AL9@<lMN7PV<WtR3'
    'J!=mg_(H;x;u1*+-bNNCz5Uf*^D4i~@rNd({@e@`Y0zE6EiS9W$&v|aX_#DRSrC5xS??`1S^PZClBH73NET%2_;PR)3=6=?qIyc<'
    '%LMLK*1gqPdA})>@}6QTZh1H%K|#pV<UZ>xikUj@v|yt&lS)ckyc4-p%`7{wu*6qjNSlgVV=)0QZPwn@W-@#P=p(=@eTEV+6ySxL'
    ';Z55vt8ot#@LW}qKd1zLj)kv-iyk=-*HkM!n@Gh4ene77=vgVKjY#<_g<e{b9*1HL&otM+;Nv&MRMhTsWHDy7J&+HeXAkC&mEF{4'
    'LKU;T3P6J#jX1-q^cO$8DTa{6d%RHmPjg%ynk*TUn^CYc_gls#DdiesZ+22F8O2dk?L>+7>OF<4XqqJW@l^*&Bs@^~#|7!ZYWjjF'
    'E1S6dtyq%EG{V0_IYT9m!dwaRe2O+>+(-_w<|{w5pV+NB<916^jZU{UqVJs`)q)F)q}po!4h^?))2mXs-{ATrS$ayy$>5_>5t|5x'
    '6e~%jY_9p93GLG8ahQ}fjj1!Y`4W5%aPiPobz115w{Ph9WbZO5WDlB|A}_HVdIkaSJeNvMMt5}~ZJoE(J%*y#H<H{iU|i`$C<yYL'
    ';0Y4Ab=k8aKKP(Nst#C7Sf^JGuK<mr<Abubp7DNV6O0=}BJ4qD`^E<Jqp=Jdn*&pEztGp2`wqledj5_l-cBOl3NJ;&46~A;K<4KN'
    '>t_#XE1G)6MA7;UH|aViEHSddDDtD+&ZH`>MTF}`3Y1Nn-AK3IzSL|wKIwUAm)AN4gqfpBA2=X7RtIg37znQUvJSH6*Rj3-#?1qR'
    '7MwFMtbQh~h3L*=cIUNlUnfajY^sjvA+l6!W0dC*oktN(p%OqMY~i5*FGvtHxo<K{2CdZAM=UVS&Qx0diGH;7$VaLVZeqtlKzv&G'
    'F+!KcCBo^9_qk8tX$wUx>OGM6oPUmLlI0;e)e4Nz={b`lzjb-_GnT>b&-CYn%(^89>E;r4bNo6x+c=G$o-JU-eYD6bo{mU~P53V~'
    'Zd4EDKWwCx=uV`dvOGYx27p2GHZQx(H!4I<uc7=RPr5uflcIY!8EN2%8dKn}Jtt?ivfI~g)Mo;EHr?-8A-2N5lyP?!`TS^dFx$<T'
    '!J;UMh616JXAJAFWHef!fUR|O*wdqu5ueoPPbo4|=ywD7G$k@0!2u}4K<!#$;vM$OCl*F-Qt<G#Xcs<mBW1pi!$rf&;PoI$sR(xH'
    'POB3N*6w_9#%MlTyK{(GlW(4F*aN3kPRUAWSuk$sNo%rhD=={0bfv($HXdGro`ZXlHuBHYhv&>~$lN>$ZxlIM2Z=CXV8W+Q-7RfX'
    '$t2y0d?!)LmIT+C#uLa9-g$C}s+rkMUK9!SXSQZ8LQ5&bRQ=RWMzo-qX@)gxFUksii8v$>C`6X77N@V<f@Hn>d#Eif%}~0pnQ}AS'
    '<8arMNR_4i8LE$!8NVsPRykF8;BvWmM@zSyX{;E&NtGCoq7wI?f2hb2>2|(K5o80*SdZoZ<jwG+VQZ<}G)tdl9k5^E?&o*EZe-Cp'
    '(H>w#p_Xb0eP4MWxI;&rH8BC>Aq%10KKHFMBu{#*xS`o&=Ixu*c69K2manElI5+yLaXgA0@tLNS)2dhAq4jQ<#^}NX_u2n1q}%H)'
    'ux*JyMRwdW5R!bv1?G}GXl2~pzK)juV`thdUUwcuf?RxAMm}_FZNg$xQ4J>}1rUd4d1hkY<O55o9sI8hA2Zl!towip+-y;7Wqnv8'
    'T&?FiqbEtk1Ujq0<^a<?FvY}=(upO}@)4i&qqOWd*xfnqpH-wK@jWGnctieD3W4@QA8dhYh3^}@_(dQ6(It_V5lJ>`>vWK)6P6g~'
    '>odgR^w?^JG}Wi>N2A)z*kU*rO)OdT2LufStDL-{=lwg@nY@8y3Y*j0oi8@PV5eg0W>eOIMz@lf=otSdYbbcDcez2p_qzVbmgui_'
    '%4b#E`lm{b(sJ_I)u=8uW`SraQak<U_GQxb+Udmg>S!J<!$Q<Df1W+HvIlOr`H3KZTru4s5nu_v7gqH{-Jz*C{EqN~gV=I=EQ1RN'
    '8rqOq$Jd*rS~H>$o(hSFcWuB4yYb#%ps^>s6Zl#BT{=r1{k*z`t`wb~+0l@Uvb=IG@(J~)IHzT$CAUN5DiM|pv{H&Fe$XME9TYPk'
    'E0QnYhyg$K=;4S*!%jL(NHQ9I4^j?9QiIla(WGUOL2s<y_D>E6`XX95vLF1tz$B7cHTd_duK-3;ig1dmr?l%03`mHic(b9AC8jIf'
    'dusWl46$5IeWa%n*A>bc5lQDT`~3pzZAgQE=O1se7uP*X?iQr39`^b}QcgXUiXJvTD_5!XJR|Fm|C;)D6SYrADwp(?!J)z=5Zd^H'
    'zzsL5R<i5P&=76#S?f&w*-U02Wco%x>bWb$Qg6PA`+n!?%t+jKPrDn_PLz8ZyR*r4hl9fJO4XpqXOiw1;iEPN?N}wYx?Ve7fmUnk'
    'HuxA;=&a$+6tU}L)|zd`4Y{3M)E2pQ2v?5Lj`bMoRBN}B|D<lHeSzAdj94G9&VG>%$QD&o-_(EUeClxX@w(+)mawC&s_z<5$GVR{'
    '9LGNFFh+DF>UgW-Fn<h!{31*KkkF?pS2AbqLd(XA!V8cuz()gO{!b`7C!}>url=`x;u5Ty9hiB*^@y5t`JS?mSq@TDa~O;qyh^C`'
    'kcxj-iJHzro{bBN+jm0nTAl#u({NBOar(6M8oOh1gKJxJGzxA8h-yIv8S^2~nchX;2g_&K>c&BusTI7OfhRg+A;X?*iQ8U`>uM%i'
    '+jO4h>thN#N02g$)n!c=j*|(~`Jm^?&C;eK$7RVyakBK+Abx15P($*9O(Tu+hB8P7ak`7K!2uz<k`d#{r0v?;TYr6x;X_@)b8LrF'
    ')2aFBPpDtrQS`<@l;EjlsbqoACiqR=C@8whmrqqs!KKx_*Nj{VD7QvT?37(Z-0DUv!5P>m91FMb@<$cb&Gd-M6z3RYr}G2Umg`I<'
    'GmnGT%ZSiKRd=lmzv){P>s=3poVlu_AxU%f7kn($J-PoC6Vw=9;QQRm@&*`MbUk(`$~bN3oWzWvLkTrroJ(|9K~YLq`71`~@JqA6'
    '1NqR)HMurdt(Dps`xQ+-Ob1xfBA#PWWR#dSW(rs`Eb*pIv0@eph^OlR=AXd4jBgrF%x1aP%PB5hOgSAGQwv!ICQ(vkKS7FQHz6K&'
    '#k6)wkx?3Z-A~IRmnn5GViS-ilX~~prxfXq!<8ijGy&jF{+~NiqS0AuldE5S7|w{WPJdk%W;T*7=l-{i2{?dIv9_XFb%u_P#~~z}'
    '2qn>=Mkd52M$a$FP3)2*q^2kY*L?RvxeY&r&&Xw7^7}f$Vv=?KoIo53V)VpHWC93j>UuyyUQVzd8Qq7B#uXexLO@*1{f9o7&6xWG'
    'SZ&2^ECp)GjQI*-FRS%7M+>f8m<u5p5e;p5D>-7$gpL8K@eURj_5|FW2mk5+mOUir2(1hFWbW+$!c)5`*__LN^pv;lk>|;m{-RO4'
    'g(d+2ZO?M6Nyq-Jp-dQQ24CbKEb?}udPf?pR(<mp&qGtwglZceB-QOX+Of_iS{EXL#TP>P1xn47F6}Njzr!ndz?9xuEgi4{$FmDR'
    'G{V%59izC1kF>U6&}HPdjIBE{sH6n|R--HGzA&KUhU~A^hXpg?1t`78%q&qo{D3K^sk?cG+qMNL8hqS>?5-P(>FRTtG~zk}G3OLP'
    '{YbcTb|grc0S1e`w}m~tP4*1*KvvD)s%GlFpk_Kl%MWz=sAG(ZOJ_MPLOLgN7+Ax=J2Rq+2f$=b{z+<kkV)53@ZA&NndGW2qKmdJ'
    'S$Cm;VY~NHbY4FQz<8%2DM4g9ZzwG@=SJ)2s_#V?vv&-=PHSm(8Hu*KsQqcFEw5qSM-8lM0%(v6vRbac>*m|SMV7^8XJ>YN2bU%('
    'Z^WQUAUsGE6TfIW&Eo~oLP%S8Z*m`ts?)|PF6?jD^ohyCe-XdpsmSWB<bqW6Hj+I$g30Db&<H5P)ZJ|c%*3&NL1v7%MvxpTS~h#F'
    'lKVIaDI{iAM;+}L?Aj1$hBv{K(xZwUY}=Y@>58PayM|-}4&8fsJT;siTBv;RH!otwz5{Vs%CA62e;a=fE~1dt3m_V#$J$*&m@%L3'
    '_}C=81bCehH8hu3QDj$S=>)jQC{er?f=SxU=}ML(x=yPz*4_~^j1Oic@PXhGuJr?UW)2fe+~?+z0K^-VzYZbE%^?daC-d{_$?8N_'
    'vqGknH61UXEYjeR-|i%f^IL2Tm%B=e0fS?#y0{r$FxApN>KN*uiBZnLE%XIRin)@eDaR=(8HPI31y;y^W;7J$F&)>OOrz_0wx<gF'
    '8XUzJgmH@6x@=&T;>tsV#>3TRg!J*E;O+%1JNpv+HdMh`6mY%oo;U4FKQ0yRJGZaY63{H!34Yr(-@9niS)IdZAUTR_NG7W?h)I3&'
    'J5bdU*b_(gO%WJ1KPqYnmz9;gj_Agjjgm@?Sh$oo{v1~XW+54SDY?V63j2`2M4&a!C+s8cJ`d#MrE*L7c5(YXXVzbe1b^k6>jyNC'
    'HqktEK->Vc0_VZ|f$MR7)Kue`Z8)prgur<Y%xcIAEh)9OX9H<fE;KBe*`#qaZ`{h+(u2PuLCYs~=}5o-#A+)t#_~KXnue(5h3ElW'
    'k$vE1E27hJ;HTzmZq46=PeB2C9X63IRuOs{16|Z<_2CA)dDTye^k%qq%>9<Z_^<Fr-Qc+!lWv74gY*Qw4U|wZ)ZYT0$LBJyc#GW<'
    '`HccbaENJINeYG%+_m91-1+D;BjOUkXcq{0AVi8q`6u6#Yo0Y=se$+uuZW{;<K+lDi`X<4w4l!Qz$WfWZRzI61oEnjxkhW2k2}#{'
    '+N`m?4SruiB-Ab{1wwk^;Byk^rCjxX8%PJN_<hW}i;i*x4As;#g;%%Jh9D@_Y-xr3DAF)7XK6VVRLxz=U#HkRQB6X1-$mm_|BsnU'
    'PX7bE{+eBk`p#;2*3E-MH0vIiTHQ~nVj)aUlb6b5x_2g4;ZFR%0Mzp#6iJGsWO{Uu>6*jOL+W+~mP`ThS?k6#>|8QH!mix4u*H66'
    'B4f#_Ja6qdl}>i-PPB$ip$&cvq{(S~P1zEJZ+Mp$PDkp5O>*+>!Ox$-y<hFCpb%wr`2%82`x?KALSpk_6Uh}TG!t6IaoZb_Sx}7#'
    '+zuoOUhB_*OiqW0eQMg~`HcUUWTR5ekpXR1`cn}(W5E+Ltpp=4WJlafIxjM$Xiz9ywz!f=cYyX^6)Q74<udAXHARiF;@@m!k;i0$'
    'gj#iL)DnjX%Nzb+?q0J|`w`Y}YL9^tb5=)fHEa%7J(qiIVOi=Mv{o(Ivg{qOZ%W1a=Uy`4ZJXi>KkNZpL3HblCz?02Zb;5p?34L7'
    'pXINHOwA5JTEJ=F;97PUt2eX;!S8>8bple;)$OQ;^>+yo61nC??!3y&j7R$?<sC#LGm&?aRqNS(pKP3xr{$S{v-0a{N7O#lBn^%e'
    's>d!F&ciK!ny+5=Tin;~eVf-7P|-S&l2+3^mTzrxzk^jHa_(@=G@BfnJdUZF_%enchK#?qLdaWVxa6#CG88=<Siqq+a-f%tGK*|t'
    '-<AYx2q+GbvmMSD9vp?*tEid|`@@%oxEswySVdLQ^I|d~jXP8T6k%E%glO+dq1CXxVsus{XFMDJy`CkagaXvmJ}@h#XkpEIID;@!'
    'ccFZ1{N>9ly($psgO<h8Ih?HmvzT~0E*#bGQaOXuA&k#eCk^&!kGfn;9=sD}Ac4CoFh}NU?7=Snq5~`PNwpNVftVSyR9A1_vY$br'
    '+iDzw2tn`3`iCMFKb#@?C&deTi}S6hud+dLlP1%-bV*Na5;#8BT}kO&`=`AzFvLBj46VHGB&@GA>TZ<-Cc{y4_hYPE)KW#s9~VoF'
    '4TA~6Rp@niVCP{GU5%)}!(2(lP_tBt@}buLwKetaVy1Zzx9raT5bg-rSpbE4z`lb`R?nT*bvvJS9J$P<z@D`y(=d*`*x<||T~Ct&'
    '`AmPpcPpPFA|V;ZcsK16NUEg%Cj2zQrsQVHteQ-<5y-*v>mSD)egN?L>XaiUY<nrJwJcW2q;kbQpxpjRPXxIB**u-U?C=7w?(@iA'
    't{IOE|5}iMNh7xi!b39m7T$8P*Nf`26fc38P{9*}$CB*@1}vtbtuf{PrIK-&`;6Mo@(<tE)V*f@lI<)%ti%_yO!<o}Co;Ku3GcRa'
    'A;VPcvd(B)_6s*xbR|d%0P@l=P#Aj*<0)|*_G1uDnGH*QSKPSX9EGYTpy7KO7(M6Vj(-<S-F7x=olvrq638e7n?FVvGA|u>QFAQ~'
    'X)&eEg-Wz<&P_}<O{i5@hm=vDms`R;HEc%1IWNi)&zr!zZfA>L_6Sk0MUYGZ0x~9%lJC4(vCW9-0JH9-mfRK3M(dt8i|3q=ZbS?7'
    'r_$KdD??39LW?*dTQ>gTn$ZSJ03cD=PolV$Ha<`!Ygq+e9r)TdThniC*Zvz!aN61v=Q5v&0OraO7^T-TGP}a1AStn$SY&fcfSC{&'
    'pQ<!ngg@BF1hTgssftTToX+H3f?l;~q<e*!Xf=5@)arHdYI*MusKq>NkT8QlCgVc5sbivxEh&hExNI@EsYOCCRGf%a>8|x}0#liR'
    'LTQ|#X!PD7i8^d9XE2%S;nsZ9ujqO!w5(`PFSs<h>E{i@yk$bu?pG1w&FvNNnt|}Zq{QF0V{5U6L>#E-zbiRV$w9^jK1k$;HIG8C'
    '%BU%ofy@*@YA%K(4DPS`MAyEe43Qw;Z!wa1n+wAVuhM{EL~Ky;{>ZX2p{S4`TK7x!3rpkT7ne``z0?>jOB68VuCj6W`v`As(Je?|'
    'Ja@F3Om*&RFN{RjKW98?yl<(|XSa~$+DH(=1rTO>+Rb#%o=wW8gUQ&GT(f#cdO0oF-`7%Fzd$P}|Hyq+NvF4y{JH2$F*(p<rzKKf'
    'Z_Rsc)%&I6KqO*Kt}T8SV-At~n&jeObFVW*XzI7|2w-Skzwp1Yt!Ya<1r{FIEU0>21lGP+zx*N<S%^#}Jh>kezY0bnsKu|mO9M;1'
    'W^Kmn4L-2@r0TDw<hFz`JwXlsbb00hhJZSq&u3oZx9w$3T|A%<J$9zAl$L^7$TtQ$uUn8FkiI#me?ZHv`1RPRERuK76(tNF7@AQZ'
    '3R@t94_^H_CTi%dqc9GwFDr)IG)tzn=3Mrq(G%h!{1dbGxO-oQt5rcW=@hYp>^OmGsrZrxF?RFpuK;|lWm{;%xT7_Rc&b&&%!I2S'
    'zJLoNxf&`}N|9B)jPk7kaI?qLd#XXUB``R&G)R#QNr(TVMlsg({B0M74Lb+$+<TZMN+y{kMy%>OslA}gLCz^3&4Uk64hJyo6^y}G'
    '26edpM4Q3hR9d8So~zY-T%kD8L@hDm2_Bv^x0gI3LE;@!{nlLIMy=*FjBI{Tbq}qaT85YU<Hxz^8a1Qv2a~&d2y|c1<C}tHf)Gaf'
    'Y7CzYk@B$XCQ9eyh-JT1L3w}@jlf<C&fg7ADZBy4Uu(G{dsLCubGufZlnN5_M~y=Rv#CH2Zf;Rg$nT&jZI#vCa#&GK$%yzga$ZR|'
    'NQe{rM1Ec}JK>rw6u`UkG>ExX)IFvP`JN1ZT%IHhKt)wdEL3bG7VM<3Na{0pg(DOW@e4(`$*d^uvKKM`%ZAcjLr6o+BNw&Sd)x<w'
    'A+hEjB|iurU;r20kY8XpWLcfywK=3oBxCSYhTpNVz7WLXiNVG0Vhq1p#dA$5+cZz4N+S_$u{6lzln;I9)wV;O^~2M#Twi*wiTj_9'
    'n;7Lc6B$2&l8XS>X|CAUd9Z@GK8f}4-dGP8$L~#`f+pyu+OJEDiA5NkYB)}IQ~)Cca?GE*@R-4O#~}bd@sv9Q$$O!QQ(T#hOc5+D'
    'l+?J?5hq@?u@e6bSfZ5@Tz|NV&Zd9gyk;5``};>H5y8sCiL3aXOkzId^RyH$@_Q{6m)7MOy0ec=HgY=vUf=X8tYONTM1AbZKRsMV'
    'j<-zYue>1*ZeF2P<bFO58_Enn&58$Hdg9NgI~K4AiI*0xp)(w4Um$KfU$rV)Bb^)ixuFPOmiQeS{hx6M=HL9=@)=uBJt+@f4&9-*'
    'C`_HyB%As^7mEfEDH%EhvlyBNrjNbnqyKYtyj82XwZ-EeISjghmPvO+uwbdJY2e#x?S&3|kqb+JQn$Jlq8_bmF7~#=DNig7KC$wa'
    'c;MFKAQ!?DJmx@vzya~K+_rsl7K{8{Mw%ZIpg3W<3}$awJ4qZ6n+6^nm40Rqmkk~zj!|_ChBt%C*&TWnI=UFoCPPw5CE|eQ7s$U0'
    'y6`fS6VJq1hprC~SzFi7|K21xWegWdURFWdW0;e0h;t0ZbWVa}UgF(gp}70%mrb&B$D8M$c(jND8zWf8ddexh?5d#3<BlWwS|M7N'
    'l|-R`1Oe6Qqcd@V$r!Wn5ptqW<szy<xrtHWw?wT&Yzb&cz<j^U3Zba;HH(+uIQowSC{Fp=gv?gL*9x!FHVHc-C2nhuElHceb9HA`'
    'u=%fcEfuoZJRE2oI!>A}ce$qNK@--%Q-Qtdh$5=49ASI;jRCO*A9yjHu<nB7ht7s8wQ)a;>!xGV>&$zt0;MbCY&OUxnljzLwmJ&x'
    '5f&$)_Qq`EL>Y(LPT3(<$6NOe!B43#N=$zb#wf_X`f6mCuuD&ln^-PZ7_mTFVkRb6_E0-b%qWj~-uC-|h5bR-TD%lezJDjFES(&W'
    '4R1aVe)s29UZ1%Tr%%##i9BA0Y=J!|d!{fsuad!T&QK!OEM0yZLAe-buNmS+l$w>u`i2oX0Ne>qTYlENw3rNUI|%xmV}harPhCPb'
    '?-OE3N6ypK@+Lde=?ky2&Dj5mtpj$_8^$rbf?<|#cSM`Xqi-UPsDu44KdFL+ORM?1u#fWUFsQ`2Snci2<Ku?MYIR~LGfrA>HkZ!1'
    '+cDna+8m&|<NZsbrUMRS<S#yfg>0Gb<K)}#oe=dszOpx4cWy16izQR1p||OKdQgr>P-)$c4|0*l<Ve46BjoDGPnu+;y@@qvj99lR'
    'WPWa#{kXxt`NaBg5Cw(^@BLRW!~p}w>XCEyiy|P-v6OG+W;(9(gxpTy>Xx|J4N{<Ztow2O?r}Et(r5(BPPS-^Eh=v_03Kv@y4@-I'
    'EpEpQJEsB(b?ODh5fP9#iHSz^7f_##2ucDPV`Xes@#r7i=(l>S{-erHkhM7&<4TH~tkMd&gR?xkoc^~rwurjjvlqTp85@0VTo0;C'
    'S*OKHqsV!;u{Wn*LfYsdPI!iQEFCrN`&0ud=Zp{P{+`8Y)!Ih#i8)GZBXAqjV3pH^Q)9K86i9RSAsXuyZ{il5r3Y9n^^HWGhVO0F'
    'yw$M%pWk<;MH_o4LOx5sJdMWa=m}|D)lwI|f(kaU6B(=kx(L}N65MYQNA---eNZVl1w~y<cW%TN!m!U2*vu2xE-S310ST7qgASUe'
    'mrnT_O9N$I%T<`cN+ZlQRfhL>$+8=2sG$!9+xUdK_qh7c6_pThh`(Yz$V_NgAA^)VB$Xa5YIp;lG*W&zfz79=zzd*5lWdP<R*m9k'
    'XjD*VXS-6RLs2m~F5Gm`SieNPlW7gZMxH`XZay|S`}i8G8dSSc;ee(?$Bga$lr5bVM<crFw^-5^(|RZ<6Exr8Upl>nZ?<PUz)exg'
    'P%sH7_M^P5x0yez3=SCv2YyR?sL-r;%xB2kTMYab_jKP|dZ=D5l`P~J$|h33*>KwNCk*nZpw>zK#Z>?ptnhRU6GWfvASD#g9PyDv'
    '+rcH9*CEg~=<u>6cAuUmF3p$Vpb}6?xQ!dlhG&`|t2?HPeDS*PffVVqy($1=XN-=xtjZ>f>bQ>t4^!?nJzcVO0lw~a3t~<bz^G91'
    'TF%XT0qs3NywIxa;)iJnmMX9n9EHpGuXO4?+G;5Sn5ybC!|vu{<vj_20r(8BLmxGjH*Rwo#t#BlgJe!{T^Z>oL;Oayd{b|0XE|-W'
    '1;lOWMv-hn7_{m9%rv}<>dg_x+QAo6!44+4jR7)X45YwqXpCqAx>=#M9sz(Jqe%S)ffBi8n+5y`_VX%R$Iv}aH*iZ!vS24#qgQVF'
    '<X^6+F-Nj~qRW$cZ_+j{1C=7tm`^`fP56VNPZuTVDT~al+r%M7^GDeWU~O!s=Xl=V5MK8qSU|^MDfzMSK~cFYU>UA3vpaYP5r!6-'
    'UKkdYri<<2KaWtP4!orl%ZXXcNbNppr>MPsX)Y_KBZB(;vA{8|Air&rZD||I4N7S#j}2vSklaAIU#fcpCdzg+RJ7({tcqba$l{-}'
    '>o7qBYXC}2!hB~Sh_53Y_ST(WJ8GR*<~k?}U$^<dI@P+8>@2P2yhWKvC9L=ag*KWt=^dkteMAwFVpJy-?k0={D6+z+JDZr$BbepR'
    'DXs6Df}o{0mxnFXupctdE<4<OFQ|_S@a~r@Gp{FbsXoVpm8EcbjlJbG3m$#fWG1;WBjofVRq+`glWV>#=l&45H{zqxGa2^h?|ziF'
    'bY1@_cK-g6{)9MmFPJEC&N(c?H)*Y^G6U(8MvI{pA=(h}e#{??c!Lot?Y8~amk^KlEVD>1lOw|TMe6J=6|eWAWJQ4*5ye}Hc$<VU'
    'A40kRh@v##-QhyikGH{1SE3CVtZgC3XHq|Eb*U;oB0(>IzSR7If`Qf*l9e<s&1GF3npKXPbbf(={wdhMfZ^ci{`fxDnT`@cgW^)#'
    'cqp@8HALKNc($<G1<k^nB>aaT6{8^jC4^lsS(+ujL8@uI=;-Qfse^GOvJr(K0At3gXbQ!iL96ZR>1)usf;+QwhucnLwd8!#Y!fhm'
    '$qErR@r=Oq`RjU}P<di)pmKNu1WKE^;v^FPOFcTPYv%d5k+C28$$y@D84vPnjIL-@g?y*D-w&Nv{Gcl*6hr|5=vQNz6N4v~X%gmh'
    'skgDX47&rmLx^JLR=|giBS@&X7#^DSUV`Qk&gA~AFJMAISK893C790}t+cvRW$8cNp+%g=1PkJHxOIOQK`}<v--C}<=@0Wl;Yt)N'
    '!fEp}UfVg0hDs`(-as)kh@r0o<nXXHNujsKQ$v6E?-5-93ZEJf4Nsc6G(-D|$?e3`tlMnFYZpWB$0=i3yE*dWLZc|-|Ev;ZSZ^mz'
    'bsrycv4e$2frcDWItKbEL`s02{C*|m?dKs}77uxs!?1umsn5*pk0Z}61SGlCTUP%wKhq`5WkPp;&Ez0zD_md}s<Vom-QnMGCGw7s'
    'phYNhok(UWf7tAP6Xa^bw~NWTo6A+KBvUnYc*Aa^LTMLodAK<Qva65@vH#jy>#yAYxi;ddC*%l7NRAAf(TFPN8G*~9vDY6o1LVJi'
    '<bp(giu8w3N9Nv4i5vxI5=@*~b`pfh%Ey6B>Ywpy(##8UV-fb9b7{Ymp8(gkGBzp1&uG1K>2hBzx5*`izudETI5_^PM1~V|9+RtE'
    '2nA=F(BY(_WHZ%Z%Vx=Q!kM}iIk&wDGCq>tQ$24%-*><t6#Eku-7p)9Wz0ZAI$)h<rmK*SPnBHJ6^lwCSr1Dk=W;--VupV>8wNNe'
    '8=@7j<%(1bX0{Ez?=Ov0TYnCpv5pOhh+ar}tokE^x`v3c-9c@b{B;r0MG<$#UjD+wiBYBcrz_P5Rv8(G6y1Yp#F!!gaJ{lp@?&D1'
    'ZePlBvZKqaSJ8-&tFg9R-l{#Wfex9Dmzqk?p_vTa!?3lhC;lp^x;5iL_01!!$UoOXj-(YBzM9&;OoI6p)TQDDT!%NBBG(z(J@-3P'
    '3i2H7s|F|Y(WScb(@KrWp1Bv{r!D@lET#P(NDOKau!pS=12FE!B{Vkb>?v3Cr&bYH^T&bS%>Wz6cu12R2kP@x7;_3II`~Z+=VPh6'
    'PvB81GBAOkZ)XnTiuu}jmij%6u2`QV>hAXC-5vC%#cq{n=q|q{{(L$?C3e4JUZ*J2Bnm$WZ#F)ob;^0OE1toRv<OVL;HC#d&>Y%s'
    'QX#ev%wT%&V+7%?j*$-DUBRXJZk?>(0WU?x4)dU#n1Q#?RoiDekq`4ssU~2J+B}_f;s(IgnLy(i%nL(yWh^P<!k+&QmeHCsh?J#y'
    '^tLd`tjY8J7QqB0g8><iV=V7dI|Bc<dVLw&*z70>gC*Ey&W}ru&f77gjm`U+*am~7pFAlBxftkw{&`KDMLc)YgMXDjJ9k5SoLOs@'
    'mJQY!HEK<w!`q_2*TXh^-)5Zq?=FS#+Z<TUjZvT5WH%fLO!^fs<{R2<!djt3joSk87Ar1;68i+E*EmASny19xgfX5S0!Z(7_+LlE'
    'pL^xELCz9;U~C=UvyoZ1kf9!&F6A93{MX~X8Rz}six1-_kt(fNIQkRxg?#I3ts5yJrvImSAe6xO7GhJjTqw-hS=m<tkH2K$cGI0`'
    'n(%0hEHDL}m`Ec67MnvoBO=Bqi(EpSHNY6mXMF9a!YONMNw{BcF}?=K?PENuyh3CIdrsl%dDv8^%!`F0>@kghkc|aFiEsSguj&<L'
    'E{^-Mj?w-rLNwPvTTnPiePpaH$SrvLLc}Ml>g`#+FMx4Ft7b&Qk+EDfh3B|LTSNab?Q|TvW`4UU5%+x(hw~rLRAsa378hz{{uNw@'
    ')w@*>;ax`dHEau@F!$)J;EP9TYx%8ADCKS`MB(iw4=85u>vz%t4e~9Y0cw>dNXX-obBnfB^DKEM8!1;N*({3o(c~6{77}L$1bO_y'
    'fAcgoXDlW{O~@t1h!jS{Z)g|%?Gl@6Ox(|_a4S;c{02;;cP4YgYs|IQed4l_G#xYGv#-i1j1lX>l^epmpK`~oBV`Cnc^c1fh_l>L'
    'r+#5QSWSK}ua;;E7gKg;@ZV;yk0;UUUl6{@VX3t%{ca3%Q*f$$0v~1EV!YDY<R=j<9FT?bWKA*tY;@acaQTK14p`jEjwll=8dB>2'
    '$?qAhM1F?39aUsBgbb;{><2}OD%i;_uOIep+c|W{OQMH$)h(8J^(5`b3KN+(vFy?`r7LPQedhZ?|6>3-TIhm$RvZSI%7M#Gua#1S'
    '4#An&HsOoebyaC>i}LpTUSYAp2M#*a$5L1tZLRUjo@rRFpC$g_>#0EYTK|qQwXg!tAgcdzJ;s32WGQoI^s#&Mu1zkPGu{KQ04P%V'
    'nq#{|K8uRwNa_tY{mi{2<kVW}0+n~vSxXX?wJ2WSgcKr}_c}++dT;|T=6$=irMTZ7N6k*f;Z{k>8hB!x|Bf(|p>av>(<`=L5E3IQ'
    '66S8^(wP7s`|UiSX&;Lz=0M*GGLQzkg4UBdMIOKUSVp~0clhGN*l8Vll+ifW(IU~lzR><VyRi{hv}~3yb1mNnXdUNu0pPqMj;(*`'
    'TG?ZJ26`(ytNRBQ<fc;L6RGfGHMlMyBAFvKcTzU8%hedL^Kr~wyt<}%!b9eE-{xQ1rYsz9VRfhyHav6G(m=p-hcUw$;{mxY2tYu#'
    'IS1a|Kj)w)b3H(0<m$uXlt&ELZ|vdt=1>Z$xc)G?xYz*EOY+-rU!G{FqYb_Dq~=Fub-o3ag`|jh+&kuU>gLU-nFTybAqcs5y{^Ab'
    'J%yRsq5`Unn~cz+`Rpp|;O2(hOLQ3ACj<Wki%MYbz#b^tI0yVir-DWOY2QGUYKFB#U{(eJ!MCA<M6DKy#i{<KNW?0pz)&kCP)NJj'
    '$81n*8!?*7gJ&4HrgW)GPoghk>N6K2wOUvr_+Hlef+Yy)K{Z-vxei3Y$t-$Fq5v5Iw1H`!1=qZ29ci^Gn!eV{K?!m-yPc$iB{xoN'
    'kZY#Udv9Fpw%4XRAJl#xeQnE04*BX!@UNXCIJhd^;(?^~3UeU|rs>$O$vzGTTO=exCeJGN?F^?C1ltBJC5g+;70WeTvvN2Z@FLpW'
    '69w<E{zXQZk(2=xCc!&fuWWC>NmYr7sr-~^Oit!vWF-rj@8LFLK9B^{UxjBRsAFi+Y08y-5={24MU!kzem6T?qvl*xy=`VvL@_=?'
    '$rsQQb~32y-;f5;qmqv}64vIs2nFgDUeuF+h}V%L)1o+vAc>dBN5eQXMyVb7&1l)a0B8rDq5e6Dx)hN#hW0XVQ9I-7Lf)eSncESg'
    'WP5YS28TXtO%$LF_b)!~g*3M`<rHe}&LKf(rCr(c`M^$6=9Fn|S^3^0bQN^jK8TMUZ>(pKSj7#)RZ?OxF8uQx8UE-#=wt35C}ppl'
    'cnj!Pc5=@+!50%=_AHMnZF!fD46YY2E!j_u8Wy=-G&(Y9N`%SsY$qK%;b_N%&U8GNJY6c+L%@@y^&R|yPXuVy(3Rjf2xh3=(|=~2'
    'iv@%yxuY5{n>98iie7=0@U1T^w(CEz_oC0lKMN7OQaX)t(k|e1!9<#OsZ&VF48dx90B0^Tex^$cpOl_|P{iCybMQR4^eCeM!TKx8'
    'K<_yHv6GiYnf};1Z6S_I<QmL!gLY@IwU1Nexp&06dyWzc-R*yLr}#)CM2f<b-7&)UHVYTov#3gYFySyS`aba=u`In&mmL&zDhJ<)'
    'Xyd5Lfe<oDuUw4GQB;G;JTawwZ13XKUWC+PMMInnos^uZ18hL2$1Enae+WX3TLr{~Dgl;n&P5t1Xvgei=pl=#Y@dAUb_9Jwi9GIe'
    ';MkE1Q&ttewenmR%bW7t4_uP1Qh@tdk|?_(SQXQgQ&zC1x%4bejNO`|6pNJQ2cVNcFQ0@Dox&)~YwXs2rHQLE+Q#xBtEocaXj07*'
    'q+(wjz%Pi4Ni3&}=q~P!oopkTejTR^ZwLh)GU)J~!xVlYs?M*Vjs{;zxh6#&c4C!;`bO9@xw%|#--LNqwy;HxMpnIru$4H4kX+gg'
    'jEGQ#|BT4;bT^_K6^BDHk@p-`yBs=W(dT_qI2x9$!t5ASVo=ksUZl#iM6g#Mk`|^tiUgzN2+B%s=gUqx$*aVhb_Vj6A6VHkybZ4n'
    '#6#QJx?hoVoYi={$m~HwYc|mD4Hy;)_GF(^PZR3B9$>pNAbeFor$g|e9~q+)Qd?gRdV#VbnSFQxdla#yK9Gb>#yb9p7H2kw<&^_?'
    'PZlk>)}EFnJ1JZo+VerzgnDN5txm|zKWyXI<?73wJZPVmo8dxYbF-DsD}&x_<TxWtNzn+q%4-K|I{^+bW}0j*)Wxngd|Z!MBc_#3'
    '7}+F*u)Xe;Q|fic&y89kRG>s>8iN+M#n-L*T#!xzqeX$aE}KZED#`se@o5}HpxjUo&Wm3*5JxAr&&~|oy_NKM!f088eaM#Jx_~eV'
    ')=2X89<KDQEg6hQr1KhM&=U9X3~11%UY?2f;6f)9iQXqzL-aO3cok)OgO(u1t^U4swhP~`Veo2|K=l917mS7ez<*;;_K+tawT`uN'
    '%by}W=2z#m&C?VOr6cBi83)d+ihhZwv&e!~|4rB*TBmy0AoWrm0Z4DQz(b0)EzevHdmqnq2L;XnM2wla8Il~ouw1V?C`=*Ms(N1G'
    'FNE@EiR^=SOyQKH(@xiUGBZbz-fip~nSGQDU-~mCvB+7JZhm>XR1?!w(WbOT0ki$fZ`zD*F>Ma}LGhPh@GCh=-yhx*K<x4?WUoza'
    'sbg$_icI*akqfu-&n`$vvDpI0cY}Itt~)9r{xTL#1Sv@<?QU?4i9;<+LHQe!61_0Y?H-LF`(d(dXKIZexUd2xJlGQ~cnI-jZh4fE'
    'Wz+ve)bWN>GeAG01lmu;!_V|UY~9FZ<-wGXnKr{ZoGq{|*Lb)4N^>n3&8K8U?IkR-8Eg^;xu}bfKJ~kKJT_EKscT{B|6<J?gpo8I'
    'Nn?T#p{^l}(a5w86UMZn;10up$UXxZS^l6hnA(^f6OdfS(nZ07nzSxwR6wAm!^S>;^{Fpa0T82Lje1Q;=jsk9$DH7JlAt%YNh7+#'
    'YQY#@g$U=K5*aYl@>P5!DmRT)d~!0v-4#;JP+H=Mq*4kYhmELAdL<~KOMG-hIhZ=8Zj7p)0uX&b>uCuUR3_OyW{EF?P&YKezuyIW'
    '6U+uY)47Ns&zzuaQ$Y?a^^}`6XF@?tt6#VIM1k^TWsZxG=oaQ*<~;s}CCGc2$(zDij~XP1ZFZ^_-(M9jHyFv#{SJmhc1$yW1+>v}'
    'cz;EWK0$diV<fn3^OqN~j<8OXCC#z_`iIg&AuwvwDzltZL+)rUfVQEgegy5e{D>OcQtw7EFMlOSrJKG;vlD#8Ha1VRf&<S#BJ+#7'
    '@7SPxwHQ8x)WMA{nUiWg%d@zGm2Crz(wc8}I}LrpPz6Ub;Ly<snhyKN74_aSq{PYvZMDa<(8-}jyzIRkuPLkT$D9=T>{x;ad!eDm'
    'wts1jQ<%d^<TEZCYOAT(c9H%C&ln{7g+W5t3!>D(@0QYs@t76A>$K;)o9yd97vF@(E9%;nBrM1{y)<NLo4|FY1+>u&S)co<@)^E8'
    '5Y|Oub@})JLK0;jeDFRP=L6Rs1k^a4OVDfrCYAwilk^rHwmHOgM!uiIpqkjruwEjh9EM6s5e{EvMTrQ!d~^9F7AAH2+m{K`z>Y}T'
    ';l5~f-3o+MbI<Trey}6X@q4mzs$uVzLUJ7IYdSd!Swb{~5~d&Q&~|WUXAI3RzZaJ5a0X40oS0|4MmKr8(rMGQwqB^){!Nz~LP`tB'
    'ZS7DK9mx%yD$%xCEE3O-2oXL;G8+icJ9A&$66V9CJhdA5%my5SCuBlj@5yHRY^e^ig4KY9eSbkl;VC^3bm~;9i-E@{fc!DZqednL'
    '^Jj6MMa~rj55Fy8bGg3M$1+3~t=lrR*F`g!8RQ+&2s#aVzD;0Wq;Gf~Cnl^-b(p@atV)p<{vvedcI#7Ac!BN=#}9A@TT;#2@k81J'
    '@#`pBs!u7M4<^Ej>NJn4Y&f;by6zCO^4D@>zeRDRltBOZ90Ft1*mXv6eo1s2M^u}$v6hWXh-PC^8Xh=Fqv%LJB_vyWQx4ek`XGMk'
    'Smx-eZTkg9kPn@Rj=e0T@;%$GY?3ZOC1L)2NXn_Zl9;*mf?0QoJzcFUhheax;E0HPE5E|d$(!zg)hYbrK?%Pk`<bQ--{P6+Z8jAf'
    'l0)b~rn9~2F*LC4PlJQNT$TsNHTec0@64mWxV@j?6p38#*Gm8bMSy~!agh9h@v<Zxbd!OE2t<LpVIo%J!E~c#TigalO&ffT<+M)f'
    '++gj$VTVIh2aA_JY@Wi;b6!a52t{bL6r1@8<lE=J*d{mUt*a3Z&z5_v)02R#%rv&SE=1$b`I<}9*-|xClnXkA9PIQKzO`a!K=*yY'
    'gNT8=Td1WY%Wc=C6qL8n(l{Av<oRTZg)oW?%-Hd!ONUj1gOB#WW6gg82S?j+?}US!v}p1mS~(iQ-_Nki^FfwkB-P77w$f-~dpzUF'
    'qdL5OC?29ze~7A^9}foi-<VU$b6!DQiY)qwMbkes!7GoRcrggS!7c1ZgAb7}gFCE67(oqW7h!u!mrtl##_%4sGf+wXhCw#kCLzSM'
    'H3K%i8nFCWXhY%?)gA}I-}aTp`><`cX3fLz8FL?)(HlV@thIrmwc<o(I26pI-0k4^KG00p0Wbq^o@E7wYAhyd)l0=1nOvq!0>tS*'
    'aZI8WfUbv=tQzn@w2-zcK)|K5FdS1GA&>pn4i|ysF7-)vV-V6Qu-}~Vd0=Yv4!yTx$yxAoGp9E;ojZcRO^mzi!<lHiUZ^f`6OUWw'
    'q_I5~r!_9Xy)nW0QJn+V29nLU;f-`UM#JRZd2DOqZy^h<Y1C)y`?Y0$q2Bq!2(OBq@oZ%O=qgJTG6cS|IEH#j+!qKy31~ia<NHTc'
    '8G0`*K1~`jy9x#p(u}OUp4de2;5=$^`?u~PzW6u_Vlly9PcA{svGfwOMO=a<G)Fc|4YG)6hl2XehBt|};u|GQu7mCEk&uu`bT42l'
    'EUAW)|6S$Uo=YjI>cx6}meAzW?J@`^V0jBnB7im15eoqR`;88`pGO^)<nNIu+FB1sBcLn`NjZcDyvUljf~s8zsaRZegy6qep~d(6'
    'YR<!+$gKKrtaxXfW&e?y%rI%Mez@ObdpQig0J(brZYpQ?HpG>2-lTsc+$gjU8S8>GIuEg-Nn{oAHuNHY@!vBf`kM<3*ER<u`KFX5'
    'Ee^fwyWO*2yn%?G`<3Ll$rn?D{1#EECe9km1d+6q$39wU_*P~*o0G2Fd1c^T{B54pdUX#T0%n6}g0uq?;{-6H7S(+O$xSXaP*(B)'
    '8>M%-^||>p%GDRJD+LT-L6@anXqg16?7559UH|IXk!JfE*eWR#W3N1h=;+7X*QRcA0a#iVkPp0=&PDF$!Q$#10|oRdQyI38s)PwU'
    '48p0f5ufgx-r6bL_a_xUD{Peor-CZ`-iT|g4m2lW-9-DZwXl5%rZ`XPBjNzoGnjLNhWYB&r}eh#Q6d8Xj@WaEeDY(+h4pJlnO*iF'
    'qdPQFNf$WZuKwetSQ3+jlYOHOt^d^aF+Wh$4J1*Xo3@JPe>f{X*e7iK-DHh^zM(QU)ijA!Dg+!XVJesS0>i^k4@T16r(5k>Wj#vh'
    'i?7;9Z&}vzsAvc_#w1Q>3Vj_k4+F^hFKO8C-Gxw&@q0Ncb%K=?aKdv~bXGZH?|R6^IZHP2dIo*rcT9FT4~A0boVqKNC$Llcjjo4O'
    '+W`%K+j^f_6gvB3_$kh&)|%v84w(b1(8et%p0M+o8@qTDX97%5jF;4Ap+m0sc@?Itq}0`saQP!QL81o&cyX<?yi{MMZqL$|&lcK7'
    'n75af2o@)GZwI%ijJJ0joubz==A3RttL_8R><>j{Y9X674=Le(14n?2ui)<jcC2C^M@;F|F|dIlZ|=2_el{38Bw6cp-{wAq0+EEZ'
    '8Nvx!>J|pcDdhR>^7vmv4Di6Jem_9^%F+?yznIXf5YRA*T$W*;X4WHbS~Do8Zn{eySGsm>9HIfvOdACPB@B!36I}ci(s8IX9=0#_'
    ')Ek8RgsRv#!M|Lqp+6W+<=EeD`kuD^@>XD^bJP4yFDRt!#=`^sZ`B}pV^?Sg0>*|^k593;n1!^)QZ%%>s3twTY?Np8q64*8qA?Wq'
    'q7-TZ0s4TO%d53NGoXAIhS`qXsbXvY3FSzB?B$1I#BFZj!`hNz1ch-@%dx|xtJcwCFnNx=P20!!1V-E|VFy$Sjtw;K?mejyKQ=WB'
    '^j`HDm+Y~rp`N;hSW^qdt1lI5F~+56pN4w~^o4CILAATrf}R^dg4na?|FpmhGt0gQD!_Sv-hTmYc*s+BFTYUYxBu#O1DF38borD*'
    'xLD;NgRDq<zG};|l`PU%D}1}Om-%eS$oHNm##bm<OI`zd!)Xshu?8L{-;MzUAG|<WnzYWOT>Cw%;C0)t80YHA;OA!mF<c1N%1F53'
    'R#g_+eXtZ(4IcS>DhH*e^S6-QPu@7S*7%c+gsgjur_igqa1qo_b?3B)&?qc9cnEcy*BGtD-a+XE_tvVbZh7WaJyfsJ!KEY4=lJ?-'
    'F)R?wV9uo3zh3)Gcn={X-Vn_GzckfQ;W`Wrf!8$gz6i}8?evrdy^+{#IW6+;Hxt07>jyfCDV@t|pripErY?8+bNxW>qbU#GFUD17'
    'oo!3CgV5;@0He~5caEgHj%7$yJGcCSDy$lqHE=^+h$Oqu)oLcM(!kA0Sr6idxIGhs2MKj3kU&CKyx*;B5pK#d=WW8yWYl{e@9b~S'
    'FA{vzWaZspM<aot?NMop+M9{f#cDhf0>0_Ye3jIN0%2yzw4gQeTnr0>;CGV$L209mOo;kFLd<8tS>vv(XX3p9^+~l_(D?@$r_U2s'
    'CN8pZ%RxCMP_|xw$xdhH-bt^D$6nxM%UE5R4mN0@O57217;p|q0=u615biAytKiJDcLAp;;}*fUuXeO3eTDVFe4H{$N#NaN$p(lL'
    'G;K^HfuGa|nfDcG*gHC|X&-sr*d~GNh^N%Ru7)<2pn=Kt-&=qAl1*KbXBrgr&zn)+_~mE^f)yAebk+<ovI50_WGy8PRzf|{|EyNH'
    'Uqi|4?;+2!<1{aQlw>btRk8)@#h*HsdLmOu0?ar{Jj?oNIIK}KrQ$SrF88OYKh@!A_+Bx*L8W4aw&Z;l*B0a%0oX^xCqrcL@FoP('
    'y>@6>oLjQ#B4NbfhFNNhNzlFc7Y8MRks#^+SQ>NU`2OW%o&b~<&d;K$<Xj8gc~f56LUFv$(~PO*7%bsKn`MN&lwEW>gb8WtO^Ae%'
    'aV`({3~P^m?q|?Tt>&OO{u?CHFI~e$)2Dq=9YO<cD&RPVi0;h~p1Q?>>g2<=0?_>mn_mGqfguS3Ww1RD+`kF6C9Ayz`|W0c-7!Tf'
    'a3$!RU4ev=U^r66Ujop{27CZ63sP0q+<CFDBSrtWeYa?UzwahoTjP#|PgJcUiEO8Or&LyH0#gtVMI=j$)tDufH3ik^_2})?s>_(U'
    'pSf}Ja(9@9_2yxCyBZ@bI`IOBR=Dir^fPHSO_{JX8jThkSDyxz`{38~M^$O^P>`BYS4E%K@wl!{;r^>%#P|>6cyy6}=K2Sm0PFFe'
    'm9L+|2cdipP(?f^sw+!ESQ)4XCkw%*bC=b;)o-r~!GoB`;W0`;tHJakds0TJeP4=gYp0#E8qmfBu(dc(IlNRCGl=}z)qRQLrjMCn'
    '(+(1w%m56XXnv9E=W~|<$q@WupBy^w7ZHg=Kq*$DbowA3mCF8tb?rN#>GDA((4x-C(JWeXixnT1Zn3?H_uTP2%9EJprJ5(m)W<bH'
    'pHg;$PH6{9sEkKYc0VclNU@=Z*xj&X6`I)JyX29xUr_#cP1O&u3mbCv#A!FPhta3Xryz9L74JMAZ3Fpaf*aevxZOZR8<_YcHgg#z'
    'JWX06oubjk##{7MRFKl0R9&j&uV-#+3|A^&bW9w(V5QSl8u2Idxj4X8H}G)ww{hUaiZ8|;J00S;Vs2=(v+^0@GJ#=G6cr%Zo!17O'
    'qLPknK@pxmX0e;@Fuz{Hlhl2!iPhENqY+w^){d=_1E+7M1!z=b<61}Wvdr&xk07uwDfe5OiLlhYSxKl;>??l>7gtz7w%41h^q}ze'
    'X{q@g^VKaaO^QYoR$<1#cXtOqRF54QpDisVS{$J=<DV(+o1=Pd(1N_BZsBNacL66f%x=6huj*N;?wpBF|IOKl<&_SJWRs9AP7!lm'
    ')xKD|7&R^)enhecPb8yXz5Q|`RX!k|N?8M+$m;)@TM4f4I?;F~L?01;Sedhf5GZp15Dx(Z$*3oU#wR-mHEbE&&KSG$*wx6a^$Ig?'
    'LFCFB+6l}Sc+?tU`a6&q99v9P44iF<g-*&drJI*;>(Z>ztL1aZzV6=u&Yrh@LL@)W3LA|EYl2sht&CQl?Txp@*5JJhjui&O&@sv+'
    '?nj+K0JC~Q%IXP|H{#yDjEdD_OTQy%PW`SW>1Qb(^-=#NzqEM#u)~0?+Ct1l*5V2FdPum!p1`@lAG+7#{~kX;zupd8`6SUmQJGIu'
    'TvGglaZc>E<vop;c@ae~1ep<PU_b1v0xRUTjNof3q9=A6k=gnx__b+ek)eA+3XaBNaR?s;&u<gOicmYAl&AFfn8CfxzIs306hs%)'
    '>EV>MOwqBC=PaE#4y~KGF0l6-xyZY2qyl|4H3$X$#L0?8hIKSo0XM+&H^NvAHCH|61jPert6L`bScpN-7mR<YsY!2iFEEZQ8oO%@'
    'AmgSNI3l?eY>&W2a&GDV*<QFXM#q(QocGKV{PV~=;lw1UX@aT;MKgG6GD$3?syFaIf`7TrNL{(9F%Wt`tQQo@?4*6L1r7^kYbO$f'
    'PmHCf1kE!Bls5@sL#Mn*(oF7SvXNBgL92j`f~qC(asnBbbTn{qMA}?%{+^{q@i5RCBW4==95|}!0rGTGZrSUGixOoMF(2&DqX#Pi'
    'xhlwHw#~&k=j^-25j5J`P{jYX)XSu<C$Qu=lVnB!)y0wf?^|^Fa<59kbhllQ#c0ZMX>>CPQyOH+6??L@58nb>k)i9YJy5wKI|#lS'
    'zxNZ<JqMmo2YPq#kA2|#!5zq4_}^go#?Q&3-Ir*5ILMxyBTQ8Xz8<wm0Z5m!W5ylM(Z%zGMQ^_5O<x$VWME2xZSKq|?BMc+K&w1u'
    '_VFYt$oWOdYau!%ifqN_Hkf9`9|Z~RjSjZJ1GA!D9Z)eDSy|Y58ddswujnPwil-7udW&7cJpR&2efTh8;)|esHIF&myHfr9{j<Fh'
    '8>avmxdOqTpF|p2nSkmtc|}0Nk46Uh52l+smE7chTSUvKcM4!O^?W_*y$SkGKrSiT9kjVrooHgS9o=dnZ7?YdMC}~Qo~%IrqUs9>'
    'r9BL2qF!+McN*WLKrM#o1YDjUc;+FPLhPFHpe|D`SLF{M(w4L7M5chrY=pY5AvOBxdG2qxwRqHjy5bu<o63dEyyXLyZIm?MKg4GW'
    '%<CMSN;9vJ*Py-86CH4@Y-ca;qvh?F5n3JF@yxwUv+wLUOTM%60vt~UIS^CeE6v<k?Gf9e=OM)OzT0-Vl!^kPOh$xv&n~i4a}rY{'
    'Wm<6;5VmmN^P49w+E*2VZclJIRH!=I#25&>@Hgh5xYrxBUmLfKA;6$F#5ivS<DNIk(KqW7#q_D@#w@NBELN94qfGdd;H`JbGol%Q'
    'JHS2CqIcqN%sb=a$<nQ0nARB$-39t=Rx?(MZvxL8k^tgi;hP>v0DX9`5L~m7(W6fPN!Xc@<sA3{94@nm!FV0}W~Bp)3Q2tf8goJ<'
    'VV>@-sj<3q#-9yH6Ai3xB6LY|SJ&PEj8D%f<imE*)xS)1>iT~g9t+0&tQKz3Kkc3ip({!+;n}cDRORSRP=^Wv6fg++%Sh4Im5J?@'
    '(wjA<4ww&Qvlyo^x;@~S4ac~JpGw>kCwZ$f%Tw8<#=IGB#3g-Cjn8J)eb}THlI?H-7z2KIM9k}Q7@_h~&)$r*bgYBUQLu)C?_o@s'
    '?@hLOg??iWcUG+Enkwaks4{FmS85-=(}FivKOTqt_ZUTOE}P~7*84uI-)rY4W}^=#`$eaaK8|G=pqf%gJ8Wd*u*vdo4hXn^f6Ww_'
    'l2oM&OO!(iChuI!fKH+br*Je>aO^t^O_FQwz^A5<jiR-1W?f=Yu-Knjh7%mvZghQMX5Y(#+Jgrj8d%U-CbTae#>lKXAv#SE9HRnB'
    'M^ckrWl8*Z-hO)tP4tA&jP%`81PDws$WXkaoUnj%Lw;CL{l?`=%5cz2gLXJsF{nZq4U7efkFc|doQ7NY<X+2)9l9J2C^j?Xq}Goi'
    '{gaB~<`Y(=Y%LSN#YFtd12ikPTUynJLZ~d!{k{CWOwBFLyqz{$5{nXP{>ZHYy85!{;dwayE|3p~cRb0xEtubuNsukY_b%P6|Nd#Q'
    '06IwEki9HP@B?(AzT4z&UDjs&o{12$+AfB$6bQtzhC<F-Dg2~L$W8<f4(CM6$IG^NL1H%fiFTPXRml9BHQh3e>Utt<HCnJ8P);})'
    '-62iJZDxHJkx<Jd1f_TpGP0y?r|C>BGb&PuBz3t5Fov*%$HxdZ!pu`+>%KM+B!s;`2GRB8Odd`+12JNKPT1wsnHJAB%>uD>QkHQ5'
    'm%wk;abUhChCRa|>?*Jih_y7nbAHXu`bYSwbudSWd_(prR7Of}AX)h<!RBEey_f8yb?U=z)pogKZD=J~nPeDblT+tNWawVMk^lez'
    '_lN0;xhM^(00FCl1dxCQVU;jKvBYQl0ssI200dcD'
)

class SM3:
    def __init__(self, data=b""):
        if isinstance(data, str):
            data = data.encode("utf-8")
        self._data = bytearray(data)

    def update(self, data):
        self._data.extend(data)

    def digest(self):
        # Chaquopy/FongMi 环境未必带 cryptography；保留纯 Python SM3 回退。
        if hashes is not None and hasattr(hashes, "SM3"):
            digest = hashes.Hash(hashes.SM3())
            digest.update(bytes(self._data))
            return digest.finalize()
        data = bytes(self._data)
        bit_len = len(data) * 8
        data += b"\x80"
        data += b"\x00" * ((56 - len(data) % 64) % 64)
        data += bit_len.to_bytes(8, "big")
        iv = [0x7380166F, 0x4914B2B9, 0x172442D7, 0xDA8A0600,
              0xA96F30BC, 0x163138AA, 0xE38DEE4D, 0xB0FB0E4E]
        def rol32(v, n):
            return ((v << n) | (v >> (32 - n))) & 0xFFFFFFFF
        for off in range(0, len(data), 64):
            block = data[off:off + 64]
            w = [int.from_bytes(block[i:i + 4], "big") for i in range(0, 64, 4)]
            for j in range(16, 68):
                x = w[j - 16] ^ w[j - 9] ^ rol32(w[j - 3], 15)
                w.append((x ^ rol32(x, 15) ^ rol32(x, 23) ^ rol32(w[j - 13], 7) ^ w[j - 6]) & 0xFFFFFFFF)
            w1 = [w[j] ^ w[j + 4] for j in range(64)]
            a, b, c, d, e, f, g, h = iv
            for j in range(64):
                tj = 0x79CC4519 if j < 16 else 0x7A879D8A
                ss1 = rol32((rol32(a, 12) + e + rol32(tj, j % 32)) & 0xFFFFFFFF, 7)
                ss2 = ss1 ^ rol32(a, 12)
                ff = a ^ b ^ c if j < 16 else (a & b) | (a & c) | (b & c)
                gg = e ^ f ^ g if j < 16 else (e & f) | ((~e) & g)
                tt1 = (ff + d + ss2 + w1[j]) & 0xFFFFFFFF
                tt2 = (gg + h + ss1 + w[j]) & 0xFFFFFFFF
                d, c, b, a = c, rol32(b, 9), a, tt1
                h, g, f, e = g, rol32(f, 19), e, (tt2 ^ rol32(tt2, 9) ^ rol32(tt2, 17)) & 0xFFFFFFFF
            iv = [(x ^ y) & 0xFFFFFFFF for x, y in zip(iv, (a, b, c, d, e, f, g, h))]
        return b"".join(x.to_bytes(4, "big") for x in iv)

xtime = lambda a: (((a << 1) ^ 0x1B) & 0xFF) if (a & 0x80) else (a << 1)

def rol(num, shift):
    shift %= 32
    # Perform the left rotation
    return ((num << shift) | (num >> (32 - shift))) & 0xFFFFFFFF

def rl8(x: int, k: int) -> int:
    n = 8
    s = k & (n - 1)
    return ((x << s) | (x >> (n - s))) & 0xff

def ror32(value, count):
    count %= 32
    low = value << (32 - count)
    value >>= count
    value |= low
    value &= 0xFFFFFFFF
    return value

def ror(value, count):
    count %= 64
    low = value << (64 - count)
    value >>= count
    value |= low
    value &= 0xFFFFFFFFFFFFFFFF
    return value

def get_key_hash(key, rand):
    to_hash = bytearray(68)
    to_hash[:32] = key
    to_hash[32:36] = rand.to_bytes(4, byteorder='little')
    to_hash[36:] = key

    d1 = (rand >> 16) & 0x000000ff
    d2 = (d1 << 11) | (rand >> 24)
    d2 ^= (d1 >> 5) ^ d1
    d2 = ~d2 & 0xffffffff

    return SM3(to_hash).digest(), d2.to_bytes(4, "little")

def split_blocks(message, block_size=16, require_padding=True):
    assert len(message) % block_size == 0 or not require_padding
    return [message[i:i + 16] for i in range(0, len(message), block_size)]

def add_round_key(s, k):
    for i in range(4):
        for j in range(4):
            s[i][j] ^= k[i][j]

def add_round_key_con(s, k, con):
    for i in range(4):
        for j in range(4):
            s[i][j] ^= k[i][con[j]]

def bytes2matrix(text):
    """ Converts a 16-byte array into a 4x4 matrix.  """
    return [list(text[i:i + 4]) for i in range(0, len(text), 4)]

def xor_bytes(a, b):
    """ Returns a new byte array with the elements xor'ed. """
    return bytearray(i ^ j for i, j in zip(a, b))

def matrix2bytes(matrix):
    """ Converts a 4x4 matrix into a 16-byte array.  """
    return bytearray(sum(matrix, []))

def mix_single_column(a, i):
    t = a[0][i] ^ a[1][i] ^ a[2][i] ^ a[3][i]
    u = a[0][i]
    a[0][i] ^= t ^ xtime(a[0][i] ^ a[1][i])
    a[1][i] ^= t ^ xtime(a[1][i] ^ a[2][i])
    a[2][i] ^= t ^ xtime(a[2][i] ^ a[3][i])
    a[3][i] ^= t ^ xtime(a[3][i] ^ u)

def mix_columns(s):
    for i in range(4):
        mix_single_column(s, i)

def inv_mix_columns(s):
    for i in range(0, 4):
        inv_mix_single_column(s, i)

def inv_mix_single_column(a, i):
    u = xtime(xtime(a[0][i] ^ a[2][i]))
    v = xtime(xtime(a[1][i] ^ a[3][i]))
    a[0][i] ^= u
    a[1][i] ^= v
    a[2][i] ^= u
    a[3][i] ^= v

    mix_single_column(a, i)

s_box = b''.join([
    b'\xFA\x7D\x08\x6B\x9C\x59\xB3\x4B\x04\x5F\x39\xD0\x38\x4A\x91\x99',
    b'\x00\x67\xA6\x20\x9F\xF5\x4D\x82\x73\x26\xEE\xDF\x18\x66\x83\x33',
    b'\x80\x03\x19\xFB\xD9\xFE\xAE\xAA\xA9\xB0\x52\xC6\x0B\xF3\x79\x25',
    b'\x4E\x78\xB4\x36\xAC\x5D\x1A\x27\x9E\x88\xDB\xBD\x3C\x63\xEC\x49',
    b'\x15\xC1\x30\x1F\xDC\xB8\x56\xD4\x6C\xCD\xCA\x09\x43\xC8\x35\xA3',
    b'\xEF\x1E\xF4\x96\xD2\xFC\x0E\x72\x7B\x94\x84\xD1\xEA\x45\x5A\x62',
    b'\x02\x3F\xD3\x12\x81\x34\x2B\xDD\x7E\xE6\x28\xF2\xA5\x46\x13\x01',
    b'\x3B\x21\xF6\x61\x37\x29\x2A\x0D\xED\x8C\xAF\xBF\x9D\x5C\xBB\x24',
    b'\x76\x0F\x75\xE4\x53\x89\xE1\x98\x8D\xB1\x9A\x65\x70\x4F\x54\x4C',
    b'\x58\xAB\x6E\x6F\x8B\x23\xC4\x07\x11\x0C\xBA\xCF\xA0\xA4\x8E\xD8',
    b'\x05\x3D\x14\xB2\xDA\x74\xC3\xD7\xE7\xBE\xD6\x7F\xDE\x48\x16\x3E',
    b'\x85\x90\xA1\x55\xB7\x77\x42\x22\xC9\x86\x50\x2E\x17\xF9\x64\x31',
    b'\x2C\x9B\xF1\x6D\x1C\x44\x68\xE3\xE9\xA8\x93\x97\xCB\x32\x57\xEB',
    b'\xE5\x71\x6A\xAD\xC0\xCC\xC7\xC5\xFD\x60\x1D\xA2\x2D\x47\xA7\xE2',
    b'\x51\x69\x5E\x7A\xCE\x0A\x41\xB6\x95\x8F\xF7\xB9\x87\xE0\x3A\x06',
    b'\x10\x8A\xB5\xF8\x5B\xD5\xF0\xBC\x92\xFF\x7C\x2F\xC2\xE8\x1B\x40',
    b'\xEC\x1B\xDA\xBD\xBA\x98\x91\x0C\xB2\x2B\x83\x41\x34\x67\xFB\x0A',
    b'\xD8\x76\xB5\x46\x05\x59\x61\x23\x75\x90\x87\x2A\xE3\x50\x15\x4C',
    b'\xAC\xB1\x79\xEB\xAE\xE5\x95\x47\x04\x68\xF0\x86\x3D\x51\x8B\x0F',
    b'\xCA\x8E\xE4\xB9\x4E\xF2\x12\x82\xBC\x0E\xD5\xF7\xEF\x28\x25\xCF',
    b'\x5B\x5D\xE9\x6A\x55\x02\xE1\x33\xBE\x93\xE7\xF5\xAD\x9D\x3E\x39',
    b'\x24\xA8\xE2\xFA\x17\x57\xD0\x7A\x0D\x08\x30\xD6\xB8\xA3\x8D\xFD',
    b'\x07\x9A\xC4\x1E\x6E\x22\x64\x97\xD2\x1D\xB0\xBF\x45\x66\x3F\x6C',
    b'\xDD\xDB\x27\x80\xA7\x11\xDC\xA6\xC5\x52\xF8\xC0\xB6\xC8\x5C\x00',
    b'\x73\x60\x7B\xA0\x19\x13\xAA\xC9\x35\x48\x4B\xD3\xA4\xCD\x9F\x99',
    b'\xF3\x10\x44\x40\x54\x7E\x29\xF4\x06\x1F\xA2\xAB\xA1\x2F\x3C\xF6',
    b'\xAF\x85\x62\x36\x21\x7F\x5E\xDF\x20\x1A\xB3\xB4\xE6\xFF\x72\x84',
    b'\x8F\x65\x26\x94\x5A\x77\xEA\x43\x78\xC7\x4A\xCC\x2C\x14\x6B\xC6',
    b'\xE8\x74\x53\xFC\xD4\x1C\xCE\x31\x70\x03\x18\x8C\x96\x38\x32\x89',
    b'\xF1\x3A\x5F\xD7\xF9\xA9\x69\xB7\x63\x37\x58\xC2\x3B\xC3\x71\xCB',
    b'\x9E\x92\x01\x8A\x0B\x4D\x88\x9B\xBB\x4F\x6D\x6F\xE0\xFE\xA5\x49',
    b'\xDE\x56\x16\x09\xED\x9C\xC1\x2D\xEE\x81\x7D\xD9\x7C\xD1\x2E\x42',
    b'\x5B\x4D\xC1\xA6\x5D\xEA\x44\xFD\x45\x4E\x1B\xA1\x3F\xD1\x89\xE1',
    b'\x7D\x2F\xAA\xDB\xAB\xAD\x59\xCB\xB1\xCE\x9A\x28\xC9\xE0\xF6\x70',
    b'\x39\x4A\xD7\xFF\x30\xF5\xDD\xBC\x57\x3B\x11\x8D\xB2\xEE\x00\xB6',
    b'\xE6\x1A\x5A\x7C\xF9\xDE\xC4\xCD\x2E\x80\xBB\xB9\x4C\xA5\x9F\x84',
    b'\x08\xC6\x6F\x42\x6C\xF0\x27\xE7\x8B\x3A\x9C\x51\xFB\x67\x21\x75',
    b'\x41\x31\xA7\xCA\x20\x43\x2A\xB7\xBF\xD9\x7A\xF2\xB5\xF8\x8C\x2C',
    b'\x23\x83\x4F\x8F\x60\xA0\x04\x13\x37\x14\xE3\x01\xC5\x63\x66\x5C',
    b'\x74\x81\xDF\x58\xBD\x68\x90\x3D\xD2\xB3\x34\xF4\x19\x93\x32\x29',
    b'\xD6\x49\xAE\x0D\x4B\xD8\x07\x9E\xAC\x1E\x2D\x0B\x40\xB8\x72\xBA',
    b'\x76\x10\x71\xA8\xE4\x56\x1D\x48\xFE\xE5\xC2\x47\x91\xDA\x87\x26',
    b'\x9D\x1F\x88\x6B\xC0\x98\xBE\x25\x09\x97\x33\xA3\x85\x16\x5E\x7F',
    b'\xDC\x6E\x54\xE9\xF7\xA9\xC8\xE8\xC3\x77\xD0\x82\x2B\xEC\x02\x62',
    b'\x8A\x92\x0E\x3E\xB0\x0F\x05\xF3\xF1\x96\x78\x38\x86\x36\x18\x3C',
    b'\x24\xCF\x0A\xB4\x53\xCC\x61\x65\xA4\xC7\x94\xD5\x15\x7E\x6D\xEF',
    b'\x79\x22\x35\x12\x6A\x8E\x52\x06\x55\x7B\x46\x64\x50\x95\xE2\x0C',
    b'\xED\xD3\x17\x03\xA2\x9B\x99\xEB\x1C\xFC\xAF\xD4\x73\x69\xFA\x5F',
    b'\xF7\x2C\x1E\xBF\xC8\xE1\xF3\x9F\x76\x80\x71\x48\xAA\x94\xAD\x64',
    b'\xFB\x89\xC6\x60\xC3\x32\xB3\x4D\xD2\xE0\x44\xDD\x5F\xA8\xB1\xC7',
    b'\x68\x23\x34\xC9\x6D\x12\x7F\xB7\xEB\x15\xBE\xA9\xD1\x78\x93\xA0',
    b'\x0C\x92\xA4\xD7\x47\xE3\x8A\xC2\x70\xAB\x26\x41\x9A\x79\xA7\xD8',
    b'\x14\x85\x8F\xC0\x6F\x56\xD0\x8C\x11\xB9\x2E\x3C\xE2\x9D\xCF\x0E',
    b'\xDE\x03\x5D\x46\x3E\xCD\x38\x43\x0F\x33\x5A\xD9\x1A\x65\x6C\x22',
    b'\x3B\xFC\x30\xA6\x88\xEA\x37\xA2\xB4\x8D\x8E\x51\x9C\xD6\x40\xEE',
    b'\xF9\xF8\x84\xF4\xAE\x97\xE9\xCA\x0A\x45\x67\x57\x04\x2F\x83\x5C',
    b'\xD5\xC5\xC4\x82\xB6\xA3\x91\x98\x1F\x4A\xAC\x96\x81\x6E\xCB\x1B',
    b'\x09\x08\xAF\x18\x95\x49\x7D\x54\xED\xFA\x16\x31\x3A\xDA\xB8\x66',
    b'\xF5\xA5\xF1\xFE\x10\x01\x06\x74\xCC\x63\xDF\x7C\x28\x25\xF6\xCE',
    b'\xB2\x4F\x8B\xE5\xBC\x87\x69\xBB\x86\x21\x07\x00\x36\xE7\x0B\x50',
    b'\x59\x9B\x1C\xE8\x62\x58\x19\x61\xF2\xBD\x27\x5E\xBA\x1D\xE6\x99',
    b'\x42\x3D\x0D\x2A\xB5\xDC\x5B\x29\xF0\x2D\x4C\x53\x7B\x6A\x73\x4E',
    b'\x3F\x75\xFF\x4B\xA1\x35\x17\x55\x72\x39\x20\xD3\xB0\xFD\xEF\x02',
    b'\xEC\x77\x7E\xE4\x2B\xDB\x90\xC1\x05\x9E\x7A\xD4\x52\x6B\x24\x13'])

inv_s_box = bytearray(1024)

class AES_V3():
    r_con = [[1, 0, 2, 3], [1, 3, 0, 2], [0, 1, 3, 2], [1, 0, 2, 3]]
    r_con2 = [[1, 0, 2, 3], [2, 0, 3, 1], [0, 1, 3, 2], [1, 0, 2, 3]]
    r_orders = [[0, 9, 14, 11, 4, 13, 2, 7, 8, 1, 6, 15, 12, 5, 10, 3],
                [0, 9, 14, 15, 4, 13, 2, 7, 8, 1, 6, 3, 12, 5, 10, 11],
                [0, 9, 14, 7, 4, 13, 2, 11, 8, 1, 6, 3, 12, 5, 10, 15],
                [0, 9, 14, 11, 4, 13, 2, 7, 8, 1, 6, 15, 12, 5, 10, 3]]

    def __init__(self, aes_key, khronos):
        self.word_size = khronos & 3  # khronos - (khronos & -4)
        self.aes_key = aes_key

        self.s_box = s_box[self.word_size << 8:]
        self.inv_s_box = inv_s_box[self.word_size << 8:]

        self.master_key = self._expand_key()
        self._key_matrices = bytes2matrix(self.master_key)
        self.con = self.r_con[self.word_size]
        self.con2 = self.r_con2[self.word_size]

        self.order = self.r_orders[self.word_size]

    def _expand_key(self):
        init_values = [0xca025ddc, 0x823dc546, 0xc9420583, 0xc298225f]
        init_value = init_values[self.word_size]
        mk = bytearray(init_value.to_bytes(4, "little"))
        mk = mk * 4

        mk = xor_bytes(mk, self.aes_key)
        mk += bytearray(32)

        rounds = 8

        for i in range(4, 12):
            idx = 4 * (i - 1)
            k0, k1, k2, k3 = mk[idx], mk[idx + 1], mk[idx + 2], mk[idx + 3]

            if i & 3 == 0:
                k00 = (init_value >> (rounds & 24)) ^ self.s_box[k1]
                k1 = self.s_box[k2]
                k2 = self.s_box[k3]
                k3 = self.s_box[k0]
                k0 = k00 & 0xff
            rounds += 2

            mk[idx + 4] = k0 ^ mk[idx - 12]
            mk[idx + 5] = k1 ^ mk[idx - 11]
            mk[idx + 6] = k2 ^ mk[idx - 10]
            mk[idx + 7] = k3 ^ mk[idx - 9]
        return mk

    @staticmethod
    def sum_data(data):
        key = bytearray(32)
        for i in range(31):
            idx = i * 8
            n0 = (data[idx] >> 4) & 2
            n1 = n0 | data[idx + 1] & 64
            n2 = n1 | (data[idx + 2] >> 2) & 1
            n3 = n2 | (data[idx + 3] << 3) & -128
            n4 = n3 | (data[idx + 4] >> 1) & 4
            n5 = n4 | (data[idx + 5] << 3) & 16
            n6 = n5 | (data[idx + 6] << 5) & 32
            n7 = n6 | (data[idx + 7] >> 4) & 8
            key[i] = (n7 & 0xff)

        key[31] = 1
        return key

    @staticmethod
    def mix_columns(data, key):
        data = bytearray(data)

        for i in range(31):
            kk = key[i]
            idx = i * 8
            # print(k, data[idx + 1], (data[idx + 1] & -65) | (k & 64))
            data[idx + 0] = (data[idx + 0] & -33) | ((kk << 4) & 0xff & 32)
            data[idx + 1] = (data[idx + 1] & -65) | (kk & 64)
            data[idx + 2] = (data[idx + 2] & -5) | ((kk * 4) & 4)
            data[idx + 3] = (data[idx + 3] & -17) | ((kk >> 3) & 16)
            data[idx + 4] = (data[idx + 4] & -9) | ((kk + kk) & 8)
            data[idx + 5] = (data[idx + 5] & -3) | ((kk >> 3) & 2)
            data[idx + 6] = (data[idx + 6] & -2) | ((kk >> 5) & 1)
            data[idx + 7] = (data[idx + 7] & 127) | ((kk << 4) & 0xff & -128)

        return data

    def encrypt(self, data, iv):
        plaintext = self.sum_data(data)
        blocks = []
        previous = iv
        for plaintext_block in split_blocks(plaintext):
            x = xor_bytes(plaintext_block, previous)
            block = self.encrypt_block(x)
            blocks.append(block)
            previous = block

        key = b''.join(blocks)
        # key = bytes.fromhex('a22c23b05bb4a831d31bbdbd1327c5f84991bca3e7d8df24e52f58b7ac61f2e0')
        # print("sign_key", key.hex())
        data = self.mix_columns(data, key)
        return key[-1:] + data

    def encrypt_block(self, plaintext):
        # print("b000", plaintext.hex())
        plain_state = bytes2matrix(plaintext)

        add_round_key_con(plain_state, self._key_matrices[0:4], self.con2)
        # print("b001", matrix2bytes(plain_state).hex())

        for i in range(1, 3):
            self.sub_bytes(plain_state)
            # print("b003", matrix2bytes(plain_state).hex())
            self.shift_rows(plain_state)
            # print("b004", matrix2bytes(plain_state).hex())
            if i == 1:
                self.shift_rows_con(plain_state, self.con2)
                mix_columns(plain_state)

            add_round_key_con(plain_state, self._key_matrices[i * 4:], self.con2)

        add_round_key(plain_state, self._key_matrices[4:])

        return matrix2bytes(plain_state)

    def decrypt(self, ciphertext, iv, data):
        assert len(iv) == 16

        blocks = []
        previous = iv

        for ciphertext_block in split_blocks(ciphertext):
            dc = xor_bytes(previous, self.decrypt_block(ciphertext_block))
            # dc = matrix2bytes(dcm)
            blocks.append(dc)
            previous = ciphertext_block

        key = b''.join(blocks)
        # print("sign_key", key.hex())
        data = self.mix_columns(data, key)
        return data

    def decrypt_block(self, ciphertext):
        assert len(ciphertext) == 16
        cipher_state = bytes2matrix(ciphertext)

        # print("b000", matrix2bytes(cipher_state).hex())
        add_round_key(cipher_state, self._key_matrices[4:])
        #         print("b001", matrix2bytes(cipher_state).hex())

        for i in range(2, 0, -1):
            add_round_key_con(cipher_state, self._key_matrices[i * 4:], self.con2)
            #             print("b002", i, matrix2bytes(cipher_state).hex())

            if i == 1:
                inv_mix_columns(cipher_state)
                self.shift_rows_con(cipher_state, self.con)

            self.inv_shift_rows(cipher_state)
            #             print("b004", i, matrix2bytes(cipher_state).hex())
            self.inv_sub_bytes(cipher_state)
        #             print("b005", i, matrix2bytes(cipher_state).hex())

        add_round_key_con(cipher_state, self._key_matrices[0:4], self.con2)

        return matrix2bytes(cipher_state)

    def shift_rows_con(self, s, c):
        for i in range(4):
            # c = self.con
            s[i][0], s[i][1], s[i][2], s[i][3] = s[i][c[0]], s[i][c[1]], s[i][c[2]], s[i][c[3]]

    def shift_rows(self, s):
        bs = matrix2bytes(s)
        for i in range(4):
            for j in range(4):
                s[i][j] = bs[self.order[i * 4 + j]]

    def inv_shift_rows(self, s):
        order = bytearray(16)
        for i in range(16):
            order[self.order[i]] = i

        bs = matrix2bytes(s)
        for i in range(4):
            for j in range(4):
                s[i][j] = bs[order[i * 4 + j]]

    def sub_bytes(self, s):
        for i in range(4):
            for j in range(4):
                s[i][j] = self.s_box[s[i][j]]

        s[0], s[1], s[2], s[3] = s[self.con2[0]], s[self.con2[1]], s[self.con2[2]], s[self.con2[3]]

    def inv_sub_bytes(self, s):
        for i in range(4):
            for j in range(4):
                s[i][j] = self.inv_s_box[s[i][j]]
        s[0], s[1], s[2], s[3] = s[self.con[0]], s[self.con[1]], s[self.con[2]], s[self.con[3]]

def leftCircularShift(k, bits):
    bits = bits % 32
    k = k % (2 ** 32)
    upper = (k << bits) % (2 ** 32)
    result = upper | (k >> (32 - (bits)))
    return (result)

def blockDivide(block, chunks):
    result = []
    size = len(block) // chunks
    for i in range(0, chunks):
        result.append(int.from_bytes(block[i * size:(i + 1) * size], byteorder="little"))
    return (result)

def F(X, Y, Z):
    return ((X & Y) | ((~X) & Z))

def G(X, Y, Z):
    return ((X & Z) | (Y & (~Z)))

def H(X, Y, Z):
    return (X ^ Y ^ Z)

def I(X, Y, Z):
    return (Y ^ (X | (~Z))) & 0xffffffff

def FF(a, b, c, d, M, s, t):
    result = b + leftCircularShift((a + F(b, c, d) + M + t), s)

    return (result)

def GG(a, b, c, d, M, s, t):
    result = b + leftCircularShift((a + G(b, c, d) + M + t), s)
    return (result)

def HH(a, b, c, d, M, s, t):
    result = b + leftCircularShift((a + H(b, c, d) + M + t), s)
    return (result)

def II(a, b, c, d, M, s, t):
    result = b + leftCircularShift((a + I(b, c, d) + M + t), s)
    return (result)

def sum_md5(data):
    check_sum = 0x20220420
    for i in range(12):
        if i % 2 == 0:
            temp = (check_sum >> 3) ^ check_sum
            check_sum = data[i] ^ (check_sum << 7)
        else:
            temp = (check_sum >> 5) ^ check_sum
            check_sum = data[i] | (check_sum << 11)
            check_sum ^= 0xffffffff

        check_sum ^= temp
        check_sum &= 0xffffffff

    check_sum |= 4
    check_sum ^= 0x1000000
    return check_sum

SV2 = [0xa7aefe20, 0x7149f1d6, 0x47e4ca07, 0xe9b58f67, 0x93b924de, 0xc614d0f5, 0x38afe0ef, 0xb2bbad73,
       0xe24444c3, 0x9d3aec9b, 0xdf7b37e4, 0xd8b16d40, 0xf8ac31b8, 0x76b9a90b, 0x31d833ee, 0x953fce64,
       0x353595a4, 0x4609c13b, 0x36925008, 0x8c6d0925, 0x5df5c177, 0x1cfbf52b, 0x8a4fa7f0, 0x114ca35e,
       0x8193f984, 0x7a7a8733, 0x316ab4d5, 0x3c20cfc9, 0xa6d84453, 0x3a18500c, 0x798ec47a, 0x97a76b28,
       0x66c4ff96, 0x51716443, 0xdd2fc3b, 0xb5696da7, 0xbbeb3ac5, 0x5c53d204, 0xd32608ce, 0x7279b9ec,
       0xf4188ecf, 0xf7d793db, 0x332cc491, 0xab76ae15, 0x9bebe727, 0x18a01384, 0x5be9f8a7, 0x5f90a754,
       0x39b663c0, 0x36673c83, 0x7c92f514, 0x9d7d94d7, 0xe2e8d9aa, 0x5f7e9ea9, 0x7abd4551, 0x569e05da,
       0x40a25632, 0x3df5a9a5, 0xbab37d80, 0x454286dc, 0x3f5d4e78, 0x3d7b75d, 0xb1fe4af7, 0xa5ab26a3]

def md5sum_v3(msg, count_v2, orders, count_v1, n=0):
    count = count_v2 & 0xff

    sv = [0] * 64
    for i in range(64):
        sv[i] = ror32(SV2[i], count_v1)

    start = [
        ror32(0x79e0f2fb, count),
        ror32(0xc8b52570, count),
        ror32(0xebc2f8cd, count),
        ror32(0x7c104d93, count)
    ]

    count = (count_v2 + 6) & 0xff
    end = [
        ror32(0x19be4866, count),
        ror32(0xe85986b4, count),
        ror32(0xe19b326e, count),
        ror32(0x71d1d7d4, count)
    ]
    A = start[0]  # 0x79e0f2fb
    B = start[1]  # 0xc8b52570
    C = start[2]  # 0xebc2f8cd
    D = start[3]  # 0x7c104d93

    a = A
    b = B
    c = C
    d = D
    block = msg[:64]
    M = blockDivide(block, 16)

    order1 = orders[:16]
    order2 = orders[16:32]
    order3 = orders[32:48]
    order4 = orders[48:]
    # Rounds
    a = FF(a, b, c, d, M[order1[0]], 7, sv[0])
    d = FF(d, a, b, c, M[order1[1]], 12, sv[1])  # 0xb6bc6ddb
    c = FF(c, d, a, b, M[order1[2]], 17, sv[2])  # 0xf80b15d4
    b = FF(b, c, d, a, M[order1[3]], 22, sv[3])
    a = FF(a, b, c, d, M[order1[4]], 7, sv[4])
    d = FF(d, a, b, c, M[order1[5]], 12, sv[5])
    c = FF(c, d, a, b, M[order1[6]], 17, sv[6])
    b = FF(b, c, d, a, M[order1[7]], 22, sv[7])
    a = FF(a, b, c, d, M[order1[8]], 7, sv[8])
    d = FF(d, a, b, c, M[order1[9]], 12, sv[9])
    c = FF(c, d, a, b, M[order1[10]], 17, sv[10])
    b = FF(b, c, d, a, M[order1[11]], 22, sv[11])
    a = FF(a, b, c, d, M[order1[12]], 7, sv[12])
    d = FF(d, a, b, c, M[order1[13]], 12, sv[13])
    c = FF(c, d, a, b, M[order1[14]], 17, sv[14])
    b = FF(b, c, d, a, M[order1[15]], 22, sv[15])

    a = GG(a, b, c, d, M[order2[0]], 5, sv[16])
    d = GG(d, a, b, c, M[order2[1]], 9, sv[17])
    c = GG(c, d, a, b, M[order2[2]], 14, sv[18])
    b = GG(b, c, d, a, M[order2[3]], 20, sv[19])
    a = GG(a, b, c, d, M[order2[4]], 5, sv[20])
    d = GG(d, a, b, c, M[order2[5]], 9, sv[21])
    c = GG(c, d, a, b, M[order2[6]], 14, sv[22])
    b = GG(b, c, d, a, M[order2[7]], 20, sv[23])
    a = GG(a, b, c, d, M[order2[8]], 5, sv[24])
    d = GG(d, a, b, c, M[order2[9]], 9, sv[25])
    c = GG(c, d, a, b, M[order2[10]], 14, sv[26])
    b = GG(b, c, d, a, M[order2[11]], 20, sv[27])
    a = GG(a, b, c, d, M[order2[12]], 5, sv[28])
    d = GG(d, a, b, c, M[order2[13]], 9, sv[29])
    c = GG(c, d, a, b, M[order2[14]], 14, sv[30])
    b = GG(b, c, d, a, M[order2[15]], 20, sv[31])

    a = HH(a, b, c, d, M[order3[0]], 4, sv[32])
    d = HH(d, a, b, c, M[order3[1]], 11, sv[33])
    c = HH(c, d, a, b, M[order3[2]], 16, sv[34])
    b = HH(b, c, d, a, M[order3[3]], 23, sv[35])
    a = HH(a, b, c, d, M[order3[4]], 4, sv[36])
    d = HH(d, a, b, c, M[order3[5]], 11, sv[37])
    c = HH(c, d, a, b, M[order3[6]], 16, sv[38])
    b = HH(b, c, d, a, M[order3[7]], 23, sv[39])
    a = HH(a, b, c, d, M[order3[8]], 4, sv[40])
    d = HH(d, a, b, c, M[order3[9]], 11, sv[41])
    c = HH(c, d, a, b, M[order3[10]], 16, sv[42])
    b = HH(b, c, d, a, M[order3[11]], 23, sv[43])
    a = HH(a, b, c, d, M[order3[12]], 4, sv[44])
    d = HH(d, a, b, c, M[order3[13]], 11, sv[45])
    c = HH(c, d, a, b, M[order3[14]], 16, sv[46])
    b = HH(b, c, d, a, M[order3[15]], 23, sv[47])

    a = II(a, b, c, d, M[order4[0]], 6, sv[48])
    d = II(d, a, b, c, M[order4[1]], 10, sv[49])
    c = II(c, d, a, b, M[order4[2]], 15, sv[50])
    b = II(b, c, d, a, M[order4[3]], 21, sv[51])
    a = II(a, b, c, d, M[order4[4]], 6, sv[52])
    d = II(d, a, b, c, M[order4[5]], 10, sv[53])
    c = II(c, d, a, b, M[order4[6]], 15, sv[54])
    b = II(b, c, d, a, M[order4[7]], 21, sv[55])
    a = II(a, b, c, d, M[order4[8]], 6, sv[56])
    d = II(d, a, b, c, M[order4[9]], 10, sv[57])
    c = II(c, d, a, b, M[order4[10]], 15, sv[58])
    b = II(b, c, d, a, M[order4[11]], 21, sv[59])
    a = II(a, b, c, d, M[order4[12]], 6, sv[60])
    d = II(d, a, b, c, M[order4[13]], 10, sv[61])
    c = II(c, d, a, b, M[order4[14]], 15, sv[62])
    b = II(b, c, d, a, M[order4[15]], 21, sv[63])

    A = (A + a) % (2 ** 32) ^ end[0]
    B = (B + b) % (2 ** 32) ^ end[1]
    C = (C + c) % (2 ** 32) ^ end[2]
    D = (D + d) % (2 ** 32) ^ end[3]

    result = bytearray(
        A.to_bytes(4, "little") + B.to_bytes(4, "little") + C.to_bytes(4, "little") + D.to_bytes(4, "little"))

    result += sum_md5(result).to_bytes(4, "little")
    return result

def bxor(b1, b2):
    b3 = bytearray(len(b1))
    for i in range(len(b1)):
        b3[i] = b1[i] ^ b2[i]
    return b3

def get_iv(iv, data):
    for i in range(len(data)):
        if i & 1 == 0:
            iv = (iv >> 4) ^ iv ^ (iv << 6) ^ data[i]
        else:
            iv = ~((iv >> 7) ^ iv ^ (data[i] | iv << 12))
        iv = iv & 0xffffffff
    return iv

def hash_f13(query_sm3, body_md5_bytes, ts_bytes, khronos):
    iv = get_iv(0x20230928, query_sm3)
    iv = get_iv(iv, body_md5_bytes)
    iv = get_iv(iv, ts_bytes)

    iv_v0 = ((iv & 15) * 171) >> 9
    branch = (iv & 15) - ((iv_v0 * 3) & 0xff)
    if branch == 0:
        return branch_0(iv_v0, khronos, query_sm3, body_md5_bytes, ts_bytes)
    elif branch == 1:
        return branch_1(iv_v0, khronos, query_sm3, body_md5_bytes, ts_bytes)
    elif branch == 2:
        return branch_2(iv, khronos, query_sm3, body_md5_bytes, ts_bytes)
    else:
        raise Exception("no branch: " + str(branch))

def branch_0(iv_v0, khronos, query_sm3, body_md5_bytes, ts_bytes):
    tt01 = [0xc4a78580, 0xb3c0fd39, 0xc58c5686, 0xc9aa3ba7, 0xf5a7adf2, 0x963c2ed1]
    iv_v1 = tt01[iv_v0]

    count_v1 = (iv_v1 + khronos + 1) & 0xff
    count_v2 = (iv_v1 + khronos) & 0xffffffff

    tt02 = [0xebb64faf, 0x7aadcc2, 0xcf3187bf, 0xe01138ff, 0x6d0bfcff, 0x5a30a3be, 0xb41ad638, 0x34180eb8, 0xf233eb6f,
            0xb1a584cc, 0xccc30dc7, 0x47d1db51, 0xd55653de, 0x70a84fa1, 0x57473c12, 0xf76f0288, 0x2c077f0a, 0xda0dcad0,
            0xfbb86f6c, 0xfdc4cf00, 0x688a020d, 0xe676c6a6, 0x8cd6338b, 0x1a3c8d0e, 0xcce8b06b, 0x6ad0ed0b, 0xa0522717,
            0xdc71ac83, 0x2285db71, 0xd5b4dda6, 0x736f8650, 0x6560306c, 0x617ce2a6, 0xe423417e, 0xa40e143, 0x544e4032,
            0x88dffb2a, 0x716c1ae0, 0x4c467a88, 0x5b23bb3, 0xe1d0b866, 0xbaa3dcb8, 0xae3374d3, 0xc3381a50, 0x1702f75b,
            0xfe6da368, 0xf0b4cf48, 0x4e0ffbb8, 0x72aad10d, 0x26c53a3d, 0xf2bce0f6, 0xb4557581, 0x4a257fdd, 0x8c3182a2,
            0xab0b3b86, 0x3d5dfb14, 0x4f103634, 0xd37b52d7, 0x444eff16, 0xeb0a33d1, 0x6ca86f6e, 0x284ba7, 0x8387cfa,
            0x5fb37586]

    tt03 = [0] * 64
    for i in range(0, 64):
        tt03[i] = ror32(tt02[i], count_v1) & 0xffffffff

    n0 = (count_v2 + 2) & 7

    pad = bytearray(4)
    seed = bytes([0xfa, 0x45, 0x61, 0xd7])
    for i in range(4):
        v = int.from_bytes(bytes([seed[i], seed[i]]), 'little')
        v = v >> n0
        pad[i] = v & 0xff

    count_v2 = count_v2 & 0xff
    init_value = [
        ror32(0x7aba4fc8, count_v2), ror32(0x67166507, count_v2),
        ror32(0x6403fa00, count_v2), ror32(0x340f512f, count_v2),
        ror32(984304912, count_v2), ror32(3005047866, count_v2),
        ror32(2874125293, count_v2), ror32(2152413264, count_v2)
    ]

    data = query_sm3 + body_md5_bytes + ts_bytes + pad + bytes.fromhex(' 00 00 00 00 00 00 01 a0')
    di = [0] * (len(data) // 4)
    for i in range(len(data) // 4):
        di[i] = int.from_bytes(data[i * 4:i * 4 + 4], "big")

    di0 = di[0]
    for i in range(112):
        di1, di14 = di[i + 1], di[i + 14]
        r_di1 = rol(di1, 14) ^ rol(di1, 25) ^ (di1 >> 3)
        r_di2 = rol(di14, 13) ^ rol(di14, 15) ^ (di14 >> 10)
        di0 = di0 + di[i + 9] + r_di1 + r_di2
        di.append(di0 & 0xffffffff)
        di0 = di1

    if iv_v0 == 5:
        v_j = branch0_xor(init_value, iv_v1, di, tt03, 100, 2, 0, 3, 5, 4, 6, 7, 2, 1, 5)
    elif iv_v0 == 4:
        v_j = branch0_xor(init_value, iv_v1, di, tt03, 96, 0, 5, 6, 7, 3, 1, 2, 5, 4, 4)
    elif iv_v0 == 3:
        v_j = branch0_xor(init_value, iv_v1, di, tt03, 99, 3, 6, 2, 4, 5, 1, 0, 0, 7, 6)
    elif iv_v0 == 2:
        v_j = branch0_xor(init_value, iv_v1, di, tt03, 96, 7, 6, 2, 1, 4, 0, 5, 4, 3, 5)
    elif iv_v0 == 1:
        v_j = branch0_xor(init_value, iv_v1, di, tt03, 96, 0, 6, 7, 5, 3, 2, 1, 5, 4, 4)
    elif iv_v0 == 0:
        v_j = branch0_xor(init_value, iv_v1, di, tt03, 101, 5, 7, 6, 3, 2, 1, 0, 5, 4, 3)

    ret = bytearray(32)
    for i in range(8):
        ret[i * 4:i * 4 + 4] = ((v_j[i] + init_value[i]) & 0xffffffff).to_bytes(4, 'big')

    ret = bxor(ret[:16], ret[16:])
    sum = sum_md5(ret)
    ret += sum.to_bytes(4, "little")
    return ret

def swap_v0(src, src_xor, tt2, table_f, order1, typ=None):
    da0 = [0] * 8
    ha0 = src_xor[:]
    for i in range(8):
        da0[i] = src[order1[i]] ^ src_xor[i]

    for round in range(10):
        rr_0 = r00(ha0[0], ha0[1], ha0[2], ha0[3], ha0[4], ha0[5], ha0[6], ha0[7], 0, table_f)
        rr_1 = r00(ha0[1], ha0[2], ha0[3], ha0[4], ha0[5], ha0[6], ha0[7], ha0[0], 0, table_f)
        rr_2 = r00(ha0[2], ha0[3], ha0[4], ha0[5], ha0[6], ha0[7], ha0[0], ha0[1], 0, table_f)
        rr_3 = r00(ha0[3], ha0[4], ha0[5], ha0[6], ha0[7], ha0[0], ha0[1], ha0[2], 0, table_f)
        rr_4 = r00(ha0[4], ha0[5], ha0[6], ha0[7], ha0[0], ha0[1], ha0[2], ha0[3], 0, table_f)
        rr_5 = r00(ha0[5], ha0[6], ha0[7], ha0[0], ha0[1], ha0[2], ha0[3], ha0[4], 0, table_f)
        rr_6 = r00(ha0[6], ha0[7], ha0[0], ha0[1], ha0[2], ha0[3], ha0[4], ha0[5], 0, table_f)
        rr_7 = r00(ha0[7], ha0[0], ha0[1], ha0[2], ha0[3], ha0[4], ha0[5], ha0[6], 0, table_f)
        rr_7 = rr_7 ^ tt2[round + 1]

        d0, d1, d2, d3, d4, d5, d6, d7 = da0[0], da0[1], da0[2], da0[3], da0[4], da0[5], da0[6], da0[7]

        da0[0] = r00(d0, d1, d2, d3, d4, d5, d6, d7, rr_0, table_f)
        da0[1] = r00(d1, d2, d3, d4, d5, d6, d7, d0, rr_1, table_f)  # 0xd0a489b35ba678e8
        da0[2] = r00(d2, d3, d4, d5, d6, d7, d0, d1, rr_2, table_f)  # 0x3be5b7f9cfd44654
        da0[3] = r00(d3, d4, d5, d6, d7, d0, d1, d2, rr_3, table_f)
        da0[4] = r00(d4, d5, d6, d7, d0, d1, d2, d3, rr_4, table_f)
        da0[5] = r00(d5, d6, d7, d0, d1, d2, d3, d4, rr_5, table_f)
        da0[6] = r00(d6, d7, d0, d1, d2, d3, d4, d5, rr_6, table_f)
        da0[7] = r00(d7, d0, d1, d2, d3, d4, d5, d6, rr_7, table_f)

        ha0[0], ha0[1], ha0[2], ha0[3], ha0[4], ha0[5], ha0[6], ha0[7] = rr_0, rr_1, rr_2, rr_3, rr_4, rr_5, rr_6, rr_7

    if typ is None:
        src[0] = da0[0] ^ src_xor[0] ^ src[0]
        src[1] = da0[7] ^ src_xor[1] ^ src[1]
        src[2] = da0[6] ^ src_xor[2] ^ src[2]
        src[3] = da0[5] ^ src_xor[3] ^ src[3]
        src[4] = da0[4] ^ src_xor[4] ^ src[4]
        src[5] = da0[3] ^ src_xor[5] ^ src[5]
        src[6] = da0[2] ^ src_xor[6] ^ src[6]
        src[7] = da0[1] ^ src_xor[7] ^ src[7]
    else:
        src[0] = da0[7] ^ typ[1]
        src[1] = da0[6] ^ typ[2]
        src[2] = da0[5] ^ typ[3]
        src[3] = da0[4] ^ typ[4]
        src[4] = da0[3] ^ typ[5]
        src[5] = da0[2] ^ typ[6]
        src[6] = da0[1] ^ typ[7] ^ src[7]
        src[7] = da0[0] ^ typ[0]
    return src

def branch_1(iv_v0, khronos, query_sm3, body_md5_bytes, ts_bytes):
    tt1 = [0x808a9c79, 0xf079807e, 0xbadf79c5, 0xa785d3ff, 0x82d8438c]
    iv_v1 = tt1[iv_v0]

    c_v1 = (iv_v1 + khronos) & 0xff
    c_v1 = ror(khronos, c_v1)

    orders = bytes.fromhex('''05 07 01 02 04 00 06 03 00 05 02 04 01 03 07 06
    05 07 02 04 01 06 03 00 03 00 02 04 06 07 01 05
    04 05 00 03 06 02 01 07 00 00 00 00 00 00 00 00''')

    order1 = orders[iv_v0 * 8:iv_v0 * 8 + 8]

    iv_v1 = (iv_v1 + khronos + 1) & 63
    tt1 = [0x87aeea5dab37cd6b, 0x7ff48becb4f54087, 0xb0724c06706bbd5d, 0x1fe5dfb1143e328d,
           0x1a2331d00af4f1f2, 0xcaff7131bb1e71ba, 0x33385e1042752218, 0xff01ed65d4a441fb,
           0xadb1ec8828c80e8, 0x62475d12f4e06fe7, 0xbd0b238da4fe72]

    tt2 = [0] * 11
    for i in range(0, 11):
        tt2[i] = ror(tt1[i], iv_v1)

    to_sign = bytearray(query_sm3 + body_md5_bytes + ts_bytes + bytes([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))

    src = [0] * (len(to_sign) // 8)
    for i in range(len(to_sign) // 8):
        src[i] = int.from_bytes(to_sign[i * 8:i * 8 + 8], 'big')

    src_xor = [c_v1, c_v1, c_v1, c_v1, c_v1, c_v1, c_v1, c_v1]

    table_f = get_branch_1_table_f(iv_v0)
    swap = swap_v0(src, src_xor, tt2, table_f, order1)
    data = [0] * 8
    data[7] = 416

    src_xor = [swap[4], swap[3], swap[2], swap[1], swap[0], swap[7], swap[6], swap[5]]
    swap = swap_v0(data, src_xor, tt2, table_f, order1, swap)

    ret = bytearray(32)
    n = 0
    for i in range(7, -1, -1):
        pp = swap[i].to_bytes(8, "little")
        ret[n + 0], ret[n + 1], ret[n + 2], ret[n + 3] = pp[1], pp[3], pp[5], pp[6]
        n += 4

    for i in range(16):
        ret[i] ^= ret[i + 16]
    ret = ret[:16]
    sum = sum_md5(ret)
    ret += sum.to_bytes(4, "little")
    return ret

def r00(r0, r1, r2, r3, r4, r5, r6, r7, tt, table_f, v=0):
    x = table_f(8 * (r0 >> 56))
    r1 = (r1 >> 45) & 2040

    if tt > 0:
        x = x ^ tt
    x = x ^ table_f(r1 + 2048)

    r2 = (r2 >> 37) & 2040
    x = x ^ table_f(r2 + 4096)

    r3 = (r3 >> 29) & 2040
    x = x ^ table_f(r3 + 6144)

    r4 = (r4 >> 21) & 2040
    x = x ^ table_f(r4 + 8192)

    r5 = (r5 >> 13) & 2040
    x = x ^ table_f(r5 + 10240)

    r6 = (r6 >> 8) & 255
    x = x ^ table_f(8 * r6 + 12288)

    r7 = r7 & 255
    x = x ^ table_f(8 * r7 + 14336)

    return x

branch_2_orders = bytes.fromhex('''
    0f 07 04 00 09 08 03 0a 06 0b 05 0d 0e 01 0c 02 0f 05 08 0c 00 09 02 01 03 07 0e 06 0b 0a 0d 04 06 05 00 07 0c 00 0a 04 08 0f 01 0b 0d 09 02 0e 06 0b 02 05 04 03 08 01 01 07 0a 00 0d 0c 09 0e
    0d 07 0e 0f 0b 02 08 03 0c 05 09 01 00 04 06 0a 0d 09 02 06 0f 0b 0a 04 08 07 00 0c 05 03 01 0e 0c 09 0f 07 06 0f 03 0e 02 0d 04 05 01 0b 0a 00 0c 05 0a 09 0e 08 02 04 04 07 03 0f 01 06 0b 00
    0b 0f 04 08 02 0a 07 00 09 0d 06 01 0e 03 05 0c 0b 06 0a 05 08 02 0c 03 07 0f 0e 09 0d 00 01 04 09 06 08 0f 05 08 00 04 0a 0b 03 0d 01 02 0c 0e 09 0d 0c 06 04 07 0a 03 03 0f 00 08 01 05 02 0e
    01 00 0d 0f 09 0a 0b 0e 04 02 08 07 03 06 0c 05 01 08 0a 0c 0f 09 05 06 0b 00 03 04 02 0e 07 0d 04 08 0f 00 0c 0f 0e 0d 0a 01 06 02 07 09 05 03 04 02 05 08 0d 0b 0a 06 06 00 0e 0f 07 0c 09 03
    0a 08 04 0f 00 0b 01 06 0d 0c 07 09 03 0e 05 02 0a 07 0b 05 0f 00 02 0e 01 08 03 0d 0c 06 09 04 0d 07 0f 08 05 0f 06 04 0b 0a 0e 0c 09 00 02 03 0d 0c 02 07 04 01 0b 0e 0e 08 06 0f 09 05 00 03
    ''')

def branch_2(iv, khronos, query_sm3, body_md5_bytes, ts_bytes):
    n0 = (iv & 15 - 2) * 86
    iv_v0 = (n0 >> 15 & 0xff) + (n0 >> 8 & 0xff)

    t001 = [0x8980f29b, 0xeb549c7f, 0xb08726db, 0xd40cb5e6, 0xe8f559e4]

    n1 = t001[iv_v0]
    count_v1 = (n1 + khronos + 1) & 0xff
    count_v2 = (n1 + khronos) & 0xffffffff

    n0 = (count_v2 + 5) & 7

    pad = bytearray(8)
    seed = bytes([0x84, 0x96, 0x77, 0x9d, 0xd4, 0x15, 0x0b, 0xf8])
    for i in range(8):
        v = int.from_bytes(bytes([seed[i], seed[i]]), 'little')
        v = v >> n0
        pad[i] = v & 0xff

    data = query_sm3 + body_md5_bytes + ts_bytes + pad + bytes.fromhex('a0 01 00 00')

    idx = iv_v0 << 6
    ret = md5sum_v3(data, count_v2, branch_2_orders[idx:idx + 64], count_v1)

    return ret

def branch0_xor(data, base, di, tt03, round, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10):
    d = data[:]

    for i in range(round):
        offset = base + i
        n0 = di[offset & 127]

        n1 = ((d[x3] ^ d[x4]) & d[x1]) ^ d[x3]

        n2 = rol(d[x1], 26) ^ rol(d[x1], 21) ^ rol(d[x1], 7)
        offset = offset & 63
        n3 = tt03[offset]

        n4 = (n0 + n1 + n2 + n3 + d[x5]) & 0xffffffff

        n5 = rol(d[x2], 30) ^ rol(d[x2], 19) ^ rol(d[x2], 10)
        n6 = (d[x2] & d[x6]) | ((d[x2] | d[x6]) & d[x7])
        n7 = n5 + n6

        o = d[x9]
        d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7] = d[7], d[0], d[1], d[2], d[3], d[4], d[5], d[6]
        d[x10] = (n7 + n4) & 0xffffffff
        d[x8] = (o + n4) & 0xffffffff
    return d

branch_1_table = None

def get_branch_1_table_f(iv_v0):
    global branch_1_table
    if branch_1_table is None:
        branch_1_table = _branch_one_bytes()

    table = branch_1_table[iv_v0 << 14:]
    def table_f(x):
        return int.from_bytes(table[x:x + 8], 'little')
    return table_f

def _varint(value: int) -> bytes:
    value = int(value)
    if value < 0:
        value &= (1 << 64) - 1
    result = bytearray()
    while value > 0x7F:
        result.append((value & 0x7F) | 0x80)
        value >>= 7
    result.append(value)
    return bytes(result)

def _sint(value: int, bits: int) -> int:
    # 正式 protobuf 编码规则：正数不先截断到有符号范围；
    # 这对 Medusa.rand 等可能大于 2**31 的 sint32 字段很重要。
    value = int(value)
    return (value << 1) if value >= 0 else (value << 1) ^ (~0)

def _proto_field(field: int, value: Any, kind: str) -> bytes:
    if value in (None, "", b"", 0, 0.0, False):
        return b""
    if kind == "sint32":
        return _varint((field << 3) | 0) + _varint(_sint(int(value), 32))
    if kind == "sint64":
        return _varint((field << 3) | 0) + _varint(_sint(int(value), 64))
    if kind == "float":
        return _varint((field << 3) | 5) + struct.pack("<f", float(value))
    if kind == "bytes":
        raw = bytes(value)
    elif kind == "string":
        raw = str(value).encode("utf-8")
    elif kind == "message":
        raw = bytes(value)
    else:
        raise ValueError(f"unknown protobuf field kind: {kind}")
    return _varint((field << 3) | 2) + _varint(len(raw)) + raw

def _proto(fields: list[tuple[int, Any, str]]) -> bytes:
    return b"".join(_proto_field(field, value, kind) for field, value, kind in fields)

def _encode_request() -> bytes:
    return _proto([
        (1, 111, "sint32"),
        (2, 10, "sint32"),
        (3, 694367, "sint32"),
        (5, 586952199, "sint32"),
    ])

def _encode_device(device: Mapping[str, Any]) -> bytes:
    fields = [
        (1, device.get("d1"), "sint32"), (2, device.get("collect_stat"), "sint32"),
        (3, device.get("aid"), "string"), (4, device.get("device_id"), "string"),
        (5, device.get("sec_device_token"), "string"), (6, device.get("app_version"), "string"),
        (7, device.get("battery"), "sint32"), (8, device.get("battery2"), "sint32"),
        (9, device.get("battery_health"), "sint32"), (10, device.get("battery_changed"), "sint32"),
        (11, device.get("network"), "string"), (12, device.get("tz"), "string"),
        (13, device.get("lan"), "string"), (14, device.get("cpu"), "sint32"),
        (15, device.get("resolution"), "string"), (16, device.get("sdcard"), "float"),
        (17, device.get("sdcard_used"), "float"), (18, device.get("memory"), "float"),
        (19, device.get("memory2"), "float"), (20, device.get("data"), "float"),
        (21, device.get("data_used"), "float"), (22, device.get("os_version"), "string"),
        (23, device.get("brightness"), "sint32"), (24, device.get("volume"), "sint32"),
        (25, device.get("ts"), "sint64"), (26, device.get("ts2"), "sint64"),
        (27, device.get("ts3"), "sint64"), (28, device.get("ts4"), "sint64"),
        (29, device.get("usb"), "sint32"), (30, device.get("hw_version"), "string"),
        (31, device.get("brand"), "string"), (32, device.get("board"), "string"),
        (33, device.get("product_name"), "string"), (34, device.get("product_device"), "string"),
        (35, device.get("product_manufacturer"), "string"), (36, device.get("hardware"), "string"),
        (38, device.get("unknown38"), "sint32"), (40, device.get("unknown40"), "sint32"),
    ]
    return _proto(fields)

def _encode_env(env: Mapping[str, Any]) -> bytes:
    fields = [
        (1, env.get("launch_time"), "sint32"), (2, env.get("unknown2"), "sint32"),
        (3, env.get("unknown3"), "sint32"), (5, env.get("unknown5"), "sint32"),
        (6, env.get("version"), "string"), (7, env.get("pid"), "sint32"),
        (12, _encode_device(env.get("device") or {}), "message"),
        (13, _proto([
            (1, (env.get("report") or {}).get("time"), "sint64"),
            (2, (env.get("report") or {}).get("state"), "sint32"),
            (4, (env.get("report") or {}).get("code"), "sint32"),
            (5, (env.get("report") or {}).get("times"), "sint32"),
            (6, (env.get("report") or {}).get("unknown6"), "sint32"),
        ]), "message"),
        (14, env.get("app_version"), "string"),
        (15, env.get("unknown15"), "sint32"), (16, env.get("unknown16"), "sint32"),
        (18, env.get("unknown18"), "sint32"), (19, env.get("unknown19"), "sint32"),
        (20, env.get("unknown20"), "sint32"), (21, env.get("unknown21"), "sint32"),
    ]
    return _proto(fields)

def _encode_medusa(values: Mapping[str, Any]) -> bytes:
    return _proto([
        (1, values.get("magic"), "bytes"), (2, values.get("version"), "sint32"),
        (3, values.get("rand"), "sint32"), (4, values.get("ms_app_id"), "string"),
        (5, values.get("device_id"), "string"), (6, values.get("license_id"), "string"),
        (7, values.get("app_version"), "string"), (8, values.get("sdk_version_str"), "string"),
        (9, values.get("sdk_version"), "sint32"), (10, values.get("xg_seed_bytes"), "bytes"),
        (12, values.get("time"), "sint32"), (13, values.get("query_body_ts_hash"), "bytes"),
        (14, values.get("query_sm3"), "bytes"), (15, _encode_request(), "message"),
        (16, values.get("sec_device_token"), "string"), (17, values.get("time2"), "sint32"),
        (18, values.get("lanusk_hash"), "bytes"), (19, values.get("query_body_hash_sm3"), "bytes"),
        (20, values.get("psk_version"), "string"), (21, values.get("call_type"), "sint32"),
        (23, _encode_env(values.get("env") or {}), "message"),
        (24, values.get("unknown24"), "string"), (26, values.get("original"), "string"),
    ])

def _json_body_md5(data: Any, data_type: str | None = None) -> str:
    if not data:
        return ""
    if isinstance(data, str):
        raw = data.encode("utf-8")
    elif isinstance(data, bytes):
        raw = data
    elif data_type == "application/json; charset=UTF-8":
        raw = json.dumps(data, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    else:
        raw = urlencode(data).encode("utf-8")
    return hashlib.md5(raw).hexdigest().upper()

def _url_encode(value: Mapping[str, Any]) -> str:
    return urlencode(value).replace("+", "%20").replace("%2A", "*")

def _get_params_encrypturl(url: str, params: Mapping[str, Any], devices: Mapping[str, Any]) -> tuple[str, dict[str, Any]]:
    result = dict(params)
    for key, value in devices.items():
        if key in result:
            result[key] = value
        elif key == "device_id" and "did" in result:
            result["did"] = value
    result["ts"] = int(time.time())
    result["_rticket"] = int(time.time() * 1000)
    return url.split("?", 1)[0] + "?" + _url_encode(result), result

def _xg_rc4(data: bytes, key: bytes) -> bytearray:
    table = list(range(256))
    j = 0
    for i in range(256):
        j = (j + table[i] + key[i % len(key)]) % 256
        table[i] = table[j]
    i = j = 0
    result = bytearray(len(data))
    for index, value in enumerate(data):
        i = (i + 1) & 0xFF
        x = table[i]
        j = (j + x) & 0xFF
        y = table[j]
        # 保持正式基线的 RC4 变体：这里只覆盖 S[i]，不交换 S[j]。
        table[i] = y
        result[index] = value ^ table[(y + y) & 0xFF]
    return result

def _reverse_bits(value: int) -> int:
    return int(f"{value:08b}"[::-1], 2)

def _encrypt_gorgon(body: Any, query: str, khronos: int, xg_rand: int, data_type: str) -> str:
    body_md5 = _json_body_md5(body, data_type).lower() if body else ""
    data = bytearray(hashlib.md5(query.encode()).digest()[:4])
    data += bytes.fromhex(body_md5)[:4] if body_md5 else b"\0\0\0\0"
    data += b"\0\0\0\0" + (67503104).to_bytes(4, "little") + khronos.to_bytes(4, "big")
    key = bytes((0x4A, 320 & 0xFF, 0x16, (xg_rand >> 8) & 0xFF, 0x47, 0x6C, 1, xg_rand & 0xFF))
    result = _xg_rc4(data, key)
    for index, value in enumerate(result):
        value = ((value >> 4) | (value << 4)) & 0xFF
        following = result[index + 1] if index + 1 < len(result) else result[0]
        result[index] = (~(_reverse_bits(following ^ value) ^ 20)) & 0xFF
    return (b"\x84\x04" + xg_rand.to_bytes(2, "little") + (320).to_bytes(2, "little") + result).hex()

def _ror64(value: int, count: int) -> int:
    count %= 64
    return ((value >> count) | (value << (64 - count))) & 0xFFFFFFFFFFFFFFFF

def _encrypt_helios(khronos: int, rand_value: int = 0) -> str:
    value = rand_value or random.randint(0, 0xFFFFFFFF)
    seed = value.to_bytes(4, "little") + b"8662"
    digest = hashlib.md5(seed).digest()
    keys = b"".join(f"{item:02x}".encode() for item in digest)
    table = [int.from_bytes(keys[:8], "little")]
    words = [int.from_bytes(keys[i:i + 8], "little") for i in range(0, 32, 8)]
    first, second = words[0], words[1]
    words = words[2:]
    for index in range(0x22):
        value2 = _ror64(second, 8)
        value2 = (value2 + first) & 0xFFFFFFFFFFFFFFFF
        value2 = (value2 ^ index) & 0xFFFFFFFFFFFFFFFF
        words.append(value2)
        value2 ^= _ror64(first, 61)
        value2 &= 0xFFFFFFFFFFFFFFFF
        table.append(value2)
        first, second = value2, words.pop(0)
    raw = (f"{khronos}-1588093228-8662").encode()
    pad = 16 - len(raw) % 16
    raw += bytes([pad]) * pad
    output = bytearray()
    for offset in range(0, len(raw), 16):
        left = int.from_bytes(raw[offset:offset + 8], "little")
        right = int.from_bytes(raw[offset + 8:offset + 16], "little")
        for index in range(0x22):
            right = (table[index] ^ (left + _ror64(right, 8))) & 0xFFFFFFFFFFFFFFFF
            left = (right ^ _ror64(left, 61)) & 0xFFFFFFFFFFFFFFFF
        output += left.to_bytes(8, "little") + right.to_bytes(8, "little")
    return base64.b64encode(value.to_bytes(4, "little") + output).decode()

def _gen_medusa_proto(url: str, url_params: Mapping[str, Any], devices: Mapping[str, Any], data: Any, khronos: int, data_type: str) -> tuple[bytes, bytes, bytes]:
    body_md5 = _json_body_md5(data, data_type).lower() if data else ""
    body_md5_bytes = bytes.fromhex(body_md5) if body_md5 else bytes(16)
    ts_bytes = khronos.to_bytes(4, "little")
    query = url.split("?", 1)[1] if "?" in url else ""
    query_sm3 = SM3(query).digest()
    query_body_hash = SM3(query.encode() + body_md5_bytes + b"none").digest()
    device_id = str(devices.get("device_id", url_params.get("device_id", url_params.get("did", ""))))
    version_name = str(devices.get("version_name", url_params.get("version_name", "7.1.3.32")))
    device_model = str(devices.get("device_model", url_params.get("device_type", "")))
    brand = str(devices.get("device_brand", url_params.get("device_brand", "")))
    sec_device_token = str(devices.get("sec_device_token") or "")
    device_sec_device_token = str(devices.get("device_sec_device_token") or "")
    proto_rand = random.randint(0, 0xFFFFFFFF)
    launch_time = random.randint(100, 120)
    process_id = random.randint(10001, 12000)
    # 这些字段是正式签名实现中的固定环境采样值，不是用户设备标识。
    report_ts = 1728388016635
    report_time = int(time.time())
    device = {
        "d1": 1, "collect_stat": 2, "aid": "8662", "device_id": device_id,
        "sec_device_token": device_sec_device_token,
        "app_version": "!noperm!", "battery": -888888, "battery2": -888888,
        "battery_health": 3, "battery_changed": -888888, "network": "!notset!",
        "tz": "Asia/Shanghai,8", "lan": "zh_CN", "cpu": 4,
        "sdcard": 255.24993896484375, "sdcard_used": 35.58599090576172,
        "memory": 3.467449188232422, "memory2": 3.467449188232422,
        "data": 255.1754913330078, "data_used": 42.17544174194336,
        "os_version": str(devices.get("os_version", url_params.get("os_version", ""))),
        "brightness": 41, "volume": 36, "ts": report_ts, "ts2": report_ts,
        "ts3": report_ts, "ts4": report_ts + 2, "usb": -1, "hw_version": device_model,
        "brand": brand, "board": device_model, "product_name": device_model,
        "product_device": str(devices.get("device_manufacturer", brand)),
        "product_manufacturer": brand, "hardware": brand, "unknown38": 31,
    }
    env = {
        "launch_time": launch_time, "unknown2": 146331399,
        "unknown3": 146331396, "unknown5": 7, "version": "v04.06.04.03-bugfix",
        "pid": process_id, "device": device,
        "report": {"time": report_time, "state": -2, "code": 200, "times": 0, "unknown6": 0},
        "app_version": version_name,
    }
    values = {
        "magic": b"\xf7\xe8_\xfa\xd7\xd7\xdc;\xd6*\xc8pW\xcfa\x18",
        "version": 3, "rand": proto_rand, "ms_app_id": "8662",
        "device_id": device_id, "license_id": "1588093228", "app_version": version_name,
        "sdk_version_str": "v04.06.04-ml-android", "sdk_version": 67503104,
        "xg_seed_bytes": (320).to_bytes(8, "little"), "time": khronos,
        "query_body_ts_hash": hash_f13(query_sm3, body_md5_bytes, ts_bytes, khronos),
        "query_sm3": query_sm3[:6], "sec_device_token": sec_device_token, "time2": khronos,
        "lanusk_hash": b"", "query_body_hash_sm3": query_body_hash, "psk_version": "none",
        "call_type": 312, "env": env,
        "unknown24": '{"cmr":16777216,"cmr2":16777216,"un_h":1879194040,"vpn":0,"kd":0,"fkd":3672518972,"pd":-1872573247,"dyn":"","do":0,"tk":true}',
    }
    return _encode_medusa(values), query_sm3, hash_f13(query_sm3, body_md5_bytes, ts_bytes, khronos)

def _xmxor_two(data: bytes, key: bytes) -> bytearray:
    encoded = bytearray(len(data))
    for index, value in enumerate(data):
        position = (index * 4) & 28
        d0, d1 = key[position], key[position + 1]
        d2 = (rl8(value, 4) + d0) ^ d1
        d2 = rl8((~d2) & 0xFF, 3)
        d2 = ((d2 + d1) & 0xFF) ^ d0
        encoded[-index - 1] = (~d2) & 0xFF
    return encoded

def _xmxor(data: bytes, key: bytes) -> bytearray:
    value = _xmxor_two(data, key)
    last_flag = value[-1] ^ value[-2]
    data0 = value[0]
    value[0] = (~last_flag + value[0]) & 0xFF
    value[1] = ((value[0] ^ value[-1] ^ 254) + value[1]) & 0xFF
    value[2] = (value[2] + ((last_flag - data0) ^ rl8(value[1], 3) ^ 2)) & 0xFF
    for index in range(len(value) - 4):
        temp = rl8(value[index + 2], 3) ^ value[index + 1] ^ (index + 3)
        value[index + 3] = (~temp + value[index + 3]) & 0xFF
    value[-1] ^= value[-2]
    value[0] = ((value[0] ^ value[1]) + sum(value[1:])) & 0xFF
    return value

def _gen_medusa(url: str, url_params: Mapping[str, Any], devices: Mapping[str, Any], data: Any, khronos: int, data_type: str) -> str:
    config_key = b"\xf1Y3vvn\xa9\x8d4\xf3\x1b\x05z\x9d[\xe4"
    config_iv = b"\x1f\xe1\t\xa4\x12R\x83\xf4\x18\xde\x9e\x05\x1a\x96\x9e\x12"
    sign_key = b"\x8e\xbd\xfa8\x06\xec\xc5\xce\xe7\x94#\xe6\x02\x9e\xd8%@\xbc\"\x18\xbb~\xae\xf7\x1c\xb6\x91\xf7\xaa\x8a\xa2\xf5"
    proto, query_sm3, body_sm3 = _gen_medusa_proto(url, url_params, devices, data, khronos, data_type)
    hash_rand = random.randint(0, 0xFFFFFFFF)
    xm_rand = random.randint(0, 0xFFFFFFFF)
    key, seed = get_key_hash(sign_key, hash_rand)
    mixed = _xmxor(proto, key)
    mixed = (320).to_bytes(8, "little") + mixed
    mixed = bytearray(mixed[::-1])
    for index in range(len(mixed)):
        mixed[index] ^= seed[~index & 3]
    hash_bytes = hash_rand.to_bytes(4, "little")
    check_bit = ((query_sm3[0] & 63) << 14) | 0x18000001 | ((body_sm3[0] & 63) << 8)
    mixed = b"\x35" + xm_rand.to_bytes(4, "little") + check_bit.to_bytes(4, "little") + mixed + hash_bytes[2:]
    mixed = AES_V3(config_key, khronos).encrypt(mixed, config_iv)
    version = bytes.fromhex("03 00 00 00 f7 e8 5f fa d7 d7 dc 3b d6 2a c8 70 57 cf 61 18")
    version_or = b"".join((int.from_bytes(version[i:i + 4], "little") ^ khronos).to_bytes(4, "little") for i in range(0, 20, 4))
    return base64.b64encode(version_or + hash_bytes[:2] + (256).to_bytes(2, "little") + mixed).decode()

def _core_sixgod(url: str, params: Mapping[str, Any], devices: Mapping[str, Any], data: Any, header: Mapping[str, Any]) -> tuple[dict[str, str], str]:
    data_type = str(header.get("content-type", header.get("Content-Type", "")))
    xg_rand = random.randint(0, 0xFFFF)
    encrypted_url, url_params = _get_params_encrypturl(url, params, devices)
    khronos = int(time.time())
    encoded_query = _url_encode(url_params)
    values = {
        "khronos": str(khronos),
        "ladon": base64.b64encode(khronos.to_bytes(4, "big")).decode(),
        "argus": base64.b64encode(khronos.to_bytes(4, "little")).decode(),
        "gorgon": _encrypt_gorgon(data, encoded_query, khronos, xg_rand, data_type),
        "helios": _encrypt_helios(khronos, 0),
        "medusa": _gen_medusa(encrypted_url, url_params, devices, data, khronos, data_type),
    }
    signs = {
        "x-ladon": values["ladon"], "x-khronos": values["khronos"],
        "x-argus": values["argus"], "x-gorgon": values["gorgon"],
        "x-helios": values["helios"], "x-medusa": values["medusa"],
    }
    if data:
        signs["x-ss-stub"] = _json_body_md5(data, data_type)
    result_headers = {str(key).lower(): str(value) for key, value in header.items()}
    result_headers.update(signs)
    if devices.get("ua"):
        result_headers["user-agent"] = str(devices["ua"])
    result_headers["x-tt-dt"] = str(devices.get("x_tt_dt", ""))
    return result_headers, encrypted_url

def _device_config(config: Mapping[str, Any]) -> dict[str, str]:
    device_id = _text(config.get("device_id"))
    install_id = _text(config.get("install_id"))
    if not device_id or not install_id:
        raise HongguoPluginError(
            "缺少红果 device_id/install_id 配置",
            code="HG_E_DEVICE",
            detail="device_id=%s install_id=%s" % (_hg_tail(device_id), _hg_tail(install_id)),
        )
    return {
        "device_id": device_id, "iid": install_id, "install_id": install_id,
        "device_brand": "Redmi", "device_model": "25053RT47C", "device_type": "25053RT47C",
        "device_manufacturer": "Xiaomi", "os_version": "16", "version_name": "7.1.3.32",
        "x_tt_dt": _text(config.get("x_tt_dt")),
        "sec_device_token": _text(config.get("sec_device_token")),
        "device_sec_device_token": _text(config.get("device_sec_device_token")),
        "ua": APP_UA,
    }

def _hiker_query(params: Mapping[str, Any]) -> str:
    """海阔视界 hgPhxQuery() 的等价实现：原样拼接，不做 URL 编码（resolution 里的 * 保留字面）。"""
    parts = []
    for key, value in params.items():
        parts.append("%s=%s" % (key, value))
    return "&".join(parts)


def _video_model(video_id: str, config: Mapping[str, Any], video_url: str | None = None,
                 sign_mode: str = "sixgod", single: bool = False) -> dict[str, Any]:
    devices = _device_config(config)
    params = {
        "iid": devices["install_id"],
        "device_id": devices["device_id"],
        "ac": "wifi",
        "channel": "update_64",
        "aid": "8662",
        "app_name": "novelread",
        "version_code": "71332",
        "version_name": "7.1.3.32",
        "device_platform": "android",
        "os": "android",
        "ssmix": "a",
        "device_type": "25053RT47C",
        "device_brand": "Redmi",
        "language": "zh",
        "os_api": "36",
        "os_version": "16",
        "manifest_version_code": "71332",
        "resolution": "1280*2772",
        "dpi": "520",
        "update_version_code": "71332",
        "host_abi": "arm64-v8a",
        "dragon_device_type": "phone",
        "pv_player": "71332",
        "compliance_status": "0",
        "need_personal_recommend": "1",
        "player_so_load": "1",
        "is_android_pad_screen": "0",
    }
    payload = {
        "biz_param": {
            "detail_page_version": 0,
            "device_level": 3,
            "disable_digg_stat": False,
            "need_all_video_definition": True,
            "need_mp4_align": False,
            "use_os_player": False,
            "use_server_dns": False,
            "video_platform": 1024,
        },
    }
    if single:
        # video_model/v1/（multi_ 停服后的现行接口）：顶层 video_id
        payload["video_id"] = video_id
    else:
        payload["mixed_video_id_map"] = {"1004": [video_id]}
    request_headers = {
        "User-Agent": APP_UA,
        "Accept": "application/json; charset=utf-8,application/x-protobuf",
        "Content-Type": "application/json; charset=UTF-8",
        "x-xs-from-web": "0",
        "x-ss-req-ticket": str(int(time.time() * 1000)),
        "x-tt-request-tag": "t=0;n=0",
        "sdk-version": "2",
        "passport-sdk-version": "50561",
        "x-vc-bdturing-sdk-version": "3.7.2.cn",
    }
    if devices.get("cookie"):
        request_headers["Cookie"] = devices["cookie"]
    endpoint = video_url or VIDEO_URL
    body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    if sign_mode == "profile":
        # 2026-11-24 移植：hongguo.js 官方 profile 签名（v04.10.03-ml-android）。
        # 用 profile 专用设备（注册/查询同为 73932 版本），注册失败时回退主链路设备号。
        _pdev = _hg_profile_device()
        if isinstance(_pdev, dict) and _pdev.get("device_id") and _pdev.get("install_id"):
            devices = dict(devices)
            devices.update(_pdev)
        signed_headers, signed_url = _profile_sign_request(endpoint, devices, body)
    elif sign_mode in ("hiker", "hiker_medusa"):
        # 2026-11-10 20:11 同机同网现场：海阔视界能播、狼壳空体。逐字比对两边请求，
        # 参数、UA、body 完全一致，唯一实质差异在签名头：
        #   海阔 FQ.signHeaders(qs, body, false, 8662, 1611921764) 只产出
        #     x-ladon / x-argus / x-ss-stub / x-khronos / x-ss-req-ticket；
        #   我们走 _core_sixgod，额外塞了 x-gorgon / x-medusa / x-helios / x-tt-dt
        #     这类视频接口并不认的六神签名。本函数按海阔那套只签 ladon+argus。
        query = _hiker_query(params)
        _hiker_sig = _dm_sign_headers(
            query,
            body,
            str(devices.get("device_id") or ""),
            str(devices.get("install_id") or ""),
            8662,
            1611921764,
        )
        signed_headers = {
            "User-Agent": APP_UA,
            "Accept": "application/json; charset=utf-8,application/x-protobuf",
            "Content-Type": "application/json",
            "x-xs-from-web": "0",
            "sdk-version": "2",
        }
        signed_headers.update(_hiker_sig)
        if sign_mode == "hiker_medusa":
            # 2026-11-16 实测：只发 ladon/argus 服务端回 200 空体，
            # 在同一 khronos 下再补一个 x-medusa（内联 _gen_medusa，
            # 与六神全套的区别是不发 x-gorgon / x-helios / x-tt-dt），
            # multi_video_model 立即回 19KB 真数据。生成失败时降级为纯海阔。
            try:
                _medusa_ts = int(_hiker_sig.get("x-khronos") or time.time())
                _medusa_url, _medusa_params = _get_params_encrypturl(endpoint, params, devices)
                signed_headers["x-medusa"] = _gen_medusa(
                    _medusa_url, _medusa_params, devices, payload, _medusa_ts, "application/json"
                )
            except Exception as exc:
                # 静默降级成纯海阔会直接导致 200 空体，必须留痕。
                _hg_diag("sign", "x-medusa 生成失败，降级为纯海阔",
                         code=_hg_err_code(exc), detail=exc)
        if devices.get("cookie"):
            signed_headers["Cookie"] = str(devices["cookie"])
        signed_url = endpoint + "?" + query
    else:
        signed_headers, signed_url = _core_sixgod(
            endpoint,
            params,
            devices,
            payload,
            request_headers,
        )
    started = time.time()
    _hg_diag(
        "req", "video_model",
        api=("single" if single else "multi"),
        sign=sign_mode,
        host=urlparse(endpoint).netloc,
        n=len(body),
        did=_hg_tail(devices.get("device_id")),
        cookie=("y" if devices.get("cookie") else "n"),
        x_tt_dt=("y" if devices.get("x_tt_dt") else "n"),
    )
    try:
        # 签名头只记「有没有」，不落值：日志会给用户看，不能带凭据。
        response = requests.post(
            signed_url,
            headers=signed_headers,
            data=body,
            timeout=30,
        )
    except Exception as exc:
        _hg_fail("video_model/req", exc,
                 api=("single" if single else "multi"), sign=sign_mode,
                 host=urlparse(endpoint).netloc, ms=_hg_ms(started))
        raise
    response_data = _json_response(response, stage="video_model")
    data = response_data.get("data") or {}
    if not isinstance(data, Mapping):
        raise HongguoPluginError("video_model 数据为空", code="HG_E_MODEL_EMPTY")
    entry: Any = data.get(video_id)
    if entry is None:
        for value in data.values():
            if isinstance(value, Mapping):
                entry = value
                break
            if isinstance(value, list) and value and isinstance(value[0], Mapping):
                entry = value[0]
                break
    if not isinstance(entry, Mapping):
        entry = data
    raw_model = entry.get("video_model") if isinstance(entry, Mapping) else None
    if raw_model is None:
        raw_model = data.get("video_model")
    if raw_model is None and ("video_list" in data or "dynamic_video_list" in data):
        raw_model = data  # video_model/v1/ 可能直接把播放模型铺在 data 顶层
    if isinstance(raw_model, str):
        try:
            raw_model = json.loads(raw_model)
        except ValueError as exc:
            raise HongguoPluginError("video_model JSON 无效", code="HG_E_NON_JSON") from exc
    if not isinstance(raw_model, Mapping):
        raise HongguoPluginError(
            "video_model 为空", code="HG_E_MODEL_EMPTY",
            detail="keys=" + ",".join(list(data.keys())[:8]),
        )
    model = dict(raw_model)
    try:
        rows = model.get("video_list") or model.get("dynamic_video_list") or []
        _hg_diag(
            "ok", "video_model",
            api=("single" if single else "multi"), sign=sign_mode,
            ms=_hg_ms(started), rows=(len(rows) if isinstance(rows, (list, tuple)) else 0),
            keys=len(model.keys()),
        )
    except Exception:
        pass
    return model

def _video_list_from_model(model: Mapping[str, Any]) -> Any:
    for key in ("video_list", "dynamic_video_list"):
        if model.get(key) is not None:
            return model[key]
    dynamic = model.get("dynamic_video")
    if isinstance(dynamic, Mapping):
        for key in ("dynamic_video_list", "video_list", "list"):
            if dynamic.get(key) is not None:
                return dynamic[key]
    video_info = model.get("video_info")
    if isinstance(video_info, Mapping):
        data = video_info.get("data")
        if isinstance(data, Mapping):
            return _video_list_from_model(data)
    data = model.get("data")
    if isinstance(data, Mapping):
        return _video_list_from_model(data)
    return None


_QUALITY_ORDER = ("2160", "1440", "1080", "720", "576", "540", "480", "360")

def _int(value: Any) -> int:
    match = re.search(r"\d+", _text(value))
    return int(match.group()) if match else 0

def _quality(value: Any) -> str:
    text = _text(value).lower()
    match = re.search(r"(2160|1440|1080|720|576|540|480|360)", text)
    return match.group(1) if match else "1080"

def _quality_hint(value: Any) -> str:
    """同 _quality，但识别不出时返回空串。
    不能一律兜底 '1080'：否则所有未标注清晰度的条目会合并到同一个 key 并互相覆盖，
    最终只剩最后一条，导致切任何清晰度拿到的都是同一条（甚至是没有视轨的那条）。"""
    text = _text(value).lower()
    match = re.search(r"(2160|1440|1080|720|576|540|480|360)", text)
    return match.group(1) if match else ""

def _definition_of(item: Mapping[str, Any]) -> str:
    """从一条播放模型条目里提取清晰度，尽量覆盖上游各种字段命名。"""
    if not isinstance(item, Mapping):
        return ""
    meta = item.get("video_meta")
    if not isinstance(meta, Mapping):
        meta = {}
    for value in (
        item.get("definition"),
        item.get("definition_code"),
        item.get("video_definition"),
        item.get("definition_type"),
        item.get("vheight"),
        item.get("height"),
        item.get("quality"),
        item.get("gear_name"),
        item.get("quality_name"),
        item.get("p"),
        meta.get("definition"),
        meta.get("vheight"),
        meta.get("height"),
        meta.get("quality"),
    ):
        hint = _quality_hint(value)
        if hint:
            return hint
    return ""

def _select_quality(video_list: Any, wanted: str = "1080") -> tuple[str, dict[str, Any]]:
    def rows_from(value: Any, hinted_quality: str = "") -> list[tuple[str, dict[str, Any]]]:
        if isinstance(value, list):
            result: list[tuple[str, dict[str, Any]]] = []
            for item in value:
                result.extend(rows_from(item, hinted_quality))
            return result
        if not isinstance(value, Mapping):
            return []
        if any(
            key in value
            for key in (
                "main_url",
                "backup_url",
                "backup_url_1",
                "play_addr",
                "spade_a",
                "encrypt_info",
            )
        ):
            return [(hinted_quality, dict(value))]
        result = []
        for key, item in value.items():
            if key in {"dynamic_video", "video_info", "data"} and isinstance(item, Mapping):
                result.extend(rows_from(item, hinted_quality))
                continue
            if key in {"video_list", "dynamic_video_list", "list"}:
                result.extend(rows_from(item, _quality_hint(key)))
                continue
            if isinstance(item, (Mapping, list)):
                result.extend(rows_from(item, _quality_hint(key)))
        return result

    candidates = rows_from(video_list)
    rows: dict[str, dict[str, Any]] = {}
    # 无法识别清晰度时用 idxN 兜底成唯一 key，保证每条候选都被保留（不再互相覆盖）
    for index, (hinted_quality, item) in enumerate(candidates):
        definition = _definition_of(item) or _quality_hint(hinted_quality) or ("idx%d" % index)
        # 同一清晰度出现多条（bvc2 + hvc1 ABR 变体）时，优先留下壳能解的那条，
        # 否则先到的 bvc2 会把可播的 hvc1 顶掉，表现为只有声音没有画面
        if definition not in rows or (
            _hg_entry_is_bytevc2(rows[definition]) and not _hg_entry_is_bytevc2(item)
        ):
            rows[definition] = item
    if not rows:
        raise HongguoPluginError("播放模型没有清晰度")
    requested = _quality(wanted)
    order = [requested] + [item for item in _QUALITY_ORDER if item != requested]
    for definition in order:
        if definition in rows:
            return definition, rows[definition]
    # 清晰度全部识别不出：按码率/体积降序，取质量最好的一条（而不是碰运气取最后一条）
    def _rank(key: str) -> int:
        item = rows[key]
        bitrate = _int(item.get("bitrate") or item.get("bit_rate") or 0)
        size = _int(item.get("size") or item.get("duration_ms") or 0)
        return bitrate * 1000000 + size
    definition = max(rows, key=_rank)
    return definition, rows[definition]

def _fallback_api_value(value: Any) -> str:
    if isinstance(value, Mapping):
        return _first(
            value.get("fallback_api"),
            value.get("url"),
            value.get("api"),
            value.get("data"),
        )
    if isinstance(value, (list, tuple)):
        for item in value:
            result = _fallback_api_value(item)
            if result:
                return result
        return ""
    text = _text(value)
    if text.startswith("{"):
        try:
            decoded = json.loads(text)
        except ValueError:
            decoded = {}
        if decoded:
            return _fallback_api_value(decoded)
    return text if len(text) > 10 else ""

def _decrypt_spade_url(value: str, key_seed: bytes) -> str:
    raw = _b64(value)
    if len(raw) < 20 or raw[0] != 0xA8 or raw[2:4] != b"\x01\x00":
        raise HongguoPluginError("spade URL 头无效")
    cipher_data = raw[4 : len(raw) - (len(raw) - 4) % 16]
    if not cipher_data:
        raise HongguoPluginError("spade URL 密文为空")
    constants = bytes.fromhex(
        "4dd4c2e6b83162090e52b3c7a6733ba4"
        "1cb2462b829ab58a196b39db57177524"
        "f49baf7f08e8d68d26a72e37c1a95a2f"
        "1f05a51892aef2949732b62a38aadd58"
    )
    first = hashlib.sha512(key_seed).digest()
    second = hashlib.sha512(first + constants).digest()
    plaintext = _aes_cbc_decrypt(second[:16], second[16:32], cipher_data)
    if plaintext:
        padding = plaintext[-1]
        if 1 <= padding <= 16 and padding <= len(plaintext):
            plaintext = plaintext[:-padding]
    return plaintext.rstrip(b"\0").decode("utf-8", errors="replace")

def _key_seed_from_model(model: Mapping[str, Any]) -> bytes:
    value = _text(model.get("key_seed"))
    if value:
        return _b64(value)
    for key in ("dynamic_video", "video_info", "data"):
        nested = model.get(key)
        if isinstance(nested, Mapping):
            result = _key_seed_from_model(nested)
            if result:
                return result
    return b""
def _page(url):
    last_err = None
    for attempt in range(2):
        try:
            # 复用线程本地 session（keep-alive），省掉每次新建连接 + TLS 握手的开销
            r = _hg_session().get(
                url,
                headers={
                    "Accept": "text/html,application/xhtml+xml;q=0.9,*/*;q=0.8",
                    "Cache-Control": "no-cache",
                },
                timeout=8,
            )
            if r.status_code != 200:
                raise HongguoPluginError(
                    "页面 HTTP %d" % r.status_code,
                    code=("HG_E_HTTP_4XX" if r.status_code < 500 else "HG_E_HTTP_5XX"),
                )
            r.encoding = r.encoding or "utf-8"
            if not r.text or "_ROUTER_DATA" not in r.text:
                raise HongguoPluginError(
                    "页面没有路由数据（%d 字节）" % len(r.text or ""),
                    code="HG_E_NON_JSON",
                )
            return r.text
        except Exception as err:
            last_err = err
            _hg_diag("page", "miss", n=attempt + 1, url=_hg_clean(url, 120),
                     code=_hg_err_code(err), detail=err)
            if attempt == 0:
                try:
                    time.sleep(0.3)
                except Exception:
                    pass
    if isinstance(last_err, HongguoPluginError):
        raise last_err
    raise HongguoPluginError("page fetch failed: %s" % last_err, code=_hg_err_code(last_err))

def _data(url):
    html = _page(url)
    m = re.search(r"(?:window\.)?_ROUTER_DATA\s*=\s*", html)
    if not m:
        return {}
    try:
        return json.JSONDecoder().raw_decode(html[m.end():])[0]
    except (ValueError, TypeError):
        return {}

def _item(x):
    x = x or {}
    vd = x.get("video_data") if isinstance(x.get("video_data"), dict) else x
    sid = str(
        vd.get("series_id")
        or x.get("series_id")
        or x.get("keyword")
        or vd.get("keyword")
        or ""
    )
    name = str(
        vd.get("series_title")
        or vd.get("series_name")
        or x.get("series_name")
        or x.get("name")
        or "未命名"
    )
    count = vd.get("episode_cnt") or x.get("episode_cnt") or 0
    try:
        if str(sid).isdigit() and count:
            _HG_STAMP[str(sid)] = int(count)
    except Exception:
        pass
    pic = str(vd.get("series_cover") or x.get("series_cover") or "")
    intro = str(vd.get("series_intro") or x.get("series_intro") or "")
    return {
        "vod_id": sid,
        "vod_name": name,
        "vod_pic": pic,
        "vod_remarks": ("全%s集" % count) if count else "",
        "vod_content": intro,
    }

def _cat_item(x):
    return _item(x)

# ===================== 分季 + 首页板块（本次改动） =====================
_HG_TAB_MAP = {
    "all": ("real-drama", u"热播短剧"),
    "human": ("real-drama", u"热播真人剧"),
    "comic": ("comic-drama", u"热播漫剧"),
}
_HG_SEASON_CACHE = {}
_HG_TRIM_SIDS = set()
# 列表页顺手记下的「官方当前集数」：分类/榜单/搜索的卡片都带 episode_cnt，
# 拿它当版本戳，官方加了集数，下次进详情就能立刻发现缓存过期（零额外请求）。
_HG_STAMP = {}

# ===================== 自动刷新（打开即刷新 + 后台轮询） =====================
_HG_SWR_AFTER = max(60.0, float(os.environ.get("HG_SWR_MIN", "30") or 30) * 60)
_HG_POLL_EVERY = max(300.0, float(os.environ.get("HG_POLL_MIN", "120") or 120) * 60)
_HG_POLL_MAX = 3
_HG_REFRESH_LOCK = threading.Lock()
_HG_REFRESHING = set()
_HG_POLL_STARTED = [False]


def _hg_refresh_one(sid):
    """重拉一部剧的详情 + 分季并写回缓存。「打开即刷新」和后台轮询共用。"""
    sid = str(sid or u"")
    if not sid.isdigit():
        return False
    with _HG_REFRESH_LOCK:
        if sid in _HG_REFRESHING:
            return False
        _HG_REFRESHING.add(sid)
    try:
        try:
            _HG_SEASON_CACHE.pop("sd:" + sid, None)
            _HG_SEASON_CACHE.pop("season:" + sid, None)
        except Exception:
            pass
        sd = _hg_sd(sid)
        if not sd:
            _hg_diag("refresh", "fail", sid=sid, why="详情拉取失败")
            return False
        seasons = _hg_seasons(sid, sd)
        _all = _hg_disk_load()
        _pl = {"v": 4, "ts": time.time(),
               "trim": 1 if sid in _HG_TRIM_SIDS else 0,
               "cnt": int(sd.get("episode_cnt") or 0),
               "self": _hg_slim(sd),
               "seasons": [{"no": no, "sd": _hg_slim(d)} for no, d in seasons]}
        _all[sid] = _pl
        for _no, _d in seasons:
            _xid = str(_d.get("series_id") or u"")
            if _xid and _xid != sid:
                _all[_xid] = _pl
        _hg_disk_save(_all)
        _hg_diag("refresh", "ok", sid=sid, cnt=_pl["cnt"], seasons=len(seasons))
        return True
    except Exception as exc:
        _hg_diag("refresh", "fail", sid=sid, err=type(exc).__name__)
        return False
    finally:
        with _HG_REFRESH_LOCK:
            _HG_REFRESHING.discard(sid)


def _hg_refresh_async(sid):
    """后台刷新：不阻塞当前这次打开。"""
    def _run():
        try:
            _hg_refresh_one(sid)
        except Exception:
            pass
    try:
        t = threading.Thread(target=_run, name="hg-refresh")
        t.daemon = True
        t.start()
    except Exception:
        pass


def _hg_poll_once():
    """轮询一轮：把缓存里超过轮询间隔的剧各刷一遍（每次最多 3 部）。"""
    due = []
    for sid, pl in list(_hg_disk_load().items()):
        if not isinstance(pl, dict):
            continue
        ts = float(pl.get("ts") or 0)
        if ts and time.time() - ts > _HG_POLL_EVERY:
            due.append((ts, sid))
    due.sort()
    done = 0
    for _ts, sid in due[:_HG_POLL_MAX]:
        if _hg_refresh_one(sid):
            done += 1
    if due:
        _hg_diag("poll", "round", due=len(due), done=done)
    return done


def _hg_poll_start():
    """后台轮询线程：只在本进程里起一次；HG_POLL=0 关掉。"""
    if str(os.environ.get("HG_POLL", "") or "").strip() in ("0", "false", "no", "off"):
        return
    with _HG_REFRESH_LOCK:
        if _HG_POLL_STARTED[0]:
            return
        _HG_POLL_STARTED[0] = True

    def _loop():
        while True:
            try:
                time.sleep(_HG_POLL_EVERY)
                _hg_poll_once()
            except Exception:
                time.sleep(600)

    try:
        t = threading.Thread(target=_loop, name="hg-poll")
        t.daemon = True
        t.start()
        _hg_diag("poll", "start", every_min=int(_HG_POLL_EVERY / 60))
    except Exception:
        pass
_HG_SEARCH_API = SITE + "/api/search/result/"
_HG_SEASON_RE = re.compile(u"第\\s*([0-9]{1,3}|[一二三四五六七八九十]{1,3})\\s*[季部]")
# 标题结尾的裸数字也当季号（如「……我终于发达了7」），数字前不能紧跟数字，避免把年份 1980 当季号
_HG_TAIL_RE = re.compile(u"(?:[\\s·\\-—_：:.、]+)?(?<![0-9])([0-9]{1,3}|[一二三四五六七八九十]{1,3})\\s*$")
# 「反向拿捏2：和闺蜜穿七零带着婆婆一起离」这类：季号贴在主标题末尾、后面接冒号副标题。
# 只看冒号前的主标题尾部，1~2 位阿拉伯数字或半/全角括号数字；数字前不能紧跟数字（防 1980、2024）
_HG_MAIN_TAIL_RE = re.compile(u"(?:[\\s·\\-—_]*)(?:[（(]\\s*([0-9]{1,2})\\s*[)）]|(?<![0-9])([0-9]{1,2}))\\s*$")
# 「…刚下刑场你让我去考试一季 / 二季」这种省略「第」的写法：数字+季 收尾。
# 只在结尾认，且前面至少留 4 个字当基名，避免把「人间四季」这类片名当第 4 季
_HG_TAIL_SEASON_RE = re.compile(u"(?<![0-9一二三四五六七八九十])([0-9]{1,3}|[一二三四五六七八九十]{1,3})\\s*季\\s*$")
_HG_CN = u"零一二三四五六七八九十"


def _hg_cn(n):
    try:
        n = int(n)
    except Exception:
        return str(n)
    if n <= 10:
        return _HG_CN[n]
    if n < 20:
        return u"十" + _HG_CN[n % 10]
    if n < 100:
        return _HG_CN[n // 10] + u"十" + (_HG_CN[n % 10] if n % 10 else u"")
    return str(n)


def _hg_num(t):
    t = str(t or "")
    if t.isdigit():
        return int(t)
    if t == u"十":
        return 10
    if t.startswith(u"十"):
        return 10 + (_HG_CN.index(t[1]) if len(t) > 1 and t[1] in _HG_CN else 0)
    if u"十" in t:
        a, _, b = t.partition(u"十")
        return _HG_CN.index(a) * 10 + (_HG_CN.index(b) if b and b in _HG_CN else 0)
    return _HG_CN.index(t) if t in _HG_CN else 0


def _hg_season_no(name):
    m = _HG_SEASON_RE.search(name or "")
    if m:
        return _hg_num(m.group(1))
    ts = _HG_TAIL_SEASON_RE.search(name or "")
    if ts and len((name or u"").strip()) - len(ts.group(0)) >= 4:
        n = _hg_num(ts.group(1))
        return n if 0 < n <= 99 else 0
    t = _HG_TAIL_RE.search(name or "")
    if t:
        n = _hg_num(t.group(1))
        return n if 0 < n <= 99 else 0
    # 冒号副标题写法：季号在主标题末尾（第一部没有数字，按第一季处理）
    main, sub = _hg_split_title(name)
    if sub:
        mm = _HG_MAIN_TAIL_RE.search(main)
        if mm:
            n = int(mm.group(1) or mm.group(2) or 0)
            return n if 0 < n <= 99 else 0
    return 0


def _hg_bare_style(name):
    """True 表示这部剧的季号是裸数字写法（标题里没有「第N季/部」）。"""
    return not _HG_SEASON_RE.search(name or u"")


def _hg_split_title(name):
    """按第一个冒号拆成（主标题, 副标题）；没有冒号时副标题为空串。"""
    raw = (name or u"").strip()
    for sep in (u"：", u":"):
        i = raw.find(sep)
        if 0 < i < len(raw) - 1:
            return raw[:i].strip(), raw[i + 1:].strip()
    return raw, u""


def _hg_main_style(name):
    """「主标题+季号：副标题」写法里剥掉季号的主标题；不适用时返回空串。

    只认这种形状：没有「第N季/部」、整个标题末尾没有裸数字（那是「道印入体：…7」
    的写法，季号挂在副标题后面）、冒号前的主标题 4~12 个字。这样普通带副标题的剧
    不会被拉去多探两轮。
    """
    raw = (name or u"").strip()
    main, sub = _hg_split_title(raw)
    if not sub or not (4 <= len(main) <= 12):
        return u""
    if _HG_SEASON_RE.search(raw) or _HG_TAIL_RE.search(raw):
        return u""
    mn = _HG_MAIN_TAIL_RE.sub(u"", main).strip(u"：:·-—_ 　")
    if mn == main and re.search(u"[0-9]", main[-2:]):
        # 主标题自己就以数字结尾（重生1980、2024 这类），不是季号写法
        return u""
    return mn


def _hg_probe_kws(base, n, name):
    """缺失季的探测关键词。主标题带季号的写法要按原样拼，只搜基名搜不到。"""
    if _HG_TAIL_SEASON_RE.search(name or u""):
        # 「…考试一季」这类省略「第」的：兄弟季叫「…考试二季」，不是「…考试第2季」
        return [base + _hg_cn(n) + u"季", base + u"第" + _hg_cn(n) + u"季"]
    mn = _hg_main_style(name)
    if mn:
        main, sub = _hg_split_title(name)
        if _HG_MAIN_TAIL_RE.search(main):
            # 手上已是第 N 部（主标题自带数字）：另一部靠基名搜索就能带出来，不必再探
            return []
        return [mn + str(n) + u"：" + sub]
    if _hg_bare_style(name):
        # 两种命名站上都有：正文多写「第N季」，也有裸数字结尾的，各探一次（都受 9s 预算约束）
        return [base + u"第%s季" % _hg_cn(n), base + str(n)]
    return [base + u"第%s季" % _hg_cn(n)]


def _hg_base_name(name):
    raw = (name or u"").strip()
    b = _HG_SEASON_RE.sub(u"", raw).strip(u"：:·-—_ 　")
    if b == raw:
        # 裸数字结尾：剥掉数字再当基名，基名不足 4 个字就不剥（防「重生1980」这类误伤）
        b2 = _HG_TAIL_RE.sub(u"", raw).strip(u"：:·-—_ 　")
        if len(b2) >= 4 and b2 != raw:
            b = b2
    if b == raw:
        # 「…你让我去考试一季 / 二季」：省略「第」的季号写法
        b3 = _HG_TAIL_SEASON_RE.sub(u"", raw).strip(u"：:·-—_ 　")
        if len(b3) >= 4 and b3 != raw:
            b = b3
    if len(b) < 4:
        return u""
    return b


def _hg_group_id(sd):
    si = sd.get("season_info") if isinstance(sd, dict) else None
    if isinstance(si, dict):
        g = si.get("series_group_id")
        if g:
            return str(g)
    return u""


_HG_TLS = threading.local()


def _hg_session():
    """每线程复用一条 requests 会话：keep-alive + gzip，省握手开销。"""
    ses = getattr(_HG_TLS, "ses", None)
    if ses is None:
        ses = requests.Session()
        ses.trust_env = False
        ses.headers.update({
            "User-Agent": UA,
            "Referer": SITE + "/",
            "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8",
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Accept-Encoding": "gzip, deflate",
        })
        _HG_TLS.ses = ses
    return ses


def _hg_fetch_sd(sid, timeout=8):
    """单次请求拉详情（不重试），失败返回 {}。"""
    started = time.time()
    try:
        r = _hg_session().get(SITE + "/detail?series_id=" + quote(str(sid), safe=u""), timeout=timeout)
        if r.status_code != 200:
            _hg_fail("detail/http", HongguoPluginError(
                "详情页 HTTP %d" % r.status_code,
                code=("HG_E_HTTP_4XX" if r.status_code < 500 else "HG_E_HTTP_5XX")),
                sid=sid, n=len(r.content or b""), ms=_hg_ms(started))
            return {}
        j = _router_data(r.text)
        p = ((j.get(u"loaderData") or {}).get(u"detail_page") or {}) if isinstance(j, dict) else {}
        data = p.get(u"seriesDetail") or {}
        if not data:
            _hg_fail("detail/empty", HongguoPluginError(
                "详情页没有 seriesDetail", code="HG_E_MODEL_EMPTY"),
                sid=sid, n=len(r.text or ""), ms=_hg_ms(started))
        return data
    except Exception as exc:
        _hg_fail("detail/fetch", exc, sid=sid, ms=_hg_ms(started))
        return {}


# 分季详情缓存：**只放进程内**，按用户要求不在设备本地建 json 文件。
# 原来这里落盘 hg_seasons_cache.json（6h/24h 跨进程缓存），现在改成内存表：
# 进程存活期间详情/分季仍然零请求复用，进程重启后重新拉一次，不留任何本地文件。
_HG_DISK_MEM: dict[str, Any] = {}


def _hg_slim(sd):
    """只留拼线路要用的字段，控制缓存文件体积。"""
    if not isinstance(sd, dict):
        return {}
    cele = [str(c.get("nickname") or "") for c in (sd.get("celebrities") or []) if isinstance(c, dict)]
    return {
        "series_id": str(sd.get("series_id") or ""),
        "series_name": str(sd.get("series_name") or ""),
        "series_cover": str(sd.get("series_cover") or ""),
        "series_intro": str(sd.get("series_intro") or ""),
        "episode_right_text": str(sd.get("episode_right_text") or ""),
        "episode_cnt": sd.get("episode_cnt") or 0,
        "tags": sd.get("tags") if isinstance(sd.get("tags"), list) else [],
        "celebrities": [{"nickname": n} for n in cele if n],
        "vid_list": [str(x) for x in (sd.get("vid_list") or [])],
        "season_info": sd.get("season_info") if isinstance(sd.get("season_info"), dict) else {},
    }


# ---- 本地缓存文件（默认开；HG_CACHE_FILE=0 回到纯内存） ----
_HG_CACHE_FILE_ON = str(os.environ.get("HG_CACHE_FILE", "1") or "").strip().lower() not in (
    "0", "false", "no", "off")
try:
    _HG_CACHE_MAX_BYTES = max(256, int(os.environ.get("HG_CACHE_MAX_KB", "4096") or 4096)) * 1024
except (TypeError, ValueError):
    _HG_CACHE_MAX_BYTES = 4 * 1024 * 1024
_HG_CACHE_LOADED = [False]
_HG_CACHE_LAST = [0.0]
_HG_CACHE_N = [0]


def _hg_store_path():
    """分季缓存文件：和日志同目录，/sdcard/Download/hg_cache.json（不可写则由 _hg_diag_dir 兜底）。"""
    try:
        d = _hg_diag_dir()
    except Exception:
        d = ""
    return os.path.join(d, "hg_cache.json") if d else ""


def _hg_cache_read():
    p = _hg_store_path()
    if not p:
        return {}
    try:
        with open(p, "r", encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        return {}
    except Exception as exc:
        _hg_diag("cache", "load-fail", err=type(exc).__name__)
        return {}
    if not isinstance(data, dict):
        return {}
    out = {}
    now = time.time()
    for k, v in data.items():
        if not isinstance(v, dict) or v.get("v") != 4:
            continue
        ts = float(v.get("ts") or 0)
        if not ts:
            continue
        # 用和 detailContent 同一套有效期判断，过期条目干脆不带进来
        ttl = 600 if v.get("trim") else (12 * 3600 if len(v.get("seasons") or []) > 1 else 2 * 3600)
        if now - ts < ttl:
            out[str(k)] = v
    return out


def _hg_cache_write(mem, force=False):
    """原子写：先写 .tmp 再 replace，写一半断电也不会留坏文件。"""
    if not _HG_CACHE_FILE_ON:
        return
    p = _hg_store_path()
    if not p:
        return
    now = time.time()
    grew = len(mem) > _HG_CACHE_N[0]
    if not force and not grew and now - _HG_CACHE_LAST[0] < 120:
        return
    try:
        items = sorted(mem.items(), key=lambda kv: kv[1].get("ts", 0), reverse=True)
        blob = json.dumps(dict(items), ensure_ascii=False, separators=(",", ":"))
        if len(blob.encode("utf-8")) > _HG_CACHE_MAX_BYTES:
            # 超限：按时间从旧到新砍掉四分之一再序列化一次
            keep = dict(items[:max(1, int(len(items) * 0.75))])
            blob = json.dumps(keep, ensure_ascii=False, separators=(",", ":"))
        tmp = p + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(blob)
        os.replace(tmp, p)
        _HG_CACHE_LAST[0] = now
        _HG_CACHE_N[0] = len(mem)
        _hg_diag("cache", "save", n=len(mem), kb=int(len(blob.encode("utf-8")) / 1024) + 1)
    except Exception as exc:
        _hg_diag("cache", "save-fail", err=type(exc).__name__, path=p)


def _hg_disk_load():
    """分季缓存：进程内为主；首次调用时从本地 hg_cache.json 捞回上次的内容。"""
    try:
        if not _HG_CACHE_LOADED[0]:
            _HG_CACHE_LOADED[0] = True
            if _HG_CACHE_FILE_ON:
                try:
                    disk = _hg_cache_read()
                except Exception:
                    disk = {}
                if disk:
                    for k, v in disk.items():
                        _HG_DISK_MEM.setdefault(k, v)
                    _HG_CACHE_N[0] = len(_HG_DISK_MEM)
                    _hg_diag("cache", "load", n=len(disk), path=_hg_store_path())
        return _HG_DISK_MEM
    except Exception:
        return {}


def _hg_disk_save(all_data):
    """写进程内缓存，并按需落盘（默认开，HG_CACHE_FILE=0 关闭）。"""
    try:
        items = sorted(all_data.items(), key=lambda kv: kv[1].get("ts", 0), reverse=True)[:120]
        new = dict(items)
    except Exception:
        return
    _HG_DISK_MEM.clear()
    _HG_DISK_MEM.update(new)
    try:
        _hg_cache_write(_HG_DISK_MEM)
    except Exception:
        pass


def _hg_sd(sid):
    """单部详情：进程缓存 300s（失败 60s）→ 网络单次请求。"""
    key = u"sd:" + str(sid)
    hit = _HG_SEASON_CACHE.get(key)
    if hit and time.time() - hit[0] < 300:
        return hit[1]
    sd = _hg_fetch_sd(sid)
    if not sd:
        sd = {}
        _HG_SEASON_CACHE[key] = (time.time() - 240, sd)   # 失败短缓存 60 秒
        _trim_store(_HG_SEASON_CACHE, cap=256)
        return sd
    _HG_SEASON_CACHE[key] = (time.time(), sd)
    _trim_store(_HG_SEASON_CACHE, cap=256)
    return sd


def _hg_candidates(kw, pages=2, deadline=None):
    """站内搜索取候选 (sid, name)，只认 query 参数，看 hasMore 翻页。"""
    out = []
    seen = set()

    def _page(pg):
        try:
            return _search_api(kw, pg) or {}
        except Exception:
            return {}

    # 多页时两页一起发（基名搜索固定翻 2 页，串行等于白等一个往返）
    if pages > 1 and (deadline is None or time.time() <= deadline):
        try:
            with concurrent.futures.ThreadPoolExecutor(max_workers=min(3, pages)) as _ex:
                _pgs = list(_ex.map(_page, range(1, pages + 1)))
        except Exception:
            _pgs = [_page(1)]
    else:
        _pgs = [_page(1)]
    for d in _pgs:
        rows = d.get(u"searchList") or []
        for it in rows:
            vd = it.get(u"video_data") if isinstance(it.get(u"video_data"), dict) else it
            sid = str(vd.get(u"series_id") or it.get(u"series_id") or u"")
            if not sid.isdigit() or sid in seen:
                continue
            seen.add(sid)
            out.append((sid, str(it.get(u"name") or vd.get(u"series_title") or u"")))
            if len(out) >= 40:
                return out
        if not d.get(u"hasMore"):
            break
    return out


def _hg_probe_first(kws, n=None):
    """按顺序试探测关键词，命中即停。

    「第N季」和「N季」两种写法各发一次搜索时，实测两边返回的是同一批剧，
    一半请求是重复的；这里改成：谁先返回「带这一季号码的条目」就停。
    但如果所有写法都只有别的季号（比如真身叫「…2」而先试的「…二季」只回了诱饵），
    就继续试下一种写法，避免为了省请求把真季漏掉。
    """
    first = []
    for kw in kws or []:
        try:
            rows = _hg_candidates(kw, 1, time.time() + 3)
        except Exception:
            rows = []
        if rows and not first:
            first = rows
        if not rows or n is None:
            continue
        for _sid, nm in rows:
            if _hg_season_no(nm) == n:
                return rows
    return first




_HG_PRE_LOCK = threading.Lock()
_HG_PRE_RUNNING = [0]
_HG_PRE_MAX = 3


def _hg_prefetch(sids, limit=3, seasons=True):
    """后台预热：给刚出现的 series_id 预拉详情写缓存。绝不阻塞调用方，异常全吞。

    seasons=False 时只热详情（进程内 300 秒），不跑分季合并。分类/榜单翻一页
    就有 20 条，如果每条都跑「详情 + 基名搜索 2 页 + 补探 + 兄弟季详情」，
    等于后台同时点开好几部剧，翻三五页就是几十个请求。
    """
    if not sids:
        return
    todo = [str(x) for x in sids if str(x).isdigit()][:limit]
    if not todo:
        return
    try:
        disk = _hg_disk_load()
    except Exception:
        disk = {}

    def _run():
        for sid in todo:
            with _HG_PRE_LOCK:
                if _HG_PRE_RUNNING[0] >= _HG_PRE_MAX:
                    return
                _HG_PRE_RUNNING[0] += 1
            try:
                c = disk.get(sid)
                if isinstance(c, dict):
                    continue
                if not seasons:
                    # 只热详情：不写分季 payload，避免把「只有一季」锁进缓存
                    _hg_sd(sid)
                    continue
                sd = _hg_sd(sid)
                if not sd:
                    continue
                _ses = _hg_seasons(sid, sd)
                _all = _hg_disk_load()
                # 这里必须和 detailContent 读缓存的版本号一致（都认 v4），
                # 之前写 v3，于是首页/榜单的后台预取全部被判过期，白跑一遍。
                _pl = {"v": 4, "ts": time.time(),
                       "cnt": int(sd.get("episode_cnt") or 0), "self": _hg_slim(sd),
                       "seasons": [{"no": no, "sd": _hg_slim(d)} for no, d in _ses]}
                _all[sid] = _pl
                for _no, _d in _ses:
                    _xid = str(_d.get("series_id") or u"")
                    if _xid and _xid != sid:
                        _all[_xid] = _pl
                _hg_disk_save(_all)
            except Exception:
                pass
            finally:
                with _HG_PRE_LOCK:
                    _HG_PRE_RUNNING[0] -= 1

    try:
        t = threading.Thread(target=_run, name="hg-prefetch")
        t.daemon = True
        t.start()
    except Exception:
        pass


_HG_OVR_CACHE = {"ts": 0.0, "data": {}}


def _hg_season_override():
    """手工分季表 hg_seasons.json：站点没把几季挂在同一组时，用它强行合并。

    文件放在日志同目录或 /sdcard/Download，格式：
        {"重生70猎户带妻女吃香喝辣": ["7691625956405939262", "7676505795629943832"]}
    键可以是剧名、去掉季号后的基名，或当前 series_id；值是同属一部剧的 series_id 列表。
    60 秒内只读一次盘；文件不存在或写错就当没有，不影响正常合并。
    """
    now = time.time()
    if now - _HG_OVR_CACHE["ts"] < 60:
        return _HG_OVR_CACHE["data"]
    data = {}
    dirs = []
    try:
        d = _hg_diag_dir()
        if d:
            dirs.append(d)
    except Exception:
        pass
    dirs.append("/sdcard/Download")
    for root in dirs:
        path = os.path.join(root, "hg_seasons.json")
        try:
            with open(path, "r", encoding="utf-8") as fh:
                raw = json.load(fh)
        except Exception:
            continue
        if isinstance(raw, dict):
            data = raw
            break
    _HG_OVR_CACHE["ts"] = now
    _HG_OVR_CACHE["data"] = data
    return data


def _hg_seasons(sid, sd, budget=9.0):
    """真分季：基名搜索一页 + 缺失季定向探测；探测与拉详情同池并发，命中即收敛。

    预算分两级：已经拿到 2 季以上就按软预算（5 秒）收工——够用了，别让壳里干等；
    还只有单季说明线索没找齐，才继续用硬预算（9 秒）。被截断的结果只缓存 2 分钟，
    下次进来会用完整体预算再跑一遍补全，不会把「少一季」锁住。
    """
    ck = u"season:" + str(sid)
    hit = _HG_SEASON_CACHE.get(ck)
    if hit and time.time() - hit[0] < 900:
        return hit[1]
    # 2026-11-24 移植官方取季（合并季数以官方为准）：plan/v + cell/change 精确拿到
    # 这部剧的全部季（季号/series_id/集数），比基名搜索猜季可靠——不再漏季、
    # 也不会把「…夺宝篇」这类番外错并进来。官方没给或详情补不齐时回退原有探测。
    try:
        _off = _hg_official_seasons_merged(sid, budget)
    except Exception as _exc:
        _hg_diag("season", "official-miss", sid=sid, code=_hg_err_code(_exc))
        _off = []
    if _off:
        return _off
    gid = _hg_group_id(sd)
    base = _hg_base_name(sd.get("series_name") or u"")
    if not base:
        return [(0, sd)]
    _t_start = time.time()
    t_end = _t_start + budget
    _nm0 = sd.get("series_name") or u""
    _bare = _hg_bare_style(_nm0)
    # 「反向拿捏2：副标题」这类写法的主标题；非空才值得多探一轮
    _main_ref = _hg_main_style(_nm0)
    _hg_diag("season", "start", sid=sid, name=_hg_clean(_nm0, 30), gid=gid or "-",
             base=_hg_clean(base, 30), sno=_hg_season_no(_nm0))
    if not gid:
        if _hg_season_no(_nm0) < 1 and not _main_ref:
            # 没有组号、标题里也没有季号线索：只靠搜索猜「哪几部是同一部剧」
            # 会把「…夺宝篇」「…封神」这类番外并进来，所以保持单线路。
            # 真要合并，写 hg_seasons.json 显式指定 series_id。
            _hg_diag("season", "single", sid=sid, gid="-", base=_hg_clean(base, 30),
                     found=0, ms=0, why="没有组号且标题无季号（可用 hg_seasons.json 指定）")
            return [(0, sd)]
        # 标题写了「第一季」却没有组号：只给一小段预算去找第二季，别让打开详情变慢
        budget = min(budget, 4.5)
        t_end = min(t_end, _t_start + budget)

    def _same_group(d):
        """同一部剧的判据：两边都有组号就认组号；一边缺组号时退到「基名一致 + 明确季号」。

        站点只有部分条目带 season_info（series_group_id），另一半没有。旧逻辑
        只要当前这部缺组号就直接放弃合并，于是「第二季/第三季」永远进不了播放线路。
        """
        if not isinstance(d, Mapping):
            return False
        if str(d.get("series_id") or u"") == str(sid):
            return True
        g = _hg_group_id(d)
        if gid and g:
            return g == gid
        b = _hg_base_name(d.get("series_name") or u"")
        if not b or not base or b != base:
            return False
        if gid or g:
            # 一边有组号、一边没有：同基名就认，否则「缺组号的那一季」永远合不进来
            return True
        # 两边都没有组号：只认标题里明确写了 第N季/第N部 的，避免把「…夺宝篇」这类番外并进来
        return _hg_season_no(d.get("series_name") or u"") >= 1

    known = {(_hg_season_no(_nm0) or 1): str(sid)}
    extra = []
    try:
        _cand = _hg_candidates(base, 2, time.time() + min(4.5, budget))
        _hg_diag("season", "search", sid=sid, base=_hg_clean(base, 30), gid=gid or "-",
                 n=len(_cand))
        for csid, nm in _cand:
            # 基名不同的（「…罪名不朽」「…考试啊」这类同前缀的别的剧）不占季号名额，
            # 只留一条当备选。否则搜索里每冒出一部，就要多拉一次详情，
            # 拉回来又被组号否掉、季号被释放、再补探，来回烧请求。
            if _hg_base_name(nm) != base:
                extra.append(csid)
                continue
            n = _hg_season_no(nm)
            # 同一主标题、没有季号的那一部就是第一部
            if not n and _main_ref and _hg_main_style(nm) == _main_ref:
                n = 1
            if n and n not in known:
                known[n] = csid
            elif not n:
                extra.append(csid)
    except Exception:
        pass
    found = {str(sid): sd}
    pending = {}
    probed = set()
    _soft_end = _t_start + min(5.0, budget)
    _trimmed = [False]

    def _expired():
        """到点没有：已有多季走软预算，只有单季走硬预算。"""
        now = time.time()
        if len(found) >= 2:
            if now >= _soft_end:
                _trimmed[0] = True
                return True
            return False
        return now >= t_end
    with concurrent.futures.ThreadPoolExecutor(max_workers=12) as ex:
        for cid in list(known.values()) + extra[:1]:
            if cid != str(sid) and cid not in found and cid not in pending:
                pending[ex.submit(_hg_sd, cid)] = (u"detail", cid)
        while pending and not _expired():
            done = None
            try:
                done, _ = concurrent.futures.wait(list(pending), timeout=0.1,
                                                  return_when=concurrent.futures.FIRST_COMPLETED)
            except Exception:
                break
            for f in done:
                kind, key = pending.pop(f)
                try:
                    val = f.result(timeout=0.1)
                except Exception:
                    val = None
                if kind == u"detail":
                    if val:
                        found[key] = val
                        # 同名诱饵（标题像第 N 季但其实是别的剧）抓进来了：
                        # 释放这一季的名额，让下面的缺口探测重新去找真身
                        if str(key) != str(sid) and not _same_group(val):
                            for _k, _v in list(known.items()):
                                if str(_v) == str(key):
                                    known.pop(_k, None)
                else:
                    for csid, nm in (val or [])[:4]:
                        if _hg_season_no(nm) == key and csid not in found and csid not in known.values():
                            known[key] = csid
                            pending[ex.submit(_hg_sd, csid)] = (u"detail", csid)
                            break
            # 缺失季：1..max+1 里没着落的，补探测（每轮最多 4 个）
            # 已从搜索里认到季号、详情还在路上的，也算有着落，不再重复探同一季
            _ver = set(x for x in known.keys() if x)
            for _k, _d in found.items():
                if _d and _same_group(_d):
                    _ver.add(_hg_season_no(_d.get(u"series_name") or u""))
            # 原逻辑只在「标题带季号 / 搜索已带回兄弟季」时才补探，于是
            # 「组号在、但第二季没进搜索首页」的剧就只剩第一季。有组号时补探是安全的
            # （下面用组号过滤诱饵），所以放宽；但为了不给单季剧拖时间，只补探 1 个。
            _gate = (len(_ver) >= 2 or _hg_season_no(_nm0) > 0 or bool(_main_ref))
            if (len(probed) < 9 and not _expired() and (_gate or bool(gid))):
                mx = max(_ver) if _ver else 1
                _nums = [x for x in range(1, mx + 2) if x not in _ver and x not in probed]
                if _hg_season_no(_nm0) == 0:
                    # 当前是「无季号」那条：先探第2季，别把唯一一次补探花在第1季上
                    _nums.sort(key=lambda x: (x == 1, x))
                for n in _nums[:(4 if _gate else 1)]:
                    probed.add(n)
                    pending[ex.submit(_hg_probe_first,
                                      _hg_probe_kws(base, n, _nm0), n)] = (u"probe", n)
    # 收尾补漏：诱饵被剔除后总会留下空洞，按缺的季号再定向探一次（最多 2 个）
    _have = set()
    for _x, _d in found.items():
        if _d and _same_group(_d):
            _have.add(_hg_season_no(_d.get(u"series_name") or u""))
    _mx = max(_have) if _have else 1
    _need = [x for x in range(1, _mx + 1) if x not in _have][:2]
    # 收尾补漏是唯一的串行尾巴（每个 future 最多等 4~5 秒），这里一并封顶，
    # 到点就带着已拿到的季返回，别把详情页拖到 8 秒以上。
    if _need and not _expired():
        # 两个缺号并发探，不再一个搜完再搜下一个
        _cand = {}
        try:
            _kwjobs = [(_hg_probe_kws(base, _n, _nm0), _n) for _n in _need]
            with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, len(_kwjobs))) as _ex:
                _fs = {_ex.submit(_hg_probe_first, kws, _n): _n
                       for kws, _n in _kwjobs}
                for _f in list(_fs):
                    try:
                        _cand[_fs[_f]] = _f.result(timeout=2) or []
                    except Exception:
                        _cand[_fs[_f]] = []
        except Exception:
            _cand = {}
        _jobs = []
        for _n, _cl in _cand.items():
            for _cid, _nm in (_cl or [])[:3]:
                if _hg_season_no(_nm) == _n and _cid not in found:
                    _jobs.append((_n, _cid))
        if _jobs:
            try:
                with concurrent.futures.ThreadPoolExecutor(max_workers=min(4, len(_jobs))) as _ex:
                    _fs2 = {_ex.submit(_hg_sd, _cid): _n for _n, _cid in _jobs}
                    _got = set()
                    for _f in list(_fs2):
                        _n = _fs2[_f]
                        if _n in _got:
                            continue
                        try:
                            _d = _f.result(timeout=3)
                        except Exception:
                            continue
                        if _d and _same_group(_d):
                            found[str(_d.get("series_id") or "")] = _d
                            _got.add(_n)
            except Exception:
                pass
    # 手工分季表：显式指定的 series_id 一律并入（跳过组号/基名判断，但仍走去重）
    _ovr_ids = set()
    try:
        for _k in (str(sid), base, _nm0):
            _v = _hg_season_override().get(_k) if _k else None
            if isinstance(_v, (list, tuple)):
                _ovr_ids = set(str(x) for x in _v if str(x).strip().isdigit())
                if _ovr_ids:
                    break
    except Exception:
        _ovr_ids = set()
    for _oid in list(_ovr_ids):
        if _oid in found:
            continue
        _d = _hg_sd(_oid)
        if _d and (_d.get("vid_list") or []):
            found[_oid] = _d
            _hg_diag("season", "override", sid=_oid,
                     name=_hg_clean(_d.get("series_name") or u"", 30))
    seasons = []
    for x, d in found.items():
        if not d:
            continue
        if x != str(sid) and x not in _ovr_ids and not _same_group(d):
            continue
        seasons.append((_hg_season_no(d.get(u"series_name") or u""), d))
    # 防误判：分集内容与当前剧或已收季高度重叠的（同一部的重复条目）一律剔除
    def _vset(d):
        return set(str(v) for v in (d.get("vid_list") or []))
    _self_v = _vset(sd)
    _uniq = []
    for no, d in seasons:
        v = _vset(d)
        if not v:
            continue
        _is_self = (d is sd) or (str(d.get("series_id") or u"") == str(sid))
        dup = False
        if not _is_self and _self_v:
            small = min(len(v), len(_self_v))
            if small and len(v & _self_v) >= max(1, int(small * 0.5)):
                dup = True
        if not dup:
            for _n2, _d2 in _uniq:
                v2 = _vset(_d2)
                small = min(len(v), len(v2)) if v2 else 0
                if small and len(v & v2) >= max(1, int(small * 0.5)):
                    dup = True
                    break
        if not dup:
            _uniq.append((no, d))
    seasons = _uniq
    if len(seasons) < 2:
        # 凑不出第二部同组剧就保持单线路原样，绝不凭空造季
        _hg_diag("season", "single", sid=sid, gid=gid or "-",
                 base=_hg_clean(base, 30), found=len(found),
                 why=("没有组号且搜索无意向兄弟季" if not gid else "组内只有这一季"),
                 ms=_hg_ms(_t_start))
        _HG_SEASON_CACHE[ck] = (time.time(), [(0, sd)])
        _trim_store(_HG_SEASON_CACHE, cap=256)
        return [(0, sd)]
    if _trimmed[0]:
        _hg_diag("season", "trim", sid=sid, got=len(seasons), ms=_hg_ms(_t_start),
                 why="已够 2 季，软预算 5 秒收工（结果只缓存 2 分钟，下次补齐）")
        try:
            _HG_TRIM_SIDS.add(str(sid))
        except Exception:
            pass
    else:
        try:
            _HG_TRIM_SIDS.discard(str(sid))
        except Exception:
            pass
    _hg_diag("season", "merged", sid=sid, gid=gid or "-", n=len(seasons),
             nos=[t[0] for t in seasons], ms=_hg_ms(_t_start),
             trim=1 if _trimmed[0] else 0)
    seasons.sort(key=lambda t: (t[0] if t[0] else 1))
    if not any((d is sd) or (str(d.get("series_id") or "") == str(sid)) for _n, d in seasons):
        seasons.insert(0, (0, sd))
    # 被软预算截断的结果只留 2 分钟：读缓存的条件是「写入时间距今 < 900 秒」，
    # 所以把 ts 往前挪，等价于缩短 TTL，不用改读取处。
    _HG_SEASON_CACHE[ck] = (time.time() - (900 - 120) if _trimmed[0] else time.time(), seasons)
    _trim_store(_HG_SEASON_CACHE, cap=256)
    return seasons


def _hg_cat_list(rows):
    out = []
    try:
        for x in rows:
            out.append(_cat_item(x))
    except Exception:
        pass
    try:
        # 列表页只热 2 条详情，分季留到真正点进去时算（原来是 6 条全跑分季）
        _hg_prefetch([x.get("vod_id") for x in out], 2, seasons=False)
    except Exception:
        pass
    return out


# ===================== 官方排行榜（/rank/<key>） =====================
# 官网排行榜共 8 个榜单：全站/真人剧/AI 剧 各分热播与新剧，另有口碑榜、追剧榜。
# 每页 20 条、共 5 页，rank 字段是全站名次（第 2 页从 21 开始）。
_HG_RANK_TABS = [
    ("hot-drama", u"热播榜"),
    ("new-drama", u"新剧榜"),
    ("hot-real-drama", u"真人剧热播"),
    ("new-real-drama", u"真人剧新剧"),
    ("hot-ai-drama", u"AI剧热播"),
    ("new-ai-drama", u"AI剧新剧"),
    ("prestige-drama", u"口碑榜"),
    ("followed-drama", u"追剧榜"),
]
_HG_RANK_KEYS = set(k for k, _ in _HG_RANK_TABS)


_HG_RANK_CACHE = {}


def _hg_rank_page(key, page=1):
    """取官方排行榜页：/rank/<key>?page=N，数据在 _ROUTER_DATA 的 rankList。"""
    k = key if key in _HG_RANK_KEYS else "hot-drama"
    try:
        page = max(1, int(page or 1))
    except (TypeError, ValueError):
        page = 1
    _ck = (k, page)
    _hit = _HG_RANK_CACHE.get(_ck)
    if _hit and time.time() - _hit[0] < 600:
        _hg_diag("rank", "cached", key=k, page=page, n=len(_hit[1][0] or []))
        return _hit[1][0], _hit[1][1], page
    url = SITE + "/rank/" + k
    if page > 1:
        url += "?page=%d" % page
    j = _data(url)
    for _k, v in ((j.get(u"loaderData") or {}) or {}).items():
        if isinstance(v, dict) and isinstance(v.get("content"), dict):
            c = v["content"]
            if isinstance(c.get("rankList"), list):
                rows = c.get("rankList") or []
                pag = c.get("pagination") or {}
                try:
                    _HG_RANK_CACHE[_ck] = (time.time(), (rows, pag))
                    _trim_store(_HG_RANK_CACHE, cap=64)
                except Exception:
                    pass
                _hg_diag("rank", "ok", key=k, page=page, n=len(rows))
                return rows, pag, page
    _hg_diag("rank", "empty", key=k, page=page)
    return [], {}, page


def _hg_rank_list(rows):
    """rankList → TVBox 卡片：备注放「第N名 · 热度 · 评分 · 标签」。"""
    out = []
    for x in rows or []:
        if not isinstance(x, dict):
            continue
        sid = str(x.get("seriesId") or x.get("id") or u"")
        name = str(x.get("title") or u"").strip()
        if not sid.isdigit() or not name:
            continue
        try:
            _cnt = int(x.get("episodeCount") or x.get("openEpisodeCount") or 0)
            if _cnt:
                _HG_STAMP[sid] = _cnt
        except Exception:
            pass
        bits = []
        rk = x.get("rank")
        if isinstance(rk, int) and rk > 0:
            bits.append(u"第%d名" % rk)
        heat = str(x.get("heatText") or x.get("primaryMetricText") or u"").strip()
        if heat:
            bits.append(heat)
        score = str(x.get("scoreText") or u"").strip()
        if score:
            bits.append(score)
        it = {
            "vod_id": "hg-series-v1:" + sid,
            "vod_name": name,
            "vod_pic": x.get("cover") or u"",
            "vod_remarks": u" · ".join(bits),
        }
        desc = x.get("description")
        if desc:
            it["vod_content"] = str(desc)
        tags = [str(t) for t in (x.get("tags") or []) if str(t).strip()][:2]
        if tags:
            it["vod_remarks"] = (it["vod_remarks"] + u" · " + u"、".join(tags)).strip(u" ·")
        out.append(it)
    return out


def _hg_rank_content(tid, page, cat=""):
    """排行榜/新剧两个入口共用：tid=rank 默认热播榜，tid=new 默认新剧榜。"""
    key = str(cat or u"").strip()
    if key not in _HG_RANK_KEYS:
        key = "new-drama" if str(tid) == "new" else "hot-drama"
    if str(tid) == "new" and not key.startswith("new-"):
        key = "new-drama"
    if str(tid) == "rank" and key.startswith("new-"):
        key = "hot-drama"
    try:
        rows, pgn, pgno = _hg_rank_page(key, page)
    except Exception as exc:
        _hg_diag("rank", "fail", key=key, page=page, err=type(exc).__name__)
        rows, pgn, pgno = [], {}, page
    items = _hg_rank_list(rows)
    pages = int((pgn or {}).get("totalPages") or 0) or 1
    return {
        "page": pgno,
        "pagecount": pages,
        "limit": len(items),
        "total": pages * 20,
        "list": items,
    }


def _hg_home_sections():
    """按首页 homeSections 分板块出卡，标题取 tab_name，取不到给兜底名。"""
    ck = u"home"
    hit = _HG_SEASON_CACHE.get(ck)
    if hit and time.time() - hit[0] < 900:
        return hit[1]
    out = []
    seen = set()
    try:
        j = _data(SITE + u"/")
        secs = (((j.get(u"loaderData") or {}).get(u"page") or {}).get(u"homeSections")) or []
    except Exception:
        secs = []
    if isinstance(secs, list):
        for sec in secs:
            if not isinstance(sec, dict):
                continue
            tt = str(sec.get(u"tab_type") or u"")
            tid, tname = _HG_TAB_MAP.get(tt, ("real-drama", u"红果热播"))
            tn = str(sec.get(u"tab_name") or u"").strip()
            if tn and tn.lower() not in (u"null", u"none", u"undefined"):
                tname = tn
            for x in (sec.get(u"video_list") or []):
                it = _item(x)
                vid = str(it.get("vod_id") or u"")
                if not vid.isdigit() or vid in seen:
                    continue
                seen.add(vid)
                it["type_id"] = tid
                it["type_name"] = tname
                out.append(it)
    _HG_SEASON_CACHE[ck] = (time.time(), out)
    _trim_store(_HG_SEASON_CACHE, cap=256)
    return out



_HG_SEARCH_PRIMED = [False]


_HG_SEARCH_CACHE = {}


def _search_api(key, page=1):
    """搜索结果的 120 秒缓存：同一次打开里「基名」和「基名第N季」会被反复搜，
    实测一部剧能打出 8~14 次搜索、其中一半是同关键词重复。"""
    try:
        ck = (str(key or u""), int(page or 1))
    except (TypeError, ValueError):
        ck = (str(key or u""), 1)
    hit = _HG_SEARCH_CACHE.get(ck)
    if hit and time.time() - hit[0] < 120:
        _hg_diag("season", "search-cached", kw=_hg_clean(ck[0], 24), pg=ck[1])
        return hit[1]
    res = _search_api_raw(key, page)
    try:
        _HG_SEARCH_CACHE[ck] = (time.time(), res)
        _trim_store(_HG_SEARCH_CACHE, cap=128)
    except Exception:
        pass
    return res


def _search_api_raw(key: str, page: int = 1) -> dict:
    """官网搜索接口 /api/search/result（搜索页已改客户端渲染，SSR 无数据）。

    原来每次搜索都先抓一遍 586KB 的首页拿 ttwid，一部十季剧要搜七八次，
    白花七八个首页请求（实测每次 250~1200ms）。现在复用线程本地 session 直连搜索，
    真的返回空列表时才补一次首页 cookie 重试，且每个进程只补一次。
    """
    empty = {"searchList": [], "totalCount": 0, "totalPages": 1, "hasMore": False}
    params = {"aid": "8662", "query": str(key or ""), "page": str(max(1, int(page or 1)))}

    def _once():
        try:
            r = _hg_session().get(SITE + "/api/search/result", params=params, timeout=8,
                                  headers={"Accept": "application/json, text/plain, */*"})
            if r.status_code != 200:
                return None
            return r.json()
        except Exception:
            return None

    data = _once()
    try:
        if not (isinstance(data, dict) and data.get("searchList")) and not _HG_SEARCH_PRIMED[0]:
            # 极少数情况下上游要 ttwid 才回数据：补一次首页再试（仅一次）
            _HG_SEARCH_PRIMED[0] = True
            try:
                _hg_session().get(SITE + "/", timeout=8)
            except Exception:
                pass
            data = _once()
    except Exception:
        data = data if isinstance(data, dict) else None
    if not isinstance(data, dict):
        return empty
    try:
        rows = data.get("searchList") or []
        if not isinstance(rows, list) or not rows:
            return empty
        try:
            total_pages = int(data.get("totalPages") or 1)
        except Exception:
            total_pages = 1
        try:
            total_count = int(data.get("totalCount") or 0)
        except Exception:
            total_count = 0
        return {
            "searchList": rows,
            "totalCount": total_count,
            "totalPages": max(1, total_pages),
            "hasMore": bool(data.get("hasMore")),
        }
    except Exception:
        return empty


def _search_loader(key: str, page: int = 1) -> dict:
    """搜索：优先官网 XHR 接口，失败退回旧 SSR 页（已多半无数据，仅兜底）。"""
    api = _search_api(key, page)
    if api.get("searchList"):
        return api
    last = {}
    for attempt in range(2):
        try:
            data = _data(SITE + "/search/" + quote(str(key), safe=""))
            loaded = (data.get("loaderData") or {}).get("search_(keyword)/page") or {}
            if loaded.get("searchList"):
                return loaded
            last = loaded or last
        except Exception:
            pass
        try:
            time.sleep(0.4 * (attempt + 1))
        except Exception:
            pass
    return last


def _search_by_keywords(keywords, page: int) -> dict:
    """多关键词轮换：第 N 页用第 N 个关键词（循环），避免搜索无法翻页。"""
    page = max(1, int(page or 1))
    kws = [k for k in (keywords or []) if k]
    if not kws:
        kws = ["短剧"]
    key = kws[(page - 1) % len(kws)]
    p = _search_loader(key)
    rows = p.get("searchList") or []
    # 去重空 id
    out = []
    seen = set()
    for x in rows:
        it = _item(x)
        vid = str(it.get("vod_id") or "")
        if not vid or vid in seen:
            continue
        seen.add(vid)
        out.append(it)
    # 虚拟页数：关键词数；若站点有 totalCount 也参考
    total = int(p.get("totalCount") or 0)
    pagecount = max(len(kws), (total + 9) // 10 if total else len(kws))
    return {
        "page": page,
        "pagecount": max(1, pagecount),
        "limit": len(out),
        "total": total or len(out) * pagecount,
        "list": out,
    }


_HG_SCAN_CACHE = {}


def _hg_scan_remember(ck, res):
    try:
        _HG_SCAN_CACHE[ck] = (time.time(), res)
        _trim_store(_HG_SCAN_CACHE, cap=64)
    except Exception:
        pass
    return res


def _hg_search_scan(key, page=1, max_pages=3):
    """搜索兜底：官方搜索接口被风控时，扫官方分类页按标题命中（并发）。"""
    key = str(key or "").strip()
    page = max(1, int(page or 1))
    empty = {"page": page, "pagecount": 1, "limit": 0, "total": 0, "list": []}
    if not key:
        return empty
    _ck = (key, page)
    _hit = _HG_SCAN_CACHE.get(_ck)
    if _hit and time.time() - _hit[0] < 300:
        return _hit[1]
    routes = [r for r, _n, _c in _HG_CONTENT_TYPES]
    jobs = [(r, p) for r in routes for p in range(1, max_pages + 1)]

    def work(rp):
        r, p = rp
        try:
            return _hg_category_page(r, "", p).get("recommendList") or []
        except Exception:
            return []

    hits = []
    seen = set()
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
            for rows in ex.map(work, jobs):
                for x in rows:
                    if not isinstance(x, dict):
                        continue
                    nm = str(x.get("series_name") or x.get("series_title") or "")
                    if key and key not in nm:
                        continue
                    it = _item(x)
                    vid = str(it.get("vod_id") or "")
                    if not vid or vid in seen:
                        continue
                    seen.add(vid)
                    hits.append(it)
    except Exception:
        pass
    if not hits:
        return _hg_scan_remember(_ck, empty)
    per = 20
    st = (page - 1) * per
    chunk = hits[st:st + per]
    return _hg_scan_remember(_ck, {
        "page": page,
        "pagecount": max(1, (len(hits) + per - 1) // per),
        "limit": len(chunk),
        "total": len(hits),
        "list": chunk,
    })


# =============================================================================
# 弹幕子系统（红果 App 评论 / 弹幕接口）
#
# 接口：POST https://api5-normal-lq.fqnovel.com/novel/commentapi/comment/list/{vid}/v1/
#       body: business_param.book_id = 剧集 series_id, start_offset_time = 窗口起点(ms)
#       返回 data.data_list[].comment.expand.offset_time（毫秒）与 .content.text
#       按 30s 一个窗口顺序取，直到该窗口为空且 extra.next_query_danmaku_list_time > 0
#       （说明已到片尾）。
#
# 签名：该接口不吃视频接口那套六神（gorgon/medusa），要的是 x-ladon + x-argus
#       + x-ss-stub。ladon 是 34 轮 Feistel；argus 是 protobuf(25 字段) →
#       Simon-64 分组 → 551 变体（魔数/异或/倒序）→ AES-128-CBC。
#       下面的实现与 Hiker 版 JS 逐字节一致（同输入同随机数下 x-ladon / x-argus
#       完全相等），因此同一份签名在 TVBox 的 Chaquopy 里也能直接用。
# =============================================================================
_DM_ENABLED = True          # 总开关：关掉则 playerContent 不再挂弹幕
_DM_HOST = "api5-normal-lq.fqnovel.com"
_DM_WINDOW_MS = 30000       # 每个取数窗口（毫秒）
_DM_MAX_WINDOWS = 20        # 最多取 20 个窗口（约 10 分钟，覆盖短剧整集）
_DM_TTL = 1800              # 弹幕缓存有效期（秒，只用于取到内容的成功结果）
_DM_FAIL_TTL = 45          # 取失败的结果只压 45 秒，绝不把一次失败锁死半小时
_DM_MIN_GAP = 0.28         # 两次弹幕请求之间的最小间隔（秒），削峰防接口限流
_DM_PAGE_WORKERS = 2       # 每批并发的取数窗口数，降低瞬时并发
_DM_RETRY_DELAY = 6.0      # 撞上限流后隔多久再补一次
_DM_WAIT = 18               # 弹幕路由最多等取数完成多少秒
_DM_IN_PLAYER = "list"      # playerContent 里 danmaku 字段形态: list / url / off
_DM_PUSH_LOCAL = True       # 额外用壳的 127.0.0.1:9978/action 推一次（老壳兜底）
_DM_SID_MAP: dict[str, str] = {}
_DM_CACHE: dict[str, dict[str, Any]] = {}
_DM_EVENTS: dict[str, threading.Event] = {}
_DM_LOCKS = threading.Lock()
_DM_POST_LOCK = threading.Lock()
_DM_POST_LAST = 0.0
_DM_PUSHED: dict[str, float] = {}
_DM_STREAM_HIT: dict[str, float] = {}
_DM_HIT: dict[str, float] = {}
_DM_LAST_ERR = ""

_DM_AES_KEY = bytes.fromhex("d31e3718288a1027baab59f146a09a9c")
_DM_AES_IV = bytes.fromhex("ea180a0336ed352fcd24e4d50018ae54")
_DM_SIMON_KEY = bytes.fromhex("fc78e0a9657a0c748ce51559903ccf03510e51d3cff232d71343e88a321c5304")
_DM_M551 = bytes.fromhex("f2f7fcfff2f7fcff")
_DM_TAIL551 = bytes.fromhex("eafb2cfe8568519154")
_DM_PREFIX551 = bytes.fromhex("f281")

_DM_U32 = 0xFFFFFFFF


# ---------------------------- SM3 ----------------------------
_DM_SM3_IV = (0x7380166F, 0x4914B2B9, 0x172442D7, 0xDA8A0600,
              0xA96F30BC, 0x163138AA, 0xE38DEE4D, 0xB0FB0E4E)


def _dm_rotl32(a: int, k: int) -> int:
    k &= 31
    if not k:
        return a & _DM_U32
    return ((a << k) | (a >> (32 - k))) & _DM_U32


def _dm_sm3_cf(v: list, bl: bytes, off: int) -> list:
    w = [((bl[off + i * 4] << 24) | (bl[off + i * 4 + 1] << 16) |
          (bl[off + i * 4 + 2] << 8) | bl[off + i * 4 + 3]) & _DM_U32 for i in range(16)]
    for j in range(16, 68):
        xj = (w[j - 16] ^ w[j - 9] ^ _dm_rotl32(w[j - 3], 15)) & _DM_U32
        w.append((xj ^ _dm_rotl32(xj, 15) ^ _dm_rotl32(xj, 23) ^
                  _dm_rotl32(w[j - 13], 7) ^ w[j - 6]) & _DM_U32)
    w1 = [(w[j] ^ w[j + 4]) & _DM_U32 for j in range(64)]
    a, b, c, d, e, f, g, h = v
    for j in range(64):
        t = 0x79CC4519 if j < 16 else 0x7A879D8A
        ss1 = _dm_rotl32((_dm_rotl32(a, 12) + e + _dm_rotl32(t, j % 32)) & _DM_U32, 7)
        ss2 = ss1 ^ _dm_rotl32(a, 12)
        if j < 16:
            ff = a ^ b ^ c
            gg = e ^ f ^ g
        else:
            ff = (a & b) | (a & c) | (b & c)
            gg = (e & f) | (~e & g)
        tt1 = (ff + d + ss2 + w1[j]) & _DM_U32
        tt2 = (gg + h + ss1 + w[j]) & _DM_U32
        d, c, b, a = c, _dm_rotl32(b, 9), a, tt1
        h, g, f, e = g, _dm_rotl32(f, 19), e, (tt2 ^ _dm_rotl32(tt2, 9) ^ _dm_rotl32(tt2, 17)) & _DM_U32
    return [(a ^ v[0]) & _DM_U32, (b ^ v[1]) & _DM_U32, (c ^ v[2]) & _DM_U32, (d ^ v[3]) & _DM_U32,
            (e ^ v[4]) & _DM_U32, (f ^ v[5]) & _DM_U32, (g ^ v[6]) & _DM_U32, (h ^ v[7]) & _DM_U32]


def _dm_sm3(data: bytes) -> bytes:
    orig = len(data)
    msg = bytearray(data)
    msg.append(0x80)
    reserve = (orig % 64) + 1
    end = 56
    if end < reserve:
        end += 64
    msg.extend(b"\0" * (end - reserve))
    msg.extend(struct.pack(">Q", orig * 8))
    v = list(_DM_SM3_IV)
    for i in range(len(msg) // 64):
        v = _dm_sm3_cf(v, msg, i * 64)
    return b"".join(struct.pack(">I", x) for x in v)


def _dm_sm3_prefix6(data: bytes) -> bytes:
    return _dm_sm3(data)[:6]


# -------------------- 64 位字运算（(hi, lo) 双 32 位） --------------------
def _dm_u64le(b: bytes, off: int) -> tuple:
    lo = (b[off] | b[off + 1] << 8 | b[off + 2] << 16 | b[off + 3] << 24) & _DM_U32
    hi = (b[off + 4] | b[off + 5] << 8 | b[off + 6] << 16 | b[off + 7] << 24) & _DM_U32
    return (hi, lo)


def _dm_u64le_write(v: tuple, out: bytearray) -> None:
    for j in range(8):
        out.append(((v[1] >> (8 * j)) if j < 4 else (v[0] >> (8 * (j - 4)))) & 0xFF)


def _dm_x64(a: tuple, b: tuple) -> tuple:
    return (a[0] ^ b[0], a[1] ^ b[1])


def _dm_add64(a: tuple, b: tuple) -> tuple:
    lo = a[1] + b[1]
    hi = a[0] + b[0] + (1 if lo > _DM_U32 else 0)
    return (hi & _DM_U32, lo & _DM_U32)


def _dm_not64(a: tuple) -> tuple:
    return ((~a[0]) & _DM_U32, (~a[1]) & _DM_U32)


def _dm_rotl64(a: tuple, n: int) -> tuple:
    n = ((n % 64) + 64) % 64
    if n == 0:
        return (a[0], a[1])
    if n == 32:
        return (a[1], a[0])
    if n < 32:
        hi = ((a[0] << n) | (a[1] >> (32 - n))) & _DM_U32
        lo = ((a[1] << n) | (a[0] >> (32 - n))) & _DM_U32
    else:
        m = n - 32
        hi = ((a[1] << m) | (a[0] >> (32 - m))) & _DM_U32
        lo = ((a[0] << m) | (a[1] >> (32 - m))) & _DM_U32
    return (hi, lo)


def _dm_rotr64(a: tuple, n: int) -> tuple:
    return _dm_rotl64(a, (64 - (n % 64)) % 64)


_DM_SZ_HI = 0x3DC94C3A
_DM_SZ_LO = 0x046D678B


def _dm_simon_zbit(k: int) -> int:
    return (_DM_SZ_LO >> k) & 1 if k < 32 else (_DM_SZ_HI >> (k - 32)) & 1


def _dm_simon_expand(k: list) -> list:
    key = list(k)
    for i in range(4, 72):
        tmp = _dm_rotr64(key[i - 1], 3)
        tmp = _dm_x64(tmp, key[i - 3])
        tmp = _dm_x64(tmp, _dm_rotr64(tmp, 1))
        key.append(_dm_x64(_dm_x64(_dm_not64(key[i - 4]), tmp),
                           (0, (_dm_simon_zbit((i - 4) % 62) ^ 3) & _DM_U32)))
    return key


def _dm_simon_encrypt(pt: tuple, key: list) -> tuple:
    x, x1 = pt[0], pt[1]
    for i in range(72):
        t = x1
        r1 = _dm_rotl64(x1, 1)
        r8 = _dm_rotl64(x1, 8)
        f = (r1[0] & r8[0], r1[1] & r8[1])
        x1 = _dm_x64(_dm_x64(x, f), _dm_x64(_dm_rotl64(x1, 2), key[i]))
        x = t
    return (x, x1)


# ---------------------------- AES-CBC（无填充） ----------------------------
def _dm_aes_cbc_encrypt(key: bytes, iv: bytes, data: bytes) -> bytes:
    if not data:
        return b""
    if AES_BACKEND == "cryptography":
        enc = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
        return enc.update(data) + enc.finalize()
    if AES_BACKEND == "pycryptodome":
        return CryptoAES.new(key, CryptoAES.MODE_CBC, iv).encrypt(data)
    if len(data) % 16:
        data = data[:len(data) - (len(data) % 16)]
    aes = _PureAES128(key)
    prev = iv[:16].ljust(16, b"\0")
    out = bytearray()
    for i in range(0, len(data), 16):
        block = bytes(a ^ b for a, b in zip(data[i:i + 16], prev))
        enc = aes.encrypt_block(block)
        out.extend(enc)
        prev = enc
    return bytes(out)


def _dm_pkcs7(data: bytes) -> bytes:
    n = 16 - (len(data) % 16)
    return data + bytes([n]) * n


# ---------------------------- protobuf 写入 ----------------------------
class _DmPbuf:
    """最小的 protobuf 编码器：字段顺序即写入顺序（与 JS 版 Pbuf 一致）。"""

    def __init__(self) -> None:
        self._fields: list = []
        self._blobs: list = []

    def v(self, idx: int, val: int) -> "_DmPbuf":
        self._fields.append((idx, 0, int(val), 0))
        return self

    def _blob(self, idx: int, data: bytes) -> "_DmPbuf":
        self._blobs.append(data)
        self._fields.append((idx, 2, 0, len(self._blobs) - 1))
        return self

    def s(self, idx: int, text: Any) -> "_DmPbuf":
        return self._blob(idx, str(text).encode("utf-8"))

    def raw(self, idx: int, data: bytes) -> "_DmPbuf":
        return self._blob(idx, data)

    def pb(self, idx: int, sub: "_DmPbuf") -> "_DmPbuf":
        return self._blob(idx, sub.to_buf())

    def to_buf(self) -> bytes:
        out = bytearray()
        for idx, kind, val, ref in self._fields:
            _dm_varint(out, idx * 8 + (kind & 7))
            if kind == 0:
                _dm_varint(out, val)
            else:
                blob = self._blobs[ref]
                _dm_varint(out, len(blob))
                out.extend(blob)
        return bytes(out)


def _dm_varint(out: bytearray, value: int) -> None:
    value &= 0xFFFFFFFFFFFFFFFF
    while value >= 128:
        out.append((value % 128) | 128)
        value //= 128
    out.append(value % 128)


# ---------------------------- argus / ladon ----------------------------
def _dm_simon_padded(pb: bytes) -> bytes:
    key = _dm_simon_expand([_dm_u64le(_DM_SIMON_KEY, 0), _dm_u64le(_DM_SIMON_KEY, 8),
                            _dm_u64le(_DM_SIMON_KEY, 16), _dm_u64le(_DM_SIMON_KEY, 24)])
    out = bytearray()
    for i in range(len(pb) // 16):
        off = i * 16
        ct = _dm_simon_encrypt((_dm_u64le(pb, off), _dm_u64le(pb, off + 8)), key)
        _dm_u64le_write(ct[0], out)
        _dm_u64le_write(ct[1], out)
    return bytes(out)


def _dm_argus_encrypt(bean: "_DmPbuf") -> str:
    pb = _dm_pkcs7(bean.to_buf())
    un = _DM_M551 + _dm_simon_padded(pb) + _DM_TAIL551
    buf = bytearray(un[:8])
    for i in range(8, len(un)):
        buf.append((un[i] ^ _DM_M551[i % 8]) & 0xFF)
    buf.reverse()
    body = _dm_pkcs7(bytes(buf) + b"ao")
    return base64.b64encode(_DM_PREFIX551 + _dm_aes_cbc_encrypt(_DM_AES_KEY, _DM_AES_IV, body)).decode()


def _dm_query_param(query: str, name: str) -> str:
    text = str(query or "")
    if text.startswith("?"):
        text = text[1:]
    if "#" in text:
        text = text.split("#", 1)[0]
    for part in text.split("&"):
        if not part:
            continue
        key = part.split("=")
        if key[0] == name:
            return "=".join(key[1:]) if len(key) > 1 else ""
    return ""


def _dm_argus_sign(query: str, stub_hex: str, ts: int, aid: int, license_id: int,
                   device_id: str, install_id: str = "", rand_field: int = 0) -> str:
    if not rand_field:
        rand_field = random.randint(1, 2147483647)
    body_hash = _dm_sm3_prefix6(bytes.fromhex(stub_hex)) if stub_hex else _dm_sm3_prefix6(b"\0" * 16)
    query_hash = _dm_sm3_prefix6(query.encode("utf-8")) if query else _dm_sm3_prefix6(b"\0" * 16)
    bean = _DmPbuf()
    bean.v(1, 1077940818).v(2, 2).v(3, rand_field)
    bean.s(4, aid).s(5, device_id).s(6, license_id)
    bean.s(7, _dm_query_param(query, "version_name"))
    bean.s(8, "v04.04.05-ov-android").v(9, 134744640).raw(10, b"\0" * 8).v(11, 0)
    bean.v(12, ts * 2)
    bean.raw(13, body_hash).raw(14, query_hash)
    bean.pb(15, _DmPbuf().v(1, 1).v(2, 1).v(3, 1).v(7, 0xC792ECCC))
    bean.s(16, install_id).s(20, "none").v(21, 738)
    bean.pb(23, _DmPbuf().s(1, "NX551J").v(2, 8196).v(4, 0x80E0D800))
    bean.v(25, 2)
    return _dm_argus_encrypt(bean)


def _dm_ladon_expand(md5hex: str) -> bytearray:
    ht = bytearray(288)
    for i in range(min(32, len(md5hex))):
        ht[i] = ord(md5hex[i])

    def load(off: int) -> tuple:
        lo = (ht[off] | ht[off + 1] << 8 | ht[off + 2] << 16 | ht[off + 3] << 24) & _DM_U32
        hi = (ht[off + 4] | ht[off + 5] << 8 | ht[off + 6] << 16 | ht[off + 7] << 24) & _DM_U32
        return (hi, lo)

    temp = [load(0), load(8), load(16), load(24)]
    b0, b8 = temp[0], temp[1]
    temp = [temp[2], temp[3]]
    for i in range(34):
        x9 = b0
        x8 = _dm_rotr64(b8, 8)
        x8 = _dm_add64(x8, x9)
        x8 = (x8[0], x8[1] ^ i)
        temp.append(x8)
        x8 = _dm_x64(x8, _dm_rotl64(x9, 3))
        for j in range(8):
            ht[(i + 1) * 8 + j] = ((x8[1] >> (8 * j)) if j < 4 else (x8[0] >> (8 * (j - 4)))) & 0xFF
        b0 = x8
        b8 = temp.pop(0)
    return ht


def _dm_ladon_block(ht: bytearray, src: bytearray, off: int) -> bytes:
    d0 = ((src[off + 4] | src[off + 5] << 8 | src[off + 6] << 16 | src[off + 7] << 24) & _DM_U32,
          (src[off] | src[off + 1] << 8 | src[off + 2] << 16 | src[off + 3] << 24) & _DM_U32)
    d1 = ((src[off + 12] | src[off + 13] << 8 | src[off + 14] << 16 | src[off + 15] << 24) & _DM_U32,
          (src[off + 8] | src[off + 9] << 8 | src[off + 10] << 16 | src[off + 11] << 24) & _DM_U32)
    for i in range(34):
        h0 = (ht[i * 8 + 4] | ht[i * 8 + 5] << 8 | ht[i * 8 + 6] << 16 | ht[i * 8 + 7] << 24) & _DM_U32
        h1 = (ht[i * 8] | ht[i * 8 + 1] << 8 | ht[i * 8 + 2] << 16 | ht[i * 8 + 3] << 24) & _DM_U32
        total = _dm_add64(d0, _dm_rotr64(d1, 8))
        d1 = (h0 ^ total[0], h1 ^ total[1])
        d0 = _dm_x64(d1, _dm_rotl64(d0, 3))
    out = bytearray()
    _dm_u64le_write(d0, out)
    _dm_u64le_write(d1, out)
    return bytes(out)


def _dm_ladon_encrypt_raw(md5hex: str, data: bytes) -> bytes:
    ht = _dm_ladon_expand(md5hex)
    pad = 16 - (len(data) % 16)
    src = bytearray(data) + bytes([pad]) * pad
    out = bytearray()
    for i in range(len(src) // 16):
        out.extend(_dm_ladon_block(ht, src, i * 16))
    return bytes(out)


def _dm_ladon_encrypt(ts: int, license_id: int, aid: int, rand4: bytes) -> str:
    data = ("%d-%d-%d" % (ts, license_id, aid)).encode("utf-8")
    keygen = rand4 + str(aid).encode("utf-8")
    enc = _dm_ladon_encrypt_raw(hashlib.md5(keygen).hexdigest(), data)
    return base64.b64encode(rand4 + enc).decode()


def _dm_sign_headers(query: str, body: bytes, device_id: str, install_id: str = "",
                     aid: int = 8662, license_id: int = 1611921764) -> dict:
    ts = int(time.time())
    stub = hashlib.md5(body).hexdigest() if body else ""
    headers = {
        "x-ss-req-ticket": str(ts * 1000),
        "x-khronos": str(ts),
        "x-ladon": _dm_ladon_encrypt(ts, license_id, aid, bytes(random.getrandbits(8) for _ in range(4))),
        "x-argus": _dm_argus_sign(query, stub, ts, aid, license_id, device_id, ""),
    }
    if stub:
        headers["x-ss-stub"] = stub
    return headers


# ---------------------------- 取数 ----------------------------
def _dm_query(device_id: str) -> str:
    """评论接口的固定 query（与红果 App 7.3.9.32 一致）。"""
    return (
        "device_id=%s&ac=wifi&channel=xiaomi_8662_64&aid=8662"
        "&app_name=novelread&version_code=73932&version_name=7.3.9.32"
        "&device_platform=android&os=android&ssmix=a&device_type=23127PN0CC"
        "&device_brand=xiaomi&language=zh&os_api=34&os_version=14"
        "&manifest_version_code=73932&resolution=1200*2670&dpi=520"
        "&update_version_code=73932&host_abi=arm64-v8a&dragon_device_type=phone"
        "&pv_player=73932&compliance_status=0&need_personal_recommend=1"
        "&player_so_load=1&is_android_pad_screen=0"
    ) % device_id


def _dm_page(vid: str, series_id: str, start_ms: int, device_id: str,
             install_id: str = "") -> tuple[list, dict, dict]:
    """取一个时间窗的弹幕，返回 (items, common_list_info, extra)。"""
    payload = {
        "business_param": {
            "book_id": str(series_id),
            "playlet_item_duration": 0,
            "start_offset_time": int(start_ms),
        },
        "comment_source": 601,
        "comment_type": 20,
        "count": 90,
        "group_id": str(vid),
        "group_type": 30,
        "server_channel": 1000,
        "sort": 1,
    }
    body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    query = _dm_query(device_id)
    headers = {
        "content-type": "application/json; charset=utf-8",
        "User-Agent": "com.dragon.read",
        "accept": "application/json",
    }
    headers.update(_dm_sign_headers(query, body, device_id, install_id))
    url = "https://%s/novel/commentapi/comment/list/%s/v1/?%s" % (_DM_HOST, vid, query)
    sess = requests.Session()
    sess.trust_env = False
    global _DM_POST_LAST
    with _DM_POST_LOCK:
        _gap = _DM_MIN_GAP - (time.time() - _DM_POST_LAST)
        if _gap > 0:
            try:
                time.sleep(_gap)
            except Exception:
                pass
        _DM_POST_LAST = time.time()
    response = sess.post(url, data=body, headers=headers, timeout=20)
    data = _json_response(response, stage="danmaku")
    if isinstance(data, Mapping) and data.get("code") not in (0, None):
        raise HongguoPluginError("弹幕接口 code=%s %s" % (data.get("code"), data.get("message") or ""))
    payload_data = (data or {}).get("data") if isinstance(data, Mapping) else None
    payload_data = payload_data if isinstance(payload_data, Mapping) else {}
    items = []
    for row in payload_data.get("data_list") or []:
        if not isinstance(row, Mapping):
            continue
        comment = row.get("comment") or {}
        common = (comment.get("common") or {}) if isinstance(comment, Mapping) else {}
        text = str(((common.get("content") or {}).get("text")) or "").strip()
        if not text:
            continue
        expand = (comment.get("expand") or {}) if isinstance(comment, Mapping) else {}
        offset = expand.get("offset_time")
        if offset is None:
            offset = expand.get("offset")
        try:
            offset_ms = int(offset or 0)
        except (TypeError, ValueError):
            offset_ms = 0
        stat = (comment.get("stat") or {}) if isinstance(comment, Mapping) else {}
        items.append({
            "text": text,
            "ms": max(0, offset_ms),
            "like": _int(stat.get("digg_count")),
            "role": _int(expand.get("playlet_role_type")),
        })
    info = payload_data.get("common_list_info") or {}
    extra = payload_data.get("extra") or {}
    return items, info if isinstance(info, Mapping) else {}, extra if isinstance(extra, Mapping) else {}


def _dm_fetch(vid: str, series_id: str, device_id: str, install_id: str = "") -> list:
    """按 30s 窗口取整集弹幕（4 路并发，边取边判断片尾），返回按时间排序的 [{text, ms}]。"""
    global _DM_LAST_ERR
    items: list = []
    seen: set = set()
    windows = [i * _DM_WINDOW_MS for i in range(_DM_MAX_WINDOWS)]
    empty_batches = 0
    stop = False
    try:
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=_DM_PAGE_WORKERS)
    except Exception:
        pool = None
    try:
        for base in range(0, len(windows), _DM_PAGE_WORKERS):
            if stop:
                break
            batch = windows[base:base + _DM_PAGE_WORKERS]
            if pool is None:
                results = []
                for start in batch:
                    try:
                        results.append(_dm_page(vid, series_id, start, device_id, install_id))
                    except Exception as exc:
                        if not _DM_LAST_ERR:
                            _DM_LAST_ERR = str(exc)
                        results.append(([], {}, {}))
            else:
                futures = [pool.submit(_dm_page, vid, series_id, start, device_id, install_id)
                           for start in batch]
                results = []
                for future in futures:
                    try:
                        results.append(future.result(timeout=25))
                    except Exception as exc:
                        if not _DM_LAST_ERR:
                            _DM_LAST_ERR = str(exc)
                        results.append(([], {}, {}))
            batch_empty = True
            for page, _info, extra in results:
                if page:
                    batch_empty = False
                    for item in page:
                        key = (item["text"], item["ms"] // 500)
                        if key in seen:
                            continue
                        seen.add(key)
                        items.append(item)
                try:
                    next_ms = int(extra.get("next_query_danmaku_list_time") or 0)
                except (TypeError, ValueError):
                    next_ms = 0
                # 空窗 + 片尾时间戳 => 本集已结束，后面窗口不用再问
                if not page and next_ms > 0:
                    stop = True
            empty_batches = empty_batches + 1 if batch_empty else 0
            if empty_batches >= 2:
                break
    finally:
        if pool is not None:
            try:
                pool.shutdown(wait=False)
            except Exception:
                pass
    items.sort(key=lambda x: x["ms"])
    return items


def _dm_rows(items: list) -> list:
    """原始弹幕（含 ms）转成播放器行：time 秒 + type/color/text。"""
    out = []
    for row in items or []:
        if not isinstance(row, Mapping):
            continue
        try:
            ms = int(row.get("ms") or 0)
        except (TypeError, ValueError):
            ms = 0
        text = str(row.get("text") or "").strip()
        if not text:
            continue
        out.append({"time": round(ms / 10.0) / 100.0, "type": 1,
                    "color": 16777215, "text": text})
    return out


def _dm_state(vid: str) -> dict:
    with _DM_LOCKS:
        return dict(_DM_CACHE.get(vid) or {})


def _dm_set_state(vid: str, items: list, error: str = "") -> None:
    with _DM_LOCKS:
        _DM_CACHE[vid] = {"t": time.time(), "items": items, "error": error,
                          "ttl": _DM_TTL if items else _DM_FAIL_TTL}
        event = _DM_EVENTS.get(vid)
    if event is not None:
        event.set()


def _dm_get(vid: str, series_id: str = "", device_id: str = "", install_id: str = "",
            wait: float = 0, force: bool = False) -> dict:
    """拿一集弹幕（带缓存 + 后台去重）。wait 秒内没取完就先返回当前状态。

    force=True 时忽略缓存里「上次取失败」的结果，重新请求一次；
    取到的内容仍然按 _DM_TTL 缓存，失败只按 _DM_FAIL_TTL 短存，避免一次限流就哑掉半小时。
    """
    vid = str(vid or "")
    if not vid:
        return {"items": [], "error": "missing vid"}
    series_id = str(series_id or "")
    if not series_id:
        # 没有 series_id（book_id）时接口只会回 103001，别浪费请求
        return {"items": [], "error": "no sid"}
    with _DM_LOCKS:
        state = dict(_DM_CACHE.get(vid) or {})
        _ttl = float(state.get("ttl") or _DM_TTL)
        _fresh = state and (time.time() - float(state.get("t") or 0)) < _ttl
        if _fresh and not (force and not (state.get("items") or [])):
            return state
        event = _DM_EVENTS.get(vid)
        need_spawn = event is None or event.is_set()
        if need_spawn:
            event = threading.Event()
            _DM_EVENTS[vid] = event
    if need_spawn:
        def _worker():
            err = ""
            try:
                items = _dm_fetch(vid, series_id, device_id, install_id)
                if not items:
                    err = _DM_LAST_ERR or "empty"
                    # 一次取空多半是撞了接口限流，歇一会儿补一次再下结论
                    if "103001" in err or "参数错误" in err:
                        try:
                            time.sleep(_DM_RETRY_DELAY)
                        except Exception:
                            pass
                        items = _dm_fetch(vid, series_id, device_id, install_id)
                        if items:
                            err = ""
            except Exception as exc:
                items, err = [], str(exc)
            _dm_set_state(vid, items, err)
        threading.Thread(target=_worker, daemon=True).start()
    if wait > 0:
        try:
            event.wait(wait)
        except Exception:
            pass
    return _dm_state(vid)


def _dm_remember_series(vid: str, series_id: str) -> None:
    if not vid or not series_id:
        return
    _DM_SID_MAP[str(vid)] = str(series_id)


def _dm_series_of(vid: str) -> str:
    return str(_DM_SID_MAP.get(str(vid or "")) or "")


def _dm_series_load() -> None:
    """弹幕 vid→剧集 映射只留在进程内存：按用户要求不读也不写本地 json 文件。"""
    return


def _dm_series_save() -> None:
    """只保留进程内映射（_DM_SID_MAP）：按用户要求不落盘，不生成 series_map.json。"""
    return


def _dm_xml_escape(text: str) -> str:
    return (str(text).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace('"', "&quot;").replace("'", "&apos;"))


def _dm_to_xml(chat_id: str, items: list) -> bytes:
    """B 站 XML 弹幕格式，DanmakuFlameMaster / 各壳原生支持。"""
    body = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        "<i><chatserver>hongguo</chatserver><chatid>%s</chatid><mission>0</mission>"
        "<maxlimit>99999</maxlimit><state>0</state><real_name>0</real_name><source>k-v</source>"
        % _dm_xml_escape(chat_id),
    ]
    for row in _dm_rows(items):
        body.append('<d p="%.2f,1,25,%d,0,0,0,0">%s</d>'
                    % (float(row["time"]), int(row["color"]), _dm_xml_escape(row["text"])))
    body.append("</i>")
    return "".join(body).encode("utf-8")


def _dm_to_json(items: list) -> bytes:
    return json.dumps(_dm_rows(items), ensure_ascii=False).encode("utf-8")


def _dm_push_local(url: str, vid: str) -> None:
    """老壳可能不读 playerContent.danmaku，用壳自己的本地接口补推一次。

    短剧预载会在上一集还在播时先把下一集的 playerContent 要来（也会走到这里），
    若当场就推，等于把下一集的弹幕源塞给正在播的这一集，切过去后壳反而不再来取。
    所以推迟到「别的集已经几秒没有取流、这一集也没被播放器自己取过弹幕」时才推，
    并且允许同一集隔一段时间重推（不再是一集一辈子一次）。
    """
    if not _DM_PUSH_LOCAL or not url or not vid:
        return
    now = time.time()
    if now - float(_DM_PUSHED.get(vid) or 0) < 240:
        return
    _DM_PUSHED[vid] = now

    def _run():
        try:
            from urllib.parse import quote as _quote
            for _i in range(8):
                time.sleep(4.0)
                if _DM_HIT.get(vid, 0) > time.time() - 30:
                    return          # 播放器自己来取过了，不必推
                _others = [t for k, t in list(_DM_STREAM_HIT.items()) if k != vid]
                if _others and max(_others) > time.time() - 4.0:
                    continue        # 还有别的集在取流，说明在预载/还没切过来
                target = "http://127.0.0.1:9978/action?do=refresh&type=danmaku&path=" + _quote(url, safe="")
                session = requests.Session()
                session.trust_env = False
                session.get(target, timeout=3)
                return
        except Exception:
            pass
    try:
        threading.Thread(target=_run, daemon=True).start()
    except Exception:
        pass


class Spider(_BaseSpider):
    def __init__(self):
        self.device_id = str(random.randint(10**17, 10**18 - 1))
        self.install_id = str(random.randint(10**17, 10**18 - 1))

    def _adopt_working_pair(self):
        pair = _working_device_pair()
        if pair is None:
            # 冷启动（本机无持久化设备）：先注册一对再播，随机号取流必回空体。
            try:
                pair = _rotate_stream_device()
            except Exception:
                pair = None
        if pair is not None:
            self.device_id = pair["device_id"]
            self.install_id = pair["install_id"]

    def getName(self):
        return "红果短剧"

    def isVideoFormat(self, url):
        u = str(url or "").lower()
        return (".mp4" in u) or ("video_mp4" in u) or ("m3u8" in u) or ("mime_type=video" in u) or ("qznovelvod" in u)

    def manualVideoCheck(self):
        return False

    def getDependence(self):
        return []

    def download(self, path, url):
        return ""

    def liveContent(self):
        return {}

    def isVPAYard(self, flag):
        return False

    def action(self, action):
        """壳的扩展动作入口：action("diag"/"selfcheck"/"log") 返回最近一次失败摘要。"""
        name = str(action or "").strip().lower()
        if name in ("diag", "selfcheck", "log", "hg_diag", "hg_selfcheck"):
            try:
                return _hg_last_error_text()
            except Exception:
                return ""
        return ""

    def init(self, extend=""):
        # 每次源实例使用随机合法设备标识；不依赖用户私有配置。
        try:
            _hg_banner()
        except Exception:
            pass
        try:
            _hg_cache_cleanup(False)
        except Exception:
            pass
        try:
            _dm_series_load()
        except Exception:
            pass
        try:
            _hg_poll_start()
        except Exception:
            pass
        return None

    def _danmaku_payload(self, port: int, vid: str) -> dict:
        """把本机弹幕地址挂进 playerContent，并顺手预热取数。"""
        if not _DM_ENABLED or not port:
            return {}
        sid = _dm_series_of(vid)
        if not sid:
            try:
                _dm_series_load()
                sid = _dm_series_of(vid)
            except Exception:
                sid = ""
        if not sid:
            # 剧集映射还没建立（没走过 detailContent），这集先不挂弹幕
            return {}
        query = urlencode({
            "vid": vid,
            "sid": sid,
            "fmt": "xml",
            "did": self.device_id or "",
            "iid": self.install_id or "",
        })
        url = "http://127.0.0.1:%d/hg_dm?%s" % (port, query)
        # 不在这里预取弹幕：短剧预载会提前替下一集调 playerContent，
        # 于是两集弹幕请求在几百毫秒内挤在一起，最容易撞上接口限流（code=103001），
        # 一旦那次失败被当成结论，切过去就再没有弹幕了。改由播放器真来取 /hg_dm 时再拉。
        _dm_push_local(url, vid)
        label = "红果弹幕"
        if _DM_IN_PLAYER == "url":
            return {"danmaku": url}
        if _DM_IN_PLAYER == "list":
            return {"danmaku": [{"name": label, "url": url}]}
        return {}

    def destroy(self):
        try:
            _hg_cache_cleanup(False)
        except Exception:
            pass

    def homeContent(self, filter):
        """分类=官方内容类型（真人剧/漫剧/漫画），二级分类取官方分类路由。"""
        # 官方 App 顶部两个入口就是「排行榜 / 新剧」（官网 /rank/<key>），
        # 所以放在分类最前面，打开首页第一屏就能点到。
        class_list = [
            {"type_id": "rank", "type_name": u"排行榜"},
            {"type_id": "new", "type_name": u"新剧"},
        ] + [{"type_id": k, "type_name": n} for k, n, _ in _HG_CONTENT_TYPES]
        filters = {}
        for k, _n, cats in _HG_CONTENT_TYPES:
            if len(cats) > 1:
                filters[k] = [{
                    "key": "cat",
                    "name": "分类",
                    "value": [{"n": nm, "v": v} for v, nm in cats],
                }]
        filters["rank"] = [{
            "key": "cat",
            "name": u"榜单",
            "value": [{"n": nm, "v": k} for k, nm in _HG_RANK_TABS if not k.startswith("new-")],
        }]
        filters["new"] = [{
            "key": "cat",
            "name": u"榜单",
            "value": [{"n": nm, "v": k} for k, nm in _HG_RANK_TABS if k.startswith("new-")],
        }]
        # 首页那块「热门推荐」是壳拿 homeContent.list 自己起的名渲染的。
        # 按你的要求默认不返回，首页只剩分类入口；想恢复设 HG_HOME_REC=1。
        vlist = []
        _rec_on = str(os.environ.get("HG_HOME_REC", "") or "").strip().lower() in (
            "1", "true", "yes", "on")
        if _rec_on:
            try:
                vlist = _hg_home_sections()
            except Exception:
                vlist = []
            try:
                _hg_prefetch([x.get("vod_id") for x in vlist], 6)
            except Exception:
                pass
            _hg_diag("home", "rec", n=len(vlist))
        else:
            _hg_diag("home", "rec", n=0, why="已关闭首页推荐（HG_HOME_REC=1 可恢复）")
        return {"class": class_list, "filters": filters, "list": vlist}

    def categoryContent(self, tid, pg, filter, extend):
        """走官方分类页 /category/{route}/{item}?page=N，标题取官方 series_name。"""
        try:
            page = max(1, int(pg))
        except (TypeError, ValueError):
            page = 1
        route = _hg_route_of(tid)
        ext = {}
        if isinstance(extend, str) and extend:
            try:
                ext = json.loads(extend)
            except Exception:
                ext = {}
        elif isinstance(extend, dict):
            ext = dict(extend)
        cat = str(ext.get("cat") or ext.get("分类") or "").strip()
        if isinstance(filter, dict):
            f2 = str(filter.get("cat") or filter.get("分类") or "").strip()
            if f2 and not cat:
                cat = f2
        if cat in ("all", u"全部", "0", "all_cat"):
            cat = ""
        if str(tid) in ("rank", "new"):
            return _hg_rank_content(tid, page, cat)
        try:
            p = _hg_category_page(route, cat, page)
        except Exception:
            p = _hg_category_page("real-drama", cat, page)
        rows = p.get("recommendList") or []
        page_data = p.get("pagination") or {}
        return {
            "page": page,
            "pagecount": int(page_data.get("totalPages") or 1),
            "limit": len(rows),
            "total": int(page_data.get("total") or len(rows)),
            "list": _hg_cat_list(rows),
        }

    def searchContent(self, key, quick=False, pg="1"):
        try:
            page = max(1, int(pg))
        except (TypeError, ValueError):
            page = 1
        key = str(key or "").strip() or "短剧"
        # 漫剧相关搜索走关键词轮换，提升翻页体验
        if key in ("漫剧", "动漫短剧"):
            return _search_by_keywords(_MANJU_KEYWORDS, page)

        p = _search_loader(key, page)
        rows = p.get("searchList") or []
        if not rows:
            # 官方搜索风控不可用时，扫官方分类页按标题命中兜底
            scanned = _hg_search_scan(key, page)
            if scanned.get("list"):
                return scanned
        try:
            total = int(p.get("totalCount") or 0)
        except Exception:
            total = 0
        try:
            total_pages = int(p.get("totalPages") or 1)
        except Exception:
            total_pages = 1
        out = []
        seen = set()
        for x in rows:
            it = _item(x)
            vid = str(it.get("vod_id") or "")
            if not vid or vid in seen:
                continue
            seen.add(vid)
            out.append(it)
        if not total:
            total = len(out)
        try:
            _hg_prefetch([x.get("vod_id") for x in out], 2)
        except Exception:
            pass
        return {
            "page": page,
            "pagecount": max(1, min(50, total_pages if total_pages else 1)),
            "limit": len(out),
            "total": total,
            "list": out,
        }


    def detailContent(self, ids):
        """壳可能一次要好几个（批量解析）：逐部出卡；只传一个时行为完全不变。"""
        id_list = list(ids) if isinstance(ids, (list, tuple)) else [ids]
        out = []
        for _one in id_list[:10]:
            try:
                out.extend(self._detail_one(_one).get("list") or [])
            except Exception as exc:
                _hg_diag("detail", "skip", id=_hg_clean(_one, 30), err=type(exc).__name__)
        if len(id_list) > 1:
            _hg_diag("detail", "batch", asked=len(id_list), got=len(out))
        return {"list": out}

    def _detail_one(self, ids):
        sid = str(ids[0] if isinstance(ids, (list, tuple)) else ids)
        sid = sid.replace("hg-series-v1:", "")
        s = {}
        seasons = []
        # 磁盘缓存（6 小时）：同一部剧二次进入零请求
        try:
            _c = _hg_disk_load().get(sid)
            # 单季结果只锁 2 小时：一次搜索抖动就当成「这部剧只有一季」并锁 24 小时，
            # 是「第二季没合并」最隐蔽的一种。v4 顺带作废旧版缓存。
            # 先判类型再取字段：缓存值万一不是 dict，原来会在这一行抛异常被外层吞掉，
            # 结果是把好缓存整条清空重来。
            _ttl = 600
            if isinstance(_c, dict):
                _ttl = 12 * 3600 if len(_c.get("seasons") or []) > 1 else 2 * 3600
                if _c.get("trim"):
                    _ttl = 600
            if isinstance(_c, dict):
                # 列表页看到过这部剧的当前集数，和缓存里记的不一样 → 官方加集了，直接重拉
                _now = _HG_STAMP.get(sid)
                _old = _c.get("cnt")
                if _now and _old and int(_now) != int(_old):
                    _hg_diag("detail", "stale-cnt", sid=sid, cached=_old, now=_now,
                             why="官方集数变了，缓存作废")
                    _c = None
                    # 连 5 分钟的详情缓存和 15 分钟的分季结论一起作废，
                    # 否则「重拉」还是从这两个内存缓存里拿旧数据，等于白作废
                    try:
                        _HG_SEASON_CACHE.pop("sd:" + str(sid), None)
                        _HG_SEASON_CACHE.pop("season:" + str(sid), None)
                    except Exception:
                        pass
            if isinstance(_c, dict) and _c.get("v") == 4 and time.time() - float(_c.get("ts") or 0) < _ttl:
                seasons = [(int(x.get("no") or 0), x.get("sd") or {})
                           for x in (_c.get("seasons") or []) if isinstance(x, dict)]
                for _no, _d in seasons:
                    if str(_d.get("series_id") or u"") == sid:
                        s = _d
                        break
                if not s:
                    s = _c.get("self") or {}
                # 打开即刷新：缓存超过 HG_SWR_MIN（默认 30 分钟）就先返回旧的，
                # 同时后台重拉一次，下次进来就是最新的。不阻塞这次打开。
                if time.time() - float(_c.get("ts") or 0) > _HG_SWR_AFTER:
                    _hg_diag("detail", "swr", sid=sid,
                             age_min=int((time.time() - float(_c.get("ts") or 0)) / 60))
                    _hg_refresh_async(sid)
        except Exception:
            s = {}
            seasons = []
        if not s:
            s = _hg_sd(sid)
            try:
                seasons = _hg_seasons(sid, s)
            except Exception:
                seasons = [(0, s)]
            try:
                _all = _hg_disk_load()
                _payload = {"v": 4, "ts": time.time(), "trim": 1 if str(sid) in _HG_TRIM_SIDS else 0,
                            "cnt": int(s.get("episode_cnt") or len(_hg_slim(s).get("vid_list") or []) or 0),
                            "self": _hg_slim(s),
                            "seasons": [{"no": no, "sd": _hg_slim(d)} for no, d in seasons]}
                _all[sid] = _payload
                # 同组的其它季也各存一份，从搜索直接点别的季也能零请求命中
                for _no, _d in seasons:
                    _xid = str(_d.get("series_id") or "")
                    if _xid and _xid != sid:
                        _all[_xid] = _payload
                _hg_disk_save(_all)
            except Exception:
                pass
        vids = s.get("vid_list") or []
        if not vids:
            _hg_fail("detail/no-vids", HongguoPluginError(
                "详情里没有 vid_list", code="HG_E_MODEL_EMPTY"),
                sid=sid, keys=len(s.keys()) if isinstance(s, Mapping) else 0)
        actors = [str(x.get("nickname")) for x in (s.get("celebrities") or []) if isinstance(x, dict) and x.get("nickname")]
        # 弹幕映射：把每一季的每一集都登记到本剧
        try:
            _dm_series_load()
            for _no, _d in seasons:
                for _one in (_d.get("vid_list") or []):
                    _dm_remember_series(_one, sid)
            for _one in vids:
                _dm_remember_series(_one, sid)
            _dm_series_save()
        except Exception:
            pass
        play_from = []
        play_url = []
        if len(seasons) > 1:
            # 多季：一季一条线路，画质固定超清（1080），线路名「第一季 超清」
            used = set()
            # 季号 → 线路名：按季号排位命名，没季号的按它在序列里的位次补
            seq = sorted(seasons, key=lambda t: (t[0] if t[0] else 1))
            label_of = {}
            for i, (no, d) in enumerate(seq, 1):
                label_of[id(d)] = u"第%s季" % _hg_cn(no if no else i)
            # 当前点进来的那一季排第一，壳默认选中的就是它，避免点第五季却落在第一季上
            def _is_self(d):
                if d is s:
                    return True
                return str(d.get("series_id") or u"") == str(sid)
            ordered = [x for x in seq if _is_self(x[1])] + [x for x in seq if not _is_self(x[1])]
            for no, d in ordered:
                evids = [str(v) for v in (d.get("vid_list") or []) if str(v).isdigit()]
                if not evids or tuple(evids) in used:
                    continue
                used.add(tuple(evids))
                label = (label_of.get(id(d), u"红果") + u" 超清")
                if label in play_from:
                    label = label + u"2"
                eps = "#".join(
                    "%d%s%s%s:%s" % (i + 1, "$", EPISODE_PREFIX, "1080", v)
                    for i, v in enumerate(evids)
                )
                play_from.append(label)
                play_url.append(eps)
            # 全季连播：按季号把所有季的集数顺次拼成一条线路，放在最前面（壳默认选它）。
            # 这样第一季最后一集播完，壳的「自动下一集」会直接接第二季第一集，
            # 不用退回列表手动换线路。各季各自的线路照旧保留。
            if len(play_from) >= 2:
                _seen_all = set()
                _eps_all = []
                for _no, _d in seq:
                    for _v in (_d.get("vid_list") or []):
                        _v = str(_v)
                        if not _v.isdigit() or _v in _seen_all:
                            continue
                        _seen_all.add(_v)
                        _eps_all.append("%d%s%s%s:%s" % (
                            len(_eps_all) + 1, "$", EPISODE_PREFIX, "1080", _v))
                if len(_eps_all) > len(play_url[0].split("#")):
                    play_from.insert(0, u"全季连播 %d集" % len(_eps_all))
                    play_url.insert(0, "#".join(_eps_all))
                    _hg_diag("detail", "chain", sid=sid, seasons=len(play_url) - 1,
                             eps=len(_eps_all))
        if not play_from:
            # 单季：沿用模板五档画质线路，原样不动
            for q, line_name in _HG_QUALITY_LINES:
                eps = "#".join(
                    "%d%s%s%s%s:%s" % (i + 1, "$", EPISODE_PREFIX, q, "", str(v))
                    for i, v in enumerate(vids)
                )
                play_from.append(line_name)
                play_url.append(eps)
        # 弹幕映射补齐：详情命中磁盘缓存时，上面登记 vid 的那段会被跳过，
        # 导致 playerContent 里算不出 sid、弹幕字段直接消失。这里按最终播放列表补一遍。
        try:
            _seen_vid = set()
            for _grp in play_url:
                for _ep in str(_grp or "").split("#"):
                    if "$" in _ep:
                        _v = _ep.rsplit("$", 1)[-1].strip()
                        if _v and _v not in _seen_vid:
                            _seen_vid.add(_v)
                            _dm_remember_series(_v, sid)
            if _seen_vid:
                _dm_series_save()
        except Exception:
            pass
        _hg_diag("detail", "ok", sid=sid, vids=len(vids), seasons=len(seasons),
                 lines=len(play_from))
        return {"list": [{"vod_id": sid, "vod_name": str(s.get("series_name") or ""), "vod_pic": str(s.get("series_cover") or ""), "vod_year": "", "vod_area": "", "vod_director": "", "vod_actor": ",".join(actors), "vod_content": str(s.get("series_intro") or ""), "vod_remarks": str(s.get("episode_right_text") or ""), "vod_play_from": "$$$".join(play_from), "vod_play_url": "$$$".join(play_url)}]}

    def playerContent(self, flag, id, vipFlags=None):
        self._adopt_working_pair()
        # 从线路名（flag，如“红果超清/红果高清”）与集 token 双路解析清晰度。
        # token 已是 'hg-episode-v1:<q>:<vid>'，flag 用于旧壳只传线路名时兜底。
        token_q, vid = _split_episode_token(id)
        line_q = "1080"
        for name_key, candidate_q in _QUALITY_LINE_NAME_TO_Q.items():
            if name_key in str(flag or ""):
                line_q = candidate_q
                break
        q = line_q if token_q == "1080" and str(flag) else token_q
        q = q if q in _QUALITY_LINE_NAME_TO_Q else "1080"
        if not str(vid).isdigit():
            _hg_fail("playerContent/token", HongguoPluginError(
                "集 token 里没有有效 vid", code="HG_E_TOKEN"),
                token=_hg_clean(id, 60), flag=_hg_clean(flag, 40))
            return {
                "parse": 1,
                "jx": 0,
                "playUrl": "",
                "url": SITE + "/",
                "msg": "红果取流失败：集 token 里没有有效 vid",
                "header": {"User-Agent": UA},
            }
        # 取流优先级：本机 Range 流服务 > 上游直通直链 > 壳代理。
        # 壳代理（fongmi / OK影视 的 /proxy?do=py）实测会忽略 Range：对 bytes=0-1023
        # 也回 200 + 整片 + chunked，既无 Content-Range 也无 Accept-Ranges，且必须
        # 等整片下载 + CENC 解密完成后才吐首字节（单集 12~17MB，实测 8.7s / 16.3s，
        # 超过播放器默认 8s 读超时）。首集常因缓存或重试侥幸起播，切到第二集时播放器
        # 按新 URL 重新请求即超时失败，表现为“第 1 集能放、第 2 集不能放”。
        # 本机流服务支持 206 / Content-Range / Accept-Ranges，首字节约 1s，切集稳定。
        # 会话构建（取 video_model + 拉 moov）在冷启动时约 3~18s，若等到播放器连上来
        # 才建会话，响应头会被拖延到读超时。这里先建好会话再交 URL。
        cfg = {"device_id": self.device_id or "", "install_id": self.install_id or ""}
        session = None
        build_err = None
        build_started = time.time()
        _hg_diag("play", "start", vid=vid, q=q, line=_hg_clean(flag, 40),
                 did=_hg_tail(self.device_id), iid=_hg_tail(self.install_id))
        try:
            session = _stream_session(vid, cfg, q)
        except Exception as exc:
            build_err = exc
            code = _hg_fail("playerContent/session", exc, vid=vid, q=q,
                            ms=_hg_ms(build_started))
            # 空体/超时是成波来的：同一秒重试没用，挂后台继续试，
            # 用户过一会儿再点一次通常直接命中缓存。
            if _hg_retryable(exc):
                try:
                    _warm_burst(vid, dict(cfg), q)
                    _hg_diag("warm", "已挂后台重试", vid=vid, q=q, code=code)
                except Exception:
                    pass

        def _try_start_server(wait):
            # 启本机服务对弹幕(直通路)/中转(CENC路)是加分项而非前提；宿主环境禁止
            # bind 127.0.0.1 时 _start_stream_server 可能挂起，放线程里限时等，
            # 拿不到端口就放弃，绝不让播放器干等。
            box = {}
            def _run():
                try:
                    box["port"] = _start_stream_server()
                except Exception:
                    pass
            t = threading.Thread(target=_run, daemon=True)
            t.start()
            t.join(wait)
            return box.get("port", 0)

        # 直通流（上游本来就是标准 hvc1/avc1 未加密）：本机服务起不来时可以直接把
        # 上游 https 直链交给播放器，播放器自己发 Range，不会卡在“正在获取播放信息”。
        plain_url = ""
        if isinstance(session, _PlainSession):
            plain_url = session.url or ""

        port = _try_start_server(1.5 if plain_url else 3.0)
        if not port:
            _hg_diag("route", "本机流服务不可用", plain=int(bool(plain_url)))
        if port:
            query = urlencode(
                {
                    "vid": vid,
                    "q": q,
                    "did": self.device_id or "",
                    "iid": self.install_id or "",
                }
            )
            result = {
                "parse": 0,
                "jx": 0,
                "playUrl": "",
                "url": "http://127.0.0.1:%d/hg.mp4?%s" % (port, query),
                "header": {"User-Agent": UA},
            }
            try:
                result.update(self._danmaku_payload(port, vid))
            except Exception:
                pass
            _hg_diag("route", "本机流服务", port=port, q=q,
                     session=("plain" if plain_url else "cenc"))
            return result
        # 本机服务不可用（宿主禁 bind 127.0.0.1）：直通流直接交上游直链。
        if plain_url:
            _hg_diag("route", "上游直链", host=urlparse(plain_url).netloc, q=q)
            return {
                "parse": 0,
                "jx": 0,
                "playUrl": "",
                "url": plain_url,
                "header": {"User-Agent": MEDIA_UA},
            }
        # 回退：壳代理（保留壳自带的 do=py，不要覆盖 do）
        proxy = ""
        try:
            if hasattr(self, "getProxyUrl"):
                proxy = (self.getProxyUrl() or "").strip()
        except Exception:
            proxy = ""
        if proxy:
            sep = "&" if "?" in proxy else "?"
            url = proxy + sep + urlencode(
                {
                    "vid": vid,
                    "q": q,
                    "hg": "cenc",
                    "did": self.device_id or "",
                    "iid": self.install_id or "",
                }
            )
            _hg_diag("route", "壳代理", proxy=_hg_clean(proxy, 60))
            return {
                "parse": 0,
                "jx": 0,
                "playUrl": "",
                "url": url,
                "header": {
                    "User-Agent": MEDIA_UA,
                    "Referer": "https://novel.snssdk.com/",
                },
            }
        # 一条路都不通：错误码写进日志和「最近失败」摘要，再回退到官网首页。
        reason = ""
        if build_err is not None:
            reason = _hg_clean(build_err, 160)
            code_text = _hg_err_code(build_err)
            if code_text and not reason.startswith(code_text):
                reason = "%s %s" % (code_text, reason)
        _hg_fail(
            "playerContent/route",
            build_err if build_err is not None else HongguoPluginError(
                "无可用播放路由", code="HG_E_NO_ROUTE"
            ),
            vid=vid, q=q, port=port, plain=int(bool(plain_url)), proxy=int(bool(proxy)),
            ms=_hg_ms(build_started),
        )
        try:
            print("[红果] 取流失败 vid=%s q=%s：%s（原因见 hg_last_error.txt / hg_diag.log）"
                  % (vid, q, reason or "无可用播放路由"))
        except Exception:
            pass
        return {
            "parse": 1,
            "jx": 0,
            "playUrl": "",
            "url": SITE + "/",
            "msg": "红果取流失败：" + (reason or "无可用播放路由"),
            "header": {"User-Agent": UA},
        }

    def proxy(self, param):
        """部分壳调用 proxy 而不是 localProxy。"""
        return self.localProxy(param)

    def localProxy(self, param):
        """壳本地代理：优先读缓存；无原生 AES 时避免一上来就解 1080 整集导致超时失败。"""
        import traceback
        param = param or {}
        self._adopt_working_pair()
        vid = str(
            param.get("vid")
            or param.get("id")
            or param.get("mediaId")
            or ""
        ).strip()
        if not vid or not str(vid).isdigit():
            for _key, value in param.items():
                text = str(value or "").strip()
                if text.isdigit() and len(text) >= 10:
                    vid = text
                    break
        if not vid:
            return [400, "text/plain; charset=utf-8", b"missing vid"]

        try:
            cfg = {
                "device_id": str(param.get("did") or self.device_id or ""),
                "install_id": str(param.get("iid") or self.install_id or ""),
            }
            user_q = str(param.get("q") or param.get("quality") or "").strip()
            # 有原生 AES：优先 1080；纯 Python AES 很慢：先 720 保证能播，再尝试更高
            if user_q:
                order = [user_q, "1080", "720", "480", "360"]
            elif _aes_is_fast():
                order = ["1080", "720", "480", "360"]
            else:
                order = ["720", "480", "1080", "360"]
            # dedupe
            seen_q = set()
            quals = []
            for q in order:
                if q and q not in seen_q:
                    seen_q.add(q)
                    quals.append(q)

            # 缓存命中直接返回。用户指定线路清晰度(user_q)时，只认该清晰度缓存，
            # 不能回退命中其它清晰度缓存（否则请求480会拿到360内容）。
            if user_q:
                primary = [user_q]
            else:
                primary = quals
            for q in primary:
                cached = _hg_cache_get(vid, q)
                if cached and _hg_cached_ok(cached):
                    return [200, "video/mp4", cached]

            model = None
            rows = None
            for _round in range(4):
                try:
                    model = _video_model(vid, cfg)
                except Exception as err:
                    if not _is_empty_model_error(err) or _round >= 3:
                        raise
                    pair = _rotate_stream_device()
                    cfg = {"device_id": pair["device_id"], "install_id": pair["install_id"]}
                    self.device_id = pair["device_id"]
                    self.install_id = pair["install_id"]
                    continue
                rows = _video_list_from_model(model)
                if rows:
                    break
                if _round >= 3:
                    break
                pair = _rotate_stream_device()
                cfg = {"device_id": pair["device_id"], "install_id": pair["install_id"]}
                self.device_id = pair["device_id"]
                self.install_id = pair["install_id"]
            if not rows:
                return [500, "text/plain; charset=utf-8", b"empty video list"]

            last_err = None
            for wanted in quals:
                try:
                    # 再查一次该清晰度缓存（model 解析后）
                    cached = _hg_cache_get(vid, wanted)
                    if cached and _hg_cached_ok(cached):
                        return [200, "video/mp4", cached]

                    if _hg_is_bytevc2(rows):
                        # 只认这一档自己验过的标准 hvc1 直通流；encv 是加密壳，不能直接回吐
                        try:
                            plain_sess = _hg_plain_session(model, wanted, True)
                        except Exception:
                            plain_sess = None
                        if plain_sess is not None:
                            body = b""
                            try:
                                body = _multi_download(
                                    plain_sess.url,
                                    headers={"User-Agent": MEDIA_UA, "Referer": "https://novel.snssdk.com/"},
                                    timeout=150 if _aes_is_fast() else 120,
                                    workers=4,
                                )
                            except Exception as dl_err:
                                last_err = "plain download failed q=%s err=%s" % (wanted, dl_err)
                                body = b""
                            _i = body.find(b"stsd") if body else -1
                            if body and (_i < 0 or body[_i + 16 : _i + 20] in _DECODABLE_ENTRIES):
                                try:
                                    _hg_cache_put(vid, wanted, body)
                                except Exception:
                                    pass
                                return [200, "video/mp4", body]

                    _, item = _select_quality(rows, wanted)
                    url = _media_url(item)
                    spade = _spade_value(item)
                    if not url or not spade:
                        last_err = "missing url/spade q=%s" % wanted
                        continue
                    try:
                        key_seed = _key_seed_from_model(model)
                        if key_seed:
                            url = _decrypt_spade_url(url, key_seed)
                    except Exception:
                        pass

                    # 下载超时：纯 AES 环境更短，避免壳端空等后失败
                    dl_timeout = 150 if _aes_is_fast() else 90
                    media_headers = {
                        "User-Agent": MEDIA_UA,
                        "Referer": "https://novel.snssdk.com/",
                    }
                    try:
                        body = _multi_download(
                            url,
                            headers=media_headers,
                            timeout=dl_timeout,
                            workers=4 if _aes_is_fast() else 3,
                        )
                    except Exception as dl_err:
                        last_err = "download failed q=%s err=%s" % (wanted, dl_err)
                        continue
                    if not body:
                        last_err = "empty body q=%s" % wanted
                        continue

                    # 纯 AES 且体积过大时跳过超大 1080，减少必超时
                    if (not _aes_is_fast()) and wanted in ("1080", "4k") and len(body) > 45 * 1024 * 1024:
                        last_err = "skip large %s without native AES size=%s" % (wanted, len(body))
                        continue

                    plain = decrypt_mp4_cenc(body, derive_content_key(spade))
                    if len(plain) < 64 or (b"ftyp" not in plain[:64] and b"moov" not in plain[:4096]):
                        last_err = "bad mp4 after decrypt q=%s" % wanted
                        continue
                    # 视轨校验：个别清晰度解出来只有音轨，换下一个清晰度，避免播出「只有声音」的片
                    _mo, _ms = _find_box(memoryview(plain), b"moov", 0)
                    if _mo >= 0 and _ms > 8 and not _moov_has_video_track(bytes(plain[_mo : _mo + _ms])):
                        last_err = "no video track q=%s" % wanted
                        continue
                    try:
                        _hg_cache_put(vid, wanted, plain)
                    except Exception:
                        pass
                    return [200, "video/mp4", plain]
                except Exception as one_err:
                    last_err = "%s q=%s" % (one_err, wanted)
                    continue

            msg = "hg localProxy failed: %s" % last_err
            return [500, "text/plain; charset=utf-8", msg.encode("utf-8")]
        except Exception as exc:
            msg = "hg localProxy failed: %s\n%s" % (exc, traceback.format_exc())
            return [500, "text/plain; charset=utf-8", msg.encode("utf-8")]

