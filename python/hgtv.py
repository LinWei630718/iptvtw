# hongguo Spider
import base64
import gzip
import hashlib
import http.cookiejar
import json
import random
import re
import ssl
import struct
import time
import urllib.error
import urllib.parse
import urllib.request
import zlib

try:
    from base.spider import Spider as BaseSpider
except Exception:
    class BaseSpider(object):
        def getCache(self, key): return None
        def setCache(self, key, value): return "fail"
        def delCache(self, key): return "fail"
        def getProxyUrl(self): return "fail"

# 6.0.0-fix（蜂蜜影视 / TVBox 适配版）
# 本文件在原版基础上修复：
#   1) 播放链路重做：改走站点自身放行的签名直链（网页播放器走的同一条），
#      不再依赖已失效的 App 播放模型接口，直链为 h264+aac 的 mp4，任意播放器可解
#   2) 翻页不再强依赖内核缓存，内核不给缓存也能正常翻页
#   3) 推荐流 / 搜索按 18 条合并成页，列表不再一次只出 6 部
#   4) 网络请求加超时与重试，弱网下不再整页空白
#   5) 站点未开放的集数给出明确提示，不再卡死或黑屏
_HG_MEM = {}
_HG_MODEL_MISS = {"n": 0}
_FEED_PAGE_SIZE = 18


def _random():
    return random.random()


def _now_ms():
    return int(time.time() * 1000)


def _rand32():
    return int(_random() * 4294967296)


def to_bytes(value):
    if isinstance(value, bytes):
        return value
    if isinstance(value, (bytearray, list, tuple)):
        return bytes(bytearray(value))
    return str(value).encode("utf-8")


def to_hex(data):
    return bytes(data).hex()


def hex_to_bytes(text):
    return bytes.fromhex(text)


def md5_bytes(data):
    return hashlib.md5(bytes(data)).digest()


def md5_hex(value):
    if isinstance(value, (bytes, bytearray, list, tuple)):
        return hashlib.md5(to_bytes(value)).hexdigest()
    return hashlib.md5(to_bytes(value)).hexdigest()


def sha512_bytes(data):
    return hashlib.sha512(bytes(data)).digest()


_B64_TABLE = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"


def b64_encode(data):
    return base64.b64encode(bytes(data)).decode("ascii")


def b64_decode(text):
    s = str(text).strip().replace("-", "+").replace("_", "/")
    pad = len(s) % 4
    if pad:
        s += "=" * (4 - pad)
    out = bytearray()
    acc = 0
    bits = 0
    for ch in s:
        if ch == "=":
            break
        v = _B64_TABLE.find(ch)
        if v < 0:
            continue
        acc = (acc << 6) | v
        bits += 6
        if bits >= 8:
            bits -= 8
            out.append((acc >> bits) & 0xff)
    return bytes(out)


def b64url_encode(data):
    return b64_encode(data).replace("+", "-").replace("/", "_").rstrip("=")


def utf8_decode(data):
    return bytes(data).decode("utf-8")


_AES_SBOX = (
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
)
_AES_INV_SBOX = [0] * 256
for _i, _v in enumerate(_AES_SBOX):
    _AES_INV_SBOX[_v] = _i
_AES_INV_SBOX = tuple(_AES_INV_SBOX)
_AES_RCON = (0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36)


def _aes_xtime(a):
    return (((a << 1) ^ 0x1b) & 0xff) if (a & 0x80) else ((a << 1) & 0xff)


def _aes_gmul(a, b):
    p = 0
    while b:
        if b & 1:
            p ^= a
        a = _aes_xtime(a)
        b >>= 1
    return p


_AES_M02 = tuple(_aes_gmul(i, 0x02) for i in range(256))
_AES_M03 = tuple(_aes_gmul(i, 0x03) for i in range(256))
_AES_M09 = tuple(_aes_gmul(i, 0x09) for i in range(256))
_AES_M0B = tuple(_aes_gmul(i, 0x0b) for i in range(256))
_AES_M0D = tuple(_aes_gmul(i, 0x0d) for i in range(256))
_AES_M0E = tuple(_aes_gmul(i, 0x0e) for i in range(256))


def _aes_expand_key(key):
    ek = list(key)
    for i in range(10):
        t = ek[-4:]
        t = t[1:] + t[:1]
        t = [_AES_SBOX[b] for b in t]
        t[0] ^= _AES_RCON[i]
        for _j in range(4):
            t = [t[k] ^ ek[-16 + k] for k in range(4)]
            ek += t
    return [ek[i:i + 16] for i in range(0, 176, 16)]


def _aes_encrypt_block(blk, rk):
    s = [a ^ b for a, b in zip(blk, rk[0])]
    for r in range(1, 10):
        s = [_AES_SBOX[b] for b in s]
        s = [s[0], s[5], s[10], s[15], s[4], s[9], s[14], s[3], s[8], s[13], s[2], s[7], s[12], s[1], s[6], s[11]]
        o = [0] * 16
        for c in range(4):
            a0, a1, a2, a3 = s[c * 4], s[c * 4 + 1], s[c * 4 + 2], s[c * 4 + 3]
            o[c * 4] = _AES_M02[a0] ^ _AES_M03[a1] ^ a2 ^ a3
            o[c * 4 + 1] = a0 ^ _AES_M02[a1] ^ _AES_M03[a2] ^ a3
            o[c * 4 + 2] = a0 ^ a1 ^ _AES_M02[a2] ^ _AES_M03[a3]
            o[c * 4 + 3] = _AES_M03[a0] ^ a1 ^ a2 ^ _AES_M02[a3]
        s = [a ^ b for a, b in zip(o, rk[r])]
    s = [_AES_SBOX[b] for b in s]
    s = [s[0], s[5], s[10], s[15], s[4], s[9], s[14], s[3], s[8], s[13], s[2], s[7], s[12], s[1], s[6], s[11]]
    return bytes(a ^ b for a, b in zip(s, rk[10]))


def _aes_decrypt_block(blk, rk):
    s = [a ^ b for a, b in zip(blk, rk[10])]
    for r in range(9, 0, -1):
        s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11], s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
        s = [_AES_INV_SBOX[b] for b in s]
        s = [a ^ b for a, b in zip(s, rk[r])]
        o = [0] * 16
        for c in range(4):
            a0, a1, a2, a3 = s[c * 4], s[c * 4 + 1], s[c * 4 + 2], s[c * 4 + 3]
            o[c * 4] = _AES_M0E[a0] ^ _AES_M0B[a1] ^ _AES_M0D[a2] ^ _AES_M09[a3]
            o[c * 4 + 1] = _AES_M09[a0] ^ _AES_M0E[a1] ^ _AES_M0B[a2] ^ _AES_M0D[a3]
            o[c * 4 + 2] = _AES_M0D[a0] ^ _AES_M09[a1] ^ _AES_M0E[a2] ^ _AES_M0B[a3]
            o[c * 4 + 3] = _AES_M0B[a0] ^ _AES_M0D[a1] ^ _AES_M09[a2] ^ _AES_M0E[a3]
        s = o
    s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11], s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
    s = [_AES_INV_SBOX[b] for b in s]
    return bytes(a ^ b for a, b in zip(s, rk[0]))


def aes_cbc_encrypt(key, iv, data):
    rk = _aes_expand_key(bytes(key))
    prev = bytes(iv)
    out = bytearray()
    pad = 16 - (len(data) % 16)
    padded = bytes(data) + bytes([pad]) * pad
    for i in range(0, len(padded), 16):
        blk = bytes(a ^ b for a, b in zip(padded[i:i + 16], prev))
        enc = _aes_encrypt_block(blk, rk)
        out += enc
        prev = enc
    return bytes(out)


def aes_cbc_decrypt_raw(key, iv, data):
    rk = _aes_expand_key(bytes(key))
    prev = bytes(iv)
    out = bytearray()
    for i in range(0, len(data) - 15, 16):
        blk = bytes(data[i:i + 16])
        dec = _aes_decrypt_block(blk, rk)
        out += bytes(a ^ b for a, b in zip(dec, prev))
        prev = blk
    return bytes(out)


_GORGON_84 = (0x4a, 0x16, 0x47, 0x6c, 0x84, 0x04)


def _rc4xg(data, key):
    s = list(range(256))
    j = 0
    for i in range(256):
        j = (j + s[i] + key[i % len(key)]) & 0xff
        s[i] = s[j]
    a = 0
    b = 0
    out = bytearray(len(data))
    for k in range(len(data)):
        a = (a + 1) & 0xff
        x = s[a]
        b = (b + x) & 0xff
        y = s[b & 0xff]
        s[a] = y
        out[k] = data[k] ^ s[(y + y) & 0xff]
    return bytes(out)


def _reverse_bits(n):
    r = 0
    for i in range(8):
        r |= ((n >> i) & 1) << (7 - i)
    return r & 0xff


def gorgon(body_json, query, khronos, xg_rand):
    xg_seed = 320
    data = bytearray(20)
    data[0:4] = md5_bytes(to_bytes(query))[0:4]
    if body_json:
        data[4:8] = md5_bytes(to_bytes(body_json))[0:4]
    mssdk = 67503104
    data[12] = mssdk & 0xff
    data[13] = (mssdk >> 8) & 0xff
    data[14] = (mssdk >> 16) & 0xff
    data[15] = (mssdk >> 24) & 0xff
    data[16] = (khronos >> 24) & 0xff
    data[17] = (khronos >> 16) & 0xff
    data[18] = (khronos >> 8) & 0xff
    data[19] = khronos & 0xff
    key = bytes([_GORGON_84[0], xg_seed & 0xff, _GORGON_84[1], (xg_rand >> 8) & 0xff,
                 _GORGON_84[2], _GORGON_84[3], (xg_seed >> 8) & 0xff, xg_rand & 0xff])
    out = bytearray(_rc4xg(bytes(data), key))
    for i in range(len(out)):
        a = out[i]
        out[i] = ((a >> 4) | (a << 4)) & 0xff
        a = out[i + 1] if i + 1 < len(out) else out[0]
        a ^= out[i]
        a = _reverse_bits(a)
        out[i] = (~(a ^ 20)) & 0xff
    ret = bytearray(6 + len(out))
    ret[0] = _GORGON_84[4]
    ret[1] = _GORGON_84[5]
    ret[2] = xg_rand & 0xff
    ret[3] = (xg_rand >> 8) & 0xff
    ret[4] = xg_seed & 0xff
    ret[5] = (xg_seed >> 8) & 0xff
    ret[6:] = out
    return to_hex(ret)


_TT_KEY1 = bytes([
    0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
    0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
    0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
    0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25])
_TT_KEY2 = bytes([
    0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
    0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
    0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D])
_TT_MAGIC = bytes([0x74, 0x63, 0x05, 0x10, 0x00, 0x00])


def _tt_seeds():
    return bytes(a ^ b for a, b in zip(_TT_KEY1, _TT_KEY2))


def _tt_key_iv(seed):
    return sha512_bytes(sha512_bytes(seed) + _tt_seeds())


def random_bytes(n):
    return bytes(int(_random() * 256) & 0xff for _ in range(n))


def tt_encrypt(buff, rand_num=None):
    buff = to_bytes(buff)
    rand = to_bytes(rand_num) if rand_num else random_bytes(32)
    key_iv = _tt_key_iv(rand)
    plain = sha512_bytes(buff) + buff
    ct = aes_cbc_encrypt(key_iv[0:16], key_iv[16:32], plain)
    return _TT_MAGIC + rand + ct


def playback_url(value, seed):
    if not value or re.match(r"^https?://", value, re.I):
        return value
    data = b64_decode(value)
    if not seed:
        return utf8_decode(data)
    if len(data) < 20 or data[0] != 0xa8 or data[2] != 1 or data[3] != 0 or (len(data) - 4) % 16:
        raise ValueError("紅果備援網址格式不符")
    key_iv = _tt_key_iv(b64_decode(seed))
    plain = aes_cbc_decrypt_raw(key_iv[0:16], key_iv[16:32], data[4:])
    pad = plain[-1]
    if 0 < pad <= 16 and all(b == pad for b in plain[-pad:]):
        plain = plain[:len(plain) - pad]
    return utf8_decode(plain).rstrip("\x00")


def _count_bits(n):
    c = 0
    while n:
        c += n & 1
        n >>= 1
    return c


def derive_content_key(spade_b64):
    raw = b64_decode(spade_b64)
    if len(raw) < 3:
        raise ValueError("spade_a 資料過短")
    v6 = raw[0] ^ raw[1] ^ raw[2]
    v8 = len(raw) - v6 + 47
    if v8 <= 0 or v8 > len(raw) * 2:
        raise ValueError("spade_a 長度超出範圍")
    if 1 + v8 > len(raw):
        v8 = len(raw) - 1
    if v8 < 33:
        raise ValueError("spade_a 長度不足")
    v13 = bytearray(raw[1:1 + v8])
    va = 85
    vb = 246
    for i in range(v8):
        popcnt = _count_bits(i)
        if i & 1:
            v24 = va
            va = v13[i]
        else:
            v24 = vb
            vb = v13[i]
        v25 = v24 ^ v13[i]
        v26 = -21 - popcnt
        v13[i] = (v26 + v25) & 0xff
    hex_str = "".join(chr(v13[i]) for i in range(1, 33))
    if not re.match(r"^[0-9a-f]{32}$", hex_str, re.I):
        raise ValueError("spade_a 內容金鑰無效")
    return bytes.fromhex(hex_str)



_SBOX_HEX = (
    "fa7d086b9c59b34b045f39d0384a91990067a6209ff54d827326eedf18668333800319fbd9feaeaaa9b052c60bf379254e78b436ac5d1a279e88dbbd"
    "3c63ec4915c1301fdcb856d46ccdca0943c835a3ef1ef496d2fc0e727b9484d1ea455a62023fd31281342bdd7ee628f2a54613013b21f66137292a0d"
    "ed8cafbf9d5cbb24760f75e45389e1988db19a65704f544c58ab6e6f8b23c407110cbacfa0a48ed8053d14b2da74c3d7e7bed67fde48163e8590a155"
    "b7774222c986502e17f964312c9bf16d1c4468e3e9a89397cb3257ebe5716aadc0ccc7c5fd601da22d47a7e251695e7ace0a41b6958ff7b987e03a06"
    "108ab5f85bd5f0bc92ff7c2fc2e81b40ec1bdabdba98910cb22b83413467fb0ad876b546055961237590872ae350154cacb179ebaee595470468f086"
    "3d518b0fca8ee4b94ef21282bc0ed5f7ef2825cf5b5de96a5502e133be93e7f5ad9d3e3924a8e2fa1757d07a0d0830d6b8a38dfd079ac41e6e226497"
    "d21db0bf45663f6cdddb2780a711dca6c552f8c0b6c85c0073607ba01913aac935484bd3a4cd9f99f3104440547e29f4061fa2aba12f3cf6af856236"
    "217f5edf201ab3b4e6ff72848f6526945a77ea4378c74acc2c146bc6e87453fcd41cce317003188c96383289f13a5fd7f9a969b7633758c23bc371cb"
    "9e92018a0b4d889bbb4f6d6fe0fea549de561609ed9cc12dee817dd97cd12e425b4dc1a65dea44fd454e1ba13fd189e17d2faadbabad59cbb1ce9a28"
    "c9e0f670394ad7ff30f5ddbc573b118db2ee00b6e61a5a7cf9dec4cd2e80bbb94ca59f8408c66f426cf027e78b3a9c51fb6721754131a7ca20432ab7"
    "bfd97af2b5f88c2c23834f8f60a004133714e301c563665c7481df58bd68903dd2b334f419933229d649ae0d4bd8079eac1e2d0b40b872ba761071a8"
    "e4561d48fee5c24791da87269d1f886bc098be25099733a385165e7fdc6e54e9f7a9c8e8c377d0822bec02628a920e3eb00f05f3f19678388636183c"
    "24cf0ab453cc6165a4c794d5157e6def792235126a8e5206557b46645095e20cedd31703a29b99eb1cfcafd47369fa5ff72c1ebfc8e1f39f76807148"
    "aa94ad64fb89c660c332b34dd2e044dd5fa8b1c7682334c96d127fb7eb15bea9d17893a00c92a4d747e38ac270ab26419a79a7d814858fc06f56d08c"
    "11b92e3ce29dcf0ede035d463ecd38430f335ad91a656c223bfc30a688ea37a2b48d8e519cd640eef9f884f4ae97e9ca0a456757042f835cd5c5c482"
    "b6a391981f4aac96816ecb1b0908af1895497d54edfa16313adab866f5a5f1fe10010674cc63df7c2825f6ceb24f8be5bc8769bb8621070036e70b50"
    "599b1ce862581961f2bd275eba1de699423d0d2ab5dc5b29f02d4c537b6a734e3f75ff4ba1351755723920d3b0fdef02ec777ee42bdb90c1059e7ad4"
    "526b2413"
)

_BRANCH1_HEX = (
    "57bf108bb79db062f9ddb8b34a47bee8b3bef94ab8dde8474ae8b3b8f9be47dd61a28104334537d70437613381a2d745844ab4e398eafd11e3fd8498"
    "b44a11eae0677de42bdb422fe442e02b7d672fdb2b2fe47de042db677ddb2be0e42f67427fb56009323089a309897f3260b5a33032a309607f8930b5"
    "88777897ba1b4c37a579502595a42a7a252aa59550797aa4957a2550a52aa47950a495a5257a792a71b7ad0fc64af7740ff771c6adb7744ac6740fad"
    "71f74ab7ad4ac6710f74b7f7d7dad7646d7835c056055ecede53bf4acebf56de5e054a53de4ace5e56bf5305c3c7d76d93b272b56d72c393d7c7b5b2"
    "93b56dd7c372b2c7d7b293c36db5c772196c2cae6fb8f4c9aef4196f2c6cc9b86fc9ae2c19f4b86c2cb86f19aec96cf4ca8445f3da65a0d9f3a0cada"
    "4584d965dad9f345caa065844565dacaf3d984a09d415e0a15e72db0d0483dccade17a3dcc7ad0ad3d483de1ad3dcc3dd07ae1483b3669b3fe69f1c0"
    "b3f13bfe6936c069fec0b3693bf169366969fe3bb3c036f1fb407d7119d0737d4a82922f142983eb2f834a149282eb2914eb2f924a832982e1e69661"
    "20ce20e16120e12096e6e1ce20e16196e120cee696ce20e161e1e620e8f5c7f5c3f1318f0e7195b2de25fc8c31d58c3f73e7ed053fed31738cd505e7"
    "bb93ef436f426d60436dbb6fef9360426f6043efbb6d4293ef426fbb4360936d7a8422cd8c1a6cbdcd6c7a8c2284bd1a8cbdcd227a6c1a84221a8c7a"
    "cdbd846c8d3c89a068272dff6da1970434f1935d04936d3497a15df1345d04976d93f1a1888d2395dfa471c3957188df238dc3a4dfc395238871a48d"
    "23a4df8895c38d71ef80ad78927a572fed9462e342008202e382ed42629402004202e362ed820094d7d6aa5215e91722d67b5a2923764ace294ad623"
    "5a7bce7623ce295ad64a767b7c20c708d75b6b2f8a863eb553222f19b52f8a533e8619222975afbaa835aefc004f0783418cf92083f90041074f208c"
    "4120830700f98c4f078c410083204ff94e0c3ce26817cbbce2cb4e683c0cbc1768bce23c4ecb170c3c17684ee2bc0ccbe03eaca1d3ed343ba134e0d3"
    "ac3e3bedd33ba1ace034ed3eacedd3e0a13b3e3425bad462ed342dba622d25edd4baba34edba62d4252d34bad434ed2562baba2d81efc3c2b2998c62"
    "c28c81b2c3ef62992beea0010d0d2b2c012b2b0da0ee2c0d58c8c81dbf1dd92e1dd958bfc8c82e1dbf2e1dc858d91dc8c81dbf581d2ec8d9661b9bd3"
    "a7dea3a3d3a366a79b1ba3debc000d2766aef97d27f9bc660d007dae1503589bbd35e99c9be915bd58039c35bd9c9b5815e935035835bd159b9c03e9"
    "b6a79f1124c5f6de11f6b6249fa7dec524de119fb6f6c5a79fc524b611dea7f689142f17f133a64017a689f12f144033f140172f89a633142f33f189"
    "174014a6e071c11cfddce1e61ce1e0fdc171e6dcfde61cc1e0e1dc71c1dcfde01ce671e1573a33f11cd478d5f178571c333ad5d41cd5f1335778d43a"
    "33d41c57f1d53a78088862792e8b46c17946082e6288c18b2ec1796208468b88a397d3d4982794a7168ea4a594625286a5521694a48e86629486a5a4"
    "1652628ea4629416a5868e523652e9e425bf9eade49e3625e952adbf5d78159161828c68918c5d611578688265233c612b4b3e183c5f705354a17d68"
    "537d3c54705f68a1546853703c7da15f05723e53ac7c9500539505ac3e72007cac00533e05957c7222a8d4d0a278258979620edc245999ffdc997924"
    "0e62ff5924ffdc0e799959620e592479dcff62990e2115ca88f7e96fcae90e8815216ff7886fca150ee9f72115f7880eca6f21e97a7a6411296f4dc5"
    "114d7a29647ac56f29c511647a4d6f7aa17e640038a10088ec09b67a9b1717957a17ec9bb6099517e1d815cc4d697309a3b908439dcd2806197bd310"
    "7be431a7395563bebc5262f5be6239bc6355f552bcf5be63396252555fbe8576d139e4ee78c54a1b0d4907568e1099d55f091b20f4f2f425fd010966"
    "10f33f107699b4f3fc2fa67faae412417f12fcaaa62f41e4aa417fa6fc12e42f304e0ce6a51ceb26e6eb30a50c4e261cec21b0822072c91182c9ec20"
    "b021117281714f5d5fda5a1e5d5a815f4f711eda5f1e5d4f815ada714fda5f815d1e715a9253415beb0378cb5b7892eb4153cb03ebcb5b4192780353"
    "4103eb925bcb5378275da5010193d70d01d72701a55d0d93010d01a527d7935da5930127010d5dd71c2e6cc9bea8234ac9231cbe6c2e4aa8be4ac96c"
    "1c23a82e6ca8be1cc94a2e2338be0e2fe188dba0727eabe029bfadd5b3ec71c239251eecc21eb33971ecec2516a29c99b12be8ba99e816b19ca2ba2b"
    "b1ba999c16e82ba29c2bb11699baa2e8137bc881eebf705d6abb48af5a035eecf1b29be8d3533f50e83ff1d39bb250530a716072958e748172740a95"
    "6071818e958172600a748e71608e950a728171748fb79e7e30ab783d7e788f309eb73dab41bcf00b0e0acbbd0bcb410ef0bcbd0adc0ca1ab3a6fa77f"
    "aba7dc3aa10c7f6f3a7faba1dca76f0ca16f3adcab7f0ca7cc4684a5a53334958eef8e8a60047518328c3027538eba8527ba3253308c858e7d498c9e"
    "bd72f8a89ef87dbd8c49a8728d241b0200b1fed702fe8d001b24d7b13c57407bc917c9aa06297e12272a713c6dc4662e4c19b589a7127f3355911801"
    "9bdbb0574b6586dfa90b9b50940c6e597a1f95f95f6d7740f9777a5f951f406d34bae0af9a8e09519868071b426d140abf6dc8e692cd2f176a1f98c1"
    "46d792ea80df3d55049f39fed9702876b0fbe59d46d77ab9480f14cbf97972f29a7851810b440a1219c2557a7528d032eaa055a519b591c5b76ada15"
    "2d69a74edb0dc882a359df7c25dc6ef422829bb09940d1ebeb30d1408299a29bb1ab5f88c5db4e586e25f459dc7cdfa3f5f17e424c5aa508f4fc6edc"
    "59a5235f084225da714cf5feb39517f23e70a1ed9884c43f19b0da51d1bf5ab0041998c417f0b33ef2956da1a1beed1570f297331bc43bbc4bdd0da6"
    "6d7221f095beb3975a99d104b0bf4498bc4abd12a85215d2a587fb38e3d65b3abab8dbd60763a57bbdd23ca8924a52151528d2cad212bd3cfb5625e3"
    "b807badbd21295d24aa83c3d5b63ba87d6b87ba529e75f2b6faf02a5d936b9e1c9ebe35adae1e3ebb64959b9e06bed6bb236bc1a026f25672fabdfa9"
    "b96bd9c9e1b6da6325ab022f67efa95fe3c9dab6eb6139d9b6b76457960c7a5cb2795065ed22c2ec6c65c2a279ed32d0e40c3616d7375cfa7a16dcb7"
    "0cd76436d0a2326de5f96c425c57fa8c3716b66442edecf92265d03270663de8d61ea49eb4d9f81dff341be0e01d9bb459ffb478d8ce202f858af316"
    "a4d61ee61e68bd70f8b434ff9d59609b1e68a41ee6d670bd1b7fe0d9b49df834949741250a49c1f5e7309070104bf370f07073cb30106790be7da0be"
    "b80ce8b9418af51749a5c114104b6790f0b07073752541c9178a94c17390f030cb70106782986ac69fb9f3f6a1a1b6ddb7f74930b0ddc9f7a137a136"
    "47f4fae3fae1f898f39ff69839c6ea82b677a1b7dd21b0c94687b84a59ef127ec937b0a1f7dd36a142c6de66113d360daeb6d04b029af8c9ff469e44"
    "50b493965e3d429166460db636110d46bde65e42509a2e82cbb6c9f88d66363d4611c25e7882c9369acbd0aec6efe1ca11c438d281764ab171210041"
    "9777c0563c49bdab61c4c691ca6fd2b8b811d26fc4cae1c64a218171b1764100d2ca38c4ef91c6618071c17621314a01bb1425eb11ad3d670c45439f"
    "da299197173e906384ebadb5916b6b55a98af40bbd11e7142d6b25bbfe94ba575dd41a5767eb3dad94113b2591da17c5291fc30ca72090c103807cc6"
    "0bf16527341e06de5e27061e71b48b651080a783c120c67cfc03c620804190a7659e0b3427715e86c6c17c80a083271006345e711ea7e50b9fe99d50"
    "56709a761ab19692766a5d5ddd125d6ab1769a161d701fd6d0e9769a1ad6f669f0d01d1f166a9af612315dddf6501af069569f9ddd765d31ea92161a"
    "961577d0808686158e8e6cac5f646497172c64e48edf8e6cb1c0f76161d94c4686809595065077966ce48e5fac0e17e44c61c640d9e177b1e45f970e"
    "64acec0e3e5e80861333d7fc9acdf48a5eac01cece8a01accdde9a7451b38dcde953efd1d7937c5eb306803e74ac9ade8a4dce81efe951b3d3cd8d51"
    "815ece4dac8af49a5312ef884f5bfbe2990bd3c4f8170aa0a0448a978bf819536fdbd3cf0892627bfbcf6212db08ef53d39799f8c40b200ae2087b5b"
    "92cf53ef8a78a08b9744d319b87e738e60f070eeea78bc2b8e199d6aea2b9d99780e6abc73f0b8608e7eee70f060ee7e700ef3b8bc196a8eabf86a1d"
    "6e8e70f0fee038731d8eeaf8992b3c6a4497e03c3104a345b152290b4a524743430b47d2524a3129600444b13c9745a3d3d1cb696acc13ca2952314a"
    "8b524347c53c23041731c4e0474ac352520b2931b42ebc8ac8304146349e2fb829aad03e8cb2119eb095251f561ba974f2925fcfc148c6aeb00a3c34"
    "2f2ab429389ebed05f724f9b9274a9d6d0a93e1e2ab82fb4395680299f824a3e2ceecc3c1207b1ffff3c31076e92accc8002399f2956be4a4411546a"
    "6851bc924c872c923cee7fb1bea9ca02561f390031927f6e87bccc2c10c437e50a87f4fbb78826bd1432bde2623d3db28894b7a63787900a65c4fbf4"
    "f48a7b4407e5b790c4503f32009c50007be57407c48a90b7bd94e20832bda6378470ec0ae6a6b4b9fa9caa315f5e29b1d38cbd69883df2984af6045b"
    "bdcd8b8b83d15c84a1ce66142ade7adfb11c31a90bbd0bf64ddb84ca295fb11cdeb1aa7a104788cceaaf840d20fe17d33f5572897988f91f08bb4cda"
    "f72fdf42bbe81c72337a79fa92fe800417d5a03f537e09f22bbc62a58d86a403f23f097e55d3972008f610584110b9e4ed2eadc0afa7380f8fc0b8a7"
    "ae2f6d2d13182706f3528e7539c1647610d89008ad27edafc02e8f380ef3759852062713b82f8faea7402deda9f5e5ad2049bc81c980eb9380d2ae86"
    "8693aed28080c9eb65c9a9a0adf501bcbca08175c9ade529ebd2c980938086ae812d3cc9f5a0a9e5ae808680d293ebc9175fa564368e11546a39bf55"
    "f094dfd6501c5f879770c46d250e17b6645fd4111136545f8e64259712618fd99c3876f6d4e4110e5f361725f659f638e19c120fd158dd4c4e0bf415"
    "76b55da457ad012fae893de440f75fb85d0b51ceccd8157474ce95588b4c5d5129f49ff8e94d59a8954c748b584e51dda878d94df4e9a91fb8ca4039"
    "30053ac7553fbc4718cfdb9e9ec75b4f3f9855bc40853830b94a47ba3a30c74a05b9c0388585e5200778de5e47393a854ab0b840de205ef8050785e5"
    "069dbfd550eed3370cc777474530823a4a6623c2d2d2199a3f6e86d0559db7d3d3d0371deed53f86c7135d992918c642b7d5536e9d5086bf42194698"
    "932947ddeb46920d018058ff1e83143f89139538559e2ba0bde48b64d4be2446cf5e397c5801ff46800d92eb805389bf99aa488c394ffcbe5ec62454"
    "c436623317a68cda20bd8fcafcafb63b054cb4830da1360a281a5df0574dc784efcd6dd8aba532c3b6fc3bbdafca0fa075b50fcc60a36b49acd4854d"
    "284a06b78bdf366473c9e69765a36bbd5ca4078ad23a14681975d0aabd052205890ce12a7fc0ef9e2a82cf1cc0fc3c39794dbca8c196b453a7ed0664"
    "ce6c38143bd8fdf28a8cdac8e25b35edcd75986820c14cd184fa783f2126ad5251b712fa2c6ebeeffad1ac6fbe126e37acd8d52fc4e26d277f04a112"
    "ed38a67a7511c14dd84ca0e82f7a7e37eeacd291e2e85f2d58820c4cd30de21ddea5ee069950dff60a38f9cbf6d9ca0b791fb8d0d00bf8591ff9cab6"
    "4cadcc6802d85f22284c42e29f0c58edcb36b910f84adfd93d5ddc6deb83b1d2ed7dab9271dc03dd9e0a14696569895e695ea55e0954a90a8a5e691e"
    "544925a9d2ad31dd436bdcbd9dd2c37d9c71eb2d1e69894a6925549e5cedf0f175dba4acb1dcb5ece4705bed5481b792b397d5efd294f3af95b75781"
    "0df0b5f635591b5eecf1646ddbf5b09cad6c9bdcf0e4f571af92558197b3f7d468b63261d1bc761921685199b6f27c361b3d0bee5b866b322edb5bb2"
    "2b4b063d7d72061b8beb1b2e19a176f67c91326876d93ca8b276116132ae2b7dc61b0b5b3cf08e4ddaac7f5a4d7c5a9affce2cb038526b0f730fb45e"
    "4f38b31e746b0f520b6c67909742c5799a8d3ff06cda4e7c70da6cfc8e7f9a0d5e0f34520f736bb84878b8b9651888333988a533487858b88a20c5fa"
    "8ba4d2607acacba01285a4e05cdf3e505f5c06f4b339487898653888b87318483888a579e0ba92a0e40b45ca1bd8eee4fbd09b5064dbbbd0dbee10d8"
    "c1f94f7bcc1c63757b414c35e3cfdc79cc237afd71fd707cd0e41bd8d0fb6e9b98d050dbeedbfb243fa3435ca5ac7709cb7f234f2228da497c284d17"
    "c165db64219b8806a35e732f0621636fb3881e9b5baf1ea14833a306573cc1641bcd656864575be825014dfcaf46339b1ea30861d5cb3b602b9ea4de"
    "00a590c0b858bb2063dc08e93762e57069e3f770e508621cdc3062e348e5376900c0b860bb9018a5a0403ba5d8b810803069651ce2f748e3da0b1fc8"
    "31c2f5d62b7f4addab2e6a8dddde88738a96b592b35d8a92f588d69e85c8b5b5aa5445fa8648ed8be2948f614b86a2a14fed94c892b3f59e56ca889d"
    "32af13038f38dac5c332cf059a93382f53fe016310c020c8e35310c8e001403e3e08c0d3c160106305031aaf388fd3f2ef85f8b2131a0f0308e3603e"
    "40d0c1138b6e892eb5583b4d6e0b354d7b8998ae0f0d6bfb3478e88ebbcff44e282b384dcd0eb80f6be8743b8d6ebbae1875490b2e8d584b493bb5ae"
    "4e7b280df834abcfb60b163272c76f47723672c72f56870b4b43c0ca4a03a83b0acb8a3b684043c3a358e0fbb0b06c2607f2af4b073256764b474736"
    "d62f32b258a63063a0ecf0bb3a67c500d6666f4d403a564d6fc526e79feb493eaf5903407e1f2f40c389996be8a8d9c6e6f4a9f7cd402fe72656457a"
    "67cd667a452fd600a8f7f4a8d9e9e6c6295022c5cb45fc8c85e9cb4c7ce20510a9fd6731896d84f7f1298977c4a7ad7dbdb7ede9670449b10c453cd0"
    "c54ba2e9d0cc856962fc0b05777184bd2dc9e7a95ef595ce4c3c07350ede0c35c7557cb55c7830773f388779775cbf3947307838b839785c30473f77"
    "b50e4775fccc151e35753cde15c78c4e39374738787f709c94a185236929a598a314a918a545a9a1e5e9e8e53435e60922a24b709e1882d1513002a2"
    "589ecba29823a56129a98594a158a9940525a9a3f0629e11828b18620f46d9084fd8ca92e81715da141c4f5f9a6024635758051e235a175e45649820"
    "67ab8d543a79c9af5ae8541f0f15dc171f1acf17dc145568eb2fb9a74d49ba54e67f9e980337495658a64316491ef7bf49a2082a35b4285e9f1c2bc0"
    "944f41252540819ccf142b5f9618c93fb7435e667f1677661e8983d800df546501ab8f1c53b19e1e5944ca5b0062a81f19004e28487ac53da283f25b"
    "7d08e29b728543fafa9b43488532e27d9b5e4a7104995ed3f15b44935e0a995edbbd72ba036245c8cc69c6de34c41e7954156fbdef588e988ac1682e"
    "c25067335c423876057353da45257b82addee6c5bd94af580eef5855587d4ed5982faf94e585de05fba66d42ed3cc4fc0f845d26f98b6ad09f29bf04"
    "8219bd3c7d497f400688234466f557c2b9fb976fa15d740e10f99f04bfaae94b4410ff8be99f2ab981155eb1d24643d2964760dc53d797b69cd693f6"
    "57609747849c60323b086c4872047b08ac20885cba098c13837929c776dc9747d753a09687769756e0d7539c0987f93a4c29839375c349576940c0e4"
    "d775e964c0494043145ed0c0bae4d6f2c0d4faf2569024dedeb2e454d0d6fa006457404340e9c9f5c364c0f549406957f2c0169ee47ad0d436288eaf"
    "c34b38e27b89b0c76c4e1c3bcb081baa2f47b292aa8baf52321bc7088812870b5bb22fea07fb2c7b9c704e896bb59cdf2a78ca6f126af208872f9b8b"
    "5cd7c41e72a0fb2fd414fa4ffcf4a62c283ae74aac45a6ae8a68ac6e26a705fabaae85286766ec0a0f54bcec26faf4d417bbda2ed2abd680ee4a26ba"
    "452ca7a85ecfe3ada71fcc2aafc2c27290033c6f1c1d9863a5825c60635c65a01c98029d5da0421c985ca523726f102ffc8283c2cfaa1fde238ce76d"
    "a0a31c9d4225585c4d25b3116169e90ca1e389aecc140c63c369e89b0ef7ea1f1b83cedf6a28f7e9e91f3743e8aacedb6ea10c23ccc994a31d86e3bb"
    "a3221841dfdbea29b74e28c3b22acf15d05ef24546c0a9c4df4c552475ac807f23c006c9ff7523c9860040ac3e6a5f12a367af1c6d621bb1990b5346"
    "1c8f418a9fc4894aaa9c277e5f2f631242148d2ef8aba663a4bada0766b0d1b5505bfe9dde57e5071d90de4765fe57dbe1f7e636ecd55299cbc56f1b"
    "b2b964f3850226dac186501b5b56eac22614258395de029182448670b2604bdaa9d3760354607e9e9cbc265ec5b2d1b55e2ed2038e3fe0774f15c167"
    "7645466d64f1ad9a55691d0ab48c3a687967361c8a1dec7ef7a85b097d1637dfbd3f825089761c531356ecea1762f1b6e8e63a4c349060a61bfd68d6"
    "375f09b7c8173dbf1b7756e929427dbc9f109356f4ba88e0266c2650e54ca86f7b059cfc11a656663401ec2f5be805fcac8f7c652671f4af162c4106"
    "68fb6ce585bc0f5cec659b5c087ca5ef83e906f10eef527776142621f14f06ac2f4f058ab4b2b4445ee9d698eea135ee5445af340faaa492e99e2eee"
    "b6f5c1588534af52af04aa544f8fb444a5b4122aeef6be55c938ee81964ee9e13eceb8f577aac05bc9d9cbea4ef678b2b6ed7a58af06f85afb9aac0d"
    "56ae76f8f8ba6d524069caf9d7cadbabea57c9aac0cbd97bf658ee5a7672b8adb856b64d6e78f2fa998d9e05f72dc335b48c503b7bbe4819973e3983"
    "8dc5f50d0c345b99b0685ebb1e97ed2dd99525832d19d7953ee38d859b10b4a84c5b793e30bb6c1e5459bb882f1ca9b587b9075a3ecdc61f78366d27"
    "bc05b633c84ba1e22d1e78c7266dd63fa9279c590fbab5075caf071aa987b935d8263e2dcd7f671606386d367ec73fcd30459062fd455269c4d91c24"
    "3ccc321c7aae6f1fa82f2e0319243cdcdc320cc4703de5655089425265705d4950f28522dc1cc4d219243c2c3cdc390c241cc4d2bae0fca73d668eb1"
    "4d68f20d6ce87db73ee611bdfeb87e38a80d6c77f27de84dbcbd20a69af167ee849fd121ae52d6bb6cb2ed5de86d7708124c68a86df7ed7d97904d44"
    "8351afb9b42b9e60b28de63283ad578f50a49951a4e5bf91271114ed4d8390b1b759448fb057a3994d8f5184323e94a68be0b26d7eb2ab2df4928026"
    "b8316e84f41bb1725200605cb05d488c346e18b171a4f29befeae51db0154f528eb4f17bb87204317198b4320ef17ba410805248605cac5d4050a09d"
    "526c5c08c96e6fc43945cb5a3043a4f64571cac7fd42e4da5a55aa226bed850fe418e17acfd92e45c97a446b4ec9d97a4f2b65c4c6953fa5ee5517b5"
    "e42543d1d0a7764ae429ff8031086010f982018d579cc769311f04e0e96030886299d78981471ced9ff1290864f00020098471301f20e8e0976199e7"
    "02cd499c81f7427cd9098d87c78786b57d1a3c748546b75d578cbaa49d6607dc873574baa645b744975aac9da6dd677a2794159c67a73d94067c9ad5"
    "57b7859aa6bd444c579746aca5a49d5a9da5216065a501d4bb03f9d7a503192b93512cf07d58583623db050b19b9e3b7618565c51d34a0a15d2c5398"
    "315076f805391bb9e317abc3d9a5a3231beb1719a0cff5249fd7ac01bd66a0977313ab227b74d46c6373fad4269db362006bb3b735bf8f17a0e1c4cc"
    "63d47b7ad4ec747373201daba6b7629380b36633bda2176bfbd4feb398c436c27486221ee8e225d1d8dedbf6f43382a4c6142891e2e5227ebef894c4"
    "3be2d3d6d4bb38c2de96e4f388c2f465263ef1020268e6c23431fe853c2e3c98bb1f9cc38f5a87a33a7ee60a3bdc1c3c2e98a39f1aaffa4a67269e83"
    "9c3baedf9c23183cce9c9b231cbc3f385a076f869ae32abea79a3a1eef8a634684f274f4729a1af34acc91d2b094d442d1281801512ccf654ccad0c2"
    "91b494526811d125384f0cc1317831cf08c1450cd0518a548cd2a2d4d150ac54ca8292d40f4d3092b12bac020b2d74aa8f870aeed7b3d5462a9dbce4"
    "c907a36c84276c659011ad0baf22324caaf597dcd3a6245d2ff48b0a6d0a8ea7b40f8de70b6e8a2aaf245104951a5a14334b8ce49fdb212faf12a040"
    "ce678a952bf33f4fcc819b24924f8e1560caa7a00e806faab280d5475f2cd3218b248ffbec3f8b3b338fc4412d24bde21ed141f9e94d2fa538824caf"
    "3efdcd21a44219f1ada9584f8f2c22e5fd3e04f14db9c221e4ed5e39dd01b122140031d48f0c0027aff82da2492f854c19c560341761a8b3aa5eca57"
    "2c8777ace2a2923dc1566ff33ce634636f1a628f6d2e211cbb82b929a1f242ef827dd3364caa8ab7de772c474aac3ea76acc975720c18c5e9ebea43f"
    "2588fc4f825fd5f487dcfdcbb7d02e3a93761e62fe07c22e6103c41122b3fa2be9c00aaf5869a32182fc4535e8cf945f5c2288ffc5f44f9524424e30"
    "991d04364b3beecba3eb295063dd04c689c1bc945bcb2330eea9eb4b2e39823d04561044c984c37c1da694c1234eeb49fb2bb0cbce43bb4b2bf0eb29"
    "790a2f68605d726b7ab22ba021a0f4e4006f59722a686b7df2bae1a4ab3420606f606a7d792b48126a79600b4f723d68a1ebba7432e024a0ab6132e0"
    "fa24a0b4c965840dd5972359c4837d963d4e38a7754489c3852dd917711b14c7d7e1251c04d5c55729998d634509357984c397cd9dbd44d86336278e"
    "b7b55ace6f153ce557149d7325d62253ea072a5e76137d7a055dd7429433337617ae6b620f39d0fd7d4534563793d30254772513dd229653166a0afd"
    "277e7a53c08b5d6d17e9556b308e0eccb152412e61b93788177ec141912e50210e4caed215afe7f1d6d30f66ce31ae32500e4c812ed0518e4ea1122c"
    "b757616139c8019eb667d50fef11c6f38fe134f44d877bf551b7508611e664caedf48f9b217455e786a692d988b0b474f48d41e76f3594fbe1ef6df5"
    "945b2794b1d0f14457660a86a00ec3f1dd51118ce43a56c0bf116083a336b18dd8cc85290e1fb52f89d1b357225995e70a682ff9d6ffba9164430020"
    "0955ce13bfaf97311223e054e26fa62a258ec720c54fe24403a82dff4eefabf2f9e5e2b70dd95cb2ccf07b731bf66aa931218a4617fc55d3ed0e48ef"
    "a332ffabc12d2b7561138a925a525ded0333d8e88d420113ed6043a82f2a303f4f4e5e134dbb22a336b2f85633c71ff0bba78ae0b84a6f8148412243"
    "8162d9e85a2f17e9bfbc331b0ec50e760159b025edd469bbb4aab40e055a461ddb092b76f50bb17874e48b9edf8d3babdb8d7e34eb9baf84ef7bd4ad"
    "843e8b9b5374731d261a4830287a5d4470133613a9de1f41a8443b8eab14a13ede4f8849b22df4027ed647be77f6b24d2e04bed22eb47db6f242de07"
    "fe7226d4b7bd024e039338fa570b9620563b0a9390f827039708532b339a00f6bbc17483788777a949aaa2579a07555295a7475aa2525a09aa429a57"
    "a9570255a297a702455a595aac744f1777dbfa607a4ba7f4701f67dc77af746b4cf7d01a40777bdfaa641cf78657037cad7d4dd63df5ab6455e0e5ec"
    "55a034e5fc6be5edf53b55e0ade4ec65292b573b7c7cdd367d5c2bdb26373c792c277b3c59db763d567b2c772d3b39dc864b9f9cc1c6e2fac2968ceb"
    "4a9ff1c6418fcbf696ecca929acc46cf82fb96e15d069aad4c5834af44985d360faaac5d0c5a46a89d3d5fa49f4d085a54a6ad3c71de02db19e4a550"
    "1aaed7038dd4c3dc83d413ceac07dddaad178ed4dac3dc039f160fbc639336eb66039c361bbfe39f139f66e30f3c9bb60b6c139f96e6bf33013dd7b7"
    "0fd417979132b8ae2428f94229b89ef232a8442134982248b1fe22a9e20c121e6e6e1906691eee1c06120e620ee26c0e121e6619166e0e62e90c121e"
    "1c1ff3885e7f5c3f5dc2cfe8105729eb77de5e1053cdf833585d70fed31e33c726d406b63bf93ef43e092634d4b6fbf6db2634f90636f4be0436d9f6"
    "2ef4b63ba8c1d6ab4728d2cc42d8abd1cca6c728c7a641c8d8db2ca2dc4bc826a2c1a8d776d2f2dfc893088a133fd9d5167a494019da154f30d94673"
    "36191f4ad34570d94d1a378cd83852f9d2384c5a1987f83d1847daf83d5c398239dc183742fa8d58a977f5f20ed88a27042028d04e29362e46290030"
    "2ed82e242e08402924302ed6917e21726dad2a5562a7e46cbda79532b5e76c97a2643da2ad64b737e29ca265bdb5f6c207728c7025f292a168e8533b"
    "63982152fba238e55ae3ca9f52f7aa8bc4980f02f0743018f004c238980f107490cff8140432780008f2947fc018043076b1ccebc4c0238ec3c07b21"
    "beec84c6b47cc180c62bcee3cecbb0cc7381e624dd4eb303eec31a3aeab3d31e4a033ecd4ed3ee33bd13ca0abae343c3da3e0d1e4ed3a25ba24b2dd6"
    "adab4b23d652d24ed242a3dbae2b465da6abdb424dd35e229bc92816f83e2c2cfc2e9629cc18283bd0b0c2b2e20e1ad0eaced210b0b2d200db91ed82"
    "858cdcf18cecd2d1918df58b95dd81fcebd2818ce1829c8ddcf18bd5ea3d3a6ab6b1397db931ea3d3d6a76bae69adfc70bd0706200d0e77a92cf6bd6"
    "5b93ce593180b5d935c059b3995ed18b915e33d0cbb98955c939908e55d35bb1526cef6d7bfa194179ea5d1c616f4bf26b5f7c4ae21df169e17d6aff"
    "594c621b3f630a9448f1721142013473619a18ff683a43110f74f192014461fa32139f78cf1d6e0e1e17ccd11c67cecd110ede1f1ece1dd76fce110c"
    "611e171eccdd0fce418d577da53313cfa3534d1d8f77c5318547adc3511d3f735fad833743cd7115b268148c802896e78618bc986784e02260b488e8"
    "129c27867942793a7a394d8d29266568e1485a4aea6828562a6541492125e64869584a6a6ae828452a466951f2ebd96a23954e5e2ed5fa4bee695392"
    "26c888d68557111981872618c9d81556b2e4835136c213b615da87c6f3053745f785163ad5c74305d317fa45853605c7ca57095020e733c52307c037"
    "5559c0ea50c927c70a30e5538a579228824a0d2d9295f99f27e6c04d20f69fc59d9947e297992546f2cfed90fd2f96e9904592c7789ffee61052a18c"
    "11f276af9cee8058907e1f82f8a65ce1fc16925e718fe8a0f2d654aca7471691a657fc16d1a49742d7f4a697521c41a6130a8018ea470680797151c9"
    "9e60abb79b5079a177c1be69943697108e5dc1dcd98c62309a8b30d4471e739ab1370db12b25569f5335e6cb56552fe52b96c33b232655c55bef3b96"
    "9d43eefee55b68179074608557acb4d195b001e2089159fd1f9060462f4f5fd297493b0f31ff03614a2e11c4ff62faa7fa1244fe27c1af6a2f41fea2"
    "1af467cacab16e02e3c4605ee064c261be0e53ca22971cc11e022b081b12212798cc0e02a5ade51118f7d4f514e7a1dda515f8f5a8a51df7e5d1f514"
    "e511a7f5a4fd15d83e80b72c3915b4b534b53cb08527b91e893730b5bebc1524b53c851734b02eb93079dd70d2551a10dad53019707d1250723dd915"
    "d010507ad0d0755d3a1970128b3aa2c4e1c296ece6a2849a3cc2e1cb3182eae2ab94ccc6ace432c286eacb918eb80d8ae3ebf012f2db5a2de7b70a9e"
    "53e2c13ecb1e279cc7ce5e22ec319b13bb82ae6b21ca991929aabb92896e11cb81be221aab9bc969a92b8aceb9126b91fe0bd735b1871ce835e0c5ae"
    "b68bf4aa3df503152fbb893e290b3585fe133fbde94817a8100726571617e82847a7500940e71857192807a617184707e658a920b38ad7f378ebe907"
    "79dbb3ea87f708e3a0b0dc1bc40bbfe0cfdbabb0b01ce400f376fac7cd10baaacaf0f7b67acaad137dfac6a0f3b71acafac7701afaa6c3bd3a4353c9"
    "6c44585a465087e1f8eea808e5a85b28c3087332c358e878a22b33052b878fda97c4e8d998842ae789dfd7cb10eb7fdd48b2210041721d2be0df08b0"
    "7c91acca7305b497a212c76390e2277194519bd8466ce6c2158911702af137535466f8bdb90d7bb5c9e09695bab00945d57607a4f75199fff901d496"
    "7fa7f755e9981045a30bfeaad446a1808976b021d9fc72f1db866c2e742da9aef681196cf099e30ff8dd5345bb5fde990d876207f440b16c74ad978b"
    "891715989f2727af215ca5b740a420910e5a555a87022da3aba65d91511b597cdd802cd89276eab4c2ed463f9af5cd570914bd2e22b8099b9829bab9"
    "0e130d24bced8415bbfa8558cdf73dea56429fc5a4558a501fef27c4553af245cfefc69dc754ef8f2054a21d0317da3e5b7921ef01ab1d854948fc93"
    "9081491cfdab054b5fd9167a013feb23277f3913eadb5e01d4dd60ba41bcc3bbe93b7bd92617025ffb4b84a995194d002a5521cdabd42b816ebda553"
    "7ab88f333056baa78bbb6d7da92455d12bcd832a2dd1cb538122ad2c7ba0bbbd6f55328e84cad3232d5129ad8dbb57ba35a67b68f62a509a72feb5f2"
    "bc3eae956d931b9e9b9495ab1d3ebe6e6bc3ab01bed6be26b2fa9d2af05672f66eab3d96bb969d1cf69efa55b22af0721e96933d9eac6dbbc9a0c765"
    "7b4b76652e22cc2e9b0755d6d72e03cd56262c9a7dc3a54fce606371704d66a367c17dcb9ecf26042d2ad35663614bc675a5cf7852062d23d4ce9e2f"
    "ed41ea0967d6836e4fb3014e9b8ddff1f54f8b07deb1499ba8386f81ed0cf25281d60b476aed61ee9905b6894f4bf3df6e0dd7eb8146ea61db894fb3"
    "f1079e4d90145c4f791954a2b1340f770e030907037106090f37b70ccb809eebdb07ea8b541a4c11a4587f910f0b3707b1740609a148195c5712947c"
    "0c07713607090fb3993b6f2f88a966fc7b9f04131a6adb7d7a136a03db9d7c1f1f8e8f7944af3fae63ac2e38ff698f991d029b6c7b177adbf52ee167"
    "7488ab94df6d139a7c031b7ad163d32064ec6d16a0899fec6a0bbd24453b69f96fe4490466d460ebd52314696bee256413d160d46c9b8c0fa5e922b8"
    "1421ecd56866d363b90ced8a27986ca3418c236dfc1eae1c1702101468a7141b93d4bb7a79076cc5fc268d1b466c1ca9ac1c6e8c1b21fd466b1704a0"
    "141218171e691c26ad8c43fc12a3140018176c17d1da73b64b51b21e9d1279c95034f4a9b8de5a7be1033946aa48bf10b9b65695b256b2db1b714ed1"
    "45ad71e54fa97bd519b15372b6ded34af231cc10a97d519c00c8677c0a02193ce361e0bd105f764247bb58e67562e0110c62cc0701783a18180479ca"
    "3f600c0212e76558e6b940733a7802611ccc0708715abe6040e315e705a769f799de0965a7d6d5a5116b29696ba769d12dd1a5169d6ea7d901f7610d"
    "0fddf1a1616d9f0611d3d56da1a6692f66f5d9690fa5019f2e69a1d16dd715a3686858615971070d454676e9e8c8c6faf8edc876c14246ee96cd6414"
    "0b7c1f160075676908585969ea7041ce46eef8c51d7e17cb14660c94c6caee40fe75e9403173cdefe3056838c51ae0acd94cafe8ecad49e7ac18c0da"
    "3ef51e1d35dbd89c6b00e8733dc9e735d8e41c48c7aae9addddc18f59e1e353baa48af19e8e5dcc4b4b52f3e25f18ef87fa1009ab9304d8c889f3105"
    "4aa478b92029b6f7b63dfd8c8df03eb5ff2c26b1bc00a2307d99894ff93cf52e8eb0b72549349da18807ba78060fe78eeb37e70898d1a9a68ec7bbe2"
    "e7a0c6abbed29989e8e70e37078f0be6e7308f0b0fe6ee078aafd6c19ba1e6b80f8e33e7e60807efb9c2a3d6e1a88e9f43305a447409ce1324753414"
    "2b95b2a0a5149332b470242d7359340a464014cbc63ca13c1dbd9ca6283574942215a3b411430c5ecc334270b5901273a4342c250c136444ebc2ab88"
    "a20aed43e3f9829b5b59f2c1281be1092ff9f56cb5914a27abc043138c64ec0ae3e90bfda2429b8249976afd25f7b42982fb420b9deae3a129a8e493"
    "630598f27110fbcfe2cecc2326c9cafccf1373e062e5ab042890f39916c52b491441a586e3fe17cb74c822c9f59103e09baa2c60c8cbcc1223f9e776"
    "7048bf0f417c53ae21d32b7e8b68d24b48796b2ad6d3238b46bc4f7f7308a950507e0b49afb84774c00905400cf52303ac0879bb574e7740d36b7ad3"
    "4b298e206e4a9b4b08c7ae60e59512abcfa91af3d8238f39cdd89b86dbbcb8a8644fb0d5ea6c463118cd4518cb1193aae2adf71db44da8bcd0bb60df"
    "1dabaa97f215cbe1fe4ad8007184c8ac53259708e27f31fdb0cba49d8798ff818bce2177fff22db4e90f4830a397a72fe597207f510dfa3368483ab0"
    "c22b56da357d0922ff93e05704914b8e600f81157a8af3d0eed20afcfad2d6f2088c7bea2fe5583781716230810d8990134c6607ecf288d37ad2fe0a"
    "657032e1305f87290ad4d28efbf2e87a92c41b985a5fde0a28ed6a980cb83e090898bc6e38e92a0d5a1fc05b969c0adadc5a9ec20b1a58970968e8ba"
    "2e9d0c380f9a5a1ed8c2935c3db99eec0a680828e3184175f1554a664ff96dad96f35b050947dc06c5f17578f6451d51e270614b485672196143f5e5"
    "8963672f11f698cd657351424d1ee1f0ce29f1609f658f13b4405f118dd5cde4d51af06257db457a74ff85eb9ad8430e8c5d41d7b510e5ccc8d41545"
    "e75c89b5de94859a42ff899fe514d55dc944b7889f9efa818a97dd4453a0738cab0c9403f1bced59f5c37b848359c5eb79bcf5f4ab74a40b54880393"
    "900b8ca30373ac5480e7ed5558580e72048b0b7494a353a8705058ee0de2855fe53e7d63d0f95b0d0423a8c3707c77542d9da1a96436222cd5793bfd"
    "e366085d5efd63380d7dd3e182612c743cd195990965f87b5b3de5d69972d42d946184390088f5bf6e24d910385189e33148f1934bbe4856e5b902da"
    "ec95c347ed4b62f4d820b98e15f06f04a98ac4083895f89b654c4295f3c4efeb61caa84d6c233673ff6abb03d2fba8cc106aa350c0443bd8d5744c88"
    "a2d1057f5a2a33fcdedc86bdaafc006acbbfd3fb36ba965457fbc00ca26470cb4a5dd884976c7eb9f86d4336457aa05836bad6cb5107ad2aad438196"
    "c810aed25b20529022f8ccf107fceea9d7c48b0acccf9393da6e40166c493b7583dd2fefcc8643b1be55d3aec8a88d2c12cc14dd5c87890662d22a45"
    "a88ff713e2e6fb1e752ba1cf2be176a31fcdfae62cde76c28a5dfd428e63aaf747102ad1cd048a5e1711dc84ce2a1df9a2e777e325c8c0248efed582"
    "5dea6e30dd20dee18093bf9c09f56daff7810b6d9fadbc9091af6c0bbd809ff580fd25c2d4ca8c26c980d58ec22424feaff49dbd6c930b813e182bdd"
    "d3c5ddb6c73dd0dddeb72a199696e8e5a94091564095aa90e655ea95955492aae895e641b4c6dd2bdd1ad33d19b7ded2293ddcc75642e5e99196a894"
    "b74dcacad50e1f5f0eb7d51ecb5dcb4e7b59fd4e15782b39797b15284d39ff5a93b5e1d5005f6b5f5d0fcbc91e4fd6b64f5e1fd7cab6c90d397b4ffd"
    "2a591578cd6b9781662b13162bcf67138216956965b826b3d1b3e0beb264d0e3b2bd25bbb8bee1d22767b0b117298396116a67cf6b17116697cd832a"
    "bcb1b025e3bad267cdfaa7c503efd8a4efcc02dbc4a7a5f9f740eb8523b5f630b7f620f58433eb4129549cb7c0760679a6edc4a7d9f803cff8a7d900"
    "a7cdc6ef30b786ebf54023f58681388384879b5b8487859b83583a83482a0da60852acbf51480aaea7bc0c2ac56540cff5ed03f5598683389b838487"
    "83589a873b878184be50a40cae2b094a0fbd09b581ed4ebeed0e814db6bd0bbdcc3156179cffb4c7fecc9db717c45433d70fc7c73ca2d71fbdefb609"
    "4dbe810dbebd4f82090db5edca7a97f0333ac45582a29db4fc37f2245cb64dc687d27411ea35f712b28968308be8b1691032f63634336ab0f5ea118a"
    "d15c8676c5134cb612d0c44f76b5855e318a10f66a34b3e9e249ea5dbdbc03b68bb50b02500a098c23560e37c68d907e8e20c691367e0f57547e93c6"
    "0d23368e0b89510a008c0bb68d0b01080ab4538a7e8f340e9356c621235c6fadbdf0811ceaa2d6b8f2a7d4bd68592bd9ed8d38a78f68ed39dba52859"
    "4a55a45f885c5bab4ef9186688d4be28d44e89bc64281afaa58cd829395bef6988a35d2cf33a31f03989f3322cf35ca0010c823ce51f30061e00e433"
    "3e05810c0c0631e683003c1df3382d5f30a0f18aa1f130f05e882f3b041d3c81300ee6038bb5d3b4e896e8529788e9eab650d3b48387eef8d0b0b64f"
    "b282d3b4fb4cef84864eb7d3ec80fbb05197b4d0e8b6eb8ab453ebead288b5944fb3faecb487d28077fc7664bb6021236275b820672377fc3480bab3"
    "3404acac063434acb0acb8830bcb66328a05be0f2063657720ffba74fd2223bb74746463ca0ebf8b650a33066df6d6a473560c60566c720ea463d5f4"
    "9a3500f4b99ee4f39c98b9e6f7f102344e9f7a8f8e9a6d6c6255a4d70cf4726ef4620d70d66ca6579d6e6e8c7a4f8f9a5cc4cf98022552bc275e0051"
    "98beccc4d846789fda7f16937cdada179f927847469014db7bdb9e7ebc249ace50c4035dc6bf5000cd5c9826927c9e7a1747d8dbc47350e3555fe9cc"
    "5cc557ebe0cd5073837398c7850773f704838773c7f59b7373f473879b83c705cf5ce151eb7054c771cce85453c7e35df707c7997373848396528a49"
    "195a38925a941a3a4a918a5153639e509e8e5e4e8921182d22ba04e7e5b92c1a0523208a925a488939521a9650923a1a8a954a59b88821062fe61921"
    "84ad2cf960948df0c1f1f4857e51a14d8555e0a10946327644860932a275e1559397fc7ab6da48a550c17da1854ef5f14d5185f6a1f17cc194a44bb5"
    "fe927bda70936465fee78939e471ff8b653a6491438be295248aa052f91454f2c9b1024c4cb1f2550214c8f93be465668991fc73913888fd677167e6"
    "b0fac801f04d551645a4bc3515ebe99101e084022086fa913a28bf85a457dc235738a4df8720be292823dea7bf39845490e935bde9a51447a590e915"
    "bf4534e9205684bcdd2ba73b43ec91c79c66ec4d8ee5884955f1d6fb0c7536a3188ce6223037a5cd25846357ea6d5e5c54b227d8f08e55d54bf98ae5"
    "f9f24a89d5e7548d6fda26545ee85db040d865d2ce43ccff99f24b90bfa806fd97f4072498d1cbd3567f256c80384264da45e790bb7ff916ab9abe04"
    "91ff49f0fea9924b04f1bf986d34241d58e1152b757d696b7904c63d057679c4693d697f83c08644c80926b30a82c82547b087c0989772ac9bc03831"
    "3d056a69c77d79747e3dc57968776905943238997098afc306044c5e379c74959c0434745d974e064b6e2d4fe1050dac0549e20d4cad2f6f6dad0fe0"
    "2d4b4e05949e5c4f76053404049476354c065c9fae074d2d0f6ce149bc84236e83e2f83ae6c4b1b397087bcc72242bb98cb0a1fab3718ca0baf82a25"
    "25fba28e2871b8b009e79478b0cfb2c782a7fcb656cbf9adf8b2b928a1268f7007baffc2754dec214f6fca424da1ffc45a64ea8aa273aec4725aa0af"
    "88c6ea6666c6aea0eb5a8872a24f4ffd40c5cb6ebd6a0d78b1abed22c4728aeaae64a25bfac1ace2f53cde7a39c0f3f62a2c2c072ac805c6d1813956"
    "8129d039c65506cac9553ad2052ac4812f38282cf706f1c2c278def6acfae13d5482c5053acad1299696ced054321b114cc130163a9ee8ca70affe31"
    "9c86bee986729fbe31e8fcadaeeabc9dfe7133849c4c39ea16ca30c22a8211d46138be3beb8432fcbdad9e72ed255f24abf25c01cd544562049c4afc"
    "026c905cc70af8370800c4fa5f37926c7af6cae1a3f62531b93065d426b6119b499ca8c4f118a4f8f53226a1ca79e2f7bf6a3a2644d1e882061b5d4b"
    "aaab7d607d557e00b5e5dfe9e67fb5dd01e97d545e2d95197e6f6ec39b4b36bf5cfcb6216c08b5512860a21d425132b865a52e6c48640857e92d1029"
    "3a6d37200bb6a49dc96be24505e6e7c9e5223d502c1b5deb54117ce6f8037ef716dfaa695764d446cba8835695d6a140d8c1ee977766c3a16771f37d"
    "8fba95d068c731d5fb23089521166f3b61c5ae7e0309668a6eaec344f39570bbd18f667d7167958e7cd1f3bb0931699522d4c7fbc2660245af8b086e"
    "57c0c95fce84fab613c0fe12616a6546fac857b6855ec0cfc11264601247ff6ac8fbc085b6cf565ec057face5eb6c985f02e7537986e10efff64c06a"
    "476112122b4b4bf4f254a0481e5ae3ee956e8de9a04a2a4955f44af35b1f8c95eee9e26e4aa04a5548f32af54a2ba1f2f4484b548ce31ee86eef5b95"
    "e38c5b6fe9941eee9cbdac7ea70abc95dbae87e5648f276bafc9daf06a80afb5afdb2665e56a878fadbcbd0a94a69c7fbc9cbda77e95ac0a2787db6a"
    "8fe5ae658627af8f6b65dbe4df325c93d9e85970e78b9441cb08b5b3585cdf70e99333d88be6b5cb40b395095d5932e871d9de9233de58d892715de9"
    "b495e7b309418bca95b58b08b3cbe641987ba0f5c2915a7b67d376e2d36cfc81bc142ace5b603b83d266fdd3e281776ca05b7b907ac299f57a985bc3"
    "f57aa091fc7766816de2d3d277fcd36c80d366e35f249506530429d6c32cc3419ccd41c2fae232a0e7faf6812dc3409c41c2c3cd95282405d7535e06"
    "255f285206d7950441c2c3c2cd412c9dc2412ccdc39dc34063e618ab0bce7fda86de77db8426dfc08feb87e3631ed1ebdf87de84dac07627197fe6ce"
    "db0b62aa2a65bd4bf8191de2de7687c026dbde8576dfde27c18486da18f59a7b09d94434db682e43bbe20926459a1935d87af5081241d14e5afe1b79"
    "9b45f4d83408197bf41845087b359ad9082edb26e34369ba2f0968e227bbda42bf112b871be34648db85c4280500c605472abf49e386111b5bf124f5"
    "ae5ede012b4710e3481bbf8710bf471a87492be3c6c5da0501288504c5c685000405da2953b4ac95ecf6469c14a77c0c33446a5f55a52ad22f44aead"
    "8e11aeb7d65ef840ac47b4f69ced5294b45246ec949cadf75e75516b5cf953ea7d6aa7445e32140d830006419ef20f18c5799c962f18d0780e068318"
    "f341009e78c4d12e96799d18060f00f2199f824001820e9e401807f3d09cc4791996792e9dd07818782fc497a7c143777c6858dbc5a84b5a6874db75"
    "5843a7db6976c07da9c5da695a744b744259c169da7da677c0a7597d76da4369da4bc474755ba8694adaa9757569c45a561a40dd591a02563a90b1b2"
    "3b907f5d8785653319c502df913b7e3bb25db09041031a1a565856dc036587dfc53285197eb13a5c90b3913bb17e91915d3a3ab279cd1a00fa5c4ff2"
    "37b12ad26b067a3936a74fbd4747cd36b0367b6bd2392b061a4ecc5cf3fb7801cd4e373746bda7477a2b363907d2b16a2b7ab106386b36d3496c23bc"
    "4fed3f8b2e5e124d6728e2813f23488aedbd6d4f5e2ee2674c811229233e6ded8b4f49bc6d493e4fbd8b23ece2132f80284c5f6613e35f2880662e4c"
    "fbc139cce3c283b9e367aef0a87538aa8239fab9c3cdc1e366e239a8f1aaaf743982c1c3b9e3facdc1fb83e3ccb939c239aee2ab75f066a8ae386674"
    "aaa9e3f1a7a9314f284f472f4b492da4c41c290dc5f25c168d821110494b29c5a40c2d1cf3c4108c16115d82105cc4108317f38c282d4a0d1da548c5"
    "2c28491d0dc54aa5bbc22af0d004231978a8e0bed042a7fad2c94b7e3d5b6da478c256967c30ca462a22c30419d1baf06d4ad2a55a7fc93da6e078fa"
    "42bfa8d0e0a6a842fbd078bea9a145f14a124550b91df232b3c448fe7ca658f92a010ae41cb849b232fff3c4a67c0a2af9e458010b587de400f8a62a"
    "48f2b8ffc5321db2f3481cc4feb3b833111d94df42d22bee23c8f49adef4528a2a9411efd3df1c42c82252de9a8af5f4942b1cd2ef4310df1d102b42"
    "deee95d3c8007042011043fdf452c8f48adf229a11863a9b510c46737278c7aaeaa57cc56cf5362f2e2ad913a621f6c8634e33f62b989bd2e612c2b1"
    "d8376d132a2ff42e7dc772c4a4aa78ebc67c79a5c4ea73aae94bfa0312cce8e5f8554d5f82c8ff240beda273c8ddbf7c7f20ec3269e721e632abbf12"
    "36401c2195361a920eacf08afe4cf925c85f54834cff54c92582f85fd941604322e40493ba9e02b5b4e3be3c18cc4b39d64d609c9ebabeb4b53c02e3"
    "600541e49223d843614a199c4c38ccd7bf02bb3ce2b49eb402bf9ee23cb4bbb4d625b796a7f08206024a4fae27bb021a82b6d607f09625a74a030226"
    "af1b4ebab78224f106a6d69724d783a69607b6f0034e021abaae4b274f024abb1a2603ae7d3992955c46d850e384734a3cd867d9d8927d514794385c"
    "1d5ec211b741717c92d93846505d7c95387cd95c945093476673e2d8d94b843d56c1537e5babe5fc622d327545d1395737d1a7a77ea0e26539336357"
    "d0752d449003dd7fe1ba26f633392dd0574463752d623945755732d1e2a73765a1a6d07f915eb506bcd8d5762b15e402e3e8c01ce1171c14967b8378"
    "c0e42a1de90215e23dfd6056f17a1e6fe5c014e81ce32a03142ac1e2021de5e8831ce0797b1516961e613c6f7b56fdf074b857ff184e43df614ea61c"
    "750b6518425775de4effb819084b4b67682a998d5643b94fdf1874feb9754219fede564f65a660180b1d4f741d15c108ea301cdf1b013648ae6305fc"
    "cd5c98326a13db88183d7be5f051fb9280f6922f925579ae36040062fdaf1b49fb7a199350e53cf1fe66aa2231024e25fc244e54e2780c52f4be2a3f"
    "80daf2ef90cd259b5f2e7edb61af96ca0cbf37b7c15f351d13a268742af3bfdaee80f43e36a12819dcb2521730838dae25d5d53e0e3684da281430d1"
    "e4e435f1a202f3f3238b6fd5b42b326a7baa083e73fc01bf14243284abf41688f572911e28968dae50ec60f7cb3bb3e14e9db61b90055bd2a065d441"
    "ab4aeb50bafd805cbdec8513cfeec59d523af547f5479dee52c53acf3acfee47529dc5f5d827f88c5e942cb92cb98c275ef894d894d827b95e8cf82c"
    "f82cb9d85e278c949695c845f8e192cd92cd4595f8c8e196e19695cdf845c892c892cd96f89545e1e9581bbdbc858f7c122e87adfbeec274c274ad2e"
    "fb87ee12ee122e74fbad87c24e3bde06ba96d5f31787c44f17f06dc96dc94f8717c4f0177cefab313bf61c33aa862210f1440e9c3542163c67f7b7bd"
    "b7bd3c426716f735f73542bd673c16b7f03511d9bbfda93da93dd935bb11fdf0601e67f881162b662b66f81e81671660df18583502fde9e4e9e43518"
    "0258fddffddf18e4023558e958e9e4df021835fd2e555f9859fcd104d1049855595ffc2efc2e550459985fd15fd1042e595598fc25a86cb393431cde"
    "1cdeb3a8936c43254325a8de93b36c1c6c1cde2593a8b3438963ad70331568cce1afdd1300b87d4524dd4c7e5f0cbccfe31e7af3061994d8ebf68a83"
    "ebfe8e048e0483f6eb8afeebfeebf604eb838a8e8a8e04ebebf683fee0a8b2a3518c6ef7c12ab0a8e9cfc9c4c9c4a82ae9b0cfc1cfc12ac4e9a8b0c9"
    "db2052996a0e1ef3c0d60a88d91187b887b888d6d90a11c011c0d6b8d9880a87b75e4213a0e54fa24fa2135ea042e5b7e5b75ea2a013424ff10c2bd4"
    "0d2e20f09de846de52af49134913dee85246af9daf9de81352de46494649139d52e8deafdff18d847bbcfd34fd3484f17b8dbcdfbcdff1347b848dfd"
    "8dfd34df7bf184bca6401e8bc469770477048b40c41e69a6adb829a2693337d537d5a2b8692933ad88eb8301b40e062a02a1412faaeaa825775ede25"
    "16e7aa1caa1c255e16dee77786fdccad601a82958295adfd60cc1a86b06c55b017f312a77b9487b920805108ae9b129398031c171c17939b981203ae"
    "03ae9b179893121c121c17ae989b9303f44365660763b7cfd478a9977fccf48bf48b97787fa9ccd46e6c11a24c3a211f7551e7325c6a848384833251"
    "5ce76a756a7551835c32e784e78483755c51326a04ec1f8ef64a543854388eecf61f4a04bb8968434a732ba92ba943894a6873bb63be68f1af12d0e6"
    "d0e6f1beaf6812631263bee6aff168d068d0e663afbef112207a89f5b98b07c907c9f57ab9898b208b207ac9b9f589078907c920b97af58ba6c8df39"
    "172cd7afd7af39c817df2ca62ca6c8af1739dfd7dfd7afa617c8392c2ddbd575133adc83dc8375db13d53a2d3a2ddb831375d5dcd5dc832d13db753a"
    "65f2ca0194e4b13bb13b01f294cae465e465f23b9401cab100b0af8125c9b0df20cc7adf4bc104180418dfcc4b7ac1204a27051f822a00bd00bd1f27"
    "82052a4aee0b846b7378be45be456b0b738478ee78ee0b45736b84be84be45ee730b6b789c1285fb9730cbf8cbf8fb129785309c309c12f897fb85cb"
    "85cbf89c9712fb306f255807a53b73ea73ea0725a5583b6f3b6f25eaa50758735873ea6fa525073bec52d2cc9fe586248624cc529fd2e5ecc0eb69c8"
    "cd1e1e191e19c8ebcd691ec0e01b1deb37e4bbb4bbb4eb1b371de4e0e4e01bb437eb1dbb0000b4e083fb681f4b1fc23b59f184a684a63b1f59c2f14b"
    "f14b1fa6593bc284c284a64b591f3bf18aa8e0843a868be28be284a83ae0868a868aa8e23a84e08bb8f8baf9d0c721a332ef3ca01d5147fd47fda0ef"
    "1d3c51325132effd1da03c473c47fd321defa051a2b374c89d6b6218af71d6737d6f7649764973717dd66faf6faf71497d73d6763226c312ce535ba4"
    "5ba41226cec35332533226a4ce12c35bc35ba432ce261253d33e6dfa9507934a934afa3e956d07d307d33e4a95fa6d936d934ad3953efa078fbdbef7"
    "0308e574e574f7bd03be088f088fbd7403f7bee5bee5748f03bdf70861b7f33d8523a0905afdaeda16b9f0f4f0f4dafd16aeb95ab95afdf416daaef0"
    "630d25fa8c15b489b489fa0d8c25156315630d898cfa25b425b489638c0dfa159b6df35c84bca733a7335c6d84f3bc9bbc9b6d33845cf3a7f3a7339b"
    "846d5cbc99d7eb1a6cefca91ca911ad76cebef99ef99d7916c1aebcaebca91996cd71aefa205c04e9e4ced5602cf9994f2daa768a76894cff299da02"
    "da02cf68f29499a72bf9c4927d562df12df192f97dc4562b562bf9f17d92c42dc42df12b7df992569b268b178776414641461726878b769b769b2646"
    "87178b418b41469b87261776b9962ffaeb655b665b66fa96eb2f65b965b99666ebfa2f5b2f5b66b9eb96fa65abb4807c2a08f2c8f2c87cb42a8008ab"
    "08abb4c82a7c80f2a6e5be12bc9b86e38977f56651c6b607b607667751f5c689c68977075166f5b6f5b60789517766c60e8ee582e680d6e6d6e6828e"
    "e6e5800e800e8ee6e682e5d6235f20879189d3e654c0afe66a7489968996e6c06aaf74547454c0966ae6af89bd350dd2894991818ba0a9e2e7e69fec"
    "9fece2a0e7a9e68be68ba0ece7e2a99fa99fec8be7a0e2e6441a4750aa5789d789d7501aaa47574457441ad7aa5047894789d744aa1a50570f2668cb"
    "94d5c708c708cb269468d50fd50f260894cb68c768c7080f9426cbd563ce1d162b1e6d5c6d5c16ce2b1d1e631e63ce5c2b161d6d417b924836d07500"
    "d89b76ca6c38b89db89dca9b6c7638d81e134efea2d76093a2e7533d59c9390c4db32e6341d6dd59d556f7958afbb58342161fad3f74b9c335e4f3ee"
    "abc7e09aa0959c9bf7c1e60f4dc87b0f57095d3bf7bd2dd8a63f07d1ee893159792f27c247bf9c376745d5a82d84cf93de441b601b609384decf442d"
    "191673ddf34b692470a5dd71adaf1240db2db8ea2aca6b8070e079a9f4778ef6566ddf2a9841cfed94a292f5903c3ab0a70868680bfe4aac824dfee9"
    "9dfd335f0be774f5003466eee2b3e4627b9d3052eb3cbb1f497516d7b3e4329e78e15362d71f75ba4b15eb3c629fe0337a51b2e450629fe47a31e2b3"
    "e8f60372f5b2174e3dbb17774ae9d41fbb4bb8d0edb71e0a234b365be257168549b81cb6eebb0bd3865b5636e317214ba5636df4f2163ef208d3b5ba"
    "ec1fba4b5b562217e1874b364a361755e223875bded708f59ef158dcf0bdafc6ecd873ccd60859f09cdddff6b4253f1d5e10c35faa1a8a40c4133970"
    "dcf6f2089d59dcd73bed781be85a56cf5f1c123f5dc0b72563a5937f0b60d4f4ad98e17b049e5980a793d7600860f57f81799ce1075aac987f6360d5"
    "08f4a793f77f63900bd460a5c0d74464eff6a7f6a7f664d7ec46f4c3b17178974ca2ce0e7f4513b8645561f27078cfa24eb20d95f3bb541164617e45"
    "97a0b2cd4e0e71780c95a07a4fceb271b8547d6166f1471344136056657df1bb2b3a12acafdb0ffa8f7be8cd1b6450623b120cdaaf2bfaaf937433f9"
    "7d31f03eacdb2b0eaefb3b12faafdb13ac0f2a3a278eb5c2cd54a03185bf764f00e0f61546005be366232a1c3f07ab10a7a3c226025b2b2066471ce2"
    "2713a3aaa4c33e076f834865aa3978cc1fe2225a672b440083a3ca8e4631badd07abc0a2a63f27131a254d744aa17bbfc733ac5037b880c0264d78a3"
    "4b19bd7695df7a89824e083d74a21b794bbd264dbd76a24f48791b25de7a094d80963f893e894e78810a95dfde548be2a6a5ccb436f6d37cefc513f2"
    "de112c02117ba499f37ec7d3ec1136f69802792c12a7dd11b7e2a688a6cddc547cc73712eef1f6d3f7d310c6ef35f27eec511ee682004621a9729478"
    "59789fdf0a56b6f683316b18dc797997589cab721af633b782690856c2b255c15ecc4b9c20ae0f06d03a18a8088406bda8aaa396b8b1458832e9847c"
    "48705cb8626e4e0e52e3a55efe31d32f0cb86e5e604e4a70d30f95991d8cdd3ed32f5ee2fda53253b86e4a4c620e705c725c4c6e624a0cb8aea40e25"
    "2aa1cded9d130ed67145c9a850e138b2db7f2811aad5450d72c99c1310b07f38da2b51e1ee26a20d29cdada4d6459dcb70a9110e110eca44719dabd5"
    "261e2483e4ead52fa0419b8fbdfac64b1c24d7ebe5262e824b8cf99abfc6a34183e825d6e72e1e242c82e825e7d6271e8ff9a2c5bf4a409b419bc7fb"
    "bea2498c54730fb64c6cd7e97c5fbf9a5e20e7b0700fd66d4f54ebb4b39822bf5ee47c5fb66c57d74de8700febb46c0f4ed455739a227fe75cb05cbf"
    "5ebfe6205f7cb39801f47e9c0816a82803c0be069624c37e10607c332fe905839297c9ef500628c78030eb7d2f0513602a9d147c08aa00f494c92b07"
    "5092c7eec5ee04c8532a9397142ee3735e4aecc311fa16b9cf2dace12ee3ef4b5c16c270e2b92f14cdad11fa734a14ee5fc22ce3c3704ae05fee172e"
    "b92f10aecde1f916fb16ad2dcc11e2b97b6420af37a7790060cda9bf95961cec1b92304b7d4a97b3edbc95a8971e60cdb04b49337f961b9200afa721"
    "377b7864bf95601d94eecca9cda91f949462edbc0b139a2e657decc40000d0820feea37d119aee7c6409c72f92836fd0deac77ec2e7d08ef64c5139a"
    "c62f7d9866ed0813826f74acdf90efd2efd2ae6fdc749083f11cf5cb74bc8346e2e2ebe6431f878c1cf583be77f044c91a2aa28aeb10822fcbbcf380"
    "76441df545c9bcf77780f21c2ba28213ea182e8a2e8a13a2ea801b2a0d6f91ca389b484cbdbdc625f5cd59db6c914a98380f4fc9da25cdc5f559bfbd"
    "ca980c4b384f6d914dc998903a4b0c6f88ced22177ae8961bdc659cff5bdd925f896d33d0ef4de23b44d2a4d57fae81f96d3ddf70ef8223c1e4cfb28"
    "55eab74d3df6fade0f2094d3233cf6d20ddcfb964dfbb4e9571e4c2a4f2ae9fb54b61d4c94d0268e3136e857e76af5d35b68bbc2d126ea373096548c"
    "c1d36bf75bb8e66a8e3594e83356d026568c352432ea97d086ddcef7148e80426bf5bb6a5be4c2d3af2b4766b25d6bbcce9fce6c12b671f12a476a5c"
    "b3adbf67f26eb6cd1072cd9f665eaf6bb0bd2b47bf675e47b269ac2b6cb6cd7311f29ece9ece70b511cef36e11b7c4aff4e54b5a6a0b3ca3c953669e"
    "b4c44be6f7115bad9ca2513ecb676a0bafe4134bf659b5c458ade4c7f74912b78916003b7932b55b093c6752ca6b9fa2bd6c99e5ae5bea972d06196d"
    "1e9a5cd86e99e95baebf94e5d96d9a181d5e2c06e55abee8af976d9995e55a9aadebbf6c6d9a2c5e1cda051906195d981c2eda6dd7db1e2446dd9919"
    "9b96fb4af06e1a8eda1e98dd45d51b2723acd222abf001ca24ded59b4519db1e1a27de1d4499d5dbafd202f2a920c823ca23f3d1aa0022acf6d63448"
    "272645068f7c811c46264e9b255a9a03abbdd251033a389a9b0b965b5201bf9aabd1255ad251015baa99bf263b38960b9a035a9b589b0b3a9a97033a"
    "1d255e13a96a405da77eb22f9e838a9b255e4369a81e5d119a2f82b29f8ba77e13691c41a95e255e5e11695cab421d252f82a68a9f9b7fb27eb28b83"
    "9ea79a2f04ed4922d940d701a31d233c509a2c57b5715938af74788c573f9820502ea31d8d397758ac78b471798c3973ad5874b43c98a02d53561f23"
    "1c232c9b50a2553fd690cfbbaf1e836b889e4ff56425e730565bdd572aeed70e7a4c38f98b5e834d35cdba8c055977670b597cb4fed0e50e626fda29"
    "b3e1e076e3762a6fb2d9e1606458cc75cf2fa591bb27c664e5bd9c08b5103e4f7a136d80dff7b6609bfe1c441efd72de9c1555a36c804d127a3f13b5"
    "8056726ede079b3f3421ef3d5c2574ed2f9cd3d503d098b95bb57dab60063db79e22a0a12df82bb1c381e7a5d2df39da528a4ad643f2e8c00936f9a7"
    "77f6cf7cc19576c7b5be4a006eb7e0aaab28af01f4ec5edc29a5537f5c7fd4e92e55acf342897d92ebc588cfcd92cb78e2854f898b7d82cfe845c992"
    "a1db0fc8d5cb5e3889cf928bed75c248aff3ec7e24d5595c29d95c54898f1c6e196e59d98c5f842c214cd7eab27fe82e27e172d8baef2e4c978eb5d1"
    "cb5bf8c86c59895c841f2ed9ec2ee142b7df7a288e2cd96c895f59147c7148fc7401df96d196fc7478410c7f73dbcb237466715f5b2364c173767fdb"
    "a96a2802114fe4c0efb4e36da06b593d7b5f23d47bc66371c3f7be1ab363cf319fda935db31bd10f06e671861f68b162deff8d412e5083959d4e5e83"
    "2180d5fffe8d815523d09f4e035f1391bddb9fda8f954efe2d8051d3b66286ef11786601124d805995f5c5efcdef52459085f915315482ea3d39cbc6"
    "c2e13d8b3ac936545d82ca363b39c4e1e052f58599c51f4dc4c6e15d32893a3bff154de0925585c914feda3d0180db574cd2cde4f7c5c0fbe8bf6e4f"
    "b03ea8e8ee483068bfaee8bfb06eaf38b8eeef489c38d60a375381c6afe848b0be6e3fe83deea1376f9041891cac028b9afe9c4c9c4c8caa920efb1c"
    "7c888b689dad10010b6cad80981d7188bf0d2295a9e6e0310f8e2a3b1ac5e87618016c8d9b8da870fc1cac429c8e0a9bfb243ae1052a547e547eeb25"
    "0a3a21f4f4da893e21e56d949934e18d2e65f4dad1896ee42df59a347aeb2534015afe246a9434d12985eefd1fcfb042dde00202dd4f4318bfd7c8fb"
    "cffb1d4fb347d8d8dd8a9b229a3673537a47b00844ec9166600ae4b1489c7647f31ddf48b8c7db4f7a532d8a9b9632d3dbd84ff3bd174fc822101af4"
    "a2aa8e5a71e7e55d6271aeca0acb56057b312f712858d9da0fc6ac6169d8cfdc0aa6215882b83e1840eb60a0b04779980b021885a7ca51e265e17d7e"
    "ca7131b9892931e031e0ba79813929c14dbf7889f797ca4c488d977af9c74cbf4c3f5466763076fbe1ba29318939c071e1c61621caa413f220c171e1"
    "8ab9393947382813c575ae56a8561735c825734eba9b8836a434b7924085e3c86effa14443c0fee168af44855817752ec3a54638bb923a94a88436b7"
    "764e3858c71525a3066d1eeffb8a26312d31e66bfe1a8f06b008a2979c5b9f7872905caf979bb8080ca297589fbb78903ee68b16ff2a016d9878900c"
    "92ab57bf81066d3ef6ea1b2f7afd9a837cf1cd62cd628afc7a91f37dadd3b23d385157cdc23d58b73d51add3d8b25d5d37a1c33d6a8afc9d73c172fd"
    "53cd3dd832b15da7f27dfd6a7a819cc316bb13204fa94c5e4b5e26bf4319a01cab7452f021a802d04280f1cdbca4170c01c2acf7bd144c805326af1c"
    "40491ebb04d0fb712258a0a20d00fb1a58920cfbee5bb4b6304788e78be7be5034b746e80cc329817fb95fb8b98cbf2f715908c3cf2951b87f09b38c"
    "e4be40b83687e75b53b88ccf7929b10f47e85be43eb7b08636a77e50528ab5f3b7f356a25e7a803501bc9e86dcece1916e48c22cf5295dcec22e25cd"
    "fc596e48fe56827550ba33a7ec9181bcde9ce6018335a7fe565a72b0be4bbbbe71d3410e4b0ebe417bb3deb118bff4619ab5234c4468baf391251cbf"
    "baf421bc93154f680bbed1b17e43be4b2f4c68ba94f5b1130100400b3eb88ff6b8284e88aa036ea868a8882aae4308be1425f3dedf01ca7373d40ffa"
    "dec113252ff3ce03da1175d4ae880a4ea863b828c573d42fd3f10e1a8a8baf9b0f7d1c32f41a673dd7f766976a973417d767fdf635256342ea2c31bc"
    "b3452a61e23c3c252a63322ce13cb545213a4b87dcb9268635bc452ae36c2231f7f61a97d437676d3da9a4ef53d976307930eda354a9df368ef0d84b"
    "3770ef5b584e77df3be08bf0f7d8eb7b3f80504e34edd3a65f7930a9e05b4ef738d07b8fd036a9345de9a37fafd5efaa6d910b4f054fafdd6fe19aab"
    "5b31d690c8a85f42469ba8dfc058523138d650a2cf58419b19763bdf5338020a51429b38c6d8a05f9fabd54f6fa1ed0a793ac3d54638cfbbcabbd936"
    "43c8357ffc9e791dc9a6b1aea91ca971cdb6fe9e9979bdaec1f6ae1cb3d936cf45c87b3abeae1c99c976adf13b7f3ab349d8c6c526f09c4929af7d8a"
    "708a46f92c9fa92d62b5921fdf2749dcd2122f99df476cb5bf924f2cd967d512255a00ece4c9d46e45dc12bfd2972f69aa2df08c264f997919647461"
    "72b868b764b769627478b11855966b69b6aeffb2bb65a66fb9fe5296966bf9a2bf5eb665b469b27871681764f6b26596bb6ea95fb71864b479687261"
    "2a8fcc47ab0288b08fb04a8bacc207286b9c78771065566f687b607617556f9c9078576f16656c7bbc4a0bc8a782208f5c6f7b90187567666e5aee2b"
    "c1bb6938606d2ee8685e0ee80de8e0686e2e586e4847056ca966fe9a9568690eacf64a474905fc6aae469768eee0582e680e686dd85bd3209d981419"
    "3ef205721899386df8c92e0e7a9e6abe69be08ca7e2e9efa7845a471ad0a759494780da5a17a74454da47104a57a9578be089a2a7e6efec97594784d"
    "a4aa01759efac9be780e2a6e708cb06c428956fd5cfd608240b98c76e631e6ccb562d1d1d6c665e1bcd2e13135e6dc61b1e2d1c6f06082b64c597d8c"
    "10b4278964035d078d768cf04069b25c8ddba9bcc9668783e931e1e42f7a0d362c64f1d1fa43973b586d755fa9b85f3bd534eb321664dd9d89bd69a7"
    "cc8683db59433eefbe7a0cae207a3ed593959cc3d384bcf77095d0b57ddfdb826dfa7310b2013649e8fd4cd4d642f83ce94db4017af4cb797356548d"
    "005ac9b9791f6cfe926131d73dbf9446ec9e189395f77222b8dd82abaea2bc060f079e974a7fe76825d8e49fded93ff37a8a8086b6e0afc44b292a59"
    "0fc9a3030457da1dd7fa2a01be704e570f4063e66ed5f6ad8219f4dcbdceb3fb91546771364b2ee389173e25846e3f20572f7be10b25f649ae17233e"
    "2ef6093ea317254b253e4b2eb6d70923d1b37b71a7944efd73fd51a7bb54b1ce38b264b3257e65519d84cb61ebbebb30b3652572117eb86484305dab"
    "cbfea1bb5f3ad6462f6fe123b0bb840bdd7eeba1a5647351253e72b864b86565337e11b20cdffb6acc8e3dc76f8d9005cfd9fd6dbcd38eb781ae65f5"
    "cd6d2f8fd099c57da7aaa108443c9103ed7d8d50ef198fc5f2c521f1d3057c5b455bf2d3e10531fcd88a19be47e09905773a790d860056ff0f7c4d44"
    "f66e7f6a7aff3706b9400d56f93706568d407f3a3f563af9b700464d7c6a4f76cd6e443f1998c7197ea0c58aff5734814b5615260987f72cea24db50"
    "814bd51766167f34c75009aaf7e42c1b77092adbece41087101b8777c924eaec4b34016655d617bf34bf4b154116e657f6b887debc410625ba23c1a0"
    "fdbaa2ff73e2582bdc4c051aa3ffba3dc1faa0a2c1babde2e0babf23bfa223c1fabafda051f86bf704006e5f33493793df1703eff273b00a713a2a6c"
    "2eb0b5026276c4213d38aaec6814a3dbf0212ea275b64204fc368854a69a83c76104b0356e36a2c271b00a2c6afa7332703231aa4a3aec737c3cc30a"
    "75830b0867d28437ba94d16be8ad97d00468f993d26b27fa8494b7514427ba91b7d46bd2ab51d244a714baf7ed93e88417a850f953f9ad9728e884d0"
    "6f633fcdf75e3c21e91dc12210b1479acd777c23e11e6f3f752b6e8a68dacc4d812990c72271da1deb4db5286e5aca4c773f0d61fc5e23ef3fef773c"
    "cd1e61639d2a47899785f7f9a160656b3f18b3860ae2fa6000ad8381292c5b15ecc5bcc4a5613f732b988660c21ee5612e086014894068d08baa3a6a"
    "c79d977789c5b92a8004c7852be6e6e422355eeae51f33fd85eba6c424e600c735fde225de5f2a3333fd5099d9c1d8ed871b5b8428934ec82bc7c5e4"
    "26a6c480c780ebe605e6a404da39e1601d57948c01158e23bbfd8712605dd4b90c971ae1ea6e22da90d2dc4a0e01fb87a3bd1215ee4aea50a212dadc"
    "1de1a04c14d7b95aa15a5dd42097cc39041ab4f9d8ab6fbcc84172bd5e6ee222f9982f5afcab04b4c122885e726e7de232885e627deee24162e24132"
    "48ae5efd18b479bcef2b9ac4b4c498aff96b3c1acbf7f5abe905720e0bf760ddf644b54eab29f277ce05cbf5b74ecbf6e0445d3560cb7675dd840ef7"
    "4e35f760cbc4769de9f56b0ef2c5378b358b29f2eb45cef73700ec6b604932ec0801c637f3925e304e99bc72002579ecafd249c187a00a400608b3de"
    "f75230011240efc78960818a59ec4e803ca532792c7999fc0e6580721ea16f91fbdcc21ae732febec465210c91fb02e1da1c9e6f320ca704fee57ee1"
    "3ea744e1fe25cc324ce1323ee7a5c43ebb6fd1dac21c219e2f9efb42d1dc1aa10ed69cfa5b69c9c1bb2109b3d4a77439fa5b09d641e9ce9c06f07a1a"
    "72b3874709bb9434f367b921b04706f27a739a07db9cfa414929d6cedcce5b897ae901d60700002df8e03eda12a1e9ce479670fc2df846c7fa0df92e"
    "61fcd28769d68e30e9d287f04e563ca1bc30a1e952d6c74ef82eedfac64d07392e39f806edcd7ac7282ebe6e3ef471c8cc513fe87b074f94b8222a38"
    "a18ee1a25194cc7b7f0728cfbfcc3b0f6847d45114cf51bf4cc73b68e2a23821aa0eb8a1a2a122aab80e21f8dddb6b5c52df9cb5cc16a98489f3f094"
    "86e82c1d72e79a18d6948c09a9b3c4f0a98cc9b084f3d416d4f016a98cb389c4d26b9cf55cdf9b5dab5dd25c5c9ff5db41dba4d274a58ffe6339dd7d"
    "ef802fc2d2b44f9b7ee5c1a439c2632fddc0bd6fdd63afeffd004239826f39dde340ef3df4a492be4f65dbc1e4c1b48f52a57edb7cae563fbd85b62b"
    "186da27e036349c564d8ed7c4fe108286dc5584322a37e09e25843893e63056d45096de21863837ebd56bfabb6452e3c163cbd76bf856baeeffce9cc"
    "26611b17a672a4c635dbfa7bcc66db3c1721efe9f27be675249bc6ba64e6f5ba06dbbb72fbba726426dbb5c6e6e90c571be13cef29ef66db0c21d7fc"
    "a9b6c0339a3c65e64a4bbc647e1fb1d5956801b0932753bb8bd54a7e7c9f2471fc4a3eb1649f554b15714bfc4a5fbea49ac07326a5bcf629c0291ae5"
    "b37ca6b6dd6290d1e6a1c985ee9699bee5fa4b59d1a6c9e2c5a15d905659aea5d9bafecb59aee58bfe7ad996d9cb9659eebaa57e6690d185c9e1a2dd"
    "90dda689d1e1c562b869b9af04efa6e1a2ed81d95d54bd71f22a2d209f0a823cad71e2dd419459bd41e25dbd5994b1ed71bded4162d49d99aa3c321f"
    "ad0a20c23cc22a2db20a1fa0f9c817c86164e2b455a2a539b0da2b1db98363b9a039a0b5221d15b0a59af96b2515f0abb91a5da2606f4d8374625264"
    "83b5b9a0a37939a035a083a3b9b960b979ea27fbe239a8b851e2359486ead115fb2268aaf8b9f927e21591c6b52ad4513591c61194ea55e2d551e235"
    "91aa06d4e227bb38e879aaf9a7f92228fbb978ea35da31c203a5c972581b9785f34a87c7c28309da3265f5319bc79833d78a4547d7987387c58a471b"
    "40d09e24920d741dc331c2b209255af571f5830902e532da83e8f9544f56720e60b5d57da5e27eed27f6a69d321b0e6eb090c547eb0f5dee56d3accb"
    "58907577660df9bcfbea31b8366ea7f2269b1d0ea4c78493bfe835d8b07b624c56decb89580be1f3a437d106036825e7e67db0f9cb06d824a1f73351"
    "ead12fe7cd5951354986c55cf7fc521a4e13f2dec35542d7f47d6f0bb6e9cf41bb55dbb70a66d073eb29021ada82bf12105c69775cebab049760937f"
    "7a67ffcc2ca5a8643d248f0efbc2395d3d008d99e0760baeba8af21a3d1c785e2afd9da3cff5479dee52c53a2c94d827b95e8cf894f82cb9d85e278c"
    "13bafd805cbdec85b9d827f88c5e942c47cfeec59d523af5f53acfee47529dc5d82cb98c275ef89492e19695cdf845c812c274ad2efb87eec2ee122e"
    "74fbad87cd9695c845f8e1927ce9581bbdbc858f9692cd4595f8c8e1e1c892cd96f8954574122e87adfbeec2176dc94f8717c4f035b7bd3c426716f7"
    "b7f73542bd673c16f34e3bde06ba96d59caa862210f1440ec91787c44f17f06d337cefab313bf61cbd3542163c67f7b766601e67f881162be9fddf18"
    "e4023558fd58e9e4df0218353df03511d9bbfda9e4df18583502fde9f0a93dd935bb11fd602b66f81e816716dfe9e435180258fdd1fc2e550459985f"
    "1c4325a8de93b36c436c1cde2593a8b3042e555f9859fcd1de25a86cb393431c2ed1049855595ffcfc5fd1042e595598251cdeb3a8936c43cf24dd4c"
    "7e5f0cbc8efeebf604eb838afe8a8e04ebebf683cc8963ad7033156804ebf68a83ebfe8e45e1afdd1300b87dd8e31e7af3061994eb8e0483f6eb8afe"
    "c1c9c4a82ae9b0cfc087b888d6d90a118711c0d6b8d9880af7e0a8b2a3518c6ef3db2052996a0e1ec4c12ab0a8e9cfc9c9cfc12ac4e9a8b0b8c0d60a"
    "88d911874fe5b75ea2a0134249af9de81352de46af4649139d52e8dea2b75e4213a0e54f139de846de52af49b74fa2135ea042e5f0f10c2bd40d2e20"
    "9d4913dee85246affdbcdff1347b848dd5adb829a2693337ad37d5a2b869293334dff18d847bbcfd04a6401e8bc46977dffd3484f17b8dbcbc8dfd34"
    "df7bf184a677048b40c41e691c775ede2516e7aaa7b06c55b017f312087b9487b92080512a88eb8301b40e069586fdccad601a822502a1412faaeaa8"
    "77aa1c255e16dee7868295adfd60cc1a1c03ae9b17989312d4f48b97787fa9cc1f6e6c11a24c3a2117ae9b129398031ccff44365660763b7ae1c1793"
    "9b98120303121c17ae989b938bd478a9977fccf4846a7551835c32e7a9bb8968434a732bbb2ba943894a6873837551e7325c6a843804ec1f8ef64a54"
    "75848332515ce76a6ae78483755c51320454388eecf61f4ad01263bee6aff168078b207ac9b9f5898b8907c920b97af5e663be68f1af12d0c9207a89"
    "f5b98b0763d0e6f1beaf68121268d0e663afbef12007c9f57ab9898bd72ca6c8af1739dfdc3a2ddb831375d53ad5dc832d13db75afa6c8df39172cd7"
    "832ddbd575133adca6d7af39c817df2c2cdfd7afa617c8392ddc8375db13d53ab1e465f23b9401cabd4a27051f822a004a00bd1f2782052a3b65f2ca"
    "0194e4b11820cc7adf4bc10465b13b01f294cae4df00b0af8125c9b0200418dfcc4b7ac1be78ee0b45736b84cb309c12f897fb853085cbf89c9712fb"
    "45ee0b846b7378bef89c1285fb9730cbeebe456b0b7384787884be45ee730b6b9ccbf8fb12978530733b6f25eaa5075819c0eb69c8cd1e1ec01e19c8"
    "ebcd691eea6f255807a53b7324ec52d2cc9fe5866f73ea0725a5583b3b5873ea6fa52507ec8624cc529fd2e5bbe4e01bb437eb1d84f14b1fa6593bc2"
    "f1c284a64b591f3bb4e01b1deb37e4bba64b1fc23b59f184e0bbb4eb1b371de41f0000b4e083fb684b84a63b1f59c2f18b868aa8e23a84e0475132ef"
    "fd1da03c513c47fd321defa0e28aa8e0843a868bfd32ef3ca01d51478a8be284a83ae086a3b8f8baf9d0c7213247fda0ef1d3c51af764973717dd66f"
    "5b533226a4ce12c353c35ba432ce261218a2b374c89d6b62a43226c312ce535b49af71d6737d6f76766faf71497d73d6325ba41226cec3539307d33e"
    "4a95fa6de5088fbd7403f7be08bee5748f03bdf74ad33e6dfa950793748fbdbef70308e5d3934afa3e956d07076d934ad3953efa8fe574f7bd03be08"
    "5af0f4dafd16aeb9b415630d898cfa251525b489638c0dfa9061b7f33d8523a089630d25fa8c15b4f45afdaeda16b9f0f0b95afdf416daae63b489fa"
    "0d8c2515a7bc9b6d33845cf3caef99d7916c1aebefebca91996cd71a339b6df35c84bca79199d7eb1a6cefca9ba7335c6d84f3bcbcf3a7339b846d5c"
    "99ca911ad76cebef02a76894cff299da2d562bf9f17d92c456c42df12b7df99256a205c04e9e4cedf12bf9c4927d562d6802cf9994f2daa7a7da02cf"
    "68f294992b2df192f97dc45641769b264687178b5b65b99666ebfa2f652f5b66b9eb96fa469b268b1787764166b9962ffaeb655b9b41461726878b76"
    "768b41469b872617b95b66fa96eb2f65f208abb4c82a7c80b6c68977075166f5c6f5b60789517766c8abb4807c2a08f2078977f56651c6b6abf2c87c"
    "b42a8008e3a6e5be12bc9b8689b607667751f5c6d6800e8ee6e682e5897454c0966ae6af81bd350dd2894991e60e8ee582e680d69654c0afe66a7489"
    "0ed6e6828ee6e580e6235f20879189d3548996e6c06aaf749fe68ba0ece7e2a98957441ad7aa5047574789d744aa1a50ec8ba0a9e2e7e69fd7441a47"
    "50aa57898b9fece2a0e7a9e6e6a99fec8be7a0e24489d7501aaa4757c7d50f260894cb686d1e63ce5c2b161d00417b924836d075080f2668cb94d5c7"
    "5c63ce1d162b1e6d0fc708cb269468d5d568c7080f9426cb636d5c16ce2b1d1e931e134efea2d760c342161fad3f74b99a35e4f3eeabc7e09dd89b76"
    "ca6c38b8594db32e6341d6ddd8b89dca9b6c76380ca2e7533d59c93983d556f7958afbb5d1f7bd2dd8a63f072d1b609384decf4424191673ddf34b69"
    "0fa0959c9bf7c1e6a847bf9c376745d53b4dc87b0f57095dc2ee893159792f27602d84cf93de441bf670e079a9f4778e5f824dfee99dfd33ee0be774"
    "f50034664070a5dd71adaf12b094a292f5903c3a80db2db8ea2aca6bed566ddf2a9841cfaca70868680bfe4a62b3e4329e78e1534ee8f60372f5b217"
    "1f3dbb17774ae9d452e2b3e4627b9d30e4629fe0337a51b2d7eb3cbb1f4975163cd71f75ba4b15ebb350629fe47a31e2d349b81cb6eebb0b365b5622"
    "17e1874b5b4a361755e223870abb4bb8d0edb71ef2a5636df4f2163e85234b365be257164b865b5636e317214b08d3b5baec1fbaf6d60859f09cdddf"
    "cf3bed781be85a56255f1c123f5dc0b7dcded708f59ef15870aa1a8a40c41339ccf0bdafc6ecd8735fb4253f1d5e10c3d7dcf6f2089d59dc7fa793d7"
    "600860f5f6c0d74464eff6a7c3a7f664d7ec46f4f463a5937f0b60d4937f6360d508f4a780ad98e17b049e599881799ce1075aaca5f77f63900bd460"
    "957078cfa24eb20d13b8547d6166f147bb44136056657df10eb17178974ca2ce7897a0b2cd4e0e71f27f4513b864556145f3bb541164617e710c95a0"
    "7a4fceb2af3b120cdaaf2bfa31278eb5c2cd54a01585bf764f00e0f6fa2b3a12acafdb0f12acdb2b0eaefb3b628f7be8cd1b64503e937433f97d31f0"
    "3afaafdb13ac0f2ae2025b2b2066471cdd83a3ca8e4631ba1307abc0a2a63f271c46005be366232acc6f834865aa3978263f07ab10a7a3c2072713a3"
    "aaa4c33e001fe2225a672b4476264d78a34b19bd89de7a094d80963fdf3e894e78810a95bf1a254d744aa17b4d74a21b794bbd26c0c733ac5037b880"
    "3d95df7a89824e0825bd76a24f48791b99de112c02117ba4d37cc73712eef1f67ef7d310c6ef35f2b4de548be2a6a5cc119802792c12a7ddf236f6d3"
    "7cefc513f6f37ec7d3ec113654b7e2a688a6cddc180a56b6f683316ba820ae0f06d03a1896088406bda8aaa321ec511ee6820046561af633b7826908"
    "dfa972947859789f72dc797997589cab9cc2b255c15ecc4b2f52e3a55efe31d35cb86e4a4c620e70b8725c4c6e624a0c7cb8b1458832e9843ed30f95"
    "991d8cdd0e48705cb8626e4e700cb86e5e604e4a53d32f5ee2fda5321150e138b2db7f280ed6459dcb70a911d5110eca44719dabedaea40e252aa1cd"
    "e110b07f38da2b51a89d130ed67145c913aad5450d72c99ca4ee26a20d29cdad821c24d7ebe5262e9b8ff9a2c5bf4a408c419bc7fbbea2492f261e24"
    "83e4ead52483e825d6e72e1e4ba0419b8fbdfac6414b8cf99abfc6a31e2c82e825e7d627b4700fd66d4f54ebbf9a227fe75cb05c985ebfe6205f7cb3"
    "e954730fb64c6cd70fb66c57d74de870b07c5fbf9a5e20e75fb39822bf5ee47c73ebb46c0f4ed4558310607c332fe905ee94c92b075092c797c5ee04"
    "c8532a932801f47e9c0816a8608030eb7d2f05137e03c0be069624c3c79297c9ef500628f42a9d147c08aa00702ee3ef4b5c16c216b92f10aecde1f9"
    "b9fb16ad2dcc11e2c3142ee3735e4aece3734a14ee5fc22ce111fa16b9cf2dacfae2b92f14cdad112ec3704ae05fee17b31b92304b7d4a97a9bf9560"
    "1d94eeccbccda91f949462ed007b6420af37a77992b04b49337f961bec60cda9bf95961ccdedbc95a8971e606400afa721377b782f119aee7c6409c7"
    "d2826f74acdf90ef83efd2ae6fdc7490c40b139a2e657dec9a2e7d08ef64c5137d0000d0820feea3ec92836fd0deac7713c62f7d9866ed08c91cf583"
    "be77f0448a2ba28213ea182e2a2e8a13a2ea801b46f11cf5cb74bc83f5cbbcf38076441d8ce2e2ebe6431f872f1a2aa28aeb10821c45c9bcf77780f2"
    "c96c914a98380f4f6188ced22177ae8925bdc659cff5bdd94c0d6f91ca389b4891ca980c4b384f6ddbbdbdc625f5cd59bdda25cdc5f559bf6f4dc998"
    "903a4b0c3c96d3ddf70ef8222a4dfbb4e9571e4c4c4f2ae9fb54b61d23f896d33d0ef4ded33df6fade0f20941fb44d2a4d57fae84d1e4cfb2855eab7"
    "96233cf6d20ddcfb8cd126ea373096544286ddcef7148e80d36bf5bb6a5be4c25794d0268e3136e8268e3594e83356d0c2e76af5d35b68bb6ac1d36b"
    "f75bb8e6d0568c352432ea97672a476a5cb3adbfce6cb6cd7311f29e6e9ece70b511cef3bcaf2b4766b25d6b47665eaf6bb0bd2bf1ce9fce6c12b671"
    "9ff26eb6cd1072cd2bbf675e47b269acadb4c44be6f7115b5b8916003b7932b5a2093c6752ca6b9f5a11b7c4aff4e54bc4afe4134bf659b59e6a0b3c"
    "a3c953660b9ca2513ecb676ab758ade4c7f74912e56e99e95baebf94196d9a2c5e1cda056d06195d981c2eda97bd6c99e5ae5bea99e55abee8af976d"
    "d82d06196d1e9a5c06d96d9a181d5e2c6c95e55a9aadebbf27da1e98dd45d51b23afd202f2a920c8acca23f3d1aa002219d7db1e2446dd991e24ded5"
    "9b4519db8e9b96fb4af06e1aca23acd222abf001db1a27de1d4499d551255a9a03abbdd29b3b38960b9a035a3a589b0b3a9a970306f6d63448272645"
    "5a5201bf9aabd1259b8f7c811c46264e5b033a389a9b0b9626d251015baa99bf11255e4369a81e5db22f82a68a9f9b7f2f7eb28b839ea79a5d1d255e"
    "13a96a405e13691c41a95e259ba77eb22f9e838a7e9a2f82b29f8ba7255e11695cab421d8cb5715938af7478233c98a02d53561f3f1c232c9b50a255"
    "0104ed4922d940d7718d397758ac78b457a31d233c509a2c1d573f9820502ea3b4798c3973ad58740e565bdd572aeed776626fda29b3e1e060e3762a"
    "6fb2d9e16bd690cfbbaf1e836735cdba8c05597730889e4ff56425e74d7a4c38f98b5e830e0b597cb4fed0e580b5103e4f7a136d3f8056726ede079b"
    "ed3421ef3d5c2574916458cc75cf2fa5a31efd72de9c155508bb27c664e5bd9c44dff7b6609bfe1cb56c804d127a3f13b19e22a0a12df82b00c19576"
    "c7b5be4a016eb7e0aaab28afb92f9cd3d503d098c0528a4ad643f2e8b75bb57dab60063ddac381e7a5d2df397c0936f9a777f6cfcf42897d92ebc588"
    "4889cf928bed75c25caff3ec7e24d5597ff4ec5edc29a553928b7d82cfe845c9f35c7fd4e92e55ac89cd92cb78e2854f38a1db0fc8d5cb5e2e214cd7"
    "eab27fe828ec2ee142b7df7a148e2cd96c895f596e29d95c54898f1cc8978eb5d1cb5bf82c196e59d98c5f844c27e172d8baef2ed96c59895c841f2e"
    "5f73dbcb23746671717b5f23d47bc66331c3f7be1ab363cf967c7148fc7401dfc0a96a2802114fe47fd196fc7478410cdb5b2364c173767f3defb4e3"
    "6da06b5995deff8d412e5083d38f954efe2d805101b66286ef1178660f9fda935db31bd14efe8d815523d09f6206e671861f68b1ff9d4e5e832180d5"
    "da035f1391bddb9fc6315482ea3d39cb3bc4c6e15d32893ac9ff154de0925585ef124d805995f5c5e15d82ca363b39c415cdef52459085f954c2e13d"
    "8b3ac9364de052f58599c51fe8e8bf6e4fb03ea8e8afe848b0be6e3f893deea1376f90415714feda3d0180db48b06eaf38b8eeeffb4cd2cde4f7c5c0"
    "bfee483068bfaee8c69c38d60a375381017c888b689dad107018016c8d9b8da89bfc1cac429c8e0a4c1cac028b9afe9c31bf0d2295a9e6e01c9c4c8c"
    "aa920efb880b6cad80981d71760f8e2a3b1ac5e894f4da893e21e56dfd6a9434d12985ee021fcfb042dde0027efb243ae1052a5434d1896ee42df59a"
    "f4547eeb250a3a21da9934e18d2e65f4247aeb2534015afe53dd8a9b229a3673d37a532d8a9b9632c8dbd84ff3bd174ffbdd4f4318bfd7c847600ae4"
    "b1489c76d8cffb1d4fb347d8667a47b00844ec914ff31ddf48b8c7db710acb56057b312f85b04779980b02187ea7ca51e265e17d5a22101af4a2aa8e"
    "5869d8cfdc0aa621ca71e7e55d6271ae612858d9da0fc6aca082b83e1840eb604c4dbf7889f797caf2e1c61621caa4133920c171e18ab939e0ca7131"
    "b9892931fb4c3f5466763076c131e0ba79813929bf488d977af9c74c71e1ba29318939c092ba9b8836a434b7b7bb923a94a88436a3764e3858c71525"
    "5647382813c575ae8543c0fee168af444ea8561735c82573444085e3c86effa1385817752ec3a54678b008a2979c5b9fbf9878900c92ab572f81066d"
    "3ef6ea1b31066d1eeffb8a26900ca297589fbb78062d31e66bfe1a8f0872905caf979bb86d3ee68b16ff2a01cdadd3b23d385157a753cd3dd832b15d"
    "c3f27dfd6a7a819c627afd9a837cf1cd3dd8b25d5d37a1c37dcd628afc7a91f3d3c23d58b73d51adfd6a8afc9d73c172d0ab7452f021a802a204d0fb"
    "712258a0fb0d00fb1a58920c5e16bb13204fa94c8001c2acf7bd144c1c4b5e26bf4319a00c4280f1cdbca417bb5326af1c40491eb80cc329817fb95f"
    "0f53b88ccf7929b18647e85be43eb7b0e7ee5bb4b63047888ccf2951b87f09b3e88be7be5034b746c3b98cbf2f7159085be4be40b83687e79101bc9e"
    "86dcece101ec9181bcde9ce6b08335a7fe565a72f336a77e50528ab548c22e25cdfc596e35b7f356a25e7a80ce6e48c22cf5295da7fe56827550ba33"
    "4c18bff4619ab523132f4c68ba94f5b1f60100400b3eb88f0ebe4bbbbe71d34168baf421bc93154fb14b0ebe417bb3debf4468baf391251c4b0bbed1"
    "b17e43be731425f3dedf01ca1ac573d42fd3f10e328a8baf9b0f7d1ca8b8284e88aa036ed42ff3ce03da1175be68a8882aae43082573d40ffadec113"
    "28ae880a4ea863b8bc35256342ea2c313135bc452ae36c226df7f61a97d4376797f41a673dd7f766452a63322ce13cb5f66a973417d767fd25b3452a"
    "61e23c3c86213a4b87dcb9265b8ef0d84b3770ef8fe05b4ef738d07b7fd036a9345de9a3303da9a4ef53d9764ef7d8eb7b3f8050367930eda354a9df"
    "f0584e77df3be08ba934edd3a65f7930425b31d690c8a85f5f51429b38c6d8a00a9fabd54f6fa1ed4fafd5efaa6d910b9b38d650a2cf5841ab054faf"
    "dd6fe19a31469ba8dfc058520a19763bdf533802aefc9e791dc9a6b1f1beae1c99c976adc53b7f3ab349d8c6bb793ac3d54638cf1c9979bdaec1f6ae"
    "7fcabbd93643c8359ea91ca971cdb6fe3ab3d936cf45c87bdc62b5921fdf27496945dc12bfd2972f79aa2df08c264f998a26f09c4929af7d12bf924f"
    "2cd967d52d708a46f92c9fa9b5d2122f99df476c6e255a00ece4c9d4b255966b69b6aeff5ff6b26596bb6ea961b71864b4796872b71964746172b868"
    "65966bf9a2bf5eb61864b769627478b196bb65a66fb9fe5264b469b2787168176f6b9c7877106556665c6f7b90187567386e5aee2bc1bb69b02a8fcc"
    "47ab02887b9078576f16656c288fb04a8bacc2079c687b607617556f8fbc4a0bc8a782209a4847056ca966fe19d85bd3209d98146d3ef20572189938"
    "e8606d2ee8685e0e684905fc6aae46976e0de8e0686e2e58479568690eacf64a6deee0582e680e68947845a471ad0a75757594784da4aa016e9efac9"
    "be780e2abef8c92e0e7a9e6a784da47104a57a95fa69be08ca7e2e9e4594780da5a17a74c9be089a2a7e6efed1e631e6ccb562d10710b4278964035d"
    "5c8d768cf04069b2fd708cb06c428956c635e6dc61b1e2d1765cfd608240b98c31d6c665e1bcd2e18cf06082b64c597d3b2c64f1d1fa4397ae59433e"
    "efbe7a0cc3207a3ed593959c838ddba9bcc966879dd534eb321664dd36e931e1e42f7a0d3b586d755fa9b85fdb89bd69a7cc8683d4b2013649e8fd4c"
    "46926131d73dbf9422ec9e189395f772b5d384bcf77095d08d7af4cb79735654107ddfdb826dfa7301d642f83ce94db4fe005ac9b9791f6cf325d8e4"
    "9fded93fe6be704e570f4063dc6ed5f6ad8219f406b8dd82abaea2bc034b292a590fc9a3680f079e974a7fe7c47a8a8086b6e0af010457da1dd7fa2a"
    "e1846e3f20572f7bfdd1b37b71a7944ece73fd51a7bb54b171bdceb3fb9154674b2ef6093ea3172525364b2ee389173e3e0b25f649ae172323253e4b"
    "2eb6d70964b3652572117eb8b8a5647351253e72b264b86565337e115138b264b3257e65235f3ad6462f6fe1309d84cb61ebbebbbb84305dabcbfea1"
    "a1b0bb840bdd7eebf5bcd38eb781ae655bf2c521f1d3057cfc455bf2d3e10531c70cdffb6acc8e3d03a7aaa108443c916d6f8d9005cfd9fd7dcd6d2f"
    "8fd099c5c5ed7d8d50ef198f6a0f7c4d44f66e7f3f7c6a4f76cd6e448a1998c7197ea0c505d88a19be47e0993af93706568d407fff773a790d860056"
    "567aff3706b9400d4d3f563af9b7004634814bd51766167fbf4b34016655d6175734bf4b154116e626ff5734814b56158777092adbece410500987f7"
    "2cea24db1bc75009aaf7e42cec101b8777c924ea1a73e2582bdc4c055f51f86bf704006eef33493793df170325f6b887debc410623c1babde2e0babf"
    "ffba23c1a0fdbaa2a2a3ffba3dc1faa0a0bfa223c1fabafddb3d38aaec6814a33271b00a2c6afa7373703231aa4a3aec6cf273b00a713a2ac7fc3688"
    "54a69a83212eb0b5026276c404f0212ea275b642c26104b0356e36a293e8ad97d00468f9f9ed93e88417a850d053f9ad9728e884087c3cc30a75830b"
    "d24427ba91b7d46b6b67d28437ba94d151d26b27fa8494b7f7ab51d244a714ba3fcd777c23e11e6fef773f0d61fc5e23633fef773ccd1e61216f633f"
    "cdf75e3c1d812990c72271da9ae91dc12210b1474d752b6e8a68dacc4ceb4db5286e5aca810ae2fa6000ad836a894068d08baa3a2ac79d977789c5b9"
    "f99d2a47899785f760a5613f732b988686a160656b3f18b3c4292c5b15ecc5bc14c21ee5612e0860c785eba6c424e600802bc7c5e426a6c404c780eb"
    "e605e6a4e48004c7852be6e6ed33fd5099d9c1d8fd22355eeae51f333335fde225de5f2ac8871b5b8428934ee1605dd4b90c971a5a1de1a04c14d7b9"
    "39a15a5dd42097cc8cda39e1601d5794150e01fb87a3bd121201158e23bbfd874aea6e22da90d2dcdcee4aea50a212dab4f9982f5afcab04c418b479"
    "bcef2b9a1ab4c498aff96b3cbc041ab4f9d8ab6f4132885e627deee222c84172bd5e6ee2e2c122885e726e7dfd62e2413248ae5ef5ab29f277ce05cb"
    "8be9f56b0ef2c537f7358b29f2eb45ce0ecbf7f5abe90572f760cb7675dd840e4e0bf760ddf644b535b74ecbf6e0445d9d4e35f760cbc476ec4e99bc"
    "720025797959ec4e803ca532722c7999fc0e6580ec3700ec6b604932010608b3def75230300801c637f3925e40afd249c187a00a8a1240efc7896081"
    "6f91fb02e1da1c9e9ebb6fd1dac21c21a12f9efb42d1dc1a1a1ea16f91fbdcc2323ea744e1fe25cc0ce732febec46521e1320ca704fee57e3e4ce132"
    "3ee7a5c49cfa5b09d641e9cecedb9cfa414929d6d6dcce5b897ae901c10ed69cfa5b69c92109bb9434f367b939bb2109b3d4a7744706f07a1a72b387"
    "07b04706f27a739a2e2df846c7fa0df939f82eedfac64d07c72e39f806edcd7ada0700002df8e03ea1e9d287f04e563cfc12a1e9ce4796703061fcd2"
    "8769d68e4ebc30a1e952d6c7a2b8222a38a18ee1a1e2a23821aa0eb8f8a2a122aab80e21c8282ebe6e3ef47151bfcc3b0f6847d494cc513fe87b074f"
    "cf5194cc7b7f07286814cf51bf4cc73b1886e82c1d72e79a5dd26b9cf55cdf9bdbab5dd25c5c9ff5b5dddb6b5c52df9c16a98cc9b084f3d494cc16a9"
    "8489f3f0f0d6948c09a9b3c4c4d4f016a98cb389a4d2b44f9b7ee5c1c1f4a492be4f65dbdbe4c1b48f52a57efe41dba4d274a58f39dd63afeffd0042"
    "c26339dd7def802f6f39c2632fddc0bd3d826f39dde340ef2864d8ed7c4fe1083cbd56bfabb6452eae163cbd76bf856b2b7cae563fbd85b66de25843"
    "893e6305c5186da27e036349096dc5584322a37e7e45096de2186383e9cc66db3c1721efefe6e90c571be13cfc29ef66db0c21d717effce9cc26611b"
    "7264e6f5ba06dbbb7ba672a4c635dbfabaf27be675249bc6c6fbba726426dbb5bb956801b0932753299ac07326a5bcf6b6c0291ae5b37ca6e6a9b6c0"
    "339a3c654bfc4a3eb1649f55d54a4bbc647e1fb1718bd54a7e7c9f24a415714bfc4a5fbe90d1a6c9e2c5a15ddd6690d185c9e1a26290dda689d1e1c5"
    "85dd6290d1e6a1c99659aee58bfe7ad959ee9699bee5fa4bcb5659aea5d9bafe7ed9cb9659eebaa53cf22a2d209f0a82c2aa3c321fad0a20a03cc22a"
    "2db20a1fe1b869b9af04efa6ed41e25dbd5994b171a2ed81d95d54bdbdad71e2dd4194599971bded4162d49db5b98363b9a039a0a083b5b9a0a37939"
    "b935a083a3b9b960b4f9c817c86164e2a22515f0abb91a5d1d55a2a539b0da2b6b221d15b0a59af964606f4d8374625227fb2268aaf8b9f9f9e227bb"
    "38e879aaeaa7f92228fbb978b879ea27fbe239a8e23591c61194ea551551e2359486ead151e21591c6b52ad4d4d551e23591aa0631c28309da3265f5"
    "f5c331c2b209255ada71f5830902e5327235da31c203a5c91bd7987387c58a47c7581b9785f34a87479bc79833d78a451d40d09e24920d746e27f6a6"
    "9d321b0e0e366ea7f2269b1dd8a4c78493bfe8350e83e8f9544f56727756d3accb589075ed60b5d57da5e27eeeb090c547eb0f5db8660df9bcfbea31"
    "f9036825e7e67db0d74e13f2dec3554241f47d6f0bb6e9cf89b07b624c56decb35ead12fe7cd595106580be1f3a437d151cb06d824a1f7331a4986c5"
    "5cf7fc5204105c69775cebab1ae0760baeba8af2a33d1c785e2afd9d73bb55dbb70a66d00e2ca5a8643d248f12eb29021ada82bfcc9760937f7a67ff"
    "99fbc2395d3d008d75fb01b87bd90b269fdd8b3ba474eb8e9f3bebdda48b8e749fdd8e3ba4eb748b78dae9afb19a0de778af0ddab1e9e79a78dae7af"
    "b10d9ae978af9adab1e7e90d44b7e1d17597141144d114b775e11197496da038928eef3b4938ef6d92a03b8e1cecdbe9e349dc0d1ce9dcece3db0d49"
    "1cec0de9e3dc49db1ce949ece30ddbdcfbc244e9e46169212afddeb70555b6282ab7b6fd05de28558ac6a6abe96dbc3d2311c196c21544eee530eff8"
    "af7dd336906fc721eb3e22ca9021226febc7ca3ecc69ffef7edf487e42d4ec820a740605428206d40aec057442d405820a0674ec98bad68ed82216e7"
    "988e16bad8d6e72298bae78ed81622d6988e22bad8e7d6163e414e1c828b8c113e1c8c41824e118b3e41111c828c8b4e3e1c8b4182114e8cbb16afc3"
    "ddefc0debbc3c016ddafdeefbb16dec3ddc0efafbbc3ef16dddeafc01040db7737a1fbf401fcc50126c7762d010176fc26c52dc701fc2d012676c7c5"
    "dee56cf25cd543b4def243e55c6cb4d565f36a3181833ac365313af3816ac383edb22a2fc5db039aed2f03b2c52a9adbee287700c6b11e00ee001e28"
    "c67700b112adc9b739f16c715cabee26b5d84fed5c264fabb5eeedd86d2a6e1c762ae9d4cab65526d3dc8811ca2688b6d35511dccab61126d388dc55"
    "ca26dcb6d311558848e915600a53fb664860fbe90a15665348e966600afb5315486053e90a6615fba454276832fd665cc234a4609647cabac260ca34"
    "96a4ba47c234ba6096ca47a4d2f8c8da82abd373d2dad3f882c873abb4a4b1ee26b33d8fb4ee3da426b18fb3a5f5962a8c85da21a52adaf58c962185"
    "a5f5212a8cda85966df0075e5f5244001735cb71ecdc2bfce776756abe8ffccb1fe8340515c16f3e1f056fe815343ec1555c485d7b0918ef115d0f69"
    "b03903d54c120a455f1e88364c4588125f0a361e6a35a7c9baa20e373eee660747c16b603e076bee476660c13eee6007476bc1661173d3018defcb5d"
    "1101cb738dd35def11735d018dcbefd31101ef738d5dd3cb3875db1aebcf24e8381a2475ebdbe8cf3875e81aeb24cfdb381acf75ebe8db2438698912"
    "cb2370bb38127069cb89bb233869bb12cb70238938122369cbbb8970db1af2c73123d7cddbc7d71a31f2cd23db1acdc731d723f2dbc7231a31cdf2d7"
    "c939f29cd5bb98f3c99c9839d5f2f3bbc939f39cd598bbf2c99cbb39d5f3f298397c521a9d270901391a097c9d520127397c011a9d0927524973ecf5"
    "26226a60fbf58ed3384958a8fbd358f5388ea849fbf5a8d33858498efbd349f538a88e58d9d0f2243e85c43cd924c4d03ef23c85d9d03c243ec485f2"
    "d92485d03e3cf2c492d6f3793ea09cd492799cd63ef3d4a092d6d4793e9ca0f39279a0d63ed4f39cadefa0d5dbeca642add5a6efdba042ecadef42d5"
    "dba6eca0add5ecefdb42a0a681bb8ec1e60cdba081c1dbbbe68ea00c81bba0c1e6db0c8e81c10cbbe6a08edba01343bb7230a1e9a0bba1137243e930"
    "a013e9bb72a13043a0bb301372e943a136eae659b6a00fd0dcbf565c16e9007cdc5c00bf16567ce9dcbf7c5c1600e95656fbfd82b233d9115682d9fb"
    "b2fd113345b8aaf08278da5d45f0dab882aa5d7855161497bd0b543255975416bd14320b55163297bd540b1455970b16bd321454407af700b167fb1e"
    "9cbf8726a7f7f7319c26f7bfa78731f79cbf3126a7f7f78746cd842694e7a0d14626a0cd9484d1e746cdd12694a0e7844626e7cd94d184a0652534a0"
    "ac5e36d265a03625ac34d25eb99a84fcbadf5e48b9fc5e9aba8448dfebc82b087291e13beb08e1c8722b3b91ebc83b0872e1912beb0891c8723b2be1"
    "98ea811fd7693a8c981f3aead7818c6998ea8c1fd73a6981981f69ead78c813ae49cd7642386a530e464a59c23d73086e49c306423a586d7e464869c"
    "2330d7a590f28da487bed59c90a4d5f2878d9cbe90f29ca487d5be8d90a4bef2879c8dd59d2deb4556dff3759d45f32d56eb75df9d2d754556f3dfeb"
    "9d45df2d5675ebf3a9820842f5192c69a9422c82f5086919a9826942f52c1908a9421982f569082c1958569d83661641199d1658835641661958419d"
    "83166656199d665883415616e53e01fb2e56ed82e5fbed3e2e018256e53e82fb2eed5601e5fb563e2e8201ed6dbd82fe612fefe26dfeefbd6182e22f"
    "6dbde2fe61ef2f826dfe2fbd61e282efd65b4159bb2255abd659555bbb41ab22d65bab59bb552241d659225bbbab415572a1ff677ea674c0726774a1"
    "7effc0a672a1c0677e74a6ff7267a6a17ec0ff740dd0804c363c02830d4c02d03680833cf210253e97c25bfea9851abbb5f3a5691d08e62817c0d305"
    "1d28d30817e605c01d08052817d3c0e61d28c0081705e6d3f1ca77e8f0b94113de5520287298c5e2fcfe9efe2b9bb7ba8727bcd8b44331a0e685eea0"
    "4b2d9b39e6a09b854bee392d26e247d4ed645f8947fbb00080b966d964c4833da2737101643d71c4a283017364c4013da2717383643d73c4a2018371"
    "6fa65a4750e475ee6f4775a6505aeee46fa6ee475075e45a6f47e4a650ee5a75fb47be704f48c1b5fb70c1474fbeb548fb47b5704fc148befb704847"
    "4fb5bec1f6bc3b5db17673eb4e26aab797a436fd4eb7362697aafda44e26fdb79736a4aaeb4aa362b9de53dacdfd8ec18207ae351cb439e993cae413"
    "0000385870e21e83536cca53804cced81a88d285c9263b41f4c26bfd2d882e61cfb4162d40f9c1b39e6b193492da40979512dfb6192233ae4a002a30"
    "2a71e422fe26c940d3eb91efb4e8bfdbd9041b8167ed8b871e9e6a3ab83173cf2d25709e33486eaf47492614387e1c029d111d1689981099e5b31bcb"
    "3f641e46cd45417570f8f42c3659c035db0fc0ddcb5e30a9ec76dc215da75bfc7b6dd08e4d3fd7c4ec5edc21a55b77fcd34e7f8dd56c38c77bd5d48e"
    "3d4f6fc0dc59ef265d74a4fbd33e7f8d6dd04cc7ba0d8faebba48820c2796f9304dd714c48e7661fdf6e48e28aa6b8ad0b8fb82460df4e1f4fe26ee0"
    "484f621f6fd8e6e66a03c591747cdf49606f481fe74edae617264a270f4b0bd934365d4d6fe3ed518779c77fed9bb629e9f7be2da8b245518908b614"
    "ae20721f0c11795b3f56f681b9b5ed2ff046a9527c3b0e59f71151864efb7ff7fb46f263a22e105430a0631774b4d0c5b63e17c1a2661754a0332810"
    "d4b576c416b138c77414d1c53eb7b6c01234a056602fa013d43d77c4b610b1c60972e2105c648cf0e1580c128c7062f41d06b6e87ef57edfe1600c12"
    "748a58f4b5781dee7e07f6de1d7eb7e8f67e05de098ae010645c74f2b5f01eee067e7fdd00dabebb09dda787e06f0930b13b2e0e961f2ae762a3adf6"
    "e02f0e3039b66b092e6793e7aa1ea2f58bd1990f541b1e2c08b0e337296e390e9b578b091cd4192e97557929de1ed06c07f04031be0388755a7537a9"
    "c57e6ae77f19902d56d1dc6e684dbecd89678b935371e3b05349a76e47b903308ef5007032795aad756fc7e6b6ad3299e6468c5036e1b69d8ea84254"
    "02db4f57a8309b423641b49dae8ae0564aaf005398da3743029b4a5730abd847b68d309946e4ae524a370353d89faa40a53a4193e937e322a6d105b3"
    "543e2215d69ec617449e5b95a62105b33c52d615c647d6165c9d9e9375ef2135897d9ca50653a6b124d53d12258d753799ed79a4adb754612cd40e29"
    "833ff0fa92220268b7ab53f37de45f3e55d1ae67b40c292ca8598e63e75ee1bf287843afa0f109fead0f5161d42eb42c40a729a8087ef3f9e242eada"
    "4bc078af2a4294f852b0f16071373b380a5e03f3e87a4883cd19a88eab394dd61575b85171073b385a0b36f3925028faf240b4613958733f32030bf6"
    "989b0e687c5fee8a08789f6bec9a5e8ed120a95bdf467fc608589e6b9cee7a8fa9dbd6587f2641c7d178ae5b47df26c198eb0a685c7e9f8ea943d758"
    "2779dec6494b94581e81dbc59118495bde4d84c33ebed688916f1ed991804b5b4edc1dc1d6903f8e19b96ede3e1ed1886996bfde49db9558861b49c4"
    "d6683e8eb91e91dfce91e7acdec59c4fe6dccda99e97c74cd148e0eb940a38c9e6c4cca9969fdf4de193d2e83c4908c89a63af371151034bce99e7ac"
    "c6dc954fe10bd0e84c3891caaf779cc649c242dd9f4eaac74175c4da262186f691e729cc9fc6aac771444dda869627f12924e6c9262984f6e19127ce"
    "af479dc6c14a72dc86e621f1212e94cfb49ecff301e5a496cc03b5f6a19ee794ad367ddf0615626fcce3b4f699a706957d07adde6637156aad667fdf"
    "1602356db4a6cef3e1049d977d17aade3665076ddc750c3667d8060d0c66d8350775dc0edd0d9d901b4a87010cdede35770465089d18da9583094d07"
    "dd8599904b1f0a05dc050d36df66700c9d48df950b8519025137cfb2057d80b6fee5e3b20048b7e212ccde97ed8f98b1feb5e2b24807e0e3daef1794"
    "9dc98eb082d7c61554edc22be602f8b5b0e24be7c2558517c4d3ee2ab2a0b8ec5da092a9ba5cb0e895a1a0aafc3d3439bdbf8fe1baa4b2e8a59059a8"
    "d2bb07883ddbf700fc8d3139bdbf3fe4b290b9eca55aa0a834b9ff3d3d8cb9e76a2634a13c078d3632396fa68c26043503b52961a591f62a32016da6"
    "248c3e372ba10165f5b2912ee5f7d2d42544face6a8e36a1043d2734d524e4d7fdf642ca475e41908b0cdf5947884496db59095ffcd051bf0e644cc3"
    "470847965bd9895c540ffcb84ed361c4fc4853bf660cd4c147de41900b8f5c595467fcb8d6490bc4e7bc261b312c85212733e41c81b92e2524ad963f"
    "6ce4f485272be51cb9863124946f243df4ade68424f5953fe46cac86e784211b2935bc2694e7243dacf66d846c592fb2fa9eafeb2cfa6eb1aa5b9fef"
    "156211ac4748cb482c9a6fb15aaffbee154410aacf60494b15ca10ac4f4360496ca92bb29aff5eef154c13aa67c94048c0b2ea1c34b308cae834c31a"
    "0cb2b2c8df6ff7710910b42ae8b4c01ab40a32cbf709d877b16a172cdfb7f271110c682fc00aea1cb430b3caf711dc7769b70a28eb15f40f7b79176f"
    "f37fe90d13177c6fceaadada0d5a15b1f37fef0d13147f69de0acada15a95ab5ce12d9da5d0daab2eb15f70f7b7f116cde5acddaad1209b20bfd3ff3"
    "33a503963b330df503fea793601280b6011ce4693ba30bf5fb073695800664b2e111186c2dd4d8ad9d2f4d4b0b053ef3a333fd978728f1b914def297"
    "403047b9009e2ee8400146b828309feeae024191c32c16f7409946b8302f00ee57be4387cf0d9a883ce1c5a61d8a013d402840b9980636eff7f7f45f"
    "d9bcd5e52f74075d6ad9cc31da870500cc35cb3eeb8923161d0c982307dd2c5c72cf6931231eec119d8b0b20eb9923160d188c23113fa26e27fb4a34"
    "230ee8118d9b1b2433d53a8222af737f3b22378572d7aa7b870b3e7af2ad45da3baa3385d272277f3ff2857b420aaedd87433a7aaaf50dde33753f82"
    "aa23d77a3faa857b0a46f2dde7dde98ab59b5bb732e9bfbdb4215575ee770c163c70ad693251bdbd24b5e977571a15cbf59ed25e00c0c18213f71804"
    "bab531b954ed2775a0cd499f54269fe062539e026472c69ea6b56801ca0f9e7d94f8b6cd109971ad40942e4c36d909d25ccba091d406baf43749069a"
    "5e8f7cf7175eeb6f417409a3025081518923175145ffddce26d808a441727b3d4a32a198c484c82c9fdd584e6b5f3cf4f054d339f1e310e88ce8b0c0"
    "c3a767b1c902ae818d997b6e2981f3c421f3306a2e0aaafb7e00ee5ef68249ddf7e20e29ddbae367aba676ec797a03deb7e30ee93adde26776fa6bac"
    "66c3399ef6f96b6c83663a9e6b83766cfab926dece7a37e9a223dde76d7874dd254504d134c56d5d78c425517a12fb78c3363747ce7b9b24e88e6312"
    "fb76fa78127703077b43fa3877d236073a37fbf8764312471b288ea4e3fb4e5230513a79585ac8bebff76d41952d8a4a88c8dbfab1b20f64b1e96a7a"
    "1b6f8fa244b0a5700591fb48db71c8ba8f8832e4cc3bfe6bdfb44d39ad6d7f81374a95cadaffbbdf37921f7335bba0029d418110a3882ef6b9b505a6"
    "7581a082011dbb10aeb523b688c539a6eeb923b6858835a6a3852eb6f5b908a6a001b5027b019d90901387e02263844f076390a053c4a20ff0bb45b7"
    "f72bf0eec76290608413a30fc5eb70f73bb0f7ae85f77037f0fbebae30b045f7abf7fbee50048720e3a2934fd0f6dd4de83e3d047f7180c9b15d4b00"
    "8cce7ca0daf060597f4b8089dd717100399b3c57f510ad77bc5a4ce0a0ce70d9fc5039171b6db5b7801dbf4971cb7140acca4bf1f68066bbcb806cb1"
    "8ae676fb8a1b879d4a3a759b80078af11d40ac3b6bf26d4e3c5b9c44c9d36aad7b3b3697aabb492df6533bd7ca1d8071ac07803b6d95c934376284b2"
    "09a2ed745504b7b2d854ba8259c53e1209b7ed744415a2b27a0598c2d4be1952ba1998c2fe540552d87eba4285d914126d84c934227795b2d5099a4c"
    "bf1917290d2998e591b2ae307b0fa949ece32cad8d2e98a5f211a9303eb2b6e0eaf49c3469acbbc96ccf232df634be20f2dcaab498328d25a9ee9130"
    "bda50a63a17648698a763da3654861a9c11b7a058d4ff047fc81d7971411401bcd721c3bf70aff453a4d4145f09bcf075d9d9aef23fff2b97d880aa3"
    "76a165691752d75e02c67b15d7431a6cce4075443bd8c1d15ab0998f11a2c497828d0753cd69b2aea8c38d5ac19afb911958b0cfbbd9c151f01a988f"
    "8442d19707a20d93dc7440e3fb7257c4c0f25ce374d77b44c673dd3afa36098ec0fb5c63d7f47244ddb6c6fa33093a4e1dbac63ac9f3364e0649ddfa"
    "36fa338e5c5740e3f2fb74c45aa2c4f208dc2e4e045cda72e2ee088ef188464cb3fcf5f6c448daf26e221c8e86fc71ccc875f3b646f371ccf588fcb6"
    "f1b5468c7cf3c8f6daaec432dc48224e8e3c67f52ee67c7227664eb5fcfc6e321c7bbd89881a58d2e76e4ef5bc3c66329f9446e74942400e5f804667"
    "c289540e46025fa754c0498ece3c6735e6ae7c72bde3344e1216ea7e34563d8e236ad2fe4921b40f8f3c713674523d0eaa23d6feb43c894f21314f36"
    "340f890f71a17c360931b48f3c4f61363dea340e5692e37ef57c9e0f2827b5a41ea7b5cf3c35a86435fbfbb610a8696b1ea8b50ff53ca7643b68f536"
    "bba950ebbb50f5b6293b68ebb5e9fb36a8107b6b35759e0f27e8bca4ae63b039c33668e0f0f6aeb9232843602ecc845cfa5028e830c3ae39a8e37660"
    "c4d0ae1c4c683ae844faae5c28cc10e86ee884dc503a0ce82e68b0f9368363e0ba79962de803b48daf1597453a001ff7bc36aea06a175e112f1f9705"
    "40ba15f77ebfa0ec4c7684d5ae2abc209e76571160f6be6c7fc48c9517c0af85155f3a3705c565ef02954c952595452f85cc42d56f8cc9e9fdfd21e7"
    "e58245af0c0555d5de3d40ecd9be0790c9fdefe961cc3da7efa1c9e9fd7d0ce785cc652fd502459533a109e53968b4510968332561f4b991bf97a62e"
    "21d2772ec97933653421a891090d28ab978d74592621bfeeb71752aea84d092b8db4571973b40925e839a151f20a825c64f8ce3a4238b2dcca4ee43a"
    "479afa3563a00ee64224b2dcce4af83a7ae0c7759a0e23a63ae3c7b54e5a20a6878efa7520631ae6f20e825c78e4ca3ae735d98861290c395929e7c8"
    "358c2139a9affc21676335249921e708cc7529397c23e9a16f3527a43c27e961b56f23a469b5fc6123a72f24270cd948a9e13539cb7a91d5f77c5d67"
    "d17c8bd57add77675086607d1a024baad1778b55ddfa7c672082507d064b5aaa609a503d4b0642aa108b603d425a46aa4b5d91d5fcf77a679655e7a0"
    "99455006a705d6a055905946be958f8b60407bf9a719d660909545464fc0be8b55bb60b98fe0be4bbb5540b97ebb8f4b80a055f95650e7a085995506"
    "afa07fd8cbbb785bff7b6f98a0f84b9b96c8d6ee6a509575ff4b6f98b8e07b9b5650d6ae48d5aaf5d66ad66e954890f556d5d66ed0aa8875afb87fd8"
    "fb8b605be8ff999f291db05c195da8df3fb0a9dca1c66eed7c695a6a9969a81ff03f9ddc3420930d8fc060034489cfa5f096bf3c9300b40de0204f03"
    "28f0991f9de9bf5c8239ca05f0744107ca34c28579017007092f36ed500ce8e10a30c24581f97407f21d3a7c6ed044bcbfa7ffcae6ad2ebf15088a1c"
    "66b1b8774201cac534b07907a13be852cb668e79e866e1927b4e8b39cf1cb168c0601c593e2c0060ae59f6d1f1608fe85c5c001971408f68dcdc2019"
    "4f1cb1e860c01c59f811753bd957a289a9d61114799dfb9b519d2994963bf9db1cd2d153ad6ff03e11b92994bb56dddb912fdc135270edfe512ddc53"
    "3092effe5cf0d1936f2dd23ea9fb11541db9d69bef4e57acdddcba3d89eaed25a94dbf93000e169cb8c7200049ffeda50da9aa93d2a858aef794f6ba"
    "6d4efaa432f90407bf63b0e0816b4d73ad8dc9a56a3fa9d39bf214209333f614a27461b2c94e90064932d0f47ae4bbbfad450b507ef0ec335a068da4"
    "36d0a5e7800a8c4a1cb98812c4b76d86c88c6ba5f05a7f0ba24b18bdfaef7636c146202dfbe2a187a79ace593e3d8b4d16700d1c92dbeb519209c50c"
    "1f8740674487058e998751735150dd0f264466f9ecc67222ccdc734b099c276e0370f7b2174ceaf61d7748d7e9163fbbcf5f631b34d3f1b4177748e9"
    "d61d3fbbd35f63351bcef1b4d6bb49171de93e7735b563cfd31bf05e1bb463d3cf35f15ec3a3eb2e2922886ededb2441771c93701bd2c7b993b639d8"
    "296eebc2232e89a2b7d3c793b81b38d84071241ddf7792da93d8c71bb6b939d2b9d9c7b71b9238d289d2c9c3d242f6854d57d3db787b148d8e43d67d"
    "449421dfbd6f0baa6c5154fa822d852b88dc47226dfb0bbc51aa546e44ded68f957d2043def15ffba66dca61fedffdbe91fc98d30b04150ce8d885a8"
    "cf1db12d44ac3175d90515e80c0a84a8ad1db1452cce31750da815d80be884044574b1cfad2d301d2d74b1adcf45301d9c38041719237c8216830423"
    "9c187d38bc87bb81df5f772d1883049d22167d385e87bbdf81bd772d22380419179d7c82df2dbabd5f817787812dba5fbddf7787b6ef6e42f7e92180"
    "5b024cec8e8b03f8d56202077586cbe68b034c8eed5a02f8d9e4b9aa8768bdcbecf84d8a5b8e030274e603d58607cb6287cab9d868abbde5555e8ab7"
    "0734db653c508cef0062dd019e566bdddbb1b94c06648b5534b7db5f936f73e2d9e2245aee008c633d00dc51dc38ec54d2a9db54dd4d6ab19fdab956"
    "ab4ca6b91123946db86da723aa10954dcdc014f6a72a90d2106da7ab22b8954d2bc014a6f6cd90d2234ca611b9ab946da6d215cc2af691c0f6d3152a"
    "cca690c04ed064facdb848a974c12c958f48856963dd4d667b1e694948c12c8f9475856991b50557a7e7a4f194692c49758f84c17b484d621f6769dd"
    "a7f10591e756a5b52d55180bb5434aeb0fbcbea48800dae0690a2a82df7c3ed0b4eb192d430a4b5596e3d8b957f82f6a435418b50b2d4bebded02b68"
    "7c823f0aead47c1ff997cfed90baf61230deabb81025be146c3c988ad6dc8fccc0827d0e1ed2607306aa23ba4e9375451d6ed46a148abe3c106d9824"
    "c10e8ed682cd7cdccd0e8e82d7c07cdca6031adf97bb22e6dee71abba6972302d035d6499eb771ea96e71aa7bbde2302b635d69f49d071eaba021a97"
    "dfa723e69eebd6d1b749703448ead6b7d19f713412259647e07671d246d2967713e170249a8f63ae47e4b735e0d2961377477024e48f6346ae9bb735"
    "762596e1461271d24734629ae5afb78faf3562e49b47b68fe439ab7731e793737773aae7e531933902343a134ea472f83173aae5e7779339a4343a4f"
    "120272f8e639ab3177e59373d8eb4d44d4c092e612f83aa5024e72341da77192b050f7eb93ea71501db1f6a779487c880be5b3a1b1ea711c5193f6a7"
    "e5497c0a8979b2a151a771b0921cf7eb0aa17d78e489b34988a17de4790ab349e7f37c4039a925ad40ad7da8e73925f385aab74dd9415bdf38ad7de6"
    "a94125f341abb7d94d855adfa9f37c3841e725add9dfb785404d5bab4ddfb74185d85bab1d83cd19b64103771976cd411db70383d277e54261864027"
    "b777cd1d411902838676e56042d341274183cdb7191c03776126e4d2874241774327e486d2614077cdb36c411fa06dd4f9b82c00d2adb87f55e105f1"
    "b4bb8a70adb82cd201f8b87ffb056567b223acf6007e2dacf8d2b9b9b5710555bbf08ae0b3f765fb2366ac04282e7b17a864aa2c172c7a6528a8aa2e"
    "ee7f4f0f63ee394da92c7a296416aa2eee0162cff63d80f4642e7ba91628aa2c634c4eefef0f397f0f4d4eefef63387f094d28cf41a38d9ace9b29a3"
    "09418d4c09f975bfbd907235409b2909a3cf8d4c684059bd6ca4cb4aa34d2841cf098d9abd34750991be73f96d4a5869a4bdca405710e422c377d691"
    "2291e57656c2d711193fae75d20231d5c291e5567622d711033faed3741831d57710e4c22357d691d2d4af190375303f74d4af0319d3303fafc9460c"
    "4b61c8390c394760ae4bc9c939490fab7d1b21e54a3947ae610cc9c91b490f7dab3921e561c8464a0dafc9397de50f391bab2149abe50f1b397d2149"
    "d68bacbee7eb3a5bbe5bacead6e73b8bd384ea5932105205e65bacd6ebbe3b8b1184ea3358d25205ea8aace6bfd73b5b3204ebd3105852855804eb11"
    "d2325285ac3a07cd2c8232b0cdb00683ac2c323a04f75ddaad02ca7d2db006ad82cc323a02f65dacda05cb7d823a072dccac32b0ad7c5c0403dacbf7"
    "db7d5c0204adcaf705fdc35edec5db7a5f7ac3c405dfdbfc56b376ab4482acb7df7bc304c55fdafc82b27645aa56adb7c5fdc3de5f04db7a44b67657"
    "83aaacb3aab676835645acb3ffcffc4ce980e5424c43fd80ffe9e4ce4a7c2e85b7fce521e842fdfe814de5ce01996c7804061ba081cffce84cffe542"
    "35766be74bd3520b04a06d0007791a98cc512e80a70b3a1080112e0acca73b503dfd57366f75f9fda6112ecc0b803b50efd0e1738326e2950a502ea6"
    "81cd3b1078b1698762400f4f4050e4308bc5bdabdd41975a3673cc0b61010073cdb28ff6037a44e3e606c988370b97dc735acc41077b44e7e202c888"
    "8fa8dbc9be124dc4e688450306e3c87ae288450703e6c87ab58ea0c8ebdcdf4cc84da1dcb5eade8e6ae19e82917cf78fea4ca1b4dcc9df8e7ce19e90"
    "826bf78fdd8fa0eac8b5de4c908e9e6a7d83f7e1828f9e7c6b91f6e177ba62ede6d6ed79fa6f2f6d48559d4c73d22795c9273868546f2f496dfa9d4c"
    "46c572bda7b4d7956d4c2e55fb499d6e70b0e0c43d0601001d83050f5c6b9afb94a700999cb1a7d82d5a80f283679f69546054e2c8459400a50b934d"
    "76823410326824b5812e3dd7d7fa5b105dc2e8859281a6d723dffd4dbe6d3344665c2b257fb7b309360269d1dc5e8f924c2866903c8c9a8b82ea7ec8"
    "170f3d3cd574ceda38043a233a2c70fce69e5b4ae03c7163e9596cb2806be0f02132cb673796133180bb97bd6052b71fb8434ab7eef8d9bdde4dbae8"
    "48f7b9b3b843ba4eb7f8d9edfe1aabd9708ea79da01d9b7eae89f7dafe1adba0998ea77da91d7b9ede80f7aa1e5d77491141741b715b171e7149144d"
    "8a23e9f8be93d406de2609bae39884f39d3e9ec4ddc0c1becd3ebedd90c491ce903ece9db4cdc1dec43edeb0cdcd919e944e1e9616b22f4c7d5b5065"
    "8ba2d2efdb5fe08d52a5726bba9adec6dba3686c6c295c41e43e12118effda376d530ef31cb2ee23a20cf976f2b67eacec031922ffeef78de4c79cf6"
    "2ea84067502044cd40adc05e4027246820a86040c72e445ded882d62718ea96ba18b6d7d2e82e968ee886d21628da97ba28b7d6e6d81e928c421b8c8"
    "18e113e41824e814b1e8c3c1c121c8b8e8e41314182418e1c4e8c3b13adcfd0eecbd6bf16cd1fdeafdbe3b0c3ddc0dfcfeba6be16ed1edfd0abc3bfc"
    "7d7713ba4f0f01b41c60726cd712c05fc76f52dc721c1060126062775c1cc0df26cf553d44eb5dce54cec5465bed2d3f161338a8335c36af331fa836"
    "3c5816a3f252bc3da0d92eab205baca2b9ddfe3207601ceb01e08e7281627c0710eb0ee07c9b13cf1627d19a6e528bfdd4ceb5eab45aebde8ecd65f2"
    "c661a7924edda6e26532cd8d18a16c5b683b5d15c1ad6c8261328dc85da56c1b6d3b1d5185a86cc201a630b56f86945e9fae5061368504b606a6b03f"
    "5581946e95ae6056b18f04368226d36fc6454a750a6679a4ac2b4c434c6349aa7b240ca60b66a97c442a4ca3ac2db83a3d278d8f8d2f883cb72aad3d"
    "eb6e32dbf3484b1a436a12fb384bebdea9c258a81d525a6f5dcf68195258aaa2a2c2a85d68595a1fe0f5254504d0067f1cc7cebdc27f51b3a7e6fbc8"
    "bf7c6e57535011fce6f3814e865e41e313fc51f0d4b59780f15ec58590069b33501dd1f550f4e58168c324a128f1a560e3c154849aac2bea70a35673"
    "767014bc06e6e36ee67e640616ec73b07670b4166ce6e30e1dd0f8bedc1531373cd738ddf51e11b015d0b8fc3e1d31d73ed7d835bd1c11f0adb1fe4c"
    "828e53b752b7be8dfe8ca341aeb14ef2bc8d53875cb78ebe4d82a3f128b13c02b78b939697b69cb83b8223012bb10c37928893b692b6bc9b08872331"
    "7f1c3372ddbcad21ad1123df3cb27d7c7c1c733d22bfadd1a211d32c7fbd7d3ccf59bd8b399f9c2399532d3fbf9bcc89cf598db92b9f9c339b533d2f"
    "8f99ccb9a5d179921090c327c0d729157092a391a0d199702295c3175e6f22a2069634c7388d938485ba5fef558fe3889ab43f8d3a8d8395e4b85f8f"
    "548f83ea88b53f9d4fe25348cc930d2d0ced23cf53984d4243e2435c289f0dcd08edc3234f9c4d529fe703ca492d693d69ed334f0d2a99c79de7c309"
    "3a2f694d6aed433dcf2999075abdcd6e2ad4fa0efabe0d2ac4de5a6d54bd6dca0edafa2efebe2d046ada5acd186cceb00d1ab8ebbd6bee08ca1018bc"
    "1a6cbecde018b80bb06b0eeab81d18ccb42b07139a0e3a313a2137940e03ba1bbe2b170a33043a913321973e140aba0b9e650bfa006da36ec565910e"
    "c0c7fd6bf06b61c597cecd05c76501906ec5fdcb2f283b931d61b5dfbd2fdb1f316325980a2f88a7dd5584ab8d2ba8da855704af71d9bb4025536541"
    "65d14b21b350754973d94bb54051652160d12b43415575b90f107bb6ef01a47768727a7f1fc3f97bff7b7a1873cf697263727a7f7fc8f91b6842790e"
    "1a6dd44cda4c49187d6e64026d42097a4e68d41cde4c194d086a647203caea65235d564253c24a23ed55066ac8affbed8594ab49a5a94b88f49dcbef"
    "82201719beb38ebc8e2cb7b213b98e108320171eb9b28ebc892cb7b312be8e10f8719da6c388a91ea37e1dc89886f9a1f871ad931688a9cea67ecd18"
    "a883f9914d3662580a43ce79ca39720d63484e564336526a784dce09c83902735d4a4e66487ae85bcd0929df2d7fd8c8e90b495a497a58eddb0829cf"
    "2b7fc8d9580d49ea5e64f53d5fd7d9b2df62b55ef7dd5934576435ffbdded952dd6255b73edf59f420549fc192962a8822588f9096912ac42654cf92"
    "81902a9821589f86c0922a94d539686611948165813568156496d169d439686166958115863518646591d169b0ef62d52e58ee13eee312206855bedf"
    "b8efd26e1550ee23e5e32218d05ebe6fe81ff6f22eded62bde1b2628fed2e6ffee1ff6fe22d8d62bd21b262ef8dee6ff94b52b52b56abd15b5b51bb4"
    "2a629d559ab55b251264bdb5b2b5bb1a54659d257fe6674a072c17fa17eaf70f6c2a77467ce64767fa2f170a1aea07fc4f277766c864c32330d8000d"
    "006d0338c8d3c024e27329bce52f0f51b15b3b5f9a965aa88e72013c5dd081608d70615e00dc81328072310d6cde81508c7051603edd8102870e9f1b"
    "3411af7c822287592cee5d05e9bfb279abcbefef8b4d3b14037a78c20ebad4b299635ee859b8e49ed3620eba44dd4ef69568227e0b00986b967db40f"
    "d8233a171740463c472c3a183047d613d0231a373748461c472c1a301847d6337504455ee7fe66aa670aa5e54efe76547e045547aef566ea6e0ae5ae"
    "55f776440bf784145cbb7fe47cf4e45b8bb40f170bf7148ce4bb7f5474f454eb1bbc0f87d3156b37b76ecfbb7a7b496ad3ef64a26372a9da4fea746b"
    "7f7b6943aaea64d22a96eb3da5bdae34182c78e05ad3dcef933ea94c3ec1419b830527ee310800803c05c8e48c3dc5a65d986cb213a48128d6df82e8"
    "12462fbcd102941f3cfb4c6b4123a90d74e9b9966d9b2132e35a29f102a312472ea204a00c34bd1ef9ee6f92bb9d4db011488bfe78e8e1a9a673d6be"
    "f7dc5202e7891b33f67a9464423183e421d019d16181e3c791593ebbb19c880961d45c1454f743e6cf6293055c03874fdcbdec0593bafd001dd275ba"
    "c5cf6ec7edd8f4734dbcd7061d52ba75c7cfeec5d758cd86733cedf4edd8f3f406bc574d6ed24547bacf9df5d7d806cd743cedf3e8ba4b8a08a2dbf0"
    "3649d01dc7249cf7f6f1ed86248e746edbbaf0884ba2688af4f124ee060ef6edf6f1866d6e8ef4241c49c7f79da43650f471eea46d0ef68674f2b0b4"
    "907d61a2d5f436de1e4563d3fcd7be699b729877db822a5b14957eef4be10a22f7918860b7f563651fc81091fe026f942a955bdb90751f1165c8b7e3"
    "77bf6f243fe6b4ff4105033a7621ea025d6ceb73114c470b41053a8302216a76476c118b734c5d6b5dec736b0b4c47116a05f6023a214103476c0b11"
    "6b4cdd730ec145c6089f202720c10827461f8ec58bee57eff7dd61602041a788451f0ec6e1ee7760ef5d8bd78b6eef57e0dde1770e41c645279fa008"
    "e16ee0f7d75d0befbb9bd07d7a08a0ed0013bbe3e200fe96722e36da6a6ff9a1009363bb9600fee279aeea215aef7236f940b5e1c1b2189d7e93e296"
    "e380003b98c0419de1b279b597e2ed01cd76599514e33b805877000f935aeca776ae5577d96215cdedf69701db9c78b63889d6e40e3b9574ea361537"
    "00e3580f0077943bd55af7766c2e93a793696ec40865db2adbe9882a4465136e74850ab32924b0fddbe9aa086e6513443085a97d33a4f40a7405b38a"
    "7d24b0a9936944ee2a65db083085fda90aa4743334997e332e52aa13304be52352611a5d7c41e4b95569ed6930cb23655d611a526dc1d5e939697c64"
    "5293d8c7595af71e1a4b52dd236130657793d99e475ad25815c642ed90d27a4baf2f29228036f80335df47fee573bb3a7a46cb90c25215ed3876ee15"
    "fe8b9ae5f40a1a9fe08f82371546ed42cbd2fa10828ae0379f0f749aaebd048cf72a2ea4892f051b0fa6224483a3e035301f77b334d89c81ea88ae87"
    "645d51871bb59ad383a3b560331f77b0a22f0f441b260985f72333b0609f833580c6f7e5ae88b9e9b9c6aee9e58880f7baf56df4671c0d92b9c6e9ae"
    "f78880e58df56712749cba6dba75f46d121c8de780c6e5f7e988b9ae8d7592e76d9c3a7489e511b85d9cb444b4e5dd44381c89918d18f9e691ede36b"
    "b4e5c4dd111c09b8e39891ebe66d0df98d9866f9ebede3118965b891449cb45de398eb11f96d8de6ceea5dccf9e41c799cea7979cc64ceddbe4ea980"
    "931c8d049c6af9f9dd644ecc8dce9384801c3e297a131135b0a439f6ce6acc5df9e49c798dce8413a91cbe00699c242cd4fd7ac77a1c5447acfde9a4"
    "681f799ec26c12627a1c47d4a4fd69ac129f42629e6c6879681f1e79e26c9242691cac24c7fd7ad4121fe242f96c681e3c1f504e6a49ebf96b1fea79"
    "4ec93c50f76d5021f6d66ad36b9f796a50c93c4eea6d7653a1d677d0f76d2150d3d66af63c1f4ed079496beaea6d5376d0d677a16073866dd0c05dc7"
    "5d7350c7edc0608609b9a17418d0ddd05d73475086c0e0ed5d3998d074d089a109b9f4a150d05d9860f36d06c7c05dd05db9509821d089f42c5bd007"
    "681b75f32e0b80742bee5f3e7dd9fe88192bc1ec2e8b74003eee5f2b41d999ec08abfd7e5c41d52ebc22786d5f0b2bbe746e2e8078413cedae225c55"
    "cbde052a992a0b8a8b5e190aaaaacb0593d3fbfb18cedf438b5e0a9985aa4b2a80d8b37d0f20bd7b93d3fbfb43cedf18cb5eaa058a2a0b99dfd3c398"
    "7b4e93fb13ca73d068a3664266ca6842502393f312561a69af32509b664ac2e8732313d050562f1be9b2121a4d5d42a4ef5c7e2f134ad07342a3e668"
    "7edd6f2fa45c4d4204b9c8f09d75e41564b99d95f0758448f5eb40c634cc0f1d64b9959dc87584708feb341d464cf5c0f56bc6401dcc8f3404b9f0c8"
    "9575e41d8f6b9db4404c75c6b211c3521872ce6bce1198eb52723243f9c3464e5f48d26ace916b184372b252d243df6a4e48f946f943cec66a48525f"
    "b29152c36b724e18d2c36adf4648794e22abeff9bace96f516abbaf5f9cea2efc17a84b48c54211616abf5baefcea2f9a1fa0c96b4544104c1fa3404"
    "9654a10c22abf9eff5ce96baa17a960c8454c134ce41338ba00c2cabacc1202b8b8c4e331f970041abf2fd76ac41ab20b38c4e0b7d17ab76c1729f80"
    "1f17c180f6f27d2bce410b33ab0caca07d9776ab80721fc1ffb09777f1b65e41de3071c1f736ff97addda05511ebacaade3041f19736fff7ac5d91aa"
    "55ebada0adddd5a02aeb2c91ffb0f717c1b65e71acdd2a9120ebadd5333f533a60b9d0ff503fe07f3ab933d3681bc0419e06260150bf7f6053b933ba"
    "261b1e81c1066840dddaf9d2b4d4428d333f3ad37fb950e09f4be12d7f798812940be0e9820e0473848b02f3e90e14601439cc6271ef2a10840bf302"
    "e00e946974f8dca08978e53b6cdaa118d0c3135e948b6960f30e8402ff95cd5b5d7e7f4fd0a596cd1cf3427700c05cb3eca37d5862d1c18039b29e38"
    "c225f79c1673d0cd1ed1b9b80032e2c162d180c138b29e39ea76b2af4413f1231ed1b8b94132e2802328f23af73753ad532877adbab72372a327df5a"
    "a47db8e053282d77f2b7a33ab827a4e0dafd235fa3a75adfe07d38a423a83a72ad3753f7b8a76024dffda35aae58bbb9757bde9ddb4b1b52552793fe"
    "60c103d79ae67ec7db4b529b7e2713d5b15cef29ed75a5512c38718f4100001c934bd57e52a75b1bf44965f2090eda9c29402667ec2936e516a0fce0"
    "d9675a8bdb0c9119d74a896fc264939d200d44e91a496da04bcfb50ca0e9f5c8777f9364fe164497307ae1b51895387211250015ed6c828d405af4df"
    "d7a324138a1924b7ccf2d98de5444c88430f4f359db3f6c581ce880e0b1c3f0e169b2ce01a387c7ae79612384fdc98b9a3e6a2a0ba1f320fee652f98"
    "d4ed07e090d2ad3b7e762feec79ea737e0bd6a6a90aed32d7e763beec66a369ce369a7bfc63668a6e3699fbfc7a69f6be2bd3668932e3ad27deeac77"
    "d75d524410dd8647d685475c124553dc8f376c7373a427b14982ee3826e1bcb78f27713770b06fa78f73276d73b037a48f6f372471a473b3483abeef"
    "24b581e29387a585ec0b13a51654d9a2a8f47bdfad1f2bfb408688bca6b7f1f6281a9bae0a5710b98f44045bacfb882843be1d87bff64ddb94c3bce3"
    "1778a354a9dcdaf6fb7d23f931a7fdbf2ad019140851b30b629f5b5b603a8ae82a18d0b10b511708628b589c63ea5a3b625b885863ea9e3b625b9f8b"
    "603a5ae82bb017d009091a50082e3246f8043971093a452cfa703006747bbf02ef0ebf5b09463831fa702c0677bf037bef5abc0e7703bfbfee5a780f"
    "74bf7abfef0e035b08322e3af9044570dd84eed343006ddf981cdbb504f0170707aa0d0f96c5e8cc98d81d1707f0b70473550fd17a97b3c9040eea0c"
    "97cdabc573b1d1567bcb0f959b14b71c0704d8f1146f0f68b6cbaabc16ab686eb7bf0cc8d8a9a453b7a9b87118df01c4ba0378a0e6c4b3c549b426df"
    "d6bab76373993cadd4623fb573adba9b18c77a00b8a3dc014c73234628db56994e5745702b9b20da2b9855ec23814da54e4754212a9b70db294ced9b"
    "21a5578029ec4f5520a59b812b54984d2181eda74c23725729db4698c9f49b7191529da0591e29eb0ad390829ac43eced2baf790592a1f910ad3e882"
    "0bae4ecf49e3236b9bccf63cd292c6ba0b22cfad4a6b4fe35892ea1e098329d330166a8794d65baa335a861496aa68d757d0f8047f14bca17d491101"
    "b4c11f78b173aff05fd42cc75404bff97ca0d314f93ef22f9fdbd5a9306a175a96d687a8ed2560bc57712175c1e60c5447743da41cad059bf9b8831d"
    "7c29d8783015214aeb8a3adca8d59c261f998105fb1cacb91c05af81f9b89b1d7d7920da3049281434be2f7745cc4d07354e77bd47042ccfada36f93"
    "e0683cd735764d2f4704bccfac3f93a0e3d46d6bac933c6fe3d4a16bad6fa33fe36890d4342ebf4f47cc75052c8fc0ede2a4254a2d27ee8ee048c0a5"
    "c434cb5f6f1f8f682def26c2e1488ca4c78c5c376f6bc81fc75c8fc86f6b341fc4c8378f6c1f5f6b2cc38d24e2a4ed4a56ef62ce27e7c87354cbcfef"
    "267362e69b88a88125cdb1d754cfcb632673eee6749e2404e4f0496974269c48e5f00568754a059ce46824f05663eeca27e7cc73e32461a1eed73b4e"
    "e338a226ed4f63d5fbf0c81367931442e3a03a62ed4f27d5f81412f36443cb93f81017ca6743f390fbc8f31466931043e3602539eed7a34ef9807252"
    "4b5acfe7fbcc53834ae6715a6f0b819ab656b3bffb50cf734ae6815a6fb39b0ab5be83566f9bb283b6be0b556f830ab1b7569bbef97082ce4b5a53e7"
    "9b336c8306ee3a069a3b823204066fefc8a50f8582eec24c9a833a6e070633eccac184a6834e0cedca85c20c814ea4efc80da5c380ee864e9b6f3338"
    "06ee8206d9823e40dba89b6759a403f071ff5a710aaa76e115c16be35900a45b71fff271cace644758edf70b0be2697715e1aac2cbf647cc580966ef"
    "5a58f1a5737301fcf62e50c95459505cf452c82c545d52599cdedf1f72fec698f4ca5050555d2e58c49eed7b00e9dd039e1ec6dc739adcff9cdedfc7"
    "70fe1e9af6522d505459c85c509e83461b35139a5312469f1b998036ea12227de7f27b69534613821a999c37b27ad9489795d080eb7e7b21e56a12f2"
    "b0d2487b9581da9450829e131a35479bc84586efac23af20cbadec44ae2384235f3306ea607ea4a9cbedac84af2344225ca7e93062aa077e5ceba405"
    "62aa337e5f0732a6617ee8a8c88547aeac23ef208d1896c290735e938e5cc318929395721f7236564392faca8ec05c97929319721efa567342ca3792"
    "1e56fb3642ca73921f3672fa429256cb8d941a5e9373c290597dcfd775b6ac1758add77d7716cdb7d6a721b0a40a650858d5adcf77167db7d567b0a4"
    "a50a2208d5b36420a40aa609d623a465a40ab10859cd7faf77b6d4150e9a5904656059750d5a059965745a60b80806b497ef5bf90d06595964749a61"
    "bb58b50b96fb04ecbbb45b0594fb08eeb804085a95efb7fb0e5a98596560057587bdbc8bb7f50afa86098abfb4f9bff7edae06555967896c86890bbe"
    "b7f9bff4ed8a54ad5a6f0565ed568904596fad66ed06ad8a5867556d87bdbf08b6f58afbf999d201cb85fe9ffafd039bca9dd185d6ce97a6a5166aec"
    "fa01ffd3c99d9986d9f0080c364003325c0a6ff9cb4394f8db000ef234300940f9d199fecb85029f5c004f17742098a35c98170077a04c23d30ec580"
    "1e9ef0625c14984f77a00023c3e7064dc42bdfa1af6cdeeaf2fb7bfac861168b7b5781a05c4c039b772014a02eb56ce69817ba832eb9e7b498836e16"
    "8b060cc691f5cc1100e69a651fedc30288cec50590110ff688c6cd0d921107f48b0e06cc91f5c411b7937d259a881f514191d7b9bf996a1d4269b993"
    "bf1dd5993dd5fa06efc3211d42b96bd5bd1d919b3d2105d7ee1ff9c23d0523f9ee1fd5c23df9d622edc3051f41d5916bbd99ba1fc5dacdaddbf3ee74"
    "5e92daf43b99a8dec1897b0c0200e0605eda90aa3a99f4dfe57a4f69af2b8d8a4f2a934f70d0e6a40b1eb8d634f73b065caaf6933addda9801323963"
    "4fb1294f269bec0469204a174daf47befb9b240300e507cf3ed35ab4486a035d7aae65d0a8c4918b2801a8c06688ccb8564a7cdbb720ba84d10baff5"
    "67136c04d2a2ff6e7a78aae99cb52f1ed86401d7c0e1d3b31e259950cc20b9bd74467458e0f87108351705d5fd90791896cf6e2c27624264b794c079"
    "e2c6cc3d2f7bc1a46e3f0077749d6ef1b3db7187b641331d4ffbfc35946eddf1b37b718756b3e11c4f3bfd3574d191ee7367bd9bf63cbd01ef55533b"
    "36fd5c13efb5413bee922282e8363cba1274c73109e7bd4d9c3b699b83bd217d2e3ce292289ae2b63c89bb81837d3b7dd2f17d27a90d1447bc619b9b"
    "233d897d7cbb2189239d9b7d3c2c2d645f98289dbd8db747d1d87435dd474419f2ed3864a0ca1645a5dffbb6b882c87d2422d852c01ba54ae5d6b6bf"
    "fd58d9073244e46db56fdaa61ce61dffef1bc98f39edffddc1808e5d88ba4050db42c41a53f7dc1181cea040889a5d505bc4e21c53d7da1181bd804e"
    "48d0805afbdcda02d3514417dbfa5c04d3d14217709131c227c8894330c289d1876331481bf8fd75d7c27bb8d02962d187833148fb1dd87bd7e275b8"
    "9071d1c927288243dbfb157877f8dda2fbd5fb7d7718d8a226749f1e0268fbeec4eeb83880bf25c0705067b86c5e2d26e4d8ae2580bf38c0ab7a88d6"
    "bb9c4d9ea4b8e53820c08edf506d78b02c46673e8b8db6da5b7ea89c787b40b35d56e5a5f80e20d61dc003c5d6bd1d9bcbe469b5584573bbfd6540b6"
    "279e2d4ea235f93638d603c01de50ec04e259dba4dc58dc316fba99d6bd5dda49a1b3142d9b6ca643aa20a51d984db76617faa0229dd0c4cba2a825b"
    "d904d176616adf0c29bd024c1a91bb4ad936c264c1ac621f096c2a5da1c26c0a096c3f5da6df8c8b94ea044d52f98854984617cc64b6e7919634d6dd"
    "f2485957988614cc70757a4e1a1f595b9254f748184c99c624f67196d6bd87d410796e555a7b1a5fb1503ba4b4de52854b8a08a00dfec0eb22f8cde7"
    "039da6a0d132a4b05445bb9e9d7b85ffa266398e51bbd0b2b43e448582c627f8a3e00dbdf7917ff9dcae4ecd2f01e3bd8a0ba96b4bc1c683a90851e2"
    "c80c2cd8e760cdfd3667a03aa2eb210d57d4e146ade63459cb03d1864942a1e8682dd8ccc71dece028780dccc7ddece0f17db92b626e3aa0b16b7a39"
    "22e07dae9de4791ba70e5d6371baeb3d226079aefd99041da76e5b6371f97d3a62ae2ba01d7d9b0447e3b96e7d1bfd194783a46e79046e17272d5162"
    "7937110e4762246de67a447e5ba3f9383971770447022e6d66e4ba795b43fe38196e2411276d5762a659fe7afb78442346be7964fbf85a237a17733e"
    "39479eb37a5e1e33997337a733e1442a872f40a35a7e7e37991333a7f3242120874f4aa31a73573e39679eb344440d2c698ebdde532ae024472381af"
    "27090b75bfde711a07d5116b7f3aa91e87b8503e1b9a87c4c71135697f1aab1ea79098271b5a9ec4072bc971bf1e751a87479e389ba410da479ea730"
    "9b8418da0794935ad27a3ecf877a9e53320fd4dadb941db4f55da87a679e1a54328fd3da9bdd54a8f51db47a8713745ed29a3acf5b08d4b4b59afd7d"
    "1b5488bdb5daf47d9c611b3470d731d81cd4713b309861d72e14660874227d57dc11942130787bd70e26341d746268577c9bc131701734d82e7d2814"
    "741766426e281d067437744216f401da46dd3ccb0220dd8afb978fcb104fbbab0857155e221d808ffbd78acb76263bc26abf5f50c28a2f9d9b0be0d7"
    "50b50baf085e1b57b63f62c64a307b5f77814aa6ca82e2b2578682aaea72c1a2f430e69ed3e4fef7974266a1ea92caa2f66cdf0348ef1e20976a81a2"
    "ca42e6b2f4fefe90f337c6e4f4fe3e86f3f7d0e4f21c34daa899d084329a10d4c8e4bc99f7db0b295793905f9230fadcc804b499d5cb46baac840694"
    "12f49cd0a839da849710e93b97df4b539546daab0cd4a6842e327c671d7905416e67257c1d2112595a272d10539df1e36e6527721d211c593a4d8711"
    "533df0e32e3c72651d7907419a315007f3234dfd3a90310df34347fdc4b014869cf39a6c04e6ba949ccc9073b0dab711529e93f4e41ac6909cac9473"
    "d0b79a1352be91f4a4d4f09a9c13866c90b3b11a92d457feb091d31792b45afeea7bbeaeb365bdc8aa6e7dbeb3e8bbc59e25032155304da86abdeebb"
    "b368bec53e83252d551041a86afe7bbdb3a5aec83e0d8125552843b01e212d23558845b0d0cc222803cbaa7330c8ca22a3d30c6ba5dd2aa0dc4770df"
    "d02ac82ca3d3026bc5aa5db0dc2760dfd0c2cc2a032ba8734530a0bd7cdfcac72540d0aa7cbfddc7ece55dbcad57d03f4c5cf0bdcdffa537b74a24c8"
    "7a6b356b4c50fca5cdffbd3757a46ad57a2b286becfd45b0ad57dc3f7735a8ca3a4b646b376855c43aab6a6bcf940e582ef4ffcc0ff89f4eeecc34d4"
    "5278cb5f1ea2c4e7ef1fd854ee8c2ed4864760b0011a90c98fcef45f2e14f8cc76be342db55063b7067090a7814900da0278baa003c11ce5a2c07cba"
    "030518e165f35697dfdfd37fc2bc00b803651ae13e3768225ef90e1d621ad8bc03a100e5762806f4f084179b0eb358dcbb0a0445a96533c7bcd01d74"
    "30d72cfb681f1600346e6e908c38a047c93da7c51c74b370742e2e808c78b0479dec2bd144fc88ba3460308eac678e587430608eac278e588abccefd"
    "cd54eb08ca5dabeeed88dc142918c977ffa816ee4acb9dfceda8ce140929b876ffc817eeaa8e5cebcdd4fd08a9d637781f0ee9e8c9b716691f2ef8e8"
    "d66e6edd9e77a72bd28654d5c9a4fff652997c828336277d92d4a6dfc944f5f6d77b4a7b5d69542c52b59fd4e9d6c6e44edc63100000070bf0c0b5a6"
    "b9df315890c9197b8a4d790a283f78f699d6a205258e5c4409400546d96427480351ba30521be8d2732d834605d1258c5e78adbf7a3df2dddf241968"
    "4364c6b552e2db369b60239016fd773b28c9846206c9edf5b928a8ee87ccc3a8c3534de7ac7df1d033a2c302c78f43a0a504ce133766eeb9260bb806"
    "0e9f9ec57c766339111322b35dfe402ede76c289e777e2ce291dfaa3fa00413400ff1d6dff006d1d0041fa344b6837f5455da30f5d680fa345374bf5"
    "3768f54b450f5da30f68a35d45f5374bb8c21a59dc16f87116c271f8dc1ab8591ac259b8dc7116f884f590e3971c15e5d892f7b48b2216cb2292cb16"
    "8bf7d8b4f792b4d88bcb2216cb9216228bb4f7d835ebfe86de613be6d51c3e0e3500b358001c58b3353ed50e3e1c0ed5355800b3ff7ebdfbd67b228a"
    "7b7e8a22d6bdfffbbd7efbffd68a7b228a7e227bd6fbbdff98a9ff456c9dda0a9da90ada6cff9845ffa945986c0a9dda0497c693b970a79839646b36"
    "93f192a18a1a2bb045d6c6cdd61acdc6452b8ab02b1ab08a45cdd6c6fac2e023928d266b8dc26b2692e0fa23e0c223fa926b8d266bc2268d9223e0fa"
    "9f3b7d18d9bcea04bc3b04ead97d9f1897e26500c1935e8f93e28f5ec1659700745748b1d179ab5c79575cabd14874b14857b174d15c79ab5c57ab79"
    "d1b14874d0bc7476797e70767ebc76707974d07674bc76d079767e7076bc707e797674d09cdff1ad63adbb65addf65bb63f19cad8fafdbe2df13ddc2"
    "c21e8aa90f67fb947e245d332a7076f5c150242a53f62264f65064225324c12a24502ac15364f62286c93c849f24d1ff24c9ffd19f3c86843cc98486"
    "9fff24d11fea43a9b9efb144f364344275f6693ff6643f697534f342346442f3753ff6693f6469f6754234f3d21cf581ce882490881c9024cef5d281"
    "f51c81d2ce908824901c2488ce81f5d2ad1f84f7d60c22b30c1fb322d684adf7841ff7add6b30c22b31f220cd6f784ada1a9ff8a1e91420391a90342"
    "1effa18a292d27569a1c66ef1c2def669a272956e178f622e8a20ba0a278a00be8f6e122f67822e1e8a0a20ba0780ba2e822f6e1e806fd2810ffe5c7"
    "ff06c7e510fde8280be70a1e68e51e0de5e70d1e680a0b1ea5f874cb72ae0d72aef8720d7274a5cb74f8cba57272ae0d72f80dae72cb74a5e3b6a24d"
    "182b8d802bb6808d18a2e34da2b64de318802b8d80b68d2b184da2e3774c5d3155c0be5bc04c5bbe555d77315d4c3177555bc0be5b4cbec055315d77"
    "a4d9fa1d294ea8414ed941a829faa41dfad91da429414ea841d9a84e291dfaa471803830936e4fb6c6c16fe7dd116ccaa7070b033ab2d78bb2078bd7"
    "3a0ba7033719ebb0dffdf2dbfd19dbf2dfeb37b0eb19b037dfdbfdf29ac05ab3f6ad11934711b68ad7e8ea01e81101ead7b6478a777e6d9ac66d224d"
    "6d7e4d22c66d779aa76a2ae0b870500f706a0f50b82aa7e02a6ae0a7b80f70500f6a5070b8e02aa71b9e635e8384109d849e9d1083631b5e639e5e1b"
    "839d84109d9e1084835e631b7a15862c7b2a6d072a15076d7b867a2c86152c7a7b072a6d07156d2a7b2c867a99092a08e71697a41609a497e72a9908"
    "256358e95f443c304463303c5f5825e9574db93fdd7be4447b4d44e4ddb9573fb94d3f57dd447be4444de47bdd3fb9571b10af3f9481c02e81102ec0"
    "94af1b3faf103f1b942e81c02e10c081943faf1bd849dd6fe581217781497721e5ddd86fdd496fd8e577812177492181e56fddd8e9cb3541fc1252e6"
    "12cbe652fc35e941e88f3a0db8abf629ab8f29f6b83ae80df7158011ff19487419157448ff80f71192def7a50341f00941de09f003f792a5b9dbd230"
    "ed91d629c6e4909bd285647485e47464d290c69baa0c9631c7f4949bb1d33e98efcfd033cfd333d0ef3eb1983ed398b1ef33cfd033d3d0cfef983eb1"
    "dff6650717a13aeda1f6ed3a1765df0765f607df17eda13aedf63aa1170765df8db219bf7ef20802f2b202087e198dbf19b2bf8d7e02f20802b208f2"
    "7ebf198de3da50aa4a6cb05d6cda5db04a50e3aa50daaae34a5d6cb0efd24212f5b3dd006b1688f6bb8ab35c20f516eed73884246599fed9675c700d"
    "5c990d7067fe65d9cb987c08b08c94568c985694b07ccb08e8287400b8bea4e0be28e0a4b874e800675f0319fca9c1f6a95ff6c1fc036719035f1967"
    "fcf6a9c1f65fc1a9fc190367730e5708f8954d9a950e9a4df8577308570e0873f89a954d9a0e4d95f8085773e02cc078cb50bd0920215524c6b08786"
    "b0218687c65520247144bdde1fe1ecf79c429ee16dc73f91c742913f6d9e9ce19e42e19c6d91c73f91423fc76de19e9c133781600ec78875c7377588"
    "0e811360813760130e75c788753788c70e608113e0bde91ccdf494c3f4bdc394cde9e01ce9bd1ce0cdc3f494c3bd94f4cd1ce9e08c8d49e241229e53"
    "71fcaf317039b55739fc57b570af7131affc3171705739b5604cdac9f432e78a324c8ae7f4da60c9c942bca77cff056fff426f057cbcc9a7567f120a"
    "d0bb8896f7a55f7ce2f5dc3884d56fe5573fbba63fd5a6bb576f84e5d32e7081e11251cb122ecb51e170d38192db5deb651e7db41edbb47d655d92eb"
    "c28cbd4a715981bf598cbf8171bdc24abd8c4ac271bf5981ee6df18af0d8669fc4a4c57c89e637a6e6a4a63789c5c47c307844405cc90360c9786003"
    "5c443040a7bfb6532f431ac343bfc31a2fb6a75368c9912ec8b4a1d4b4c9d4a1c891682eda8e8961f960ef6f608e6feff989da6166e1015496809966"
    "80e16699960166540c3e40312db8c700b83e00c72d400c31b95ede634d8ed7288e5e28d74ddeb9638540fa1c1d40cb82404082cb1dfa851c3cd3a5f5"
    "ba1a79af1ad3af79baa53cf536e44604f152449c658c690fb4496ba77c8c1433b4753dbc6374cd2b766584ef4db077471679b8c2b466d875d03266cd"
    "bcefac9fb037db156a1155f56eda7e1637ae0f51188f88808fae8088180f37513baeae2a757f8fe5d8fd8d46e480f39e98b35333ac69e866a23126a8"
    "2e9885c953135b4e38ad55701d64374341e391fa6fd0ea978a1eba46cfefc49d533af447bbd01e468b6e96ea1ed046bb8aea6f9696d06eea8bba461f"
    "bbfc815cbced8413fe01da3a0082f469f401826800fe3bdaee2569b11797452c2c84e3f0b93570b34524972d16efb16997252d441669efb1b125ef69"
    "17452c96708535b2b82df0e309eb21c72f392aca3584b370b9e32cf07afdf6ffad15f744aa397c1c6a0066b1f7fc1445ac7bfff715fd44f6acf77bff"
    "fffd7af7adf744146bd6fd0dbdc376cc7d381caa6bb000660038b0666b7caa1dad359a8d8b5614613a5315b4d9fe318b153556608bac8d9b57346015"
    "8b9aad8d73c8d66c26e325433053ff8bd83ab515092e8d2773e14e31ff538b30d9143ab52fc5cb008227bd1e1a85d74c24c1f547787708d4b3fb3e31"
    "26c51fbd82cb2e013e77fa30b279d509f485c147241b4dd6d7844d1a2547c0f5c08547f425d71a4de878eda0f3ecfce0f3aeb856a391e862fc78ede0"
    "f2e8a0eded78e1fcf2ece8a0a079e9ecf2fce0ece8ae9062a3f356b9b8ae56f3a26391e891ae62e9a2b9f256eca1c844a64882555bbfcb76c7e2395b"
    "82a14854a6ec45c848a05482a7c8ec45fd48ba6654e0ecea38bfe35bc75a77cb853d14531fcef6291f5fb7c5bf27ba8568c884e6eb7eecd34992ffa3"
    "3f790c09ecc97ed2ea68e6857fc8d2eceb8468e6e6c96884eaecd37e0d9379083f49a2ff3ed4875273df63897992090d3fff49a2083fee5bad671944"
    "113920499ceba503193e6645ac095bef673f4418acef095b5b3f08efad194466a539ea039d114920213948109d03eba5ea3902a59d211149ecf144c2"
    "d1414517235307843cfe431544f14017d0edc34541f11644d145ecc3c3f1ec45d04517404253ff153d228506385adecd344f52ac535a4eac3439ccde"
    "e8f0974be5e45c1bfe0d8ecb21fad1515df1e51ae4e84a97e5f01b5ce596e94a4af1e996e55c1be4d10dfa5120fecb8fcacf1b3cd014163c16ce153c"
    "d0ca3d1abb9862eeaab6807d566c011b3144c79b8099b67cabbaee62b6987c81ab62baeeee98ba62aa807db7c76d459b30561a01016d1b57309a44c7"
    "456d9bc63100571a4f0f16067464af179cb2835053f4493b8d83dfcebb23d894640f16af75164e07e300716026dd9e6c48b3f53b529c508383b2519d"
    "523af449f5b33b4853829c50eefcda348ddb449afb33b6e5bfd76f60d12302d4af6d8f14dbfc9a448cdbee348e226c15afd1d5036f32d661bffbe5b7"
    "3581b566ed5b2326d733606fbeb7fbe5c63cbd36063b0921e1d41ea070554ec1083d3b2106c736bc3a3d210807bdc636373cc7bc0609213a4ed554c0"
    "71e1a01e1fd4a0e070c1554e54d4c04f711fe0a04ac6b0d2bf887860542a0edaf60cf5582c12482fcf55321189c66078beb04ad233135410ce2d2e49"
    "f42a0c59f654da0e0e2ada54f6580cf50c2b58f4f60e54da5f217e36285d0281f69a88c8bb73af7e02215c80295f377e5c208003297f5e3736205e7f"
    "2803815dae9a727fbaf7c889889ac8f7ba7f72af739b7eaeba89f6c8d01f751a7057ed530293ee42cabbb1df2496cda5f86bd283561f53ec7175d01b"
    "d3976b82f825a4ccb093badfca0343eeef924202cbdfbab1ba93deb0cbef02430bc9e9c8a4218d37322ae890fe01ef238cc92137a50bc9e855192c63"
    "8ee9293772b7a561da23ad53ee2b0023fe3390e883bc13e007ee254b24bdef4b0782e013caec0fbe2fda43759fa767a0df7d623142eddb752ecabe0f"
    "dbed75422f0ecabebfedcb0e2e4275da62a77d30df9fa16767a6a19fdf317d627da63163df679ea1a1b455c795bad860e5650510fc321a7fd9b4bb60"
    "95a0c655dea58524ea67bb01c6b5a15495d860bb1a65337efde41104056411e4fd7e331a32647f1bfd04e411d151e800707d49c140ea2ddcaf710849"
    "1831ad2861f996117c51c04971e9d0019631f910601929add62c10ed771567b9b9321be0cefccbb2ca32fdb3cfb8e01aae1c10e6f0352b9b52bfec83"
    "f907ce322a1d349bf0afe610341d9a2af111aee6e71cae10f02b9b34cfbe0632f85383edecbf8253f93306ce07be32cef8ed53833c85c239db228f7f"
    "4142aa488c610f0d8f85227fda3c39c323857e8edbc23d3939853cc3db8e7f22c05980f196a17a13e3887abd3fc2d9ef60430c0f8dab4048d37b39c0"
    "9b87e9298e6fea101d0227c0e87b87299bd3c139877b29e99b39d2c1c17bd3399ae92987266e02c11c8e11ebea6e108f1dc00227036fc0261cea8e11"
    "9285784ff9fe0bdee2f85f63e0726aaf659814cfe9b5c192ff85de0af878934fc198b493e965ce15181b93c483443ca75ff963e2e0ae726a72f8af6a"
    "e15ee36225b7bbd6cb3cfa68ee4bbff8c4ebb971255c96a3c2e1a6033db669fbcaba24d7a75de002c325a296adfe2414a077112d7faa4d77afde08cb"
    "09abdfcaaf7e764d60f08880b89207c0b2187f03e37a8595cc494d6f128b89f992f1c006b888608089498bf912cd6f4c85197b95e2b2027fdddbe215"
    "e1b1cd3e7b199584e37eb302ccc203a82c0133cd867e87355e6c4fa7c01cdfdef313b5c300c3cd322d03cca8b41d13c3f2c1dedf4f7f6da75e863486"
    "6893a9439123d15cd192235d906943a979a64beb7535f25e707d008e5b801862808004973bf40b3935a65ff3744b79ea0b81f4393a809605187c8062"
    "5a708f011cbd50ae9bbc73c772bdbcc79a1caf5178df593f616fb62bcb18d31e6893d64e69cdb0eba065cc9ad422aaeaddb4fd2c9b60ef8e2cf27085"
    "6dc88d08e2a58838c7e89a57ecca08dff918296668eb7a78a626b69c705aabe01e5d0111311e6ea245634c505d300b933bc86e8682c623f53067a766"
    "58d3d0cd6f5c1fa2301e1101b1fb1b8dc801e73d775c5d55eafe1ecbfc03b4750004e9d39edf893ba774e88f76f903b978db0927e90304d100fc77b4"
    "2ca1ddd417758d3edea0d52f153d748d3da08d7615d5df2c77a13d8c16dd2cd513d6438e5f7254945908c7e1736be066e10a6b64715be0c76b0867e1"
    "72c759e0634bded32e8a582cdc4bd2622f2e8b582f4b5a882cd2de638a482e5b2cde63d3fa703854d76001cc5573f838d400cc62d7acfb1b7a87ed98"
    "007060cdd6f8543bfefbf5ee5bef8928f4faedff5b2bee892bfa89ec59eff7feeff9298a58f7feef125c1a4fe6c29d6275a62a68b3fd631660a6fe17"
    "b1756a2bffa71661b229746ae690add94cc64b865a6b341b17ad28c2af68c02a16355b1b2b6aacc016591b37af099b344a8e80eb340aaf994882eb8f"
    "e90b838f48369aac800b8fe84bae359a7ceef46164f3aa135e8a9701044f7a3d4c8a3f7a05975d02f0ee10a867f77d62715dade645c722d1e65d71ad"
    "4623d1c5d15d21c546e7ad72225dc5d24573e5ad41f3d2d9e5f9c1d9d1f1da41e7d9f9c1dbf1c2f9e5d9d141f9f1dac1e5d141db0a7b28a63e9ced53"
    "b67e97ed8ec573b6717ec7b78eb5ee963fbe6e8b7f4f740bfb9174cda8c0d9d5d84391894c9104ab9040a9044f91d98b054391a84cd98b907da80fa5"
    "e6bec7129224ff477ff218121b26f3107e9244fff324131a7efe9344cc93d108d5d9a7fdd19009cdd7fdd8a7ff90a5d9d709d1ccd993fda4d5d1cc0b"
    "437290203a07d64b2272409238d74b074a73d4073a239240d473044a3b432292b67e10de5b3388cc107edcb75acf3288ce7e883058df13b6337ccc8a"
    "5813b6de71b4bc9b699ea45846a60e0879fc872a84a6fe2b7a440a0da7b49c58697298bd86e3d98ba08b2e80d8e38984a3838a2e83e22d88a28bd887"
    "88e2812ea0db878b949f3778a0292c78fc1b1c9743f4a3a3a31bf4a340fc971f2c9c2b78a0957b3495e2d32dcbb936c8d0e12f97cac9b936cae137b8"
    "ca2dd395bbe2cb35c8d1952e03da36ae6034898eadd8023662888e378edb8a3661ac34028ada368d6300ae34dd3175c55401fb6e7631c5dc556d01fb"
    "6d31f90257c574dd00336df95675ddc50665a33aa574e893386507a1a6e893769166eb77a438a106ea677790a60439a1c601e2c04cba3dd99e1e2c0c"
    "e8c85e2fc81e2c5eeb2c9c0e1b07bf9d7747b0296a026bcddab7464cf6676ccb7fafdfc0df64acc37ef7cb6faf67c0de7c6ff7cb1c45d82a5ea3ab07"
    "ddf9b5691ab78934b6f9358918b7dd69a24704a85fdb1e293ea841c1e182ab9cc3a93d40e1aa9c829caaa980e3c2413da9a8819fe23ec0416e788e79"
    "0d1242748c797a6d0c761242747a42100e7a8d6d117a76420c8e6d781d54b4a9ecb118eaa8541cb4ed19eab1e85518b2eca9b41d1956b0e8ed1da8b4"
    "6626a8209c5b5c92948c61a57f11f1c0138dc1f07c6195a45824905e9eab6422113591ef75ffe45eec35119177e75efd5d35e5fe74ef9113e736fd5c"
    "7513ed916c40bcfe500602bbbf42fc6c50ba0402b840000752febc6e0442b80053be6efcdf25850496bf75630526dd85947763bf612775bf950786dc"
    "7427bd6197df0586a72fd704f14b4899a03fea34e0aedaa7ac3ea6d8e3eaa037492c9b4bf1d7a407067927c00fdc4b966454d021fd03de47dd570046"
    "fc6720d1487adf970e04c127e46e4bc3b4475aa71692d39149431a6faa3258c61cd3536e1993436e4a1792d1ce4c433fbf63fac43e4fcf40bffbc462"
    "c44efb60be3f43cffb4c63c6becf3c437fdb971d5c84eab494d91f7c5fb487eab7dbeb845e1c947d84dab7eb5c947d1f0ac822c8fbfd6634cacb0a20"
    "f86534fe34ca66fcfac9230864c8fe36fa09c8238d6b43a92ab1c1764269ab8e2b75b1c1bc4b0b49d4cf7603b26977c12a418dab736536c09df99765"
    "80d45bb85fe31092ad5920daef2ace729465fa679f71c1352d63f221c032525aa3a3d001e0fa9282f8a28093e2d2a10330625a51c2f22d23d97f05a7"
    "f2670c9ca47ed907f30f9c659f7d0d64f0a706db0f7c659cf1dba706ce395c21e05736695d3920cce16b5636693a3455e2235ccd543a6836e15fcd21"
    "c711f57a7f84b3df8284549118c31e1a80b300e32d43f526c086181e1a578190720a7986b71dff44780a8573b6451eff460afd1cb7857b721f0b45fe"
    "b4797286d4dd201e3b80054e1ddfd4213a044e804ddc0482391c23d606de804d38d41d2383f7a67334d3530ea6f77280370fd3530ff752d23773a483"
    "d0f70e5336a78373bef2c7c4c15de5d4c5f1bfc6c0e5d45e313626890789784ee4f05fd5c2bdc6c582316927d3cb9c2b250bf19ef2fd17bcfe0bbd15"
    "f0f1269fcb30299ed36b8325ff549bee5ebd1196dc977ef189d773e35afd492840ef225a1256bf955ffdec9a4fbbc005864b442d4a6e77ad9779f4d1"
    "7b6cd3f6957549ae4ab82c4785c34d07bab7c52bc2639b7d6531fe06c6f50a2b0a33f62ac56505fef6322a09c7fd6605129316f3259adf98c1e01101"
    "71250f8025e3810d7011c10099939ade241613f3d02653872247a2b90dfd0e6bbcd89e4e9ffeda4ebd0c690ca32547ba20d38652693b2686e583bdbf"
    "998507505902669a01869b655a0698518139bebde7276a87397aa15c3779e78ee0fa001cb70031c430f800c5b4e01e03e47a798f35395ea31602e973"
    "74002d0bf24c97d6eb6ae4bd6b4cbfe6e996f2d40001092e77e817728fd135afd89511be9631a63dd026ad9dda901b11c44b1171f23152ccd0d6f5f0"
    "37c1de1d59e4e10af0beb37ec2de6c57a84554d5bb69fb59d39a61d741cb983562f7371a9103ce7b3dba0222623cdc44deb83e44613c2202efb8baaa"
    "d4fd3d9661ce4ecdb0a6a19b4d4d6c39e1b456c17790dd0c058d47ea8bc698a0ba6016267a401bed2aaabf593dbf13774ee9d01fbd41ab5f2a7ae81a"
    "ef427b182dba59aa5842bba92fea1a7df90768eb0008d2a7d30708a201f8ef68ecf20772f1b6134e5e96b41059a4bdc7b2108ec3e7d6c0cdb897a4c5"
    "5e5c16b115915cb658bcc7a6c696bca75d14b15827ac871cbfe4a828d710cec2e58eb3c0c315d6c8e2b6c08f57f413d9b3deeffdaae6f071a80198c5"
    "e9f5dbffb756dc13dff35314b1eefddffcf7ebddb7de1351f5e170a8aec1029800e0c09aadf1a976af59f737f40edb315ed180552c6ab636ea4c55d0"
    "66fbc72cb5d668362e5a518456d458812db2366ecd215bb3998c970c24b8349ecc853bc5fe4f2dc26453e8d4c04cfd2f62ebd45698147ff40a2ebb04"
    "69145e339104d71fbc142f03089ef47ae0dd2150cfeefbc4f8dce9c3c8e655275f133669941c01d701171ed1975c6b34d317061f916c3459b6e385f3"
    "cbb3a383cdbbe25a8d46a28ba3e3b583ceb3f383f3e3b583cba383b683e6a5b3cbf383b3e3ba5acd8b8e45a245ba8aa58be6ca5ba2bb428a8dce5be5"
    "218152099e22b3176dfd2edb1d8be76cb1872213992209560b86225199b21721f723e99a5181b3ab14f6504c7d38dba77e7cdd16ff9ee816e3fc8e6f"
    "1d6bdd2dff214bb3af13a2992449fe8ffee43124a321139aaffbb14fb227fb49aba399179927a311aab34ffbfa501f4acd7d8f25e6492634fcfc2789"
    "374ce621fc2489fe9dfd1061b0be276c44e4802471ae970e21fcb86fb59e651067f89815b1266cbd6dfd20bcb766109986e42041740eac97a9e70894"
    "7686442494e6a80f7446248107c55b104517b10f8c4c1d10f2f80f55b0c713094707155d11c5035d40b70f170dc7b31741175d00e2687937d33c49b1"
    "4f6939b1d2e4307b084dfd57f488141a95c36f70955ba62bf937382e87e84747a0c35f2e9593736d76c5976b90a32b5d2bc5a75b96736d90283f6ff0"
    "405358f0583857f0402bf7684637e84781f82f3fdb62f205ae8ae9ba5ab1056cc4101d6fed628ab9abda02f60166daf2adeaba8bba63ea8aa902f6dd"
    "07b46d5cc168121d14b56d1ac7005c691cb7156dc2586904903d58bcd659381d70ca0e424dd127ed3c3d5818d091bd5e360e7e3bef8e60538d03c481"
    "99747bb20dca46754ae9d027d5cfee204d09724222cdd6ef4871420d6cf36b12316ebbd3edcfd896ff5ebf81baf36bd3346e1369448f0850bfb63d52"
    "388ab055bc46570fd404d69ab56f8d985fcf80bdf9deee97bec95887fdee97dfe8f484201cf41adb87537b80c255390518f3f4da18ec248422f4ec84"
    "181cdbf0dcf01cf31a2484e87d508382c30557395251033fc57d808338555301c785837a271a83e1f9c22a4951a93868db33d4632919c34aff22e281"
    "b04820bd3c57c944cd4c504138b7b8243ba86853d96331d433ac60d1db3b5069d0ab3064d953693b7081000ea4fc79ddd96b2222efcebdfa7e85f8d9"
    "a074090409847001a67cddf8d98078fda10c0476226a22dfebfec9bdcf6dfab9ea26da23ba6acafde9de2327587d4cb1c7d5416f0b4cba0b29efc67e"
    "417fd469c05db54f92583697e2af490f4f5fae09e2979032be4b0a092c7febc6e94e7ac32ebf0b0cc34eea7e2b0f0cb95465b08c39a6a7dcc8a8a043"
    "fa07bc8f2c24a723938634de332687dc942e24a3c9dd9686698fb44e0df24e801fb8972c90f4be2f1d08824fbbaf008cf8cf40a26eb7d709bd3828fb"
    "7c9e9e817ef789c529b33ff8be680fd508b56fd7b928fb3effb62f3bb808d5699d99867e7ec7f489f699c68c7d9f7986899df6c17c7f869e78971692"
    "a89fed0695971540f0cb68fc85d2561d57ea628365d3ee8255821a571ad78652556283ed14904590f7fbcd68c890fd6df41390476894cdf8f5934710"
    "f0450127c5a5430701a9b770bfc621244747a103c0f5250560c4b4a284e55b465ac6e4438065a4b4e6ca6c803bf32fcb28cbf4cf3ee3826b5ab340b4"
    "df559ce5d37468aac447b89a48fdb20fe61f38cbba724098c3d7ac6ca874d06cc2bf9a439c73b842c0af6cd2b3ff0a4ee5cf18381ef8ca38e3b74f0d"
    "3ffb1ac8e04f0db68c14fa396e0bf7e40409a92231863d34f1140ae76c8b3cfe3f168afc69f3e40ce414f20c6f3bfe898f23eaf5fe0867bf810d313c"
    "34ae0221006701c65b86ea4d1feea5a46fe648073bbea94374089c004cefe5006f1ea6a7a0ef1da66c4e07e706ef4de768a6a71ca8bb413c76000b9c"
    "0cbc019b70a83b469bb80904733846acfd177a2be0e34d3e8ae37f8d81cba9bd4b16e23de5fb2f789661523ca7d7064b0463d24ea69739577de58f89"
    "83bbcaa9c9e1bfaa857b8d8b626c4c120f12f19cf7d8a6ed2beb925cb92ffde213afe7c695dcee5a2ff3e8a39470598e0a879b0e9e76810b0c97885a"
    "ffa936ddbd7a232c25ac7e2bbffad935b4fa935080de45b44ac6031be0228201ca62fc0d8ceb155683c12302e24a1e00332735bd492c26e625262de6"
    "4b34bf31746f8b5784c736fbec6554128efbcd0a1566ec558acb0afc020c37cbb40c30a31afa1dd678b13d9d330b0fa0b204cc3403737c7bcf4fd40e"
    "d3764c0ccb077b7fa14da60e458e4473464b8e7441a60da53efdb59d7a19d218d7987ecdd32de5a9c1f501386e016288e5992eadd7d5c87b0002125c"
    "eed02fe42c04d2e7e8005a1673f442b96ef2ce1dc9f5f21e6b72bc4660f0018a69c13d06508ba8aa77d3f6b32d634c7ba04d5a3be07d67fd84bdd9ae"
    "a635c3ae8396316b6e82bd3bb2c8c3151fa36b5eb12b237ce563a498a1adebe1b4213722889722e2ef20bb190a1a8fd47a740544c478b8899b9ad872"
    "c269ad82168d314175c12c4cc39c9d9a614d4337c4ee6f3422079cf7df717555a9fb7b2cbc717d88c2784404a60f104403f0dfd17a7e27ee9cd2a13f"
    "f30fd0d60110a44fd8e50fe4e26d279cb08476535fd435faf48036da55547fb3df85f6305a74b3547a8356bf54f4d035af219c85cb1d678165211c87"
    "cfad819b4e580f397ec95151872bac91c56d811f8c2d794fbb2862b1bd2c6921b2487b8f2b22b96cb1788f4d712f498bbdb82c6200c081355be353ed"
    "55cde1e35003308bebc3e1505d8305305eb3ee6fe81db663f8efd7bb6fbd27a2afe827b267bddffbbfe7a72862ddfbbfd2ebb7ff6fadb827fd9f5a84"
    "c9a6d0a9d499aaa0cdf68f594970693c990b778a8099fa5fc4d6a9ad9a43b66633192f19bca201ab58d46c6daca8b1025b646ddc6badd16c5cb4a208"
    "022e3ca22fb9d668d228bc662209ae3fbf266cd2283902aea62f0c3e22d968b2f0b9d38791cdab4e3029fee8155c7609c1bb43a09eddf78978295e06"
    "103ce9f58a74154b17cd95b79b77c5b51a8d4417c775b59a171d8b44457785141b9db7ca07cd4b6797e707676dc70be797674707e7c76b079747076d"
    "47c76b079d67e707fcf8ba2dfe3dd12ddafa5db63b16cfd929eca198fa70b64fc6f91ddf3ad6ba5bef47d235a30267574202a5123c45662f160c45a2"
    "32652f42620f4526324512accd934c68f8f94f124892fc1ffdc96348f4a13e949afb1e4b6f98cc43f84912fd334f462354679ff6ff4396665f274433"
    "644ff6935647332f464326345ff7639f52cf1128ed0c894888c80149e25c2f1d0dc94182e81c582f29cd511fe88c4802dbfa41786fcd20323afb21c2"
    "607d4fd8cff0312b624dd87a42f871df6a3dcb209ed27262a5c961f618993a20e4f11faac5d1f26ea6799262109afaafe81129341a8e672f822eba00"
    "0e8ab7208a2e621f228a07ba806e1f2e608f27128e0e2abab070aee08156eed1f26f705c0ed18f8e517edee081a6b0e08c6ed08f02f15f7e578a4fb7"
    "2ce7da202a87dfe02ab74c57ec8a2fd7204757ba4087bf5c2a27e7da286adb348e01b8d2b4620bd888213ade0e68dbb882d1243a386e2bda84b1d208"
    "75c7d4155305ecbbb7c5e40b5c15d37503ccb4e55bd57517dbc5147357b505ecaa9fdd419a12e484e1941d849aa24fda1a948dea94d2a14f449aaddf"
    "91e2841a1b07880333e9f664207bb078adb3703a6c1cfc76de1dc1a6787ab030a0237bbdbf9e017bf3bddd2fdb9fb12dffbd7e03a909ac356bdf1a31"
    "7d93b10efbdd2fbf701461ab788dae1ed9e6d72462dc76a7881e11a07e6d7ba474e7d7a669dc26d2a5a2067e8afb00070ea7f60085ab720afaa00605"
    "870bae7270aaa6028e0b07f5b9e139e6354808d1d1e9094138e835b645e8d9093138b6e131e6e9b531d849086658c1a2b777a0d2a25271d0b667a8c7"
    "7750d1a6b2c762a8a05761c8b2a7d2769a99a082706e71494e3406c3f38555926091407a79ae928953328695fe45c4039edbf473d54db447b3d74444"
    "de9d7bf545d444bed7fd937b74d594fbd3bd474eb201f1fa431908ece102011c48f9f3ba1308e1024cf9baf1fc0af1b341e91208d29df4865d7e1718"
    "1698741752de8dfd7d97141258fed68d879dd4fd561e18729ebe5c13c42f2165b0fa98628fab83de24b16c2ec55f931e82fea8d380bb6a9f20e97d5f"
    "3a10049f91514187f40f781f1ae49d003f702f59775f0118f19f814492bb2d0dd31e699da9ca6019734c4fb9674c0eb9295d484659484e47260d69bc"
    "ed338d19fb3ef30cf93c3d03fdee138b3b330dfdfc8ee913133bed83f9fe0c3dfe6d5f767011aad3dd6eaf137a7150f6106adfae7351f67d53667ff0"
    "7dd11eaa9021fbdbe827208f2b2f2b80e097d1f828208b20eff79bd1d0289bf1eb278f2035ae0da5aac406dbf02e2d24513fdb0dcaa6dd05ab0435ae"
    "0ba5ad3aaed4c5065096e99f7dc605d702526fe17e8d4348cd95d90077e65f96b5668168bfab38cbb58cc98700cb4869e08b024e8a4b870ec0886945"
    "09cbb78c8e8e420780eb4b0a3cf09571c66f9f1a91fa651fcc3f709666ff159cca9f31707ff63590c19f1a6c39e77085805fd9a4a7e9d054898f7035"
    "50e9a0d9847f358774e5803087af59d9021b6278685c054208125245620c7b681f47d4ebfd11ce7e00ce028cb70cd59bc929e419de76fc131929f473"
    "dc16eec97e2c14f9d3e6c919e32914ced91679fc18780336e150778c767c5387e810380151778378ec00163837711308e6708c580cde9bced14c4f39"
    "3edc4b49dfcc910e41df3b4cd99c0ece99decb01de3c4c4f93c37f550bf71a1715c7ff1a0397537bfbca1f1307779553c5d898241e24e23908c6a49d"
    "4c2f73aefa2ff456c0c79b7c2cc3a4784eaf0d96962cc47bcaf75ff04a58fd567ef5b36b735ffac5275ecf8dfe536dba7bf5465869f527a100bd8b68"
    "3ced0217182e11b5eeb14ddb57d625b928e1b21c150e371d2bb9ddb55ee6d147d8cba8241cf79b1594c5f81b18d72bace9de16af088f6df62bccd8ab"
    "149715f84a4c5acc97687e63948c0736c0450403674e6a7a93584ccc06834704c4953c008d961ce9824c1b4a35f43bacf1627b3a429b4c1d8a1c89e6"
    "7cfa6b3bf532a431a6ed9818960ff6fe05186e966919604606e6f8f69e9fa81d66161e406509986992ebe53dd6e4788d83eb0370dc02c410e6e88572"
    "dde49d3bc0e00314d3827b0c5808a4cfd101b42caf31fd9aa75bca53010424b8dca15fc8ca335d5aafab91f7cbc74831435bd7c35ac698f6409bb476"
    "3e46d7bc625746f869436e44102f45c4dc047b776491872ba1165155efa6ed674c6b865d072d63d6c1fbcefa097bb35dbee3eaaa52f7f758f5e80a88"
    "88f1701389dddf68440e38ef78e3fa1085f1880886393b35c39a866edf41763314341ea92c1a6382ea8259983735b1e584d35a05be0bed61b4e866a9"
    "f4fc4edc39a5437fe9016db4aba8fe66f406ad7ea9e8a16b6109eda6bea86bf44d1f208806e0bfa3b1cb1fc8c5db4e38e61fa0ad0320489f564472d9"
    "62f11e9bcb42380e9f5b03377b59d2426491f61ee25e92167b7159c4195bf29e7651c4625f43380b973bce020e5758238bdb023f9cb01e72fc92a3a2"
    "7fcf4f51c4baf77fab9ac3c7a10660165fd14f64cf7abff7a4d76fffdf5a714ff1dfaf77df7a4f440180036bb6c6a7dabc66dddfd03b6cc7d687c3a1"
    "ba060b6059516305b6c8dab8a83355419bed1fb378450356b1a8d9dad65aa3d9b868451134876ccd66325e32fb3fb508934da1530133f5bf88ad535b"
    "93e0d2783217ee14837787403dbbef13a45178cd44125c7f6052fcd12bb8ec12f152bc0c2078d2ebe073a70f239b579d045c78445f72add14d5f187c"
    "44b2d1647f4dd8a45172045cce8fd70e2e8f0eda36ef8a6b351a892eda8e17ce2fcf8e0e8e8ed70e3acfce0f0e9a97ce2ecf0fce15e92a962e9a2b6f"
    "8bee0a29363a6f958eeb6a352f3a16892c188a4465ca5e84b5f5bb6c772c9eb384044a25788acc5ec51e8a4c648a2458de8fa46b4605ceaef8f1755b"
    "fc7ba25b8cf33bbe75ac75b752d84331f5e16c9fc89eec27ad8e665e9024f93ffa93c790fe872ccdbe4e88668d864c68beeec73e679e8c46a8ce3eed"
    "9a2799d0f0f39f24df309987f09324fae8437d2835f73d969ee16356c49ab0f510910392c4b95e3a75f64384c1fa9eb084f0e3bed57a9641b6f583f0"
    "de9a4164a49e2350da191291529aa33ed01991041a928304d139b05e44140f7401dd3e5c31327540c8e33f541c146f41145dc43ec11e4f241c1d5474"
    "341ccf5e045d74013da5e5c44a93c3ec2034f55fd12352688aa3e5dd4cf324c5d9155fae418eae74e5dfe0b81ca21f1d540ebfc1556e99ae810e7fb9"
    "544eceb5ae149f6e59ceb54161e15cc103addca318dda01f05e2bffca3fcbcc1034d61c1069869cbb7aaeb2e69c516b0114374bc6e8bc917b82aa6eb"
    "b78b29e6ae6a0bd8eb8ea92ba60ad87751d4b6691c0370a570dc56b40963a5111cd0b67105a34974d938f8edbc3b824dc3293b0835459fb440f660f1"
    "5a67e174f1f460614047f67a360e100766d2edc9553fbb833425c80988345bbf23c5093534281bd529a5439f113d2240fddaf648b63f635bfe7bfd06"
    "b3cdaf49c4b8ed4ee9ceaf4dd3b84da4e028c256f11a5d3d7e3d03f6e67bbb5ffb26631df6bb5f7e5213586bd6be35628bd0b31362706cc31c4eed01"
    "0a57e514a3d3138270d06b6c62ccd36b63b0931073c373cc6b9010a24a450dfc14f7010ee1544d051c170eeaf4410d0a0e175ce5c12281f4f25c2513"
    "45a5e2a06dcf508f9d680c86e70bab24a6640c2bfd8b880734334105e1dce292cdb082456fef40a540afc290654fa5edefa0a24d658fc5502710c205"
    "98f275e367af8988bc3bf7eac305023890f2e775f815e26783d225106503e2f5873210d83cb7e9e7aa9b688fe8aa29f7a77b8f9c8aa8897caffb27f7"
    "4862d95c8abf263d2d30e92ea4bc1bfb61f531c51e5707bd05fd51a70177d53e3c7db926885f42caa43be90dbbfc2e300e3ba9fbad3c30e4fb2e2924"
    "b0fcad1bce981c7253ba908c22a3820ee91ff03e5395c132e6989e72b3909c8e4c1ad27825775b1aa63dd23a41d2fbbe7420083eeebe0230e23f0389"
    "34c83b017ee05eb220d4be5de7a2ecfbf3797a06fadd2716bbdd5e27f4e2a0eca7ccfee0fba23d54fddbbeece02254a7da671a33f67de6192676da07"
    "f3fd197a76661afaf91dd327954dbb0b56096a5c575e5600c12fa3f1e05d5a48a27eb61b164a5b755ca98b0d6b5c1b4a55890db62143f6b7d14f401e"
    "a05136e3d74f1e4151401641deef37a38111d38a12966f1904a4dec2fd1a8790c017059c14970e1d1c1d850e00d797146a19930f019691d2a12cd33f"
    "fb8c0bae6bcd02d17e5771969b2bb301eeccbf2ca1d241b309ff6a0e23f5cb3e987fe02c4ed3a1a9121fe16ae9ca01610e5fb3b273cee10a01bfb249"
    "78e02be38cdf3e35feec6b20833f35d8ccfe2b38953f63e0fc5828f2a7cd93331024a48ac418f6d03352e8e7b82ddc93c753289cb32df2f89253c833"
    "bcedf8270436c4f0d0b80a84019c05186f19aa373e8ea8d7fb239cfd83be7798b2391d9cecf8a60ed12170027cb89792be99231d32bd9703bc79989e"
    "18bc379da3999e7231f0066cc2a1ee186ee22610cce118b1a2ee06f1d8012c70598649f19c5e1b2c2a8eff35062ea7f6f45fe8ad808f37f92d5988f7"
    "94efbfe0118c493b995ee65c2687ffaa16ee352e8ab131493c48c473f6953f260eee2aa750c265392a1c6e3ae7bef48b4fbc9e1bdd639bb6afac4b72"
    "5672bb6bbdcca38f79da052e305c226a94b0faadfcea67d7d2ea4f42017a17d1fca7da74f7ea8db0cf9cd4f426b19898298bf13730ae575828190f6c"
    "808b08060c068f08882b79009498b4982fd1fcc6b097514938ee372b5798b157292e2bf0d3bd2d5e111edbec0cccf1ed3d3f513b6ae87758e3c5f674"
    "0a30dc2cd332c08ccc2c3c80ca1230d34ddb31312c1fecfd1a2d39d205993694f8f4d776ea6548638536993a143912cd03084870b943bf9006d707e0"
    "b80588215e63fa354fb794a79567bab45e5723efb010489fa303685925d7cb7bacc9f11a80c10728a605f718ccd10be5bac93b7799d60cbb0e5ac6ac"
    "b48c31ed813669ed422da2aade4ddbcf82f79df513f666bbb809f6eec8220f57978f916286b6ae87d386dc88205e8a887d8cae79c5ae8cf05934c604"
    "d505b330ead1151011e3e126bf83ec6628683c526e6a62cb09a7b50a0c73766a86350ddd7cc7d555a5eeefb1f0c6f5210ae3111113bbbfd1881c70de"
    "62973f908bb79d70e8f99db8734a87fe9b3e40100dc07f47cd3f405b0740903ec312da4d7d51d7e87d17dac368d1cd52e80d5afd52d143d7d203da68"
    "5751fdcd1caeb04616b7057e9685701c3eb7066ebe8670162e779c0539613de4f825474532b6e43deda288c5ad88e4b2c5e23d36c5bd242df6e2b288"
    "f6b2a485c822ed3d79cdbabfa177d88e5635878f430dc02c030007d66c8d4fb5ac0f8743750d16c0e2bf5fefbef59e88fe9e9fa28875efff48afdffe"
    "bfb5e29ebfa29fc89ef57eef0266ea7f115ba7b65167aa8236db3f66f67f6a11269b42a726c1a5f1642edc29680ed99acd64bc64b3a2c60a6c91b571"
    "acb546b371d18a22f18a06ac6251b3b59abe30f88864a3c948a3f09a8924b8fe09b8f088bee45aa3fe9ab049a3e408b8c1e74e1f4636af3a06ef0e81"
    "7a76df27e3a5781940f0a4d7c0a4f8a35770d92517dd15526c74de2a6cde15d76a34125d2ad2552c5d3457de1dd7d56a5e742c121d342f9d5d9e1f9c"
    "9d1faf1d5c1e1db41c1daf1d749e9d1fb41d2f9c5f9e1d1d19e7777ceb58eb6e6beb77d9ee583c67f0e3ebb6f8f744b7a5b08762eac3d93ebd1f49d7"
    "8c0a9c5d59301489ca94bd088a3d1499c81449b00809944af01499bdbf61320fe12749f42149f27ff4278f21344f32a1e1e73f49d187fa506aee7b2c"
    "cf3c198d509d7dda903dd94f5a1dcdbc1a0d99d07cdd8f7dfc0f599a7d9d10cda434477da0332209202207248973bd74493d47a0b433242234240709"
    "a27360bd6ceb07e1bd3583c83dc3c7ac883561eb08e1c77dabf52c83ebec870883f53d614068eabfa247a4d06264ea8090c77fa87b4acb89952687d9"
    "1547cbbb99e6498a68389ebd08bae80288281ee802ba7db8823d9e48383aa8e83828de8228ba887d31ba413f0ac47ff9cabfc17139443f3ac3c2b982"
    "075ab94747f97983079ac2825c293eddb29c6b83b22bbe5c831c5de9031dfe72a99c9c6ba91c7e83abdc325de0b8ad6813c64a23d38a2d602386e878"
    "a3a86dd33806e04a38a06de30a4693e8d61d53574c15b0ef0c30d3966f55d75d6f1753cc5dd516b0dd16932f70554cd71069b67e478a136a87537610"
    "6a8a3e69aa7e7607694a9013695036aa534a873e6d1c200ecca4db93b271f0db7977049be2e9c1c2808eecf580ecc1e2b5cec2e9f64dc63aec77bffc"
    "6c7fc6b6fcf7fa0dfc7a06eccdf776bfa426b0d6ac7d6bc4c05184ade235ba7a227a4480fab5ed91d39d5f9ba6719b48669b5f938871db9dc3a99a0a"
    "382e1cd4389cda0314aeca29948a1af829ee031ce9831a141c2eb8cae786e798d720214417a16727c4e0d886c498a7d7c660272146a72704e1a0d7d8"
    "815e8521cb9e4adb8b4ac541db9ea11e9b61058bdede814ade41459bca1e8ba16966820ac2b9c525824502e9e5b94a264cc91856fa17110f3ad1180c"
    "cf175649d15553ee4ff71e39cf5e13117977eed5796ed3cf5537d11e155113f95ef74feecb06c4eb0f6520b04f20840b30e5ebc6f02bc4cf06a54b20"
    "860b047020e5cfeb1d7652f75b7960c85b60d25d487937f64877d21b76f95d60f65d524860f95b3779fa724d10bf849490c4b2b9147f4d7a0afaa34e"
    "03eeaa7dc3ea638a3dae0e7add7d0560c47f06124446051dd23fe07d82a4f77de940107c69907702fcc0bd644aeeb6344c7ba4759d3139e4a6742119"
    "6621391d9934a4f1a62a8365cc313de54cecb40fe6fb33f4e6f3f40cf4bb4f2cb4cf3466ecfbcc33eccc34f4f33ba64ffbb77dd9c145a84e41a87dbb"
    "ce45d9f74e99fdc1f7457ba877bbbd4ee8c541d940a36cc6af9f3c82afbcac00825f46e34286ec6fa39f803ca3802c82bcdf6f46d7b83694aa121b6c"
    "2a9b7617ac12d4b82c94b6eab852171bc0bbb49044fd6c37d79a05a2fdaee22c0948bd85fb350e214359a67ff619175c36576603dc997f59d532261f"
    "022c23a50223a615252cdf32383a0a1d00ae2f29802f0a38292e1d3afdd9d740067f6ab046ea977d30ffc059f0c057c619bf7d6a99fd57702a7fc6c0"
    "e69cc315027e659342a5836613fed51cd39503c21cbe66659ca64353253ec2d502380b30de32546f214848158931eca1096c88e1a17115087d1c51af"
    "f74738fb24a7906778dbf14ff8b150e44f9b27678fa75038675be4f167a4d0cf715bb827ddc44d2098c33162d8f14d1da243e00462e00dd88443dd31"
    "44dd0de2b10358e030786f3a47333de5077def3065733a38657a2f0778f3303df8702f257d33473a14636392789088e7551cff6b0c5c4eed4c0eff55"
    "2ddc6b5ced2b7f4c1cdc554e2218937632bdccb9b20c93e239bd36585bb210ef29df7fc1e9bfd05b011f6ff2a5d59f8402f42ea2ce7de9179f783d37"
    "2961f55bf9d5cfaef94fb5e9eed51b61f2b40b5c60b844d4a084cb725438dc74ade476d77a99471fbac7366d5f5997e4af3063af525c56e05216e36f"
    "605cafb0602fa39270dc6f56a77b5bbc223cb6d9293169315fa2f98d9f39a9e94d623131180c1e111057f20050321ed80017110cf0e9afedd4cb90c6"
    "d4d0efb0c68bede9355a72a40b326d280b6d32752872249a9bb66362583ed8fb1898e3db7b7ea27699597800952560a61560b859a665801900830f50"
    "4c0bee310cae0fc0710b10434aae97f75893e33598a317ca759377ee6021903e4707d0b2071090e072877e212bcf7469bdae46debdc6f46b9e6e294f"
    "a70db91141bc1411691963da036dd2da2f1f23c50c6d5d0ffb185df38a5d19e17013ecdd91451eae33ad19761db48c5905ef3beb27eccd76855a4455"
    "bd9bb69fe08deb4314c62322d4a32b2022c6c34df98eabab4adddf6327767fa31139e0bc19e6ecd40c6b1abab2688c09aa0b6661dcd4c496134e6b15"
    "7e07d9cd50d078a4d11bb4faa5a287aed1f33b71e7940efdfa2eb487d1a29ba5a507b4d1aea2fa9b8725b49bfaa2aed1c42e7f20176f3be19a7f80b6"
    "0e80207d367d80201a80ff8e8b7b495aecc565112c0be1387c6e0ddc5a11c9658bc57b6cec65490b9145da7b656cc97bda45118b385c618d2c6e0bfc"
    "72c27ac8f14b8e8a7c0de12c5cee380b915ebffd7f6bc53dac6a0e1f871a8059fd3d3f4511ebdeff7f453f913debfddec57fbfde7deb3d11f39a757f"
    "43efb01d591f0e87ea1a2c8007000eacd91a9f6a586b8d66e3a21545a2ce54056db67fcc66458d15d8226be3e3150d58c5a2666bd01cb2359bc978c9"
    "05ccd4ff22b64e6d4c824be3c95cb853edffd4224c36854ec74bf13280e049af9146e135134970fd0cde1d02f5ecbe4f8049f147afe0b24b82cf9d3e"
    "8c6c5e75357d61f011c94693fd35619346c911701370e1117dc9b546383a5e3be83c3b3fd8bc2baed56824ba3b3f5e3bb83c3a68683b5e38bf3c3b3a"
    "3b685e3abb3c3f382eba2ba4d8e8bc553aaeabd5bce8582455a4ab58ba68aebc157b283291299260d6d6efb2ddb178ceb260281295297b1111122895"
    "e029327b7a3f92ae191538bb32ceeff8d6b1d6dd4a610fc5d487b37de1c7d76df1ef896e341a32a1f9ba1ffb4292e4ffe84f1e43217bb29fb43a9a79"
    "f91fb234fb3a219a9f79321aa13afbb47fc3641ec24f92e8a20ff5a1d4dcf758689e6442c3cf7f9211c28ffb56eb590640440e4812e77ae97b868f59"
    "116bc2d6d6d90f1106eb7bc2d9d60fc27b6b069148698efa4067441269480e1244e7c07a927a8e4069674844057b3c91707450d1c5c8d401218fff50"
    "11513cd00574fb707050bc05517411fbd0703c7b1174d10581d0d47f458f48a12b8e967733cd9314f79496132b4d0eb3063afce5523939d7947f83e3"
    "72887e7465577cb90639bad25239fc0657b965bab9527cba6539d7066374837e1488fff28ff2f3060f348505868573050fb4728fdf2ea698bbaa2d60"
    "a6155bc0460cd1f11860a62ddfaaaebbbb2d265fe0aa98aead3ba6ae982a60dfc0715bd1268c95467140dbc6158c26d14651dba6710cc095c5d38385"
    "011dd9eb0ea7ec20d4147dd265e3e0b7f3ee083601d983c56b9d85d3db38401c9849b72720d26cfd8e1427d4d2a06c54a7940e7d54fdec0ed2942027"
    "a63bbf364de33691d8fe8c6df9eff51b45f48800f56bdb23cd36bf2611e3b63b80a3085bc56b74f5ed9b8c75d8ef7ef9494d60ad59fbd688f9f50cd8"
    "9befed7e88314faf8dc14e427038b507285c95532f42cf4e88c1b10d8d4e4f08c241afb1ce0dcf31af41428887533515705c38a8d3073528385c7095"
    "281535f053dc0738989231acf42f221e16958a83b63d433d048b04d2cb73954c74a231189e2fac92d2cc041584738b4b03bd0a43963d95b6bd838a36"
    "953d164336c30a16bdbd0395e057889f0d4a97409fbd2622f2eedcab9f40081760cad78d0d1708e040ca9fd7970d88d71fca4060a2aba6dc9fee3d72"
    "2ba226f2bdee9fdcf2dca69fab6ea23d14f4479d06dc55fbb7c0a4bb90f26eec2089657329fe9af486d5c7147b5c1df4f3f4e59a207e09293beca4ee"
    "b7f2c090ecbba490c0f2b76e90eea437ecf2bbc0cd42723a326948e3888c0a3aa47fc0fb3a6372c84de942324d5506cb98637aca94dc6d6998f648eb"
    "bafb0ac088ff0c24d220ef04f8817bc90449effbd28120f89d32fb83ef8bf650cce7e919e8779f588350fb769d8bb2efef767b9dd08b83b2f66ffbb2"
    "838b509d99d8691fccf767e8d89969e8e7774c9f689f69ccd8f7996758286dd571a52e365f79590104bf8cc65536ed2e5825a8718077692189fad96e"
    "ae716d28552536d88146d98c5f3f79044601590479bfdf8c840cd9df463f01797074143a005c5f5212907a0bf76b1c4204464c2b4a58be65005f1470"
    "525c3a74ab654c3e0458464aae350b44fb5dc5596caecc06b833ffb286b24cffec332eb8a62b0784397ccdca8cd42ffb60fe81b3844a07cd26fcab39"
    "394d87a64a7c84abcd39872b04fcca26fbb3af810cfed46033fbafe054fe8c81e081af8c337efbd41f4fa170ceb6c8e34390902a1263d843f063a1c8"
    "9f364fcece48a19fe3b6704f484e21cff0b6e39f04701660bc65a8defb38a25eef8f70f612d810c343e32a10caf45e0ef0e6617ab0e39b3a4487c009"
    "0efade61cae67470f0e15e4afa668e7461f0de748e667acaba899b40308763c489ba1bc46307b0c0c4c01bb00987ba63b76421de53beff82ab38fed7"
    "18b89cda641926c5737a6db0d37fa1b7023edee4453026ed647a997329c6c624f12011cfda57fe9838b8ab9c981cfeab5ab8d7b85ac9edaef5328f3e"
    "9cfbd22f3ef17a6e400997e5a870b8e9758f6ddabeb22ec9e56917b8c07089a84bab3f0905e85d44f29f6ad3ddab37c253c2eab7f2ab9f5d30183c22"
    "20aee401a52cc6dfc0b85e613e7352d39bc46262a0643cb0012e22185362d262be44f31b5f61c65ea5b8acc04ff7b67845786cb3c05e4625e1b8dfac"
    "33b3f0002a4bc04ca9a1df618d17dbd33030c7b7f7fc44ed2ac070b34ccb0033376dc7c4b07cb0f7e1d35fdba997218d17da64ea50e448346ab4e448"
    "1764da50579ee9d27a5d8dbc185c1f80e31620860e2020c1e50efd427a8de9d73cdd529ec142207d8e0ea06500061fa09816dc6331472f94eb26efdc"
    "945c2fefb126c76b0ade77d64fd89bedd332c6b407daa4b5665a33ec3a6819b30bb588aa7a376d3fe126d8bb238b3c5c4e1b722382782922f731bae6"
    "15bb32c25e3e468a19daba1eb8a9892d279cd62aa8475740448c879b64d118135417ccc2fd0eb29ba1a0f14833ccd9a919d63474c01bd787288c4744"
    "4fecfe462372c079f21d575795babfc7eaf70271f6b3164c3fbb177649e8d71d1dbb17d7763fe84949bb17e8d71d3f767c309273886d439595309243"
    "737c6d888830926d43957c737330927c6d88954397fb484f3ba1cdd9d9fb48cd4f97a13b3bfb48a1cdd9974f4ffb4897a13bd9cd0494791a346cec76"
    "769479ec1a046c343494796cec76041a1a9479046c3476ec48b131781d1d4afe05f99087a1df525252f990528705dfa1a1f990df52520587226cdf14"
    "3519cb4474feac4379618ca0a0feac8c4374617979feac618ca07443ff69fe41e5a108c2c269fe0841ffa1e5e569fea108c2ff41d692b6b09a440fd1"
    "b7074df9d2f2d9f5b690b691b68c531f1f90b65391b68cb6b690b68c531fb6916f87f512f003bff5f587f5bf126f03f0f087f503bff56f121287f56f"
    "03f0f5bfd6901c25fa635ab0b0901c5a25d663fafa901c635ab0d62525901cd663fab05a304d3320ff6bbf11114d33bf20306bffff4d336bbf113020"
    "204d33306bff11bfd3cdbe50fb63063808808d26afb8dceacfa51dc0f06b421f1fa51d42c0cf6bf0eb441213232549737344124913eb25239c552205"
    "693ed823235522d8059c3e69c5dd2a0ec86f3e9494dd2a3e0ec56fc8c8dd2a6f3e94c50e0edd2ac56fc8943e3e52ed74d6df80e1e152ed80743edfd6"
    "d652eddf80e13e747452ed3edfd6e180cedfcf4d77899cfdfddfcf9c4dce897777dfcf899cfdce4d4ddfcfce8977fd9c9791c3d787a5d87c7c91c3d8"
    "d797a5878791c3a5d87c97d7d791c397a5877cd82694395ab0370317179439035a2637b0b09439370317265a8243ae83b03786c0b37c2ca471eea13f"
    "3f7c2ca1a4b3ee71717c2ceea13fb3a4a47c2cb3ee713fa1040e933816026f02020e936f38040216160e93026f020438380e93040216026fc68871f4"
    "ccb6b70f0f8871b7f4c6b6cc3844c701b8004e858544c74e013800b820bd1f46c5a8f99e9ebd1ff94620a8c5c5bd1fa8f99e2046d16ac8b16b523b7e"
    "db6ff29c1bd65174746ff2519cdbd61b1b6ff2d65174db9c9c6ff2dbd61b74517a77abbbfe3a90e7e777ab90bb7a3afefe77ab3a90e77abbbb77ab7a"
    "3afee79029e443086fbf0a8888e4430a0829bf6f8ba74bd0b582a180a94308a9bf34883de4cccc78422da18282cccca178e42d4242cccc2da182e478"
    "556d4e005517efefbae2ce9509b7b9bdbde2ceb995bab70909e2ceb7b9bdba9595e2cebab709bdb9be91f696b2235df8f891f65d96be23b2b291f623"
    "5df8be969691f6be23b2f85dded7f1856a64034040d7f10385de646a62b84e6e8bc83ac6c6b84e3a6e62c88b4a75e1a8f0bd66070775e166a84abdf0"
    "f075e1bd66074aa8a875e14abdf0076660b4afae133826f8f8b4af26ae60381313b4af3826f860aeaeb4af603813f82634574aff008d0ca3a3574a0c"
    "ff348d0000574a8d0ca334ffff574a348d00a30c597850e2638671fafa785071e25986636378508671fa59e2e27850598663fa7182243eddcf8d0bb0"
    "b0243e0bdd828dcfcf243e8d0bb082dddd243e828dcfb00b4b54d095d4157d3d3d54d07d954b15d4dfe460314336961717e4609631df36435b801734"
    "cb7cb22aa74fa7b97f0fac5e5e4fa7acb9a70f7f7f4fa70fac5ea7b99cc5b6293284761818c5b676299c84326b2754fc26411a4a4a27541afc6b4126"
    "9531fac03aeb150029ad7e27abb2bfc6c6ad7ebf2729b2ababad7eb2bfc62927c385885b6e1518d64a403e316947637676403e63314a476969403e47"
    "63764a31dbe6af6d8c7236dfdfe6af366ddb728c8ce6af7236dfdb6d6de6afdb728cdf36b777b987946e26e99ece3eb2e991870a0ace3e87b29e91e9"
    "e9ce3e91870a9eb21d032275ef85f8dfdf0322f8751d85efef032285f8df1d757503221d85efdff8ed9a7e79e0d3376e6e9a7e3779edd3e0e09a7ed3"
    "376eed79799a7eedd3e06e37aafdfe9a13a4c3d6d6fdfec39aaaa413f393c90e3e2830898993c9300ef3283e56cd9b84eadf8d7f7fcd9b8d8456dfea"
    "ddb4760c6d9fccfafab476cc0cdd9f6d9d5c5ef96d6a3c033f5f616398fef293935f61f2633ffe98985f61fef2933f637a080d8d4f276a6969080d6a"
    "8d7a274f92bc7b2b07f6b67777bc7bb62b92f607b9f50ad9c497dd0101f50addd9b997c4c4f50a97dd01b9d9d9f50ab997c401ddf3237af07a80b075"
    "75237ab0f0f3807a7a237a80b075f3f0f0237af3807a75b0878425e47907e5e4e48425e5e48707790304957290c7fd54540495fd7203c790d84700de"
    "a1bfb1f6f64700b1ded8bfa1a14700bfb1f6d8dede4700d8bfa1f6b13837b6b2a56fe6e2e237b6e6b2386fa5a537b66fe6e238b2b237b6386fa5e2e6"
    "909824f60ad052b2b84876e04ed8a6eaea4876a6e0b8d84ea4bf74a95059aeac04ccb5a2c2c263cf87ba552d7aa2282828ba55282d87a27ac8823a07"
    "8d1f3142d39091f639c0092dcfa727ef44ebaf9c9ca727afefcfeb44c31d72c6d53ee7c74c5b17dfec9e73d5d55b1773df4c9eecec5b179e73d54cdf"
    "df5b174c9eecd5733445101d3448e895954510e81d34483434451048e895341d1d451034483495e8e77873780b3016090978731678e7300b0b787330"
    "1609e778787873e7300b0916f4682feffdf72f4848682f2feff4f7fdfd682ff72f48f4efef682ff4f7fd482f3c375f908cc17ccbcb375f7c903cc18c"
    "2dcecf1e2e993917618727ee03302239614252143661ce6c6c4252ce1461613636425261ce6c6114af5585175ede2587f6007c86ba19bd637c1fec0b"
    "d567af36c81a153f8cddb8878ccf72170900c799b0f40b42831aecbc4526f935b7068a357d97c8f228584c494997c84cf27d58286e29a6ee7b902545"
    "06bc33157c2de307bcabdb3408395b0014caba6d02fe6b69233934c7d78658097b6197847eddf1b37b716df7839ed4b1233987d83654c90723c9d786"
    "5839340723d93654c93787087b817eddf16397b42f10673f6bc1a47e99c7ae41c04663478fd4fc7419ba93bd8f14da9c7df9b4b399a741c3c66e4740"
    "9947c04663c7ae4199c7c66e47a041438f7419ba93ddfcb48ff4b413da9c7db9cf3a9417c6084ae70f7918fa2d2555900f297558f01d2a95f64d5193"
    "b14c24c2cf1ac6084a3794e7cfca3844179607ea0ff92d255570189a1b83d7d1a1e48f14691b69cb38f5610be68f10f41f5a2e9ce61f8a20fc1f549e"
    "d0942f2d9f5d7f7b69cb38f5611b690b693b1569cb68fb01690bab49f4106d2de61f541e8a20fc9fc9a155623da60f0b58ff2bf136005f7f583ff05b"
    "ff26017fc951a23fa6056b0dc9613da60fab5502c931a6056b5da20f58ff36005fff2b71582f013ff05bff76d868f28acbad8e0034f30b02b3f61fd1"
    "34b3f61b0103f2dfec0bb53f668033ddda2104fcbc06ff51da010cbf26f4f15c3403b3f61ff10bd23403f2bff61b01d3ade2e350fc864cd9249134b1"
    "5e323247255290e6833dc259ade280fce64359dcad52fc864ce9e3d0adf2e64359ec80dc25825dc0e9933652243131529234b74efdccd9e49c78d7ff"
    "d50e48e7f36d1d2ed5fe0d18ee43672dfddc7497c8d9effcfdec9c78d7cfd9f4fd9cc8d9efdc74f7d5eef36d1d0e4827d54e67fd0d18ee239933a065"
    "72037b41398c7d7d597ac817395c8acd77797d1899a3057b33706142e43a087b63082c389973337061a2054b397c597ac8877d1d397c7d588acd7719"
    "30f98643206021e0c7124a3aeb1ef7c3c7e21efa334b1ac730896321f02640e03049206021f086e33029f026408063e1c732eb1ef7134acac7421ae7"
    "1efa33cbfb916f04825aecd918774b6f6ccbfc80741c800be0548843fb61548c9aef09d2861cbb26b5e317adfb819aef096254dc74ec148003805b48"
    "1847cf6c7bfb608cb70ab9aba7e37f7e261fc5b96dbd41f7266f1d45b7cdb9f1b7baebaf0379ae77b7aaa7e37f0eb97bb7aa0379aeb7eb7f26bf6dbd"
    "4117c5f926cfb9611d45b7fdcc1c8a47de2224c83ea48090f2fb8648ba045d2b180ab878cc8c27d4122a48cee6045075f1fe5ed5ccdc122a488e27c4"
    "8490fa4b83d8933a3e84f0f6ab80984269df65e93b228b1fee9c5ba97b9bd02bee7c9bdbab5b9920696f293bd285ef1b69ef3b228bdf6519693fd285"
    "ef6b291beeac7b9bd09b5b29ee5c99709bdbab2b176e86aad40b7f501d3f50e84da60674ebe4b688ac632c86178e0adf6b76a05417aed40b7f60865a"
    "17de6b76a0840a5feba4e32686bc688c1d5fa8463600e47da5c4f04fd308307afb6ae20a8633814ffb8a63820fe63a41a5f40fd0c8304a73a544d308"
    "30caf07fa5d4c8304af30f70fb0a8633816fe24afbea3a8163820f46e2b3d02dd8f80c4b0715279e6538a68f076518a79f253e86e2d3fddcb8002b48"
    "e223d8f80cbbd04de2d3b8002bd8fd4c07956538a61f278e07253e6618a79f85749afbf7c0ea75fa05dd57b95441dd430e1633646379f14d7841b3cc"
    "27abb20574fac0ea759afbf774ca9a7bfaf0e7f50e6619f36d337441055d495dd1d7b344ea77b22afb6b9cd26c6b97c24928835142c56f12a4a1b476"
    "a30facb35e015019ea27fb6b9c72b2daeaf77b9222bb6adc42a5c1bf1664a2746c9b22436887c159fe6ad3b62dc7f86de41393763466a704e43316a3"
    "74946607fedac62867f3bd6dfeba2dc7f86dd366fe2a67f3bdddc668e4733466a714930688b8e55681613d5c20825fd751f8fe3dec239b1e79a8e0e9"
    "ec7328eb1999aee02052f75e88ffdd3120d251f8fe8d5f37205288ffdd51f73eec1379a8e0299bee977b48e966927e7bef3faca94a3a61dde97793d7"
    "3e0deea6e9377de3d69e07aeefaf39413a6cadda990ce3308fe2933899ece0830293383fe9d73e0dee7693a7e997073e7de3d6ae153686e92f3ff9f3"
    "bcd94868f5adfed76bc7d0f6c9acdf4de595dfa6c633d0c915e62f3ff93386f915263ff6e38f39f96bc7ccd0fdd9a64fbc49a8feddf867d5afd09d9d"
    "7b491c50d0a0d6a877f29486bbb772606f7b27c9af904d7cd91d905baf907b491cd09d5daf70d91d909b4d5cbb67bb22697f70c7d0d0f874a296a687"
    "58524e7e7890474ea2070b3f0fa85737a207085b370faf3758429e77504e7e4850d92f37700c494550290779dc4f3540a2370fa857070b3fa207af07"
    "085b373f636b2e8bf3562a7e0410eb8dfd1b6a7f04f01b6b8fed1d7a632b5bfa662e8e73638bf3562a6e2e7b63fb662e8e235b7a0480fd1b6a1feb7d"
    "04e01dfa1b6b8f7d5bd5a2278a8272a86407ee846daa8e8b64670a8e8beda48e5c2b2a2c3cf64cc0a873d0f81123842c5b85d27228aa87a24b970a95"
    "e5ca4afa4962af002d250b897531f7cde4c95ebd7af24eb4fecaf97c7af2fafebc4ec47975f1cdee3957cdb475c1e4c95e3df7bd75e13957cdf4cdbe"
    "21675ced737e3cdc19699f039cd0320d376781770eb390800481de41834453590481845e49d341533787b7006391708e37770eb39060818737076391"
    "708eb780044183445389de5104d14183845e4953f3c507c913ccb87cf6f2f24e7fdf8f84f672ff8244ffde8ff305c918ccb7cc7378e23e0023921376"
    "fcece1929973d1e2f6427fdf8ff4f28ef6f2de7fff82448fc1be507df66ac3f724e54c111666c3262415e6cc16466123c067a89bd13b660f2c779100"
    "709cc9f851f1c3d88d7b88ac5578e1e55d72f85a24456113e6cc16263b53c1d7327e60c0925f736ba0585364892c8f82c594d47762eabe075952e496"
    "acdb26e0bf9646a1ba4d8390b305c0bb89cc24df87859274bf2034a8c1ce0b4b6d43957c738830927649e8d71d3fbb17d7763fe8491dbb177c6d8895"
    "4373309271f6b3164ceaf702e8d71d3f7649bb1773886d43957c309243737c6d889530926cec76041a349479cd4f97a13bd9fb48a1cdd9974f3bfb48"
    "046c3476ec1a94794f3ba1cdd997fb4897a13bd9cd4ffb481a346cec76049479ec1a046c347694798c43746179a0feac87a1df525205f990528705df"
    "a152f990618ca0744379feac781d1d4afe48b131df52520587a1f990143519cb44226cdf4379618ca074feac5391b68cb61f90b60841ffa1e5c269fe"
    "a108c2ff41e569fe8c531fb691b690b641e5a108c2ff69feb09a440fd1d692b6f9d2f2d9f5b7074d91b68c531fb690b6635ab0d625fa901cbf126f03"
    "f0f587f503bff56f12f087f5d663fab05a25901c12f003bff56f87f56f03f0f5bf1287f525fa635ab0d6901c5a25d663fab0901cc0f06b421fcfa51d"
    "bf20306bff114d336bbf113020ff4d3342c0cf6bf01fa51d20ff6bbf11304d33306bff11bf204d3350fb630638d3cdbe26afb8dcea08808d6f3e94c5"
    "0ec8dd2a4913eb252373441205693ed8239c5522c56fc8943e0edd2a1323254973eb4412d8059c3e692355220ec86f3e94c5dd2a3e0ec56fc894dd2a"
    "899cfdce4d77dfcf80743edfd6e152eddf80e13e74d652edce8977fd9c4ddfcf74d6df80e13e52ed3edfd6e1807452ed4d77899cfdcedfcf9c4dce89"
    "77fddfcf370317265ab09439d8d797a5877c91c3a5d87c97d78791c383b03786c08243aed787a5d87c9791c397a5877cd8d791c35ab0370317269439"
    "035a2637b0179439026f020438160e93a1a4b3ee713f7c2ceea13fb3a4717c2c040216026f380e93a471eea13fb37c2cb3ee713fa1a47c2c3816026f"
    "02040e936f38040216020e93a8f99e2046c5bd1fb7f4c6b6cc0f887101b8004e853844c7b16b523b7ed16ac8f4ccb6b70fc688714e013800b88544c7"
    "46c5a8f99e20bd1ff94620a8c59ebd1f3a90e77abbfe77ab519cdbd61b746ff2d65174db9c1b6ff27a3afee790bb77ab9c1bd65174db6ff2dbd61b74"
    "519c6ff2bbfe3a90e77a77ab90bb7a3afee777ab2da182e47842cccc0a0829bf6f88e443d0b582a1808ba74b005517efef556d4e086fbf0a8829e443"
    "a9bf34883da9430878422da182e4cccca178e42d4282cccc235df8be96b291f6b995bab709bde2ceb7b9bdba9509e2cebe23b2f85d9691f69509b7b9"
    "bdbae2cebab709bdb995e2ce96b2235df8be91f65d96be23b2f891f6bd66074aa8f075e10385de646a40d7f16e8bc83ac662b84e4abdf00766a875e1"
    "856a640340ded7f13a6e62c88bc6b84ea8f0bd66074a75e166a84abdf00775e18d0ca334ff00574a26ae603813f8b4af3826f860ae13b4af348d00a3"
    "0cff574aae133826f860b4af603813f826aeb4afff008d0ca334574a0cff348d00a3574a8d0bb082ddcf243e71e2598663fa78508671fa59e2637850"
    "828dcfb00bdd243ee2638671fa597850598663fa71e27850ddcf8d0bb082243e0bdd828dcfb0243eacb9a70f7f5e4fa77d954b15d43d54d031433696"
    "17dfe4600fac5ea7b97f4fa795d4157d3d4b54d09631df364317e46034cb7cb22a5b8017b97f0fac5ea74fa7bf2729b2abc6ad7e76299c843218c5b6"
    "fc26411a4a6b2754b2bfc62927abad7e29328476189cc5b61afc6b41264a2754c03aeb15009531fa27abb2bfc629ad7e7236dfdb6d8ce6af31694763"
    "764a403e63314a476976403edb728cdf366de6af5b6e1518d6c385884763764a3169403e6d8c7236dfdbe6af366ddb728cdfe6af85f8df1d75ef0322"
    "b2e991870a9ece3e87b29e91e90ace3e1d85efdff875032287946e26e9b777b991870a9eb2e9ce3e75ef85f8df1d0322f8751d85efdf03220e3e2830"
    "89f393c93779edd3e06e9a7ed3376eed79e09a7e300ef3283e8993c979e0d3376eed9a7eedd3e06e37799a7e9a13a4c3d6aafdfec39aaaa413d6fdfe"
    "f2633ffe98935f618d8456dfea7fcd9b0c6d9fccfaddb476fef2933f63985f6184eadf8d7f56cd9bcc0cdd9f6dfab476f96d6a3c039d5c5e6398fef2"
    "933f5f6197dd01b9d9c4f50a6a8d7a274f69080d2b07f6b67792bc7bb997c401ddd9f50a8d4f276a697a080db62b92f60777bc7bd9c497dd01b9f50a"
    "ddd9b997c401f50a7290c7fd54030495b0f0f3807a75237a80b075f3f07a237afd7203c790540495f07a80b075f3237af3807a75b0f0237ae47907e5"
    "e4878425e5e4870779e484256fe6e238b2a537b6b1ded8bfa1f64700bfb1f6d8dea14700386fa5e2e6b237b6dea1bfb1f6d84700d8bfa1f6b1de4700"
    "b2a56fe6e23837b6e6b2386fa5e237b6282d87a27a28ba55e04ed8a6eab84876a6e0b8d84eea4876078d1f3142c8823af60ad052b2909824a95059ae"
    "aca4bf74a2c2c263cf04ccb52d7aa2282887ba559e73d54cdfec5b17ef44ebaf9ccfa727afefcfeb449ca7274c9eecd573df5b17f639c0092dd39091"
    "c6d53ee7c7c31d72dfec9e73d54c5b1773df4c9eecd55b17301609e7780b7873e81d34483495451048e895341d344510e7300b09167878731d3448e8"
    "9534451034483495e81d4510780b301609e778731678e7300b0978731e2e9939172dcecf2feff4f7fd48682ff72f48f4effd682fee03302239618727"
    "effdf72f48f4682ff4f7fd482fef682f908cc17ccb3c375f7c903cc18ccb375f3f8cddb887c81a15ce146161366c425261ce6c6114364252170900c7"
    "998ccf72143661ce6c614252175ede2587af558586ba19bd63f6007c0bd567af367c1fec3408395b00bcabdb35b7068a354526f9f228584c497d97c8"
    "6d02fe6b6914caba42831aecbcb0f40b4cf27d58284997c8ee7b9025456e29a6157c2de30706bc33ddf16397b47b817e847eddf1b37b6197f7839ed4"
    "b17b716d3f6bc1a47e2f1067c7d7865809233934d83654c907233987865839340723c9d754c937870823d936ba93ddfcb48f74197419ba93bd8fd4fc"
    "9c7df9b4b38f14da13da9c7db98ff4b441c046634799c7aec3c66e474099a7414663c7ae419947c06e47a0414399c7c6255570189a0ff92dfa2d2555"
    "900f791858f01d2a950f2975d1a1e48f141b83d717c6084ae7cf3a9493b14c24c2f64d51084a3794e7cf1ac644179607eacfca3849f4106d2d690bab"
    "f41f5a2e9ce68f1020fc1f549ee61f8a1e8a20fc9fe61f54cb38f5610b691b692d9f5d7f7bd0942ff5611b690b69cb3869cb68fb01693b15005fff2b"
    "7158ff36f136005f7f58ff2b5bff26017f583ff03ff05bff76582f01623da60f0bc9a1553fa6056b0dc951a2a60fab5502c9613d056b5da20fc931a6"
    "f61ff10bd23403b302b3f61fd134f30b1b0103f2df34b3f6bff61b01d33403f28acbad8e00d868f23f668033ddec0bb5fcbc06ff51da2104bf26f4f1"
    "5cda010cc0e993365225825db15e323247249134e6833dc259255290529234b74e24313150fc864cd9ade2e3fce64359dcade280864ce9e3d0ad52fc"
    "4359ec80dcadf2e66d1d0e4827d5eef3e7f36d1d2ed50e4818ee43672dd5fe0dfd0d18ee23d54e67e49c78d7fffdccd997c8d9effcfddc7478d7cfd9"
    "f4fdec9cd9efdc74f7fd9cc87ac8877d1d397c597d597ac817398c7dcd77797d18395c8a588acd7719397c7d6572037b419933a07b3370614299a305"
    "7b63082c38e43a087061a2054b9973331ef7134acac732eb3aeb1ef7c3c7124afa334b1ac7c7e21ee71efa33cbc7421a43206021e030f98621f02640"
    "e03089636021f086e330492026408063e13029f08003805b4874ec146f6ccbfc8018774b0be0548843741c806c7bfb608c1847cf04825aecd9fb916f"
    "8c9aef09d2fb615426b5e317ad861cbbef096254dcfb819abd4117c5f926bf6db96dbd41f7261fc545b7cdb9f1266f1d611d45b7fd26cfb9aba7e37f"
    "7eb70ab9af0379ae77b7baebe37f0eb97bb7aaa779aeb7eb7fb7aa034b83d8933a8490fa90f2fb86483ea4802b180ab878ba045df6ab8098423e84f0"
    "47de2224c8cc1c8ad4122a48cecc8c2775f1fe5ed5e604502a488e27c4ccdc129bd09b5b29eeac7ba97b9bd02bee9c5bdbab5b9920ee7c9b709bdbab"
    "2bee5c99e93b228b1f69df653bd285ef1b696f29228bdf651969ef3b85ef6b291b693fd22686bc688ceba4e3e84da606741d3f5088ac632c86ebe4b6"
    "463600e47d1d5fa8aad40b7f50176e86df6b76a054178e0a0b7f60865a17aed476a0840a5f17de6b33816fe24afb0a860a8633814ffb6ae2820fe63a"
    "41fb8a638163820f46fbea3a4fd308307aa5c4f0d0c8304a73a5f40f0830caf07fa544d3304af30f70a5d4c838a61f278e0795659e6538a68f071527"
    "a79f253e860765186618a79f8507253e2dd8f80c4be2b3d0dcb8002b48e2d3fdf80cbbd04de223d8002bd8fd4ce2d3b8f36d3374410e6619b95441dd"
    "4305dd57646379f14d0e16335dd1d7b344055d49f7c0ea75fa749afbcc27abb2057841b3ea759afbf774fac07bfaf0e7f574ca9abf1664a27442a5c1"
    "c2492883516c6b9712a4a1b47642c56f436887c1596c9b222afb6b9cd2ea77b2b35e015019a30fac6b9c72b2daea27fb9222bb6adceaf77b66a71493"
    "06e47334763466a704e41393a374946607e433165681613d5c88b8e5b62dc7f86dfe6ad32867f3bd6dfedac6c7f86dd366feba2df3bdddc668fe2a67"
    "a8e0299beeec13791e79a8e0e9ec239beb1999aee0ec7328e966927e7b977b48d751f8fe3d20825f5e88ffdd312052f7f8fe8d5f3720d251ffdd51f7"
    "3e2052880dee7693a7e9d73ed73e0deea6e97793e3d69e07aee9377d3e7de3d6aee99707a94a3a61ddef3fac413a6caddaefaf39308fe29338990ce3"
    "830293383f99ece0d0fdd9a64f6bc7cc68f5adfed7bcd948f6c9acdf4d6bc7d0feddf867d5bc49a8e92f3ff9f3153686a6c633d0c9e595df3ff93386"
    "f915e62ff6e38f39f915263f22697f70c7bb67bba877f29486d0a0d6606f7b27c9bbb77274a296a687d0d0f89d7b491c50afd09d7cd91d905baf904d"
    "491cd09d5daf907b1d909b4d5caf70d9a857070b3fa2370f3f0fa85737a2070b5b370faf37a2070807085b373fa207af7e7890474e58524e77504e7e"
    "4858429e37700c494550d92f79dc4f35405029071b6a1feb7d0480fd8dfd1b6a7f0410eb6b8fed1d7a04f01bfa1b6b8f7d04e01d8bf3562a7e636b2e"
    "fa662e8e73632b5b562a6e2e7b638bf32e8e235b7a63fb6695e5ca4afa4b970a846daa8e8b6407ee8e8beda48e64670a002d250b894962af278a8272"
    "a85bd5a22c3cf64cc05c2b2af81123842ca873d07228aa87a25b85d2ed737e3cdc21675cb4fecaf97c7af24efebc4ec4797af2fa039cd0320d19699f"
    "cde4c95ebd7531f7ee3957cdb475f1cdc95e3df7bd75c1e457cdf4cdbe75e139445389de5104418341834453590481de5e49d3415304818483845e49"
    "5304d141770eb39080376781006391708e3787b7b39060818737770e91708eb780370763df8ff4f28ef6427f4e7fdf8f84f6f2f28244ffde8ff672ff"
    "7fff82448ff6f2dec913ccb87cf3c50718ccb7cc73f305c9002392137678e23e929973d1e2fcece1e55d72f85a5578e1111666c32624e54ccc164661"
    "232415e613e6cc16262445617df66ac3f7c1be509bd13b660fc067a800709cc9f82c7791d88d7b88ac51f1c3df8785927489cc246ba0585364925f73"
    "82c594d477892c8fa8c1ce0b4bbf2034d7327e60c03b53c1075952e49662eabee0bf9646a1acdb2690b305c0bbba4d8343957c309273886dd71d3fbb"
    "177649e8e8491dbb17d7763f6d8895309243737c7c738830926d439595437330927c6d88164ceaf70271f6b33f7649bb17e8d71dec760494791a346c"
    "a13bd9fb48cd4f97974f3bfb48a1cdd96c34769479ec1a04041a3494796cec7676ec1a9479046c34cdd997fb484f3ba1d9cd4ffb4897a13bcb44226c"
    "df143519525205f99087a1dfdfa152f9905287058ca074feac4379616179a0feac8c4374744379feac618ca04afe48b131781d1d0587a1f990df5252"
    "d9f5b7074df9d2f2a1e5c269fe0841ffff41e569fea108c2531fb690b691b68c8cb61f90b65391b6b691b690b68c531f08c2ff69fe41e5a10fd1d692"
    "b6b09a445ab0d6901c25fa6303f0f587f5bf126f6f12f087f503bff563fab0901c5a25d6d625fa901c635ab0b05a25901cd663fabff56f87f512f003"
    "f5bf1287f56f03f00638d3cdbe50fb636bff114d33bf20303020ff4d336bbf11dcea08808d26afb8421fcfa51dc0f06b6bf01fa51d42c0cfbf11304d"
    "3320ff6b11bf204d33306bff3e94c5dd2a0ec86f25237344124913ebd8239c552205693e6fc894dd2a3e0ec5c50ec8dd2a6f3e94943e0edd2ac56fc8"
    "4973eb44121323253e69235522d8059c9cfdcedfcf4d7789dfd6e152ed80743e3e74d652eddf80e18977fddfcf9c4dcece4d77dfcf899cfdfd9c4ddf"
    "cfce897780e13e52ed74d6dfe1807452ed3edfd603172694395ab037a5877c91c3d8d79797d78791c3a5d87c37b0179439035a26265ab09439370317"
    "86c08243ae83b037d87c9791c3d787a57cd8d791c397a5876f02040e93381602ee713f7c2ca1a4b3b3a4717c2ceea13f0216020e936f38040438160e"
    "93026f02026f380e93040216a13fb37c2ca471ee3fa1a47c2cb3ee71f99e20bd1f46c5a8b6cc0f8871b7f4c64e853844c701b800a8c59ebd1ff94620"
    "2046c5bd1fa8f99e3b7ed16ac8b16b52b70fc68871f4ccb600b88544c74e013890e77a77abbbfe3ad61b746ff2519cdbdb9c1b6ff2d651743afee777"
    "ab90bb7a7abbfe77ab3a90e7e790bb77ab7a3afe5174db6ff29c1bd674519c6ff2dbd61ba182e4cccc78422dbf6f88e4430a0829a1808ba74bd0b582"
    "2d4282cccca178e4e47842cccc2da182efef556d4e0055170a8829e443086fbf883da94308a9bf345df8be91f696b223b709bde2ceb995baba9509e2"
    "ceb7b9bd23b2f891f65d96bebe96b291f6235df8f85d9691f6be23b2b9bdbae2ce9509b7bdb995e2cebab70966074a75e1a8f0bd646a40d7f10385de"
    "3ac662b84e6e8bc8bdf00775e166a84a4aa8f075e1bd66070766a875e14abdf00340ded7f1856a64c88bc6b84e3a6e620ca334574aff008d3813f8b4"
    "af26ae6060ae13b4af3826f88d00a3574a0cff3434ff00574a8d0ca3a30cff574a348d0026f860b4afae1338f826aeb4af6038130bb082243eddcf8d"
    "8663fa785071e25959e26378508671fa8dcfb0243e0bdd8282ddcf243e8d0bb0b00bdd243e828dcf71fa597850e26386fa71e27850598663b22a5b80"
    "1734cb7c15d43d54d07d954b9617dfe460314336ac5ea74fa7b97f0f0f7f5e4fa7acb9a7a7b97f4fa70fac5e7d3d4b54d095d415364317e4609631df"
    "15009531fac03aeb843218c5b676299c1a4a6b2754fc2641bfc629ad7e27abb2b2abc6ad7ebf27292927abad7eb2bfc676189cc5b629328441264a27"
    "541afc6b36dfdbe6af6d8c7263764a403e316947476976403e63314a728cdfe6af366ddbdb6d8ce6af7236dfdf366de6afdb728c18d6c385885b6e15"
    "4a3169403e476376f8df1d032275ef85870a9ece3eb2e99191e90ace3e87b29e85efdf0322f8751d1d75ef032285f8dfdff87503221d85ef26e9b777"
    "b987946e9eb2e9ce3e91870ac3d6aafdfe9a13a4d3e06e9a7e3779eded79e09a7ed3376ea413d6fdfec39aaa3089f393c90e3e28283e8993c9300ef3"
    "376eed9a7e79e0d36e37799a7eedd3e03c039d5c5ef96d6adfea7fcd9b8d8456ccfaddb4760c6d9ff2933f5f616398fefe98935f61f2633f3f63985f"
    "61fef2938d7f56cd9b84eadf9f6dfab476cc0cdddd01b9f50ad9c497274f69080d6a8d7ab67792bc7b2b07f697c401f50addd9b9b9d9c4f50a97dd01"
    "01ddd9f50ab997c46a697a080d8d4f27f60777bc7bb62b92e5e4878425e47907807a75237ab0f0f3f3f07a237a80b0750779e48425e5e487fd540304"
    "957290c7c790540495fd7203b075f3237af07a8075b0f0237af3807ae6e23837b6b2a56fbfa1f64700b1ded8d8dea14700bfb1f66fa5e237b6e6b238"
    "38b2a537b66fe6e2e2e6b237b6386fa5b1f6d84700dea1bff6b1de4700d8bfa163cf04ccb5a2c2c2a6eab84876e04ed8d84eea4876a6e0b8282887ba"
    "552d7aa2a27a28ba55282d873142c8823a078d1f52b2909824f60ad0aeaca4bf74a9505973d54c5b17dfec9eaf9ccfa727ef44ebeb449ca727afefcf"
    "9eecd55b1773df4c4cdfec5b179e73d5d573df5b174c9eec092dd39091f639c0e7c7c31d72c6d53e1609e77873780b304834954510e81d34341d3445"
    "1048e895300b0978731678e7e7780b78733016090916787873e7300be8953445101d344895e81d45103448347ccb3c375f908cc1f7fd48682f2feff4"
    "f4effd682ff72f48c18ccb375f7c903c39172dcecf1e2e992239618727ee03302f48f4682feffdf7482fef682ff4f7fdbd63f6007c86ba1961366c42"
    "52ce1461611436425261ce6caf367c1fec0bd567b887c81a153f8cddc7998ccf72170900ce6c6142521436612587af5585175ede25456e29a6ee7b90"
    "8a354526f935b7064c497d97c8f22858e30706bc33157c2d5b00bcabdb3408396b6914caba6d02feecbcb0f40b42831a58284997c84cf27d340723c9"
    "d7865839f1b37b6197847eddd4b17b716df7839e870823d93654c93797b47b817eddf163a47e2f10673f6bc15809233934c7d786c907233987d83654"
    "ae419947c04663c793bd8fd4fc7419bab4b38f14da9c7df9414399c7c66e47a0fcb48f7419ba93dd7db98ff4b413da9c634799c7ae41c046474099a7"
    "41c3c66e94e7cf1ac6084a3755900f7918fa2d252a950f297558f01d07eacfca38441796189a0ff92d2555708f141b83d7d1a1e44ae7cf3a9417c608"
    "24c2f64d5193b14c690b69cb38f5611b2e9ce68f10f41f5a549ee61f8a20fc1ffb01693b1569cb686d2d690bab49f410fc9fe61f541e8a20610b691b"
    "69cb38f57f7bd0942f2d9f5d5502c9613da60fab5f7f58ff2bf13600017f583ff05bff26a20fc931a6056b5d2b7158ff36005fffff76582f013ff05b"
    "0f0bc9a155623da66b0dc951a23fa605ff51da2104fcbc061fd134f30b02b3f6f2df34b3f61b0103f15cda010cbf26f40bd23403b3f61ff101d33403"
    "f2bff61b8e00d868f28acbad33ddec0bb53f6680e3d0ad52fc864ce93247249134b15e32c259255290e6833d80dcadf2e64359ec365225825dc0e993"
    "b74e2431315292344cd9ade2e350fc8659dcade280fce643d9f4fdec9c78d7cf1d2ed50e48e7f36d672dd5fe0d18ee4374f7fd9cc8d9efdc4827d5ee"
    "f36d1d0eee23d54e67fd0d18d7fffdccd9e49c78effcfddc7497c8d92c38e43a087b6308c817398c7d7d597a7d18395c8acd7779054b9973337061a2"
    "7d1d397c597ac8877719397c7d588acd7b419933a0657203614299a3057b337086e33049206021f0f7c3c7124a3aeb1e1ac7c7e21efa334b63e13029"
    "f02640804acac732eb1ef71333cbc7421ae71efa21e030f98643206040e030896321f02617ad861cbb26b5e3fc8018774b6f6ccb8843741c800be054"
    "54dcfb819aef09625b4874ec14800380608c1847cf6c7bfbecd9fb916f04825a09d2fb61548c9aefb97bb7aaa7e37f0e41f7261fc5b96dbdb9f1266f"
    "1d45b7cdeb7fb7aa0379aeb7c5f926bf6dbd4117b7fd26cfb9611d457f7eb70ab9aba7e3ae77b7baebaf03795ed5e6045075f1fe86483ea48090f2fb"
    "b878ba045d2b180a27c4ccdc122a488e933a8490fa4b83d898423e84f0f6ab8024c8cc1c8a47de2248cecc8c27d4122a651969ef3b228bdfd02bee9c"
    "5ba97b9b9920ee7c9bdbab5b291b693fd285ef6b5b29eeac7b9bd09bab2bee5c99709bdb8b1f69df65e93b22ef1b696f293bd285865a17aed40b7f60"
    "06741d3f50e84da62c86ebe4b688ac630a5f17de6b76a084688ceba4e32686bce47d1d5fa84636007f50176e86aad40ba054178e0adf6b76f07fa544"
    "d30830ca814ffb6ae20a86333a41fb8a63820fe60f70a5d4c8304af3e24afb0a8633816f0f46fbea3a816382307aa5c4f04fd3084a73a5f40fd0c830"
    "d04de223d8f80cbba68f0715279e65383e86076518a79f25fd4ce2d3b8002bd8278e07956538a61f9f8507253e6618a70c4be2b3d02dd8f82b48e2d3"
    "fddcb800fbf774fac0ea759add4305dd57b95441f14d0e1633646379e7f574ca9a7bfaf074410e6619f36d33b344055d495dd1d775fa749afbf7c0ea"
    "b2057841b3cc27abb2daea27fb6b9c7283516c6b97c24928b47642c56f12a4a16adceaf77b9222bba27442a5c1bf1664c1596c9b224368879cd2ea77"
    "b22afb6b5019a30facb35e01d366feba2dc7f86da704e413937634666607e43316a37494c668fe2a67f3bddd9306e4733466a7143d5c88b8e5568161"
    "f86dfe6ad3b62dc7bd6dfedac62867f35f3720d251f8fe8de0e9ec239b1e79a8aee0ec7328eb1999f73e205288ffdd519beeec1379a8e0297e7b977b"
    "48e96692fe3d20825fd751f8dd312052f75e88ff9338990ce3308fe2eea6e97793d73e0d07aee9377de3d69e383f99ece083029393a7e9d73e0dee76"
    "d6aee997073e7de361ddef3faca94a3aaddaefaf39413a6c86f915e62f3ff933fed7bcd94868f5addf4d6bc7d0f6c9ac39f915263ff6e38fa64f6bc7"
    "ccd0fdd967d5bc49a8feddf8f9f3153686e92f3fd0c9e595dfa6c6339d5daf907b491cd09486d0a0d6a877f227c9bbb772606f7b4d5caf70d91d909b"
    "70c7bb67bb22697fa687d0d0f874a2961c50afd09d9d7b49905baf904d7cd91d494550d92f37700c5737a2070b3f0fa8af37a207085b370f35405029"
    "0779dc4f0b3fa2370fa85707373fa207af07085b474e58524e7e78907e4858429e77504e2e7b638bf3562a6e6a7f0410eb8dfd1b1d7a04f01b6b8fed"
    "5b7a63fb662e8e23eb7d0480fd1b6a1f8f7d04e01dfa1b6b2a7e636b2e8bf3568e73632b5bfa662e842ca873d0f811238e8b6407ee846daaa48e6467"
    "0a8e8bed87a25b85d27228aa4afa4b970a95e5ca0b894962af002d2572a85bd5a2278a824cc05c2b2a2c3cf6f7bd75c1e4c95e3df97c7af24eb4feca"
    "c4797af2fafebc4ecdbe75e13957cdf43cdc21675ced737e320d19699f039cd05ebd7531f7cde4c9cdb475f1cdee3957818737770eb3906053590481"
    "de41834441530481845e49d3b78037076391708ede51044183445389495304d14183845e9080376781770eb3708e3787b7006391137678e23e002392"
    "8f84f6f2f24e7fdfde8ff672ff8244ffd1e2fcece1929973f28ef6427fdf8ff4448ff6f2de7fff82b87cf3c507c913cccc73f305c918ccb7c9f82c77"
    "9100709cc32624e54c11166661232415e6cc164688ac51f1c3d88d7bf85a5578e1e55d72162624456113e6ccc3f7c1be507df66a660fc067a89bd13b"
    "46a1acdb26e0bf965364925f736ba058d477892c8f82c594c0bbba4d8390b305927489cc24df87850b4bbf2034a8c1ce60c03b53c1d7327ee49662ea"
    "be075952f70271f6b3164ceabb177649e8d71d3fbb17d7763fe8491dbb17e8d71d3f7649309273886d43957c309243737c6d889530926d43957c7388"
    "30927c6d88954373fb484f3ba1cdd997fb48cd4f97a13bd9fb48a1cdd9974f3bfb4897a13bd9cd4f94791a346cec76049479ec1a046c347694796cec"
    "76041a349479046c3476ec1ab131781d1d4afe48f99087a1df525205f990528705dfa152f990df52520587a16cdf143519cb4422feac4379618ca074"
    "feac8c43746179a0feac618ca074437969fe41e5a108c2ff69fe0841ffa1e5c269fea108c2ff41e592b6b09a440fd1d6074df9d2f2d9f5b790b691b6"
    "8c531fb690b65391b68cb61f90b68c531fb691b687f512f003bff56f87f5bf126f03f0f587f503bff56f12f087f56f03f0f5bf12901c25fa635ab0d6"
    "901c5a25d663fab0901c635ab0d625fa901cd663fab05a254d3320ff6bbf11304d33bf20306bff114d336bbf113020ff4d33306bff11bf20cdbe50fb"
    "630638d3808d26afb8dcea08a51dc0f06b421fcfa51d42c0cf6bf01f44121323254973eb44124913eb252373552205693ed8239c5522d8059c3e6923"
    "dd2a0ec86f3e94c5dd2a3e0ec56fc894dd2a6f3e94c50ec8dd2ac56fc8943e0e52ed74d6df80e13e52ed80743edfd6e152eddf80e13e74d652ed3edf"
    "d6e18074dfcf4d77899cfdcedfcf9c4dce8977fddfcf899cfdce4d77dfcfce8977fd9c4d91c3d787a5d87c9791c3d8d797a5877c91c3a5d87c97d787"
    "91c397a5877cd8d794395ab0370317269439035a2637b0179439370317265ab043ae83b03786c0827c2ca471eea13fb37c2ca1a4b3ee713f7c2ceea1"
    "3fb3a4717c2cb3ee713fa1a40e933816026f02040e936f38040216020e93026f020438160e93040216026f388871f4ccb6b70fc68871b7f4c6b6cc0f"
    "44c701b8004e853844c74e013800b885bd1f46c5a8f99e20bd1ff94620a8c59ebd1fa8f99e2046c56ac8b16b523b7ed16ff29c1bd65174db6ff2519c"
    "dbd61b746ff2d65174db9c1b6ff2dbd61b74519c77abbbfe3a90e77a77ab90bb7a3afee777ab3a90e77abbfe77ab7a3afee790bbe443086fbf0a8829"
    "e4430a0829bf6f88a74bd0b582a1808b4308a9bf34883da9cccc78422da182e4cccca178e42d4282cccc2da182e478426d4e005517efef55e2ce9509"
    "b7b9bdbae2ceb995bab709bde2ceb7b9bdba9509e2cebab709bdb99591f696b2235df8be91f65d96be23b2f891f6235df8be96b291f6be23b2f85d96"
    "d7f1856a640340ded7f10385de646a40b84e6e8bc83ac662b84e3a6e62c88bc675e1a8f0bd66074a75e166a84abdf00775e1bd66074aa8f075e14abd"
    "f00766a8b4afae133826f860b4af26ae603813f8b4af3826f860ae13b4af603813f826ae574aff008d0ca334574a0cff348d00a3574a8d0ca334ff00"
    "574a348d00a30cff7850e2638671fa59785071e2598663fa78508671fa59e2637850598663fa71e2243eddcf8d0bb082243e0bdd828dcfb0243e8d0b"
    "b082ddcf243e828dcfb00bdd54d095d4157d3d4b54d07d954b15d43de4603143369617dfe4609631df364317801734cb7cb22a5b4fa7b97f0fac5ea7"
    "4fa7acb9a70f7f5e4fa70fac5ea7b97fc5b629328476189cc5b676299c8432182754fc26411a4a6b27541afc6b41264a31fac03aeb150095ad7e27ab"
    "b2bfc629ad7ebf2729b2abc6ad7eb2bfc62927ab85885b6e1518d6c3403e31694763764a403e63314a476976403e4763764a3169e6af6d8c7236dfdb"
    "e6af366ddb728cdfe6af7236dfdb6d8ce6afdb728cdf366d77b987946e26e9b7ce3eb2e991870a9ece3e87b29e91e90ace3e91870a9eb2e9032275ef"
    "85f8df1d0322f8751d85efdf032285f8df1d75ef03221d85efdff8759a7e79e0d3376eed9a7e3779edd3e06e9a7ed3376eed79e09a7eedd3e06e3779"
    "fdfe9a13a4c3d6aafdfec39aaaa413d693c90e3e283089f393c9300ef3283e89cd9b84eadf8d7f56cd9b8d8456dfea7fb4760c6d9fccfaddb476cc0c"
    "dd9f6dfa5c5ef96d6a3c039d5f616398fef2933f5f61f2633ffe98935f61fef2933f6398080d8d4f276a697a080d6a8d7a274f69bc7b2b07f6b67792"
    "bc7bb62b92f60777f50ad9c497dd01b9f50addd9b997c401f50a97dd01b9d9c4f50ab997c401ddd9237af07a80b075f3237ab0f0f3807a75237a80b0"
    "75f3f07a237af3807a75b0f08425e47907e5e4878425e5e4870779e404957290c7fd54030495fd7203c790544700dea1bfb1f6d84700b1ded8bfa1f6"
    "4700bfb1f6d8dea14700d8bfa1f6b1de37b6b2a56fe6e23837b6e6b2386fa5e237b66fe6e238b2a537b6386fa5e2e6b29824f60ad052b2904876e04e"
    "d8a6eab84876a6e0b8d84eeabf74a95059aeaca4ccb5a2c2c263cf04ba552d7aa2282887ba55282d87a27a28823a078d1f3142c89091f639c0092dd3"
    "a727ef44ebaf9ccfa727afefcfeb449c1d72c6d53ee7c7c35b17dfec9e73d54c5b1773df4c9eecd55b179e73d54cdfec5b174c9eecd573df45101d34"
    "48e895344510e81d34483495451048e895341d34451034483495e81d7873780b301609e778731678e7300b097873301609e7780b7873e7300b091678"
    "682feffdf72f48f4682f2feff4f7fd48682ff72f48f4effd682ff4f7fd482fef375f908cc17ccb3c375f7c903cc18ccbcecf1e2e9939172d8727ee03"
    "302239614252143661ce6c614252ce146161366c425261ce6c6114365585175ede2587af007c86ba19bd63f61fec0bd567af367c1a153f8cddb887c8"
    "cf72170900c7998cf40b42831aecbcb026f935b7068a354597c8f228584c497d97c84cf27d58284929a6ee7b9025456ebc33157c2de30706abdb3408"
    "395b00bccaba6d02fe6b69143934c7d7865809236197847eddf1b37b716df7839ed4b17b3987d83654c90723c9d7865839340723d93654c937870823"
    "817eddf16397b47b10673f6bc1a47e2fc7ae41c046634799d4fc7419ba93bd8f14da9c7df9b4b38fa741c3c66e47409947c04663c7ae4199c7c66e47"
    "a04143997419ba93ddfcb48ff4b413da9c7db98f3a9417c6084ae7cf7918fa2d2555900f297558f01d2a950f4d5193b14c24c2f61ac6084a3794e7cf"
    "ca3844179607eacff92d255570189a0f83d7d1a1e48f141b1b69cb38f5610b698f10f41f5a2e9ce61f8a20fc1f549ee6942f2d9f5d7f7bd0cb38f561"
    "1b690b693b1569cb68fb01690bab49f4106d2d691f541e8a20fc9fe6a155623da60f0bc9ff2bf136005f7f583ff05bff26017f5851a23fa6056b0dc9"
    "613da60fab5502c931a6056b5da20fc9ff36005fff2b71582f013ff05bff765868f28acbad8e00d8f30b02b3f61fd134b3f61b0103f2df340bb53f66"
    "8033ddec2104fcbc06ff51da010cbf26f4f15cda03b3f61ff10bd23403f2bff61b01d334e2e350fc864cd9ad9134b15e323247245290e6833dc25925"
    "e280fce64359dcad52fc864ce9e3d0adf2e64359ec80dcad825dc0e9933652253131529234b74e24ccd9e49c78d7fffd0e48e7f36d1d2ed5fe0d18ee"
    "43672dd5dc7497c8d9effcfdec9c78d7cfd9f4fd9cc8d9efdc74f7fdeef36d1d0e4827d54e67fd0d18ee23d533a06572037b41998c7d7d597ac81739"
    "5c8acd77797d1839a3057b33706142993a087b63082c38e473337061a2054b997c597ac8877d1d397c7d588acd771939f98643206021e030124a3aeb"
    "1ef7c3c7e21efa334b1ac7c7896321f02640e03049206021f086e33029f026408063e13032eb1ef7134acac7421ae71efa33cbc7916f04825aecd9fb"
    "774b6f6ccbfc80181c800be05488437461548c9aef09d2fb1cbb26b5e317ad86819aef096254dcfbec148003805b487447cf6c7bfb608c180ab9aba7"
    "e37f7eb71fc5b96dbd41f7266f1d45b7cdb9f126baebaf0379ae77b7aaa7e37f0eb97bb7aa0379aeb7eb7fb7bf6dbd4117c5f926cfb9611d45b7fd26"
    "1c8a47de2224c8cca48090f2fb86483e045d2b180ab878ba8c27d4122a48cecc045075f1fe5ed5e6dc122a488e27c4cc90fa4b83d8933a8484f0f6ab"
    "8098423edf65e93b228b1f699c5ba97b9bd02bee7c9bdbab5b9920ee6f293bd285ef1b69ef3b228bdf6519693fd285ef6b291b69ac7b9bd09b5b29ee"
    "5c99709bdbab2bee6e86aad40b7f50173f50e84da606741de4b688ac632c86eb8e0adf6b76a05417aed40b7f60865a17de6b76a0840a5f17a4e32686"
    "bc688ceb5fa8463600e47d1dc4f04fd308307aa56ae20a8633814ffb8a63820fe63a41fbf40fd0c8304a73a544d30830caf07fa5d4c8304af30f70a5"
    "0a8633816fe24afbea3a8163820f46fbb3d02dd8f80c4be215279e6538a68f076518a79f253e8607d3fddcb8002b48e223d8f80cbbd04de2d3b8002b"
    "d8fd4ce2956538a61f278e07253e6618a79f85079afbf7c0ea75fa74dd57b95441dd43051633646379f14d0e41b3cc27abb20578fac0ea759afbf774"
    "ca9a7bfaf0e7f5746619f36d3374410e5d495dd1d7b3440577b22afb6b9cd2ea6b97c2492883516cc56f12a4a1b476420facb35e015019a327fb6b9c"
    "72b2daeaf77b9222bb6adceaa5c1bf1664a274429b22436887c1596c6ad3b62dc7f86dfe1393763466a704e43316a374946607e4dac62867f3bd6dfe"
    "ba2dc7f86dd366fe2a67f3bdddc668fe733466a7149306e4b8e55681613d5c88825fd751f8fe3d20239b1e79a8e0e9ec7328eb1999aee0ec52f75e88"
    "ffdd3120d251f8fe8d5f37205288ffdd51f73e201379a8e0299beeec7b48e966927e7b973faca94a3a61ddef7793d73e0deea6e9377de3d69e07aee9"
    "af39413a6caddaef0ce3308fe2933899ece0830293383f99d73e0dee7693a7e997073e7de3d6aee93686e92f3ff9f315d94868f5adfed7bcc7d0f6c9"
    "acdf4d6b95dfa6c633d0c9e5e62f3ff93386f915263ff6e38f39f915c7ccd0fdd9a64f6b49a8feddf867d5bcd09d9d7b491c50afa0d6a877f29486d0"
    "b772606f7b27c9bb904d7cd91d905baf907b491cd09d5daf70d91d909b4d5caf67bb22697f70c7bbd0f874a296a687d0524e7e7890474e58070b3f0f"
    "a85737a207085b370faf37a2429e77504e7e4858d92f37700c494550290779dc4f354050370fa857070b3fa207af07085b373fa26b2e8bf3562a7e63"
    "10eb8dfd1b6a7f04f01b6b8fed1d7a042b5bfa662e8e73638bf3562a6e2e7b63fb662e8e235b7a6380fd1b6a1feb7d04e01dfa1b6b8f7d04d5a2278a"
    "8272a85b07ee846daa8e8b64670a8e8beda48e642b2a2c3cf64cc05c73d0f81123842ca885d27228aa87a25b970a95e5ca4afa4b62af002d250b8949"
    "31f7cde4c95ebd75f24eb4fecaf97c7af2fafebc4ec4797af1cdee3957cdb475c1e4c95e3df7bd75e13957cdf4cdbe75675ced737e3cdc21699f039c"
    "d0320d196781770eb390803781de41834453590481845e49d341530487b7006391708e37770eb39060818737076391708eb780374183445389de5104"
    "d14183845e495304c507c913ccb87cf3f2f24e7fdf8f84f672ff8244ffde8ff605c918ccb7cc73f3e23e002392137678ece1929973d1e2fc427fdf8f"
    "f4f28ef6f2de7fff82448ff6be507df66ac3f7c1e54c111666c3262415e6cc164661232467a89bd13b660fc0779100709cc9f82cf1c3d88d7b88ac51"
    "78e1e55d72f85a55456113e6cc16262453c1d7327e60c03b5f736ba0585364922c8f82c594d47789eabe075952e49662db26e0bf9646a1ac4d8390b3"
    "05c0bbbacc24df87859274892034a8c1ce0b4bbf9bb4478187571fada0aa0ac92ed007a8"
)

_BRANCH2_HEX = "0f0704000908030a060b050d0e010c020f05080c0009020103070e060b0a0d04060500070c000a04080f010b0d09020e060b02050403080101070a000d0c090e0d070e0f0b0208030c0509010004060a0d0902060f0b0a040807000c0503010e0c090f07060f030e020d0405010b0a000c050a090e0802040407030f01060b000b0f0408020a0700090d06010e03050c0b060a0508020c03070f0e090d0001040906080f050800040a0b030d01020c0e090d0c0604070a03030f00080105020e01000d0f090a0b0e0402080703060c0501080a0c0f0905060b000304020e070d04080f000c0f0e0d0a01060207090503040205080d0b0a0606000e0f070c09030a08040f000b01060d0c0709030e05020a070b050f00020e0108030d0c0609040d070f08050f06040b0a0e0c090002030d0c020704010b0e0e08060f09050003"

_MOBILE_BOX_HEX = (
    "53290fe9e51f316f90f74a7e034d367784ab49237cd0135cdc632c322fd3be0e2624a417ecd9151a7ff64f60730a87f9445ec6ada2f865d22b696c41"
    "88f24c0df37b75510b939f6bc2fe6883e68bc8c722181ba0bdb08c9871b50c9a16b46eea8eed20ba4b8a14e0fcf1468dbbef05a93e5a9d7dcf068986"
    "35c1fd99f5de287a80c594daaab19b6279fbd75070cb52eb2555c456e39e7839853874e2f0013ac0b64742d8ca10e4b79c955de8b843ce4ed464a6a7"
    "2ed508091c92e7b3eedd1e1dd12afac321618fa3d65f9167c982f43d66a53c6a1997585b346dbf9672ff37cdbc073b2dae11453304df00815476b2a1"
    "3fccdb30b957a8acafe127400248591238922563e36406d37a24100b7902a028044e218453c2a399199c9d13dc40c55ba67e502273850ebdc1a2e218"
    "8b8f2d9e3cb909b8c46a2a9f4a6dd93007eafa65b7b3a881aa908cc74f0ad76bbbb58617c37012ca05a469fd44e62eecf1e4272ce860c0ae5eadf99b"
    "20d8f0234174006f3f110d7657d01645d4eff8f71471cbfe1cb2f52648727bf3c9de55153e031b4d61757db63dbf7782eeafe9018a8891362fb14759"
    "ac32bab03b349aeb5a377c5156be4c8dfbe13a684bda39cf836697c894545fe0f2491acea9fc6252f4ff1e0fe72bd2df6e67a7f635e5bcc6d1a5dd95"
    "1d89960887a18eb40c785cdb1f80ed42299333ab98cdd67f316cd54346585dccd759fb722789b08807cc0fda293f7e5e1819bb0353517020b31d3d00"
    "374952bea2c421e862040a9ec892a05b266b7a0d0cc316f483b81af39715657ffe32ad8de0c13077646035236ee5363e5f900e9a7cf850a81cd9960b"
    "6df73317226f99eaa6fff15cec34acb98246639b918ab2851466a7cdfc4ad1b52c2ae95a58d3734e47ddd5b7560193f644ef9c408b7dee39b4d6aabf"
    "4de761e3252d4c7ba3843187745d55e6a5db05d42b45caed43c0c5d0b64bfa9d94a4a9d8f2f0e1a108dcfd288fd2bc1fc7bd675412138169cb092498"
    "75ba3b68cfb11180afae104fc9789571c6dfce02413886796ae21e3c488cc21b9f423a066c2eabf98e2fdeeb5776e4f5d09a515ba58cbbab3e37b09f"
    "d4f6d9244df80512e84cd7956be301cf64f1429d58577cc241f3a2c655144f81aaf95a4e108da894b38970561ae9002619fbbac91fa922ed202bfc62"
    "cb08e0de2a7f3631435f8b47c8a3c563b4db4071ce74c46da6fa696a9e282d1e825d663b93bfd56c48dce1884bb10fccea063929f746443fd830a423"
    "2e53da21a1f2d1bdfebc3a02c10a1b8ad31d04fd616590d272ac737e98eb33af60528716bee78ec0ee8699031177277d9cff32542c67caf5f4459168"
    "1335ae0e178f3409a7803db83892dde5b9b7f0c750e24aef077badd678a09b850b84ec1597e4963cb5e675df1c0d6fb618496ecd76c35c798325590c"
    "2fb27a5e"
)

_MASK64 = (1 << 64) - 1


def _u32(n):
    return n & 0xffffffff


def _rol(n, k):
    k &= 31
    n &= 0xffffffff
    return ((n << k) | (n >> ((32 - k) & 31))) & 0xffffffff


def _ror(n, k):
    return _rol(n, 32 - (k & 31))


def _rol8(n, k):
    return ((n << k) | (n >> (8 - k))) & 255


def _ror64(n, k):
    s = k & 63
    return ((n >> s) | (n << ((64 - s) & 63))) & _MASK64


def _le(n, length=4):
    v = int(n)
    out = bytearray(length)
    for i in range(length):
        out[i] = v & 0xff
        v >>= 8
    return bytes(out)


def _read32(b, i=0, big=False):
    if big:
        return (b[i] << 24) | (b[i + 1] << 16) | (b[i + 2] << 8) | b[i + 3]
    return b[i] | (b[i + 1] << 8) | (b[i + 2] << 16) | (b[i + 3] << 24)


def _read64(b, i=0, big=False):
    n = 0
    for j in range(8):
        n = (n << 8) | b[i + (j if big else 7 - j)]
    return n


def _pad_block(data):
    padding = 16 - (len(data) % 16)
    return bytes(data) + bytes([padding]) * padding


def speck_signature(message, aid, random_value):
    prefix = _le(random_value)
    key = to_bytes(md5_hex(prefix + to_bytes(aid)))
    a = _read64(key)
    b = _read64(key, 8)
    queue = [_read64(key, 16), _read64(key, 24)]
    schedule = [a]
    for i in range(34):
        nxt = ((_ror64(b, 8) + a) & _MASK64) ^ i
        queue.append(nxt)
        a = nxt ^ _ror64(a, 61)
        schedule.append(a)
        b = queue.pop(0)
    data = _pad_block(to_bytes(message))
    out = bytearray(len(data))
    for off in range(0, len(data), 16):
        a = _read64(data, off)
        b = _read64(data, off + 8)
        for j in range(34):
            b = schedule[j] ^ ((a + _ror64(b, 8)) & _MASK64)
            a = b ^ _ror64(a, 61)
        out[off:off + 16] = _le(a, 8) + _le(b, 8)
    return b64_encode(prefix + bytes(out))


def helios(khronos, random_value=None):
    if random_value is None:
        random_value = _rand32()
    return speck_signature(str(khronos) + "-1588093228-8662", "8662", random_value)


def sm3(data):
    raw = to_bytes(data) if isinstance(data, str) else bytes(data)
    total = ((len(raw) + 9 + 63) // 64) * 64
    buf = bytearray(total)
    buf[0:len(raw)] = raw
    buf[len(raw)] = 128
    bit_len = _le(len(raw) * 8, 8)[::-1]
    buf[total - 8:total] = bit_len
    state = [0x7380166f, 0x4914b2b9, 0x172442d7, 0xda8a0600, 0xa96f30bc, 0x163138aa, 0xe38dee4d, 0xb0fb0e4e]

    def p0(x):
        return x ^ _rol(x, 9) ^ _rol(x, 17)

    def p1(x):
        return x ^ _rol(x, 15) ^ _rol(x, 23)

    for off in range(0, total, 64):
        w = [0] * 68
        for i in range(16):
            w[i] = _read32(buf, off + i * 4, True)
        for i in range(16, 68):
            w[i] = p1(w[i - 16] ^ w[i - 9] ^ _rol(w[i - 3], 15)) ^ _rol(w[i - 13], 7) ^ w[i - 6]
        a, b, c, d, e, f, g, h = state
        for j in range(64):
            ss1 = _rol((_rol(a, 12) + e + _rol(0x79cc4519 if j < 16 else 0x7a879d8a, j)) & 0xffffffff, 7)
            ss2 = ss1 ^ _rol(a, 12)
            ff = (a ^ b ^ c) if j < 16 else ((a & b) | (a & c) | (b & c))
            gg = (e ^ f ^ g) if j < 16 else ((e & f) | ((~e & 0xffffffff) & g))
            tt1 = (ff + d + ss2 + (w[j] ^ w[j + 4])) & 0xffffffff
            tt2 = (gg + h + ss1 + w[j]) & 0xffffffff
            d = c
            c = _rol(b, 9)
            b = a
            a = tt1
            h = g
            g = _rol(f, 19)
            f = e
            e = p0(tt2) & 0xffffffff
        state = [(state[i] ^ v) & 0xffffffff for i, v in enumerate([a, b, c, d, e, f, g, h])]
    out = bytearray()
    for v in state:
        out += _le(v)[::-1]
    return bytes(out)


def _checksum(data):
    n = 0x20220420
    for i in range(12):
        t = (n >> (5 if i % 2 else 3)) ^ n
        if i % 2:
            n = (~(data[i] | ((n << 11) & 0xffffffff))) ^ t
        else:
            n = (data[i] ^ ((n << 7) & 0xffffffff)) ^ t
        n &= 0xffffffff
    return ((n | 4) ^ 0x1000000) & 0xffffffff


def _with_checksum(b):
    return bytes(b) + _le(_checksum(b))


def _hash_iv(iv, b):
    for i in range(len(b)):
        if i % 2:
            iv = (~(((iv >> 7) ^ iv ^ (b[i] | ((iv << 12) & 0xffffffff))) & 0xffffffff)) & 0xffffffff
        else:
            iv = ((iv >> 4) ^ iv ^ ((iv << 6) & 0xffffffff) ^ b[i]) & 0xffffffff
    return iv


_BRANCH0_K = [
    0xebb64faf, 0x7aadcc2, 0xcf3187bf, 0xe01138ff, 0x6d0bfcff, 0x5a30a3be, 0xb41ad638, 0x34180eb8,
    0xf233eb6f, 0xb1a584cc, 0xccc30dc7, 0x47d1db51, 0xd55653de, 0x70a84fa1, 0x57473c12, 0xf76f0288,
    0x2c077f0a, 0xda0dcad0, 0xfbb86f6c, 0xfdc4cf00, 0x688a020d, 0xe676c6a6, 0x8cd6338b, 0x1a3c8d0e,
    0xcce8b06b, 0x6ad0ed0b, 0xa0522717, 0xdc71ac83, 0x2285db71, 0xd5b4dda6, 0x736f8650, 0x6560306c,
    0x617ce2a6, 0xe423417e, 0xa40e143, 0x544e4032, 0x88dffb2a, 0x716c1ae0, 0x4c467a88, 0x5b23bb3,
    0xe1d0b866, 0xbaa3dcb8, 0xae3374d3, 0xc3381a50, 0x1702f75b, 0xfe6da368, 0xf0b4cf48, 0x4e0ffbb8,
    0x72aad10d, 0x26c53a3d, 0xf2bce0f6, 0xb4557581, 0x4a257fdd, 0x8c3182a2, 0xab0b3b86, 0x3d5dfb14,
    0x4f103634, 0xd37b52d7, 0x444eff16, 0xeb0a33d1, 0x6ca86f6e, 0x284ba7, 0x8387cfa, 0x5fb37586]


def _branch0(idx, t, q, b, ts):
    base = [0xc4a78580, 0xb3c0fd39, 0xc58c5686, 0xc9aa3ba7, 0xf5a7adf2, 0x963c2ed1, 0x9d4a97c2][idx]
    count = (base + t) & 0xffffffff
    k = [_ror(v, (count + 1) & 255) for v in _BRANCH0_K]
    pad = bytes(((v * 257) >> ((count + 2) & 7)) & 0xff for v in (0xfa, 0x45, 0x61, 0xd7))
    start = [_ror(v, count & 255) for v in
             (0x7aba4fc8, 0x67166507, 0x6403fa00, 0x340f512f, 984304912, 3005047866, 2874125293, 2152413264)]
    data = bytes(q) + bytes(b) + bytes(ts) + pad + hex_to_bytes("00000000000001a0")
    di = [_read32(data, i * 4, True) for i in range(16)]
    for i in range(112):
        x = di[i + 1]
        y = di[i + 14]
        di.append((di[i] + di[i + 9] + (_rol(x, 14) ^ _rol(x, 25) ^ (x >> 3)) +
                   (_rol(y, 13) ^ _rol(y, 15) ^ (y >> 10))) & 0xffffffff)
    config = [[101, 5, 7, 6, 3, 2, 1, 0, 5, 4, 3], [96, 0, 6, 7, 5, 3, 2, 1, 5, 4, 4],
              [96, 7, 6, 2, 1, 4, 0, 5, 4, 3, 5], [99, 3, 6, 2, 4, 5, 1, 0, 0, 7, 6],
              [96, 0, 5, 6, 7, 3, 1, 2, 5, 4, 4], [100, 2, 0, 3, 5, 4, 6, 7, 2, 1, 5],
              [96, 1, 3, 4, 0, 6, 5, 2, 0, 7, 7]][idx]
    rounds, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 = config
    d = list(start)
    for i in range(rounds):
        n1 = ((d[x3] ^ d[x4]) & d[x1]) ^ d[x3]
        n2 = _rol(d[x1], 26) ^ _rol(d[x1], 21) ^ _rol(d[x1], 7)
        n4 = (di[(base + i) & 127] + n1 + n2 + k[(base + i) & 63] + d[x5]) & 0xffffffff
        n5 = _rol(d[x2], 30) ^ _rol(d[x2], 19) ^ _rol(d[x2], 10)
        n6 = (d[x2] & d[x6]) | ((d[x2] | d[x6]) & d[x7])
        old = d[x9]
        d = [d[7]] + d[0:7]
        d[x10] = (n5 + n6 + n4) & 0xffffffff
        d[x8] = (old + n4) & 0xffffffff
    ret = bytearray()
    for i, v in enumerate(d):
        ret += _le((v + start[i]) & 0xffffffff)[::-1]
    digest = bytes(ret[i] ^ ret[i + 16] for i in range(16))
    return digest + _le(_checksum(digest) | (32 if idx == 6 else 0))


_TABLE1 = None


def _branch1(idx, t, q, b, ts):
    global _TABLE1
    if _TABLE1 is None:
        _TABLE1 = hex_to_bytes(_BRANCH1_HEX)
    base = [0x808a9c79, 0xf079807e, 0xbadf79c5, 0xa785d3ff, 0x82d8438c][idx]
    cv = _ror64(t, (base + t) & 255)
    orders = [[5, 7, 1, 2, 4, 0, 6, 3], [0, 5, 2, 4, 1, 3, 7, 6], [5, 7, 2, 4, 1, 6, 3, 0],
              [3, 0, 2, 4, 6, 7, 1, 5], [4, 5, 0, 3, 6, 2, 1, 7]][idx]
    constants = [_ror64(v, (base + t + 1) & 63) for v in (
        0x87aeea5dab37cd6b, 0x7ff48becb4f54087, 0xb0724c06706bbd5d, 0x1fe5dfb1143e328d,
        0x1a2331d00af4f1f2, 0xcaff7131bb1e71ba, 0x33385e1042752218, 0xff01ed65d4a441fb,
        0xadb1ec8828c80e8, 0x62475d12f4e06fe7, 0xbd0b238da4fe72)]

    def rnd(src, j, tt):
        out = tt
        for i in range(8):
            v = (src[(j + i) & 7] >> (56 - i * 8)) & 255
            out ^= _read64(_TABLE1, (idx << 14) + i * 2048 + v * 8)
        return out

    def swap(src, xor, typ=None):
        d = [src[orders[i]] ^ xor[i] for i in range(8)]
        h = list(xor)
        for n in range(10):
            h = [rnd(h, j, constants[n + 1] if j == 7 else 0) for j in range(8)]
            d = [rnd(d, j, h[j]) for j in range(8)]
        if typ is None:
            return [d[(8 - i) & 7] ^ xor[i] ^ src[i] for i in range(8)]
        return [d[7] ^ typ[1], d[6] ^ typ[2], d[5] ^ typ[3], d[4] ^ typ[4],
                d[3] ^ typ[5], d[2] ^ typ[6], d[1] ^ typ[7] ^ src[7], d[0] ^ typ[0]]

    data = bytes(q) + bytes(b) + bytes(ts) + hex_to_bytes("800000000000000000000000")
    s = swap([_read64(data, i * 8, True) for i in range(8)], [cv] * 8)
    s = swap([0, 0, 0, 0, 0, 0, 0, 416], [s[4], s[3], s[2], s[1], s[0], s[7], s[6], s[5]], s)
    ret = bytearray()
    for v in reversed(s):
        p = _le(v, 8)
        ret += bytes([p[1], p[3], p[5], p[6]])
    return _with_checksum(bytes(ret[i] ^ ret[i + 16] for i in range(16)))


_SV2 = [
    2813263392, 1900671446, 1206176263, 3920990055, 2478384350, 3323252981, 951050479, 2998644083,
    3796124867, 2637884571, 3749394404, 3635506496, 4172034488, 1991878923, 836252654, 2503986788,
    892704164, 1175044411, 915558408, 2355956005, 1576386935, 486274347, 2320476144, 290235230,
    2173958532, 2054850355, 829076693, 1008783305, 2799191123, 974671884, 2039399546, 2544331560,
    1724186518, 1366385731, 231930939, 3043585447, 3152755397, 1548997124, 3542485198, 1920580076,
    4095250127, 4158100443, 858571921, 2876681749, 2615928615, 413143940, 1542060199, 1603315540,
    968254400, 912735363, 2090005780, 2642253015, 3806910890, 1602133673, 2059224401, 1453196762,
    1084380722, 1039509925, 3132325248, 1161987804, 1063079544, 64468829, 2986232567, 2779457187]
_ORDERS2 = None


def _branch2(iv, t, q, b, ts):
    global _ORDERS2
    if _ORDERS2 is None:
        _ORDERS2 = hex_to_bytes(_BRANCH2_HEX)
    n = (iv & 13) * 86
    idx = ((n >> 15) & 255) + ((n >> 8) & 255)
    base = [0x8980f29b, 0xeb549c7f, 0xb08726db, 0xd40cb5e6, 0xe8f559e4][idx]
    count = (base + t) & 0xffffffff
    cv1 = (count + 1) & 255
    pad = bytes(((v * 257) >> ((count + 5) & 7)) & 0xff for v in (0x84, 0x96, 0x77, 0x9d, 0xd4, 0x15, 0x0b, 0xf8))
    data = bytes(q) + bytes(b) + bytes(ts) + pad + hex_to_bytes("a0010000")
    m = [_read32(data, i * 4) for i in range(16)]
    start = [_ror(v, count & 255) for v in (0x79e0f2fb, 0xc8b52570, 0xebc2f8cd, 0x7c104d93)]
    end = [_ror(v, (count + 6) & 255) for v in (0x19be4866, 0xe85986b4, 0xe19b326e, 0x71d1d7d4)]
    a, b, c, d = start
    shifts = [[7, 12, 17, 22], [5, 9, 14, 20], [4, 11, 16, 23], [6, 10, 15, 21]]
    for j in range(64):
        r = j >> 4
        if r == 0:
            f = (b & c) | ((~b & 0xffffffff) & d)
        elif r == 1:
            f = (b & d) | (c & (~d & 0xffffffff))
        elif r == 2:
            f = b ^ c ^ d
        else:
            f = c ^ (b | (~d & 0xffffffff))
        nxt = (b + _rol((a + f + m[_ORDERS2[idx * 64 + j]] + _ror(_SV2[j], cv1)) & 0xffffffff,
                        shifts[r][j & 3])) & 0xffffffff
        a = d
        d = c
        c = b
        b = nxt
    vals = [a, b, c, d]
    return _with_checksum(b"".join(_le((vals[i] + start[i] & 0xffffffff) ^ end[i]) for i in range(4)))


def _medusa_hash(query_hash, body_hash, khronos):
    ts = _le(khronos)
    iv = _hash_iv(_hash_iv(_hash_iv(0x20230928, query_hash), body_hash), ts)
    idx = ((iv & 15) * 171) >> 9
    branch = (iv & 15) - idx * 3
    if branch == 0:
        return _branch0(idx, khronos, query_hash, body_hash, ts)
    if branch == 1:
        return _branch1(idx, khronos, query_hash, body_hash, ts)
    return _branch2(iv, khronos, query_hash, body_hash, ts)


_LEGACY_CIPHER = {
    "box": None,
    "box_hex": _SBOX_HEX,
    "rows": [[1, 0, 2, 3], [2, 0, 3, 1], [0, 1, 3, 2], [1, 0, 2, 3]],
    "order": [[0, 9, 14, 11, 4, 13, 2, 7, 8, 1, 6, 15, 12, 5, 10, 3],
              [0, 9, 14, 15, 4, 13, 2, 7, 8, 1, 6, 3, 12, 5, 10, 11],
              [0, 9, 14, 7, 4, 13, 2, 11, 8, 1, 6, 3, 12, 5, 10, 15],
              [0, 9, 14, 11, 4, 13, 2, 7, 8, 1, 6, 15, 12, 5, 10, 3]],
    "initial": [0xca025ddc, 0x823dc546, 0xc9420583, 0xc298225f],
    "wire": [5, 6, 2, 4, 3, 1, 0, 7],
    "compact": [1, 6, 0, 7, 2, 4, 5, 3],
    "key": hex_to_bytes("f1593376766ea98d34f31b057a9d5be4"),
    "iv": hex_to_bytes("1fe109a4125283f418de9e051a969e12"),
}


def _medusa_cipher(data_in, khronos, profile):
    word = khronos & 3
    if profile["box"] is None:
        profile["box"] = hex_to_bytes(profile["box_hex"])
    box = profile["box"][word * 256:(word + 1) * 256]
    con = profile["rows"][word]
    order = profile["order"][word]
    init = profile["initial"][word]
    key = profile["key"]
    mk = bytearray(48)
    for i in range(16):
        mk[i] = key[i] ^ ((init >> ((i & 3) * 8)) & 255)
    rounds = 8
    for i in range(4, 12):
        off = 4 * (i - 1)
        a, b, c, d = mk[off], mk[off + 1], mk[off + 2], mk[off + 3]
        if (i & 3) == 0:
            a, b, c, d = ((init >> (rounds & 24)) ^ box[b]) & 255, box[c], box[d], box[a]
        for j, v in enumerate((a, b, c, d)):
            mk[off + 4 + j] = v ^ mk[off - 12 + j]
        rounds += 2

    def add(s, off):
        return bytearray(v ^ mk[off + (i & ~3) + con[i & 3]] for i, v in enumerate(s))

    def xt(v):
        return ((v << 1) ^ (27 if (v & 128) else 0)) & 255

    def encrypt(block):
        s = add(block, 0)
        for rnd in (1, 2):
            s = bytearray(box[v] for v in s)
            s = bytearray(s[con[i >> 2] * 4 + (i & 3)] for i in range(16))
            s = bytearray(s[oi] for oi in order)
            if rnd == 1:
                s = bytearray(s[(i & ~3) + con[i & 3]] for i in range(16))
                for j in range(4):
                    av, bv, cv, dv = s[j], s[4 + j], s[8 + j], s[12 + j]
                    tv = av ^ bv ^ cv ^ dv
                    s[j] ^= tv ^ xt(av ^ bv)
                    s[4 + j] ^= tv ^ xt(bv ^ cv)
                    s[8 + j] ^= tv ^ xt(cv ^ dv)
                    s[12 + j] ^= tv ^ xt(dv ^ av)
            s = add(s, rnd * 16)
        return bytearray(v ^ mk[16 + i] for i, v in enumerate(s))

    if len(data_in) < 248:
        raise ValueError("Medusa 資料過短")
    wire = profile["wire"]
    compact = profile["compact"]
    summary = bytearray(32)
    summary[31] = 1
    for i in range(31):
        for j in range(8):
            summary[i] |= ((data_in[i * 8 + j] >> wire[j]) & 1) << compact[j]
    prev = profile["iv"]
    enc = bytearray(32)
    for off in range(0, 32, 16):
        blk = bytearray(summary[off + i] ^ prev[i] for i in range(16))
        prev = encrypt(blk)
        enc[off:off + 16] = prev
    data = bytearray(data_in)
    for i in range(31):
        for j in range(8):
            at = i * 8 + j
            bit = (enc[i] >> compact[j]) & 1
            data[at] = (data[at] & ~(1 << wire[j])) | (bit << wire[j])
    return bytes(enc[31:]) + bytes(data)


def _varint(value):
    n = int(value)
    out = bytearray()
    while True:
        byte = n & 127
        n >>= 7
        out.append(byte | (128 if n else 0))
        if not n:
            return bytes(out)


def _proto(fields):
    out = bytearray()
    for fid, ftype, v in fields:
        if ftype == "bytes":
            if not v:
                continue
        elif v == "" or v == 0 or v is None:
            continue
        if ftype == "int":
            n = int(v)
            out += _varint(fid * 8)
            out += _varint(-n * 2 - 1 if n < 0 else n * 2)
        elif ftype == "float":
            out += _varint(fid * 8 + 5)
            out += struct.pack("<f", v)
        else:
            b = to_bytes(v) if ftype == "str" else bytes(v)
            out += _varint(fid * 8 + 2)
            out += _varint(len(b))
            out += b
    return bytes(out)


def _f_int(fid, v):
    return (fid, "int", v)


def _f_str(fid, v):
    return (fid, "str", v)


def _f_bytes(fid, v):
    return (fid, "bytes", v)


def _f_float(fid, v):
    return (fid, "float", v)


def _mix_medusa(data, sign_key, hash_random, flags):
    key = sm3(sign_key + _le(hash_random) + sign_key)
    seed_part = (hash_random >> 16) & 255
    seed = _le((~(((seed_part << 11) | (hash_random >> 24)) ^ (seed_part >> 5) ^ seed_part)) & 0xffffffff)
    mixed = bytearray(len(data))
    for i in range(len(data)):
        idx = (i * 4) & 28
        d0 = key[idx]
        d1 = key[idx + 1]
        v = (~((_rol8(data[i], 4) + d0) ^ d1)) & 0xff
        v = (_rol8(v, 3) + d1) & 255
        mixed[len(data) - 1 - i] = (~(v ^ d0)) & 255
    last = mixed[-1] ^ mixed[-2]
    first = mixed[0]
    mixed[0] = (~last + mixed[0]) & 255
    mixed[1] = ((mixed[0] ^ mixed[-1] ^ 254) + mixed[1]) & 255
    mixed[2] = (mixed[2] + ((last - first) ^ _rol8(mixed[1], 3) ^ 2)) & 255
    for i in range(len(mixed) - 4):
        mixed[i + 3] = ((~( _rol8(mixed[i + 2], 3) ^ mixed[i + 1] ^ (i + 3))) + mixed[i + 3]) & 255
    mixed[-1] ^= mixed[-2]
    total = 0
    for i in range(1, len(mixed)):
        total += mixed[i]
    mixed[0] = ((mixed[0] ^ mixed[1]) + total) & 255
    joined = bytes(flags) + bytes(mixed)
    rev = joined[::-1]
    return bytes(v ^ seed[(~i) & 3] for i, v in enumerate(rev))


def _pack_medusa(data, q, hash_bytes, khronos, hash_random, xm_random, sign_key, magic, flags, prefix, version, cipher):
    mixed = _mix_medusa(data, sign_key, hash_random, flags)
    check = 0x18000001 | ((q[0] & 63) << 14) | ((hash_bytes[0] & 63) << 8)
    packed = bytes([prefix]) + _le(xm_random) + _le(check) + mixed + _le(hash_random)[2:]
    carrier = _medusa_cipher(packed, khronos, cipher)
    stamp = _le(khronos)
    header = bytes(v ^ stamp[i & 3] for i, v in enumerate(_le(version) + magic))
    return b64_encode(header + _le(hash_random)[0:2] + _le(256, 2) + carrier)


def medusa(query, body, khronos, device):
    q = sm3(query)
    b = hex_to_bytes(md5_hex(body)) if body else bytes(16)
    hash_bytes = _medusa_hash(q, b, khronos)
    did = str(device.get("device_id") or "")
    version = device.get("version_name") or "7.3.7.32"
    env_device = _proto([
        _f_int(1, 1), _f_int(2, 2), _f_str(3, "8662"), _f_str(4, did), _f_str(5, ""), _f_str(6, "!noperm!"),
        _f_int(7, -888888), _f_int(8, -888888), _f_int(9, 3), _f_int(10, -888888), _f_str(11, "!notset!"),
        _f_str(12, "Asia/Shanghai,8"), _f_str(13, "zh_CN"), _f_int(14, 4),
        _f_float(16, 255.24993896484375), _f_float(17, 35.58599090576172), _f_float(18, 3.467449188232422),
        _f_float(19, 3.467449188232422), _f_float(20, 255.1754913330078), _f_float(21, 42.17544174194336),
        _f_str(22, device.get("os_version") or "16"), _f_int(23, 41), _f_int(24, 36),
        _f_int(25, khronos * 1000), _f_int(26, khronos * 1000), _f_int(27, khronos * 1000), _f_int(28, khronos * 1000),
        _f_int(29, -1),
        _f_str(30, device.get("device_type") or "25053RT47C"), _f_str(31, device.get("device_brand") or "Redmi"),
        _f_str(32, device.get("device_type") or "25053RT47C"), _f_str(33, device.get("device_type") or "25053RT47C"),
        _f_str(34, device.get("device_brand") or "Redmi"), _f_str(35, device.get("device_brand") or "Redmi"),
        _f_str(36, device.get("device_brand") or "Redmi"), _f_int(38, 31)])
    env = _proto([
        _f_int(1, 110), _f_int(2, 146331399), _f_int(3, 146331396), _f_int(5, 7),
        _f_str(6, "v04.06.04.03-bugfix"), _f_int(7, 11001), _f_bytes(12, env_device),
        _f_bytes(13, _proto([_f_int(1, khronos), _f_int(2, -2), _f_int(4, 200)])), _f_str(14, version)])
    magic = hex_to_bytes("f7e85ffad7d7dc3bd62ac87057cf6118")
    data = _proto([
        _f_bytes(1, magic), _f_int(2, 3), _f_int(3, _rand32()), _f_str(4, "8662"), _f_str(5, did),
        _f_str(6, "1588093228"), _f_str(7, version), _f_str(8, "v04.06.04-ml-android"), _f_int(9, 67503104),
        _f_bytes(10, _le(320, 8)), _f_int(12, khronos), _f_bytes(13, hash_bytes), _f_bytes(14, q[0:6]),
        _f_bytes(15, _proto([_f_int(1, 111), _f_int(2, 10), _f_int(3, 694367), _f_int(5, 586952199)])),
        _f_str(16, ""), _f_int(17, khronos), _f_bytes(19, sm3(to_bytes(query) + b + to_bytes("none"))),
        _f_str(20, "none"), _f_int(21, 312), _f_bytes(23, env),
        _f_str(24, '{"cmr":16777216,"cmr2":16777216,"un_h":1879194040,"vpn":0,"kd":0,"fkd":3672518972,"pd":-1872573247,"dyn":"","do":0,"tk":true}')])
    hash_random = _rand32()
    xm_random = _rand32()
    sign_key = hex_to_bytes("8ebdfa3806ecc5cee79423e6029ed82540bc2218bb7eaef71cb691f7aa8aa2f5")
    return _pack_medusa(data, q, hash_bytes, khronos, hash_random, xm_random, sign_key, magic,
                        _le(320, 8), 0x35, 3, _LEGACY_CIPHER)


_MOBILE_LICENSE = "646637794"
_MOBILE_KEY = hex_to_bytes("b23c2a470a20d105dc3f8c4438f8272ed46d6c89ffdcdedd5108698d26e9489d")
_MOBILE_MAGIC = hex_to_bytes("2d4b4fca49750d433fb5ae2c226dcc56")
_MOBILE_CIPHER = {
    "box": None,
    "box_hex": _MOBILE_BOX_HEX,
    "rows": [[2, 0, 3, 1], [1, 3, 2, 0], [3, 2, 1, 0], [2, 3, 1, 0]],
    "order": [[0, 9, 14, 15, 4, 13, 2, 7, 8, 1, 6, 3, 12, 5, 10, 11],
              [0, 9, 14, 11, 4, 13, 2, 3, 8, 1, 6, 15, 12, 5, 10, 7],
              [0, 9, 14, 3, 4, 13, 2, 15, 8, 1, 6, 11, 12, 5, 10, 7],
              [0, 9, 14, 15, 4, 13, 2, 3, 8, 1, 6, 11, 12, 5, 10, 7]],
    "initial": [0xbbb5de72, 0xd4638d5b, 0x92a5f73b, 0x89f8a1c9],
    "wire": [6, 5, 3, 4, 2, 7, 1, 0],
    "compact": [1, 7, 3, 6, 2, 0, 4, 5],
    "key": hex_to_bytes(md5_hex(_MOBILE_KEY[0:16])),
    "iv": hex_to_bytes(md5_hex(_MOBILE_KEY[16:])),
}
_MOBILE_STARTED = None
_MOBILE_NONCE = None


def _mobile_started():
    global _MOBILE_STARTED
    if _MOBILE_STARTED is None:
        _MOBILE_STARTED = _now_ms()
    return _MOBILE_STARTED


def _medusa_v5(q, digest, stamp, params):
    global _MOBILE_NONCE
    if _MOBILE_NONCE is None:
        _MOBILE_NONCE = b64_encode(random_bytes(18)).replace("+", "-").replace("/", "_")
    cipher = _MOBILE_CIPHER
    device = _proto([
        _f_int(1, 1), _f_int(2, 2), _f_str(3, params["aid"]), _f_str(4, params["device_id"]),
        _f_str(5, _MOBILE_NONCE), _f_str(6, "!noperm!"),
        _f_str(12, "Asia/Shanghai,8"), _f_str(13, "zh_CN"), _f_str(22, params["os_version"]),
        _f_int(25, _mobile_started()),
        _f_str(30, params["device_type"]), _f_str(31, "HONOR"), _f_str(32, params["device_type"]),
        _f_str(34, "HONOR")])
    env = _proto([
        _f_str(6, "v04.10.03.04-bugfix"), _f_str(8, params["channel"]), _f_bytes(12, device),
        _f_str(14, params["version_name"])])
    flags = bytes(8)
    hash_bytes = _branch0(6, stamp, q, digest, _le(stamp))
    data = _proto([
        _f_bytes(1, _MOBILE_MAGIC), _f_int(2, 5), _f_int(3, _rand32()), _f_str(4, params["aid"]),
        _f_str(5, params["device_id"]), _f_str(6, _MOBILE_LICENSE), _f_str(7, params["version_name"]),
        _f_str(8, "v04.10.03-ml-android"), _f_int(9, 0x040a0300), _f_bytes(10, flags), _f_int(12, stamp),
        _f_bytes(13, hash_bytes), _f_bytes(14, q[0:6]),
        _f_bytes(15, _proto([_f_int(1, 1), _f_int(2, 1), _f_int(3, 1), _f_int(5, 1)])),
        _f_int(17, stamp), _f_str(20, "none"), _f_int(21, 377), _f_bytes(23, env),
        _f_str(24, '{"cmr":16777216,"cmr2":16777216,"un_h":11,"vpn":0,"kd":0,"dyn":"","do":1,"tk":true}')])
    return _pack_medusa(data, q, hash_bytes, stamp, _rand32(), _rand32(), _MOBILE_KEY, _MOBILE_MAGIC,
                        flags, 0xca, 5, cipher)


def sign_mobile(query_base, params, now=None):
    if now is None:
        now = _now_ms()
    stamp = now // 1000
    ts = _le(stamp)
    digest = bytes(16)
    for offset in range(1024):
        query = query_base + "&_rticket=" + str(now + offset)
        q = sm3(query)
        if (_hash_iv(_hash_iv(_hash_iv(0x20230928, q), digest), ts) & 15) != 12:
            continue
        return {"query": query, "headers": {
            "X-Khronos": str(stamp),
            "X-Helios": speck_signature(str(stamp) + "-" + _MOBILE_LICENSE + "-" + params["aid"],
                                        params["aid"], _rand32()),
            "X-Medusa": _medusa_v5(q, digest, stamp, params)}}
    raise ValueError("無法產生紅果播放簽名")


_CRC_TABLE = None


def _crc32(data):
    return zlib.crc32(bytes(data)) & 0xffffffff


def gzip_store(data):
    data = bytes(data)
    out = bytearray(b"\x1f\x8b\x08\x00\x00\x00\x00\x00\x00\xff")
    off = 0
    while True:
        length = min(0xffff, len(data) - off)
        last = 1 if off + length >= len(data) else 0
        out += bytes([last, length & 0xff, (length >> 8) & 0xff, (~length) & 0xff, ((~length) >> 8) & 0xff])
        out += data[off:off + length]
        off += length
        if off >= len(data):
            break
    crc = _crc32(data)
    size = len(data) & 0xffffffff
    out += bytes([crc & 0xff, (crc >> 8) & 0xff, (crc >> 16) & 0xff, (crc >> 24) & 0xff,
                  size & 0xff, (size >> 8) & 0xff, (size >> 16) & 0xff, (size >> 24) & 0xff])
    return bytes(out)


def uuid4():
    chars = "0123456789abcdef"
    out = []
    for i in range(36):
        if i in (8, 13, 18, 23):
            out.append("-")
        elif i == 14:
            out.append("4")
        elif i == 19:
            out.append(chars[int(_random() * 4) + 8])
        else:
            out.append(chars[int(_random() * 16)])
    return "".join(out)


def hex16():
    chars = "0123456789abcdef"
    return "".join(chars[int(_random() * 16)] for _ in range(16))


_API_HOST = "https://api5-normal-sinfonlinea.fqnovel.com"
_MODEL_URL = "https://api5-normal-sinfonlineb.fqnovel.com/reading/bookapi/video_tab/multi_video_model/v1/"
_APP_UA = ("com.phoenix.read/73732 (Linux; U; Android 16; zh_CN; 25053RT47C; "
           "Build/BP2A.250605.031.A3; Cronet/TTNetVersion:04657795 2026-01-23 QuicVersion:c67e9834 2025-09-08)")


def _enc(value):
    if value is True:
        text = "true"
    elif value is False:
        text = "false"
    elif value is None:
        text = "null"
    else:
        text = str(value)
    return urllib.parse.quote(text, safe="-_.~")


def encode_query(params):
    return "&".join(_enc(k) + "=" + _enc(v) for k, v in params.items())


def common_params(device):
    return {
        "iid": device["install_id"],
        "device_id": device["device_id"],
        "ac": "wifi",
        "channel": "update_64",
        "aid": "8662",
        "app_name": "novelread",
        "version_code": "73732",
        "version_name": "7.3.7.32",
        "device_platform": "android",
        "os": "android",
        "ssmix": "a",
        "device_type": "25053RT47C",
        "device_brand": "Redmi",
        "language": "zh",
        "os_api": "36",
        "os_version": "16",
        "manifest_version_code": "73732",
        "resolution": "1280*2772",
        "dpi": "520",
        "update_version_code": "73732",
        "host_abi": "arm64-v8a",
        "dragon_device_type": "phone",
        "pv_player": "73732",
        "compliance_status": "0",
        "need_personal_recommend": "1",
        "player_so_load": "1",
        "is_android_pad_screen": "0",
        "cdid": device.get("cdid") or "",
    }


def biz_param():
    return {
        "video_platform": 1024,
        "need_all_video_definition": True,
        "use_os_player": False,
        "video_id_type": 1,
        "from_video_id": "",
        "device_level": 3,
        "source": 4,
        "need_mp4_align": False,
        "image_shrink_datas_str": "",
        "screen_width_px": "1080",
        "item_map": {},
        "caller_scene": "0",
        "detail_page_version": 0,
        "use_server_dns": False,
        "use_server_dns_scene": "0",
        "expire_strategy": "0",
        "disable_digg_stat": False,
    }


def safe_json(value):
    try:
        return json.loads(value)
    except Exception:
        return None


def is_object(value):
    return isinstance(value, dict)


def as_list(value):
    return value if isinstance(value, list) else []


def as_text(value):
    return "" if value is None else str(value).strip()


class _EmptyResponse(Exception):
    pass


def response_data(res, big_ids=False, whole=False):
    if res.get("error"):
        raise ValueError("網路請求失敗：" + str(res["error"]))
    code = int(res.get("code") or 0)
    if not code or code < 200 or code >= 300:
        raise ValueError("HTTP " + str(code) if code else "網路請求失敗")
    content = res.get("content") or ""
    if not str(content).strip():
        raise _EmptyResponse("接口回傳空正文，請檢查簽名或設備狀態")
    try:
        text = str(content)
        if big_ids:
            text = re.sub(r'("[^"\\]*"\s*:\s*)(\d{16,})(?=\s*[,}\]])', r'\1"\2"', text)
        data = json.loads(text)
    except Exception:
        raise ValueError("回傳非 JSON")
    code2 = data.get("code", data.get("Code"))
    if int(code2 if code2 is not None else -1) != 0:
        raise ValueError("接口 code=" + str(code2) + " " + str(data.get("message") or data.get("Message") or ""))
    return data if whole else (data.get("data") or {})


def signed_post(http, path, device, payload):
    params = common_params(device)
    query = encode_query(params)
    body = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    now = _now_ms()
    khronos = now // 1000
    headers = {
        "User-Agent": _APP_UA,
        "Content-Type": "application/json; charset=UTF-8",
        "Accept": "application/json; charset=utf-8,application/x-protobuf",
        "X-Khronos": str(khronos),
        "X-SS-REQ-TICKET": str(now),
        "X-SS-STUB": md5_hex(body),
        "sdk-version": "2",
        "X-Gorgon": gorgon(body, query, khronos, int(_random() * 0x10000) & 0xffff),
        "X-Helios": helios(khronos),
        "X-Medusa": medusa(query, body, khronos, params),
    }
    res = http(_API_HOST + path + "?" + query, method="POST", headers=headers, data=body.encode("utf-8"))
    return response_data(res)


def signed_get(http, path, device, extra, whole=False):
    params = common_params(device)
    params.update(extra)
    query = encode_query(params)
    now = _now_ms()
    khronos = now // 1000
    headers = {
        "User-Agent": _APP_UA,
        "Accept": "application/json",
        "X-Gorgon": gorgon("", query, khronos, int(_random() * 0x10000) & 0xffff),
        "X-Khronos": str(khronos),
        "X-Helios": helios(khronos),
        "X-Medusa": medusa(query, "", khronos, params),
        "X-SS-REQ-TICKET": str(now),
        "sdk-version": "2",
    }
    res = http(_API_HOST + path + "?" + query, method="GET", headers=headers)
    return response_data(res, big_ids=True, whole=whole)


def bookmall_tabs(http, device, tab_type):
    return signed_get(http, "/reading/bookapi/bookmall/tab/v2/", device,
                      {"tab_type": tab_type, "client_req_type": 1})


def bookmall_more(http, device, params):
    return signed_get(http, "/reading/bookapi/bookmall/cell/change/v1/", device, params)


def search_tab(http, device, query, cursor, count):
    first = not cursor.get("searchId")
    params = {
        "query": query, "search_source": 2, "offset": cursor["offset"], "count": count,
        "bookstore_tab": -1, "use_lynx": False, "from_rs": False, "only_feed": False,
        "only_large_card": False, "is_first_enter_search": first,
    }
    if not first:
        params.update({
            "tab_type": 11, "search_id": cursor["searchId"], "passback": cursor["passback"],
            "last_search_page_query": query,
        })
    return signed_get(http, "/reading/bookapi/search/tab/v1/", device, params, whole=True)


def series_content(http, device, series_id, cursor=None):
    if cursor:
        data = signed_get(http, "/reading/bookapi/bookmall/cell/change/v", device,
                          dict({"filter_ids": series_id}, **cursor))
        if not is_object(data.get("cell_view")):
            raise ValueError("系列回應缺少分頁資料")
        return data["cell_view"]
    data = signed_get(http, "/reading/bookapi/plan/v", device, {
        "scene": 10, "from": "single_col_same_ip_series", "book_id": series_id, "filter_ids": series_id})
    if not isinstance(data, list):
        raise ValueError("系列回應格式無效")
    for cell in data:
        videos = as_list(cell.get("video_data")) if is_object(cell) else []
        if any(is_object(v) and int(v.get("season_index") or 0) > 0 for v in videos):
            return cell
    return None


def landpage_panel(http, device, scene):
    return signed_post(http, "/reading/distribution/category/landpage/v1/", device, {
        "req_scene": scene, "need_selector_panel": False, "req_type": "only_panel"})


def landpage_content(http, device, scene, select_items, offset, limit, session_id):
    return signed_post(http, "/reading/distribution/category/landpage/v1/", device, {
        "filter_ids": "", "req_scene": scene, "offset": offset, "need_selector_panel": False,
        "limit": limit, "select_items": select_items, "session_id": session_id or "",
        "req_type": "only_content", "client_req_type": 3 if offset == 0 else 2})


def video_detail(http, device, series_id):
    data = signed_post(http, "/novel/player/video_detail/v1/", device, {
        "series_id": str(series_id), "need_video_detail_info": True, "biz_param": biz_param()})
    vd = data.get("video_data") or {}
    if not is_object(vd) or not isinstance(vd.get("video_list"), list):
        raise ValueError("詳情缺少分集")
    return vd


def audio_detail(http, device, book_id):
    return signed_get(http, "/reading/bookapi/audio/detail/", device, {"book_id": book_id})


def audio_directory(http, book_id):
    url = "https://fanqienovel.com/api/reader/directory/detail?bookId=" + str(book_id)
    data = response_data(http(url, method="GET"))
    if not isinstance(data.get("chapterListWithVolume"), list):
        raise ValueError("缺少章節目錄")
    out = []
    for volume in data["chapterListWithVolume"]:
        out.extend(as_list(volume))
    return out


def audio_stream(http, device, book_id, item_id, tone_id):
    data = signed_get(http, "/reading/reader/audio/playinfo/", device, {
        "book_id": book_id, "item_ids": item_id, "tone_id": tone_id, "is_local_book": False})
    entry = None
    for item in as_list(data):
        if is_object(item) and as_text(item.get("item_id")) == item_id:
            entry = item
            break
    model = safe_json(entry.get("video_model")) if entry else None
    if not is_object(model) or model.get("media_type") != "audio":
        raise ValueError("該章節未提供音訊")
    for track in as_list(model.get("video_list")):
        if not is_object(track):
            continue
        codec = as_text((track.get("video_meta") or {}).get("codec_type"))
        if codec not in ("aac", "opus"):
            continue
        enc = track.get("encrypt_info") or {}
        encrypt = enc.get("encrypt")
        method = enc.get("encryption_method")
        kid = enc.get("kid") or ""
        spade = enc.get("spade_a") or ""
        encrypted = entry.get("is_encrypt") or encrypt
        if encrypted and (method != "cenc-aes-ctr" or not re.match(r"^[0-9a-f]{32}$", str(kid), re.I) or not spade):
            continue
        url = playback_url(track.get("main_url") or track.get("backup_url"), model.get("key_seed"))
        if not re.match(r"^https?://[^/\s]+\S*$", url or "", re.I):
            continue
        vid = as_text(entry.get("vid") or model.get("video_id"))
        if not encrypted:
            return {"url": url, "vid": vid}
        return {"url": url, "vid": vid, "kid": kid, "key": to_hex(derive_content_key(spade))}
    raise ValueError("紅果 App 未提供相容的音訊來源")


def video_model(http, device, vid):
    params = common_params(device)
    iid = params.pop("iid")
    device_id = params.pop("device_id")
    cdid = params.pop("cdid")
    version = "73932"
    for key in ("version_code", "manifest_version_code", "update_version_code", "pv_player"):
        params[key] = version
    params["version_name"] = "7.3.9.32"
    params["iid"] = iid
    params["cdid"] = cdid
    params["device_id"] = device_id
    params.update({
        "video_id": vid, "video_id_type": "0", "device_level": "1",
        "need_all_video_definition": "1", "need_mp4_align": "0", "use_os_player": "0",
        "video_platform": "1024", "source": "0", "from_video_id": "",
    })
    signed = sign_mobile(encode_query(params), params)
    res = http(_MODEL_URL + "?" + signed["query"], method="GET", redirect=False, headers={
        "User-Agent": _APP_UA.replace("/73732 ", "/71332 "),
        "Accept-Language": "zh-CN,zh;q=0.9",
        **signed["headers"],
    })
    data = response_data(res)
    container = data.get("video_model_data") or data
    entry = (container.get(vid) or {}).get("video_model") if is_object(container) else None
    model = safe_json(entry) if isinstance(entry, str) else entry
    if not is_object(model):
        raise ValueError("播放模型缺少指定集數")
    return model


def stream_tracks(video_list):
    out = []
    for item in as_list(video_list):
        if not is_object(item):
            continue
        meta = item.get("video_meta") or item.get("videoMeta") or item
        codec = as_text(meta.get("codec_type") or meta.get("codecType")).lower()
        if not re.match(r"^(bytevc1|h265|hevc|hvc1|hev1|h264|avc1?)$", codec):
            continue
        url = item.get("main_url") or item.get("backup_url") or item.get("backup_url_1") or \
            (as_list(item.get("backup_url_list"))[0] if as_list(item.get("backup_url_list")) else "")
        if not url:
            continue
        width = int(meta.get("vwidth") or meta.get("width") or 0)
        height = int(meta.get("vheight") or meta.get("height") or 0)
        definition = re.match(r"\d+", str(meta.get("definition") or item.get("definition") or ""))
        quality = int(definition.group(0)) if definition else 0
        if not quality:
            quality = min(width, height) if (width and height) else (height or width)
        enc = item.get("encrypt_info") or item
        kid = enc.get("kid") or ""
        spade = enc.get("spade_a") or ""
        if not quality or ((enc.get("encrypt") or kid or spade) and not (kid and spade)):
            continue
        out.append({"url": url, "quality": quality, "kid": kid, "spade": spade})
    return out


def pick_stream(model, want_quality):
    tracks = stream_tracks(model.get("video_list"))
    if not tracks:
        return None
    try:
        wanted = int(str(want_quality), 10)
    except Exception:
        wanted = 0

    def rank(track):
        return abs(track["quality"] - wanted) if wanted else -track["quality"]

    track = min(tracks, key=rank)
    url = playback_url(track["url"], model.get("key_seed"))
    if not re.match(r"^https?://[^/\s]+\S*$", url or "", re.I):
        raise ValueError("播放模型未提供媒體地址")
    return {"url": url, "kid": track["kid"],
            "key": to_hex(derive_content_key(track["spade"])) if track["kid"] else ""}


def compatible_model(http, model):
    fallback = model.get("fallback_api")
    url = as_text((fallback or {}).get("fallback_api") if is_object(fallback) else fallback)
    match = re.match(r"^(https://(?:[a-z0-9-]+\.)*(?:snssdk|fqnovel)\.com/[^?#\s]*)\?([^#\s]+)$", url, re.I)
    if not match:
        return None
    parts = [p for p in match.group(2).split("&") if not re.match(r"^(codec_type|force_codec)=", p)]
    parts.append("codec_type=1")
    res = http(match.group(1) + "?" + "&".join(parts), method="GET", redirect=False,
               headers={"User-Agent": _APP_UA, "Accept": "application/json"})
    if res.get("error") or int(res.get("code") or 0) != 200:
        return None
    outer = safe_json(res.get("content"))
    inner = (outer or {}).get("video_info") if is_object(outer) else None
    compatible = (inner or {}).get("data") if is_object(inner) else None
    if not is_object(outer) or not is_object(inner):
        return None
    if int(outer.get("Code", outer.get("code")) or 0) != 0 or int(inner.get("Code", inner.get("code")) or 0) != 0:
        return None
    if not compatible or not compatible.get("video_id") or compatible.get("video_id") != model.get("video_id"):
        return None
    if abs(float(compatible.get("video_duration") or 0) - float(model.get("video_duration") or 0)) > 0.5:
        return None
    return compatible


def clear_key_license(kid_hex, key_hex):
    if not re.match(r"^[0-9a-f]{32}$", str(kid_hex), re.I) or not re.match(r"^[0-9a-f]{32}$", str(key_hex), re.I):
        raise ValueError("無效的 ClearKey")
    return json.dumps({
        "keys": [{"kty": "oct", "k": b64url_encode(hex_to_bytes(key_hex)),
                  "kid": b64url_encode(hex_to_bytes(kid_hex))}],
        "type": "temporary"}, separators=(",", ":"))


_REG_MODEL = "22127RK46C"
_REG_VC = "73732"
_REG_VN = "7.3.7.32"
_REG_UA = "com.phoenix.read/" + _REG_VC + " (Linux; U; Android 14; zh_CN; " + _REG_MODEL + "; Build/UKQ1.230804.001)"


def register_device(http):
    now = _now_ms()
    openudid = hex16()
    cdid = uuid4()
    clientudid = uuid4()
    params = {
        "tt_data": "a", "os_api": "34", "device_type": _REG_MODEL, "ssmix": "a",
        "manifest_version_code": _REG_VC, "dpi": "420", "version_name": _REG_VN,
        "ts": now // 1000, "cpu_support64": "true", "app_type": "normal", "appTheme": "light",
        "ac": "wifi", "host_abi": "arm64-v8a", "update_version_code": _REG_VC,
        "channel": "huawei_8662_64", "_rticket": now, "device_platform": "android",
        "version_code": _REG_VC, "cdid": cdid, "os": "android", "is_android_pad": "0",
        "openudid": openudid, "package": "com.phoenix.read", "resolution": "1080*2186",
        "os_version": "14", "language": "zh", "device_brand": "Redmi",
        "need_personal_recommend": "1", "aid": "8662", "minor_status": "0",
        "app_name": "novelread", "mcc_mnc": "46007",
    }
    body = {
        "magic_tag": "ss_app_log",
        "header": {
            "display_name": "红果免费短剧", "update_version_code": _REG_VC,
            "manifest_version_code": _REG_VC, "aid": 8662, "channel": "huawei_8662_64",
            "package": "com.phoenix.read", "app_version": _REG_VN, "version_code": _REG_VC,
            "sdk_version": "3.7.3-rc.53-douyin-bugfix", "sdk_target_version": 29,
            "os": "Android", "os_version": "14", "os_api": 34, "device_model": _REG_MODEL,
            "device_brand": "Redmi", "device_manufacturer": "Xiaomi", "device_category": "phone",
            "cpu_abi": "arm64-v8a", "release_build": uuid4(), "density_dpi": 420,
            "display_density": "420dpi", "resolution": "1080x2186", "language": "zh",
            "timezone": 8, "access": "wifi", "carrier": "CHINA MOBILE", "mcc_mnc": "46007",
            "rom": "MIUI", "rom_version": "V816.0.16.0.UMKCNXM", "openudid": openudid,
            "clientudid": clientudid, "region": "CN", "tz_name": "Asia/Shanghai",
            "tz_offset": 28800, "sim_region": "cn", "not_request_sender": 0,
        },
        "_gen_time": now,
    }
    packed = gzip_store(json.dumps(body, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
    payload = tt_encrypt(packed)
    url = "https://log.snssdk.com/service/2/device_register/?" + encode_query(params)
    res = http(url, method="POST", headers={
        "Content-Type": "application/octet-stream;tt-data=a", "User-Agent": _REG_UA}, data=payload)
    if res.get("error"):
        raise ValueError("註冊失敗：" + str(res["error"]))
    code = int(res.get("code") or 0)
    if not code or code < 200 or code >= 300:
        raise ValueError("註冊失敗 HTTP " + str(code))
    data = safe_json(res.get("content"))
    if not is_object(data):
        raise ValueError("註冊回傳非 JSON")
    device_id = str(data.get("device_id_str") or data.get("device_id") or "")
    install_id = str(data.get("install_id_str") or data.get("install_id") or "")
    if not re.match(r"^\d{6,}$", device_id) or not re.match(r"^\d{6,}$", install_id):
        raise ValueError("註冊未回傳有效設備身分")
    return {"device_id": device_id, "install_id": install_id, "cdid": cdid}


_PANEL_SNAPSHOT = [['genre|全部体裁|short_play:真人剧,comic_series:漫剧,ai_series:AI剧', 'category_dim_theme|全部主题|cate_9165:动作,cate_9163:冒险,cate_9164:魔幻,cate_5000:爱情,cate_5001:家庭,cate_5002:家族,cate_5003:萌宝,cate_5004:悬疑,cate_5006:志怪,cate_5007:古装,cate_5008:玄幻,cate_5009:奇幻,cate_5010:成长,cate_5011:传奇,cate_5021:年代,cate_5022:都市,cate_5023:青春,cate_5024:喜剧,cate_5025:科幻,cate_5026:灾难,cate_5028:战争,cate_5029:综艺,cate_5030:剧情,cate_5031:逆袭,cate_5132:惊悚,cate_5133:恐怖', 'category_dim_role|全部设定|cate_5221:女强,cate_5222:女尊,cate_5223:神女,cate_5224:大男主,cate_5225:男强,cate_5226:忠诚男主,cate_5227:天之骄子,cate_5228:热血硬汉,cate_5229:群像,cate_5241:团宠,cate_5242:大叔,cate_5243:美强惨,cate_5244:小人物,cate_5245:反派主角,cate_5246:霸道男主,cate_5247:市井英雄,cate_5248:商界女王,cate_5250:直爽女主,cate_5260:大女主,cate_5201:战神,cate_5203:神豪,cate_5204:龙王,cate_5206:总裁,cate_5207:业界精英,cate_5208:医生,cate_5209:法医,cate_5210:律师,cate_5211:特工,cate_5213:黑客,cate_5214:厨师,cate_5215:厨娘,cate_5216:拳击手,cate_5217:主播,cate_5218:豪门千金,cate_5219:落魄千金,cate_5220:真假千金,cate_5235:侠客,cate_5236:剑客,cate_5237:刺客杀手,cate_5239:武林高手,cate_5261:少帅,cate_5262:军阀,cate_5263:书生,cate_5265:女帝,cate_5266:将军,cate_5268:世子,cate_5284:学神,cate_5285:天才,cate_5286:神童,cate_5287:天生灵骨,cate_5288:锦鲤,cate_5322:狼人,cate_5323:萌宠,cate_5291:傲娇,cate_5292:高冷禁欲,cate_5293:嘴硬心软,cate_5294:甜妹,cate_5295:御姐,cate_5296:古灵精怪,cate_5297:乖乖女,cate_5298:大小姐,cate_5299:灰姑娘,cate_5324:腹黑,cate_5325:毒舌,cate_5326:病娇,cate_5327:高冷,cate_5328:戏精,cate_5329:作精,cate_5330:痞少,cate_5274:宠夫,cate_5275:宠妻,cate_5276:年龄差,cate_5277:年上,cate_5278:年下,cate_5279:白月光,cate_5280:欢喜冤家,cate_5300:姐弟恋,cate_5332:强强联合,cate_5336:极品亲戚,cate_5337:后妈', 'category_dim_epoch|全部背景|cate_5311:未来,cate_5312:架空,cate_5338:现代,cate_5339:古代,cate_5340:民国,cate_5314:乡村,cate_5315:校园,cate_5301:职场,cate_5302:商界,cate_5305:黑道,cate_5318:豪门,cate_5319:世家,cate_5320:娱乐圈,cate_5306:星际,cate_5308:游戏世界,cate_5309:荒岛,cate_5310:异界,cate_5331:方言,cate_9455:英语,cate_9456:德语,cate_9457:法语,cate_9458:日语,cate_9459:韩语,cate_9474:小语种', 'sort|全部推荐|online_time:最新上架,hot_score:最高热度,hot_collect:最高收藏', 'gender|全部受众|1:男频,0:女频', 'online_time|全部时间|days_7:7天内上新,days_14:14天内上新,days_30:30天内上新,days_90:90天内上新'], ['genre|全部体裁|short_play:真人剧,comic_series:漫剧,ai_series:AI剧', 'category_dim_theme|全部主题|cate_3:现代言情,cate_19:系统,cate_36:重生,cate_37:穿越,cate_43:娱乐圈,cate_165:悬疑推理,cate_261:都市日常,cate_266:马甲,cate_303:喜剧,cate_316:剧情,cate_382:穿书,cate_395:现言甜宠,cate_439:古风言情,cate_466:闪婚,cate_475:破镜重圆,cate_598:异能,cate_739:逆袭,cate_842:追妻,cate_1007:传承觉醒,cate_1008:虐恋,cate_1013:玄幻仙侠,cate_1020:奇幻爱情,cate_1022:年代爱情,cate_1024:家庭伦理,cate_1038:战神归来,cate_1040:亲情,cate_1041:奇幻脑洞,cate_1043:无敌神医,cate_1044:赘婿逆袭,cate_1047:古风权谋,cate_1048:女性成长,cate_1050:暗恋成真,cate_1051:打脸虐渣,cate_1053:豪门恩怨', 'category_dim_role|全部设定|cate_20:神豪,cate_28:萌宝,cate_84:皇后,cate_85:王妃,cate_94:团宠,cate_378:女帝,cate_387:青梅竹马,cate_470:替身,cate_737:大叔,cate_760:大女主,cate_844:真假千金,cate_901:龙王,cate_1010:小人物,cate_1045:强者回归,cate_1046:天下无敌,cate_1049:强强联合,cate_1052:欢喜冤家', 'category_dim_epoch|全部背景|cate_4:校园,cate_11:乡村,cate_127:职场,cate_273:历史古代,cate_308:古装,cate_390:民国', 'sort|全部推荐|online_time:最新上架,hot_score:最高热度,hot_collect:最高收藏', 'gender|全部受众|1:男频,0:女频', 'online_time|全部时间|days_7:7天内上新,days_14:14天内上新,days_30:30天内上新,days_90:90天内上新'], ['genre|全部体裁|short_play:真人剧,comic_series:漫剧,ai_series:AI剧', 'category_dim_art_style|全部画风|cate_5415:3D漫,cate_5416:2D漫,cate_5417:表情包', 'category_dim_theme|全部主题|cate_9281:动作,cate_9280:综艺,cate_5876:爱情,cate_5891:年代,cate_5898:逆袭,cate_5912:传奇,cate_5916:成长,cate_5924:家庭,cate_5931:家族,cate_5936:萌宝,cate_5939:悬疑,cate_5949:惊悚,cate_5951:恐怖,cate_5955:志怪,cate_5958:古装,cate_5967:玄幻,cate_5975:奇幻,cate_5981:都市,cate_5987:青春,cate_5991:喜剧,cate_5994:科幻,cate_5998:灾难,cate_6003:冒险,cate_6014:战争,cate_6019:剧情,cate_6023:魔幻', 'category_dim_role|全部设定|cate_6171:大女主,cate_6172:女强,cate_6173:神女,cate_6174:大男主,cate_6175:男强,cate_6176:忠诚男主,cate_6177:热血硬汉,cate_6178:群像,cate_6179:团宠,cate_6180:大叔,cate_6181:小人物,cate_6182:反派主角,cate_6183:霸道男主,cate_6184:市井英雄,cate_6185:商界女王,cate_6186:直爽女主,cate_6188:废柴,cate_6190:银发,cate_9311:天之骄子,cate_9312:女尊,cate_9313:美强惨,cate_6192:战神,cate_6194:神豪,cate_6195:龙王,cate_6197:总裁,cate_6198:业界精英,cate_6199:医生,cate_6200:黑客,cate_6201:厨师,cate_6202:厨娘,cate_6203:拳击手,cate_6204:主播,cate_6205:豪门千金,cate_6206:落魄千金,cate_6207:真假千金,cate_6208:少帅,cate_6209:军阀,cate_6211:侠客,cate_6212:剑客,cate_6213:刺客杀手,cate_6215:武林高手,cate_6220:学神,cate_6221:天才,cate_6222:神童,cate_6223:天生灵骨,cate_6224:锦鲤,cate_6226:狼人,cate_6227:萌宠,cate_6228:诡物,cate_6229:异族,cate_6230:骑士,cate_6231:龙族,cate_6232:落魄弃少,cate_6233:神怪,cate_6234:毒士,cate_6236:变异体,cate_6237:女帝,cate_6238:包租公,cate_9317:世子,cate_9318:书生,cate_9321:将军,cate_9322:律师,cate_9323:法医,cate_9325:仵作,cate_9326:特工,cate_6240:腹黑,cate_6241:毒舌,cate_6242:病娇,cate_6243:高冷,cate_6244:戏精,cate_6245:作精,cate_6246:痞少,cate_6247:高冷禁欲,cate_6248:嘴硬心软,cate_6249:御姐,cate_6250:古灵精怪,cate_6251:乖乖女,cate_6252:大小姐,cate_6253:灰姑娘,cate_6254:反差萌,cate_6255:反差强,cate_9314:傲娇,cate_9315:杀伐果断,cate_9316:甜妹,cate_6257:姐弟恋,cate_6260:宠夫,cate_6261:宠妻,cate_6262:年龄差,cate_6263:年上,cate_6264:年下,cate_6265:白月光,cate_6266:欢喜冤家,cate_6267:强强联合,cate_6271:极品亲戚,cate_6272:后妈', 'category_dim_epoch|全部背景|cate_6274:现代,cate_6275:古代,cate_6276:民国,cate_6278:未来,cate_6279:架空,cate_6282:乡村,cate_6283:校园,cate_6287:豪门,cate_6288:世家,cate_6289:娱乐圈,cate_6290:职场,cate_6291:商界,cate_6292:黑道,cate_6293:公路,cate_6295:星际,cate_6297:游戏世界,cate_6298:荒岛,cate_6299:异界,cate_6301:乱世,cate_6302:秘境,cate_6303:废土,cate_6305:极寒,cate_6306:高温,cate_6307:洪荒,cate_6308:多朝代,cate_9333:海洋,cate_9334:野外,cate_6310:方言,cate_9461:英语,cate_9462:德语,cate_9463:法语,cate_9464:日语,cate_9465:韩语,cate_9473:小语种', 'sort|全部推荐|online_time:最新上架,hot_score:最高热度,hot_collect:最高收藏', 'gender|全部受众|1:男频,0:女频', 'creation_status|全部状态|creation_status_0:已完结,creation_status_1:连载中', 'online_time|全部时间|days_7:7天内上新,days_14:14天内上新,days_30:30天内上新,days_90:90天内上新'], ['genre|全部体裁|short_play:真人剧,comic_series:漫剧,ai_series:AI剧', 'category_dim_theme|全部主题|cate_316:剧情,cate_68:末世,cate_1092:科幻,cate_6:奇幻,cate_1182:冒险,cate_936:豪门,cate_7:玄幻,cate_755:脑洞', 'category_dim_role|全部设定|cate_739:逆袭,cate_756:反转,cate_36:重生,cate_37:穿越,cate_29:总裁,cate_19:系统,cate_43:娱乐圈,cate_598:异能', 'category_dim_epoch|全部背景|cate_11:乡村,cate_79:年代,cate_4:校园,cate_390:民国,cate_1:都市,cate_127:职场,cate_452:架空,cate_599:异界,cate_758:古代', 'sort|全部推荐|online_time:最新上架,hot_score:最高热度,hot_collect:最高收藏', 'gender|全部受众|1:男频,0:女频', 'online_time|全部时间|days_7:7天内上新,days_14:14天内上新,days_30:30天内上新,days_90:90天内上新']]


_WEB_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
           "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36")
_PAGE_SIZE = 24
_LANDPAGE_SIZE = 18
_AUDIO_TAB = 5
_CLASS_IDS = ["find", "drama", "comic", "ai"]
_CLASS_NAMES = ["找剧", "真人剧", "漫剧", "AI剧"]
_CLASS_SCENES = ["default", "short_play", "comic_series", "ai_series"]
_FEED_TABS = {"find": 8, "drama": 38}
_BUILTIN_DEVICE = {"device_id": "885566879363322", "install_id": "2715154228447593",
                   "cdid": "97be74ec-867a-46a6-9d2b-42d6b52b7aa1"}
_AUDIO_EPISODE = re.compile(r"^audio:(\d{6,}):(\d{6,}):(\d+)$")


def _snapshot_panel(rows):
    out = []
    for row in rows:
        parts = row.split("|")
        row_name = parts[1] if len(parts) > 1 else ""
        name = row_name[2:] if row_name.startswith("全部") and len(row_name) > 2 else row_name
        value = [{"n": "全部", "v": ""}]
        for item in "|".join(parts[2:]).split(","):
            i = item.find(":")
            if i > 0:
                value.append({"v": item[:i], "n": item[i + 1:]})
        out.append({"key": parts[0], "name": name, "value": value})
    return out


def _safe_label(value):
    return re.sub(r"[$#]", " ", str(value or "")).strip() or "正片"


def _series_id_of(value):
    raw = str(value or "").strip()
    match = re.search(r"(?:^|[?&/])(?:series_id=)?(\d{6,})(?:$|[&/?#])", raw) or re.match(r"^(\d{6,})$", raw)
    return match.group(1) if match else ""


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class Spider(BaseSpider):
    def __init__(self):
        super(Spider, self).__init__()
        self.siteUrl = "https://hongguoduanju.com"
        self.siteName = "红果短剧"
        self.options = {}
        self._ctx = ssl.create_default_context()
        self._ctx.check_hostname = False
        self._ctx.verify_mode = ssl.CERT_NONE
        self._cj = http.cookiejar.CookieJar()
        self._opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self._cj),
            urllib.request.HTTPSHandler(context=self._ctx))
        self._opener_nr = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self._cj),
            urllib.request.HTTPSHandler(context=self._ctx),
            _NoRedirect())

    def init(self, extend=""):
        if isinstance(extend, dict):
            self.options = extend
        elif extend:
            parsed = safe_json(extend)
            self.options = parsed if isinstance(parsed, dict) else {}
        return True

    def getName(self):
        return "红果短剧"

    def isVideoFormat(self, url):
        low = str(url or "").lower()
        return any(k in low for k in (".m3u8", ".mp4", ".flv", ".mkv", ".ts", ".mpd"))

    def manualVideoCheck(self):
        return False

    def destroy(self):
        self.options = {}

    def _http(self, url, method="GET", headers=None, data=None, redirect=True, retries=1):
        req_headers = dict(headers or {})
        if not any(str(k).lower() == "user-agent" for k in req_headers):
            req_headers["User-Agent"] = _WEB_UA
        body = data
        if isinstance(body, str):
            body = body.encode("utf-8")
        opener = self._opener if redirect else self._opener_nr
        last_error = ""
        for attempt in range(int(retries) + 1):
            req = urllib.request.Request(url, data=body if method.upper() in ("POST", "PUT") else None,
                                         headers=req_headers, method=method.upper())
            try:
                with opener.open(req, timeout=15) as resp:
                    raw = resp.read()
                    enc = resp.headers.get("Content-Encoding", "") if resp.headers else ""
                    if raw[:2] == b"\x1f\x8b" or enc == "gzip":
                        try:
                            raw = gzip.decompress(raw)
                        except Exception:
                            pass
                    elif enc == "deflate":
                        try:
                            raw = zlib.decompress(raw)
                        except Exception:
                            raw = zlib.decompress(raw, -zlib.MAX_WBITS)
                    return {"code": resp.getcode(), "content": raw.decode("utf-8", "ignore"), "error": ""}
            except urllib.error.HTTPError as e:
                try:
                    raw = e.read()
                    if raw[:2] == b"\x1f\x8b":
                        raw = gzip.decompress(raw)
                    content = raw.decode("utf-8", "ignore")
                except Exception:
                    content = ""
                return {"code": e.code, "content": content, "error": ""}
            except Exception as e:
                last_error = str(e)
                if attempt < retries:
                    time.sleep(0.4)
        return {"code": 0, "content": "", "error": last_error}

    def _cache_get(self, key):
        cached = _HG_MEM.get(key)
        if cached is not None:
            return cached
        try:
            raw = self.getCache(key)
        except Exception:
            return None
        if raw is None or raw == "":
            return None
        if isinstance(raw, (dict, list)):
            return raw
        try:
            value = json.loads(raw)
        except Exception:
            return None
        _HG_MEM[key] = value
        return value

    def _cache_set(self, key, value):
        _HG_MEM[key] = value
        try:
            self.setCache(key, json.dumps(value, ensure_ascii=False))
        except Exception:
            pass

    def _cache_drop(self, key):
        _HG_MEM.pop(key, None)
        try:
            self.delCache(key)
        except Exception:
            pass

    def _cached(self, key, loader):
        value = self._cache_get(key)
        if value is not None:
            return value
        result = loader()
        self._cache_set(key, result)
        return result

    def _normalize_device(self, d):
        if not is_object(d):
            return None
        device_id = as_text(d.get("device_id"))
        install_id = as_text(d.get("install_id"))
        if re.match(r"^\d{6,}$", device_id) and re.match(r"^\d{6,}$", install_id):
            return {"device_id": device_id, "install_id": install_id, "cdid": as_text(d.get("cdid"))}
        return None

    def _load_device(self):
        return self._normalize_device(self._cache_get("hongguo_device")) or dict(_BUILTIN_DEVICE)

    def _with_device(self, call):
        device = self._load_device()
        try:
            return call(device)
        except _EmptyResponse as first_error:
            try:
                fresh = register_device(self._http)
            except Exception as reg_error:
                raise ValueError(str(first_error)[:100] + "；設備更新失敗：" + str(reg_error)[:100])
            result = call(fresh)
            self._cache_set("hongguo_device", fresh)
            return result

    def _owner(self):
        device = self._load_device()
        return md5_hex(json.dumps([self.siteUrl, "guest", device["device_id"], device["install_id"]],
                                  ensure_ascii=False, separators=(",", ":")))

    def _cursor_page(self, state_key, page, initial, load):
        cursors = self._cache_get(state_key)
        if not isinstance(cursors, list) or page == 1:
            cursors = [initial]
        index = min(page - 1, len(cursors) - 1)
        cursor = cursors[index]
        while cursor:
            r = load(cursor)
            index += 1
            cursors = cursors[:index] + [r["next"]]
            self._cache_set(state_key, cursors)
            if index == page:
                if r["next"]:
                    return {"list": r["list"], "pagecount": page + 1}
                return {"list": r["list"], "pagecount": page if r["list"] else max(1, page - 1)}
            cursor = r["next"]
        return {"list": [], "pagecount": max(1, page - 1)}

    def _load_panel(self, scene):
        data = landpage_panel(self._http, self._load_device(), scene)
        rows = []
        for row in as_list(data.get("selector_rows")):
            if not is_object(row):
                continue
            rtype = as_text(row.get("type"))
            row_name = as_text(row.get("row_name"))
            if not re.match(r"^[a-z0-9_]+$", rtype) or not row_name:
                continue
            name = row_name[2:] if row_name.startswith("全部") and len(row_name) > 2 else row_name
            value = [{"n": "全部", "v": ""}]
            for item in as_list(row.get("items")):
                if not is_object(item):
                    continue
                iid = as_text(item.get("selector_item_id"))
                label = as_text(item.get("show_name"))
                if not iid or not label:
                    continue
                if any(v["v"] == iid for v in value):
                    continue
                value.append({"v": iid, "n": label})
            if len(value) > 1:
                rows.append({"key": rtype, "name": name, "value": value})
        if not rows:
            raise ValueError("篩選資料為空")
        return rows

    def _panel_for(self, scene):
        cached = self._cache_get("panel:" + scene)
        if isinstance(cached, list) and cached:
            return cached
        idx = _CLASS_SCENES.index(scene) if scene in _CLASS_SCENES else 0
        return _snapshot_panel(_PANEL_SNAPSHOT[idx])

    def _ensure_panels(self):
        for scene in _CLASS_SCENES:
            existing = self._cache_get("panel:" + scene)
            if isinstance(existing, list) and existing:
                continue
            try:
                rows = self._load_panel(scene)
                if rows:
                    self._cache_set("panel:" + scene, rows)
            except Exception:
                pass

    def _picture(self, raw_url):
        url = as_text(raw_url)
        if not url:
            return ""
        if url.startswith("//"):
            url = "https:" + url
        elif url.startswith("/"):
            url = self.siteUrl + url
        elif not url.startswith("http"):
            url = self.siteUrl + "/" + url
        return url

    def _to_card(self, item):
        if not is_object(item):
            return None
        series_id = as_text(item.get("series_id"))
        if not re.match(r"^\d+$", series_id):
            return None
        remarks = as_text(item.get("episode_right_text")) or (
            "全" + str(item.get("episode_cnt")) + "集" if item.get("episode_cnt") else "")
        card = {
            "vod_id": series_id,
            "vod_name": as_text(item.get("series_name") or item.get("series_title")) or "紅果短劇",
            "vod_remarks": "蝴蝶影视 | " + remarks if remarks else "蝴蝶影视",
            "style": {"type": "rect", "ratio": 0.7},
        }
        pic = self._picture(item.get("series_cover"))
        if pic:
            card["vod_pic"] = pic
        return card

    def _landpage_card(self, v):
        if not is_object(v):
            return None
        series_id = as_text(v.get("series_id"))
        if not re.match(r"^\d+$", series_id):
            return None
        hot_parts = []
        for entry in as_list(v.get("sub_title_list")):
            t = as_text(entry.get("content")) if is_object(entry) else ""
            if t:
                hot_parts.append(t)
        hot = " · ".join(hot_parts)
        eps = "全" + str(v.get("episode_cnt")) + "集" if v.get("episode_cnt") and str(v.get("episode_cnt")) != "0" else ""
        remarks = (eps + " · " + hot) if (eps and hot) else (eps or hot)
        card = {
            "vod_id": series_id,
            "vod_name": as_text(v.get("title")) or "紅果短劇",
            "vod_remarks": "蝴蝶影视 | " + remarks if remarks else "蝴蝶影视",
            "style": {"type": "rect", "ratio": 0.7},
        }
        pic = self._picture(v.get("cover"))
        if pic:
            card["vod_pic"] = pic
        return card

    def _audio_card(self, book, book_id):
        author = as_text(book.get("author"))
        card = {
            "vod_id": "audio:" + book_id,
            "vod_name": as_text(book.get("book_name")),
            "vod_remarks": "蝴蝶影视 | " + author if author else "蝴蝶影视",
            "style": {"type": "rect", "ratio": 1},
        }
        pic = self._picture(book.get("audio_thumb_url_hd") or book.get("thumb_url"))
        if pic:
            card["vod_pic"] = pic
        return card

    def _feed_cards(self, cells):
        out = []
        for cell in as_list(cells):
            videos = as_list(cell.get("video_data")) if is_object(cell) else []
            if not videos:
                continue
            v = videos[0]
            if not is_object(v):
                continue
            card = self._to_card({
                "series_id": v.get("series_id"), "series_name": v.get("title"),
                "series_cover": v.get("cover"), "episode_cnt": v.get("episode_cnt"),
                "episode_right_text": v.get("rec_text")})
            if card:
                out.append(card)
        return out

    def _audio_cards(self, cells):
        seen = set()
        out = []

        def collect(cell):
            if not is_object(cell):
                return
            for book in as_list(cell.get("book_data")):
                if not is_object(book):
                    continue
                book_id = as_text(book.get("book_id"))
                if re.match(r"^\d{6,}$", book_id) and as_text(book.get("book_name")) and book_id not in seen:
                    seen.add(book_id)
                    out.append(self._audio_card(book, book_id))
            for sub in as_list(cell.get("cell_data")):
                collect(sub)

        for cell in as_list(cells):
            collect(cell)
        return out

    def _load_feed(self, tab_type):
        data = bookmall_tabs(self._http, self._load_device(), tab_type)
        tab = None
        for entry in as_list(data.get("tab_item")):
            if is_object(entry) and int(entry.get("tab_type") or 0) == tab_type:
                tab = entry
                break
        box = None
        for cell in as_list((tab or {}).get("cell_data")):
            if not is_object(cell):
                continue
            subs = as_list(cell.get("cell_data"))
            if any(is_object(s) and as_list(s.get("video_data")) for s in subs):
                box = cell
                break
        if box is None:
            raise ValueError("推薦流為空")
        base = {
            "cell_id": as_text(box.get("cell_id_str") or box.get("cell_id")),
            "tab_type": tab_type,
            "session_id": as_text(tab.get("session_id")),
            "client_template": as_text(tab.get("client_template")),
            "tab_version": as_text(tab.get("tab_version")),
            "version_tag": as_text(tab.get("version_tag")),
            "show_type": as_text(box.get("show_type")),
        }
        return {"base": base, "list": self._feed_cards(box.get("cell_data")),
                "next": int(box.get("next_offset") or 0), "more": True}

    def _more_feed(self, base, offset):
        params = dict(base)
        params.update({"offset": offset, "client_req_type": 2})
        data = bookmall_more(self._http, self._load_device(), params)
        view = data.get("cell_view") or {}
        return {"list": self._feed_cards(view.get("cell_data") if is_object(view) else []),
                "next": int(data.get("next_offset") or 0),
                "more": data.get("has_more") is True or data.get("has_more") == 1,
                "session": as_text(data.get("session_id"))}

    def _feed_category(self, tab_type, page):
        key = "feed:stream:" + str(tab_type)
        state = self._cache_get(key)
        if page == 1 or not isinstance(state, dict) or not state.get("cards"):
            r = self._load_feed(tab_type)
            cards = [c for c in r["list"] if is_object(c)]
            state = {"base": r["base"], "offset": int(r["next"] or 0),
                     "more": bool(r["more"]), "cards": cards,
                     "seen": [c["vod_id"] for c in cards]}
            self._cache_set(key, state)
        need = page * _FEED_PAGE_SIZE
        guard = 0
        while (len(state["cards"]) < need and state["more"]
               and int(state["offset"]) > 0 and guard < 6):
            guard += 1
            before = int(state["offset"])
            r2 = self._more_feed(state["base"], before)
            if r2["session"]:
                state["base"]["session_id"] = r2["session"]
            added = 0
            for card in r2["list"]:
                if not is_object(card) or card["vod_id"] in state["seen"]:
                    continue
                state["seen"].append(card["vod_id"])
                state["cards"].append(card)
                added += 1
            moved = int(r2["next"] or 0) > before
            state["offset"] = int(r2["next"] or 0)
            state["more"] = bool(r2["more"]) and moved and added > 0
            self._cache_set(key, state)
            if not moved:
                break
        chunk = state["cards"][(page - 1) * _FEED_PAGE_SIZE:page * _FEED_PAGE_SIZE]
        has_more = state["more"] or len(state["cards"]) > page * _FEED_PAGE_SIZE
        return {"list": chunk, "pagecount": page + 1 if has_more else page}

    def _load_audio_feed(self):
        data = self._with_device(lambda d: bookmall_tabs(self._http, d, _AUDIO_TAB))
        tab = None
        for entry in as_list(data.get("tab_item")):
            if is_object(entry) and int(entry.get("tab_type") or 0) == _AUDIO_TAB:
                tab = entry
                break
        if tab is None or not isinstance(tab.get("cell_data"), list):
            raise ValueError("紅果未提供聽書書單")
        box = None
        for cell in tab["cell_data"]:
            if is_object(cell) and int(cell.get("show_type") or 0) == 337:
                box = cell
                break
        base = {
            "cell_id": as_text((box or {}).get("cell_id_str") or (box or {}).get("cell_id")),
            "tab_type": _AUDIO_TAB,
            "show_type": as_text((box or {}).get("show_type")),
            "client_template": as_text(tab.get("client_template")),
            "version_tag": as_text(tab.get("version_tag")),
        }
        session = as_text(tab.get("session_id"))
        return {"base": base, "list": self._audio_cards(tab.get("cell_data")),
                "offset": int(tab.get("next_offset") or 0), "session": session,
                "more": bool(base["cell_id"] and session)}

    def _more_audio_feed(self, base, cursor):
        params = dict(base)
        params.update(cursor)
        params["client_req_type"] = 2
        data = self._with_device(lambda d: bookmall_more(self._http, d, params))
        more = data.get("has_more") is True or data.get("has_more") == 1
        if not is_object(data.get("cell_view")) and more:
            raise ValueError("續頁缺少聽書書單")
        return {"list": self._audio_cards([data.get("cell_view")]),
                "offset": int(data.get("next_offset") or 0),
                "session": as_text(data.get("session_id")) or cursor.get("session_id"),
                "more": more}

    def _audio_category(self, page):
        key = "feed:audio"
        state = self._cache_get(key)
        if page == 1 or not state:
            r = self._load_audio_feed()
            more = r["more"] and len(r["list"]) > 0 and r["offset"] > 0
            cursors = {}
            if more:
                cursors["2"] = {"offset": r["offset"], "session_id": r["session"]}
            state = {"base": r["base"], "cursors": cursors, "pagecount": 2 if more else 1}
            self._cache_set(key, state)
            return {"list": r["list"], "pagecount": state["pagecount"]}
        cursor = (state.get("cursors") or {}).get(str(page))
        if not cursor:
            return {"list": [], "pagecount": page}
        r2 = self._more_audio_feed(state["base"], cursor)
        more2 = r2["more"] and len(r2["list"]) > 0 and r2["offset"] > cursor["offset"]
        if more2:
            state["cursors"][str(page + 1)] = {"offset": r2["offset"], "session_id": r2["session"]}
            state["pagecount"] = page + 1
            self._cache_set(key, state)
        return {"list": r2["list"], "pagecount": page + 1 if more2 else page}


    def _genre_option_id(self, rows, key, option):
        values = []
        for row in rows:
            if row["key"] == key:
                values = row["value"]
        for v in values:
            if v["v"] == option["v"]:
                return option["v"]
        matches = [v for v in values if v["v"] and v["n"] == option["n"]]
        if len(matches) == 1:
            return matches[0]["v"]
        raise ValueError("所選體裁沒有「" + option["n"] + "」篩選")

    def _category_selection(self, scene, selected):
        panel = self._panel_for(scene)
        genre = as_text(selected.get("genre"))
        genres = []
        for row in panel:
            if row["key"] == "genre":
                genres = row["value"]
        req_scene = scene
        if scene == "default" and genre in _CLASS_SCENES:
            for g in genres:
                if g["v"] == genre:
                    req_scene = genre
                    break
        rows = self._panel_for(req_scene)
        items = {}
        for row in rows:
            items[row["key"]] = []
        if req_scene != "default":
            items["genre"] = [req_scene]
        filtered = req_scene != scene
        for row in panel:
            if row["key"] == "genre":
                continue
            idv = as_text(selected.get(row["key"]))
            if not idv:
                continue
            option = None
            for o in row["value"]:
                if o["v"] == idv:
                    option = o
                    break
            if option is None:
                continue
            items[row["key"]] = [idv if req_scene == scene else self._genre_option_id(rows, row["key"], option)]
            filtered = True
        return {"reqScene": req_scene, "items": items, "filtered": filtered}

    def _filter_page(self, scene, items, cursor):
        data = landpage_content(self._http, self._load_device(), scene, items,
                                cursor["offset"], _LANDPAGE_SIZE, cursor["session"])
        cards = []
        for v in as_list(data.get("video_data")):
            card = self._landpage_card(v)
            if card:
                cards.append(card)
        offset = int(data.get("next_offset") or 0)
        more = (data.get("has_more") is True or data.get("has_more") == 1) and offset > cursor["offset"]
        return {"list": cards,
                "next": {"offset": offset, "session": as_text(data.get("session_id")) or cursor["session"]} if more else None}

    def _filter_category(self, class_index, page, selected):
        self._ensure_panels()
        scene = _CLASS_SCENES[class_index]
        sel = self._category_selection(scene, selected)
        tab = _FEED_TABS.get(_CLASS_IDS[class_index])
        if not sel["filtered"] and tab is not None:
            return self._feed_category(tab, page)
        key = "cur:find:" + self._owner() + ":" + md5_hex(json.dumps(
            [_CLASS_IDS[class_index], sel["reqScene"], sel["items"]], ensure_ascii=False, separators=(",", ":")))
        return self._cursor_page(key, page, {"offset": 0, "session": ""},
                                 lambda cursor: self._filter_page(sel["reqScene"], sel["items"], cursor))

    def _search_page(self, keyword, cursor):
        key = "search:app:" + self._owner() + ":" + md5_hex(json.dumps(
            [keyword, cursor], ensure_ascii=False, separators=(",", ":")))
        cached = self._cache_get(key)
        if cached is not None:
            return cached
        data = self._with_device(lambda d: search_tab(self._http, d, keyword, cursor, _PAGE_SIZE))
        tab = None
        for entry in as_list(data.get("search_tabs")):
            if is_object(entry) and int(entry.get("tab_type") or 0) == 11:
                tab = entry
                break
        if tab is None:
            raise ValueError("搜尋回應缺少短劇分頁")
        offset = int(tab.get("next_offset") or 0)
        search_id = as_text(tab.get("search_id")) or cursor.get("searchId")
        more = (tab.get("has_more") is True or tab.get("has_more") == 1) and offset > cursor["offset"] and bool(search_id)
        result = {"list": self._feed_cards(tab.get("data")),
                  "next": {"offset": offset, "searchId": search_id,
                           "passback": as_text(tab.get("passback"))} if more else None}
        self._cache_set(key, result)
        return result

    def _matches_series(self, keyword, title):
        match = re.match(r"^(.+?)第[\d一二三四五六七八九十百零〇两兩]+[季部篇]$", title or "")
        return bool(match) and as_text(match.group(1)) == keyword

    def _series_cards(self, card):
        series_id = card["vod_id"]
        key = "seasons:" + self._owner() + ":" + series_id

        def load():
            cell = series_content(self._http, self._load_device(), series_id)
            videos = []
            seen = set()
            while cell:
                videos.extend(as_list(cell.get("video_data")))
                if cell.get("has_more") is not True and cell.get("has_more") != 1:
                    break
                cursor = {"cell_id": as_text(cell.get("cell_id_str") or cell.get("cell_id")),
                          "offset": int(cell.get("next_offset") or 0),
                          "session_id": as_text(cell.get("session_id"))}
                ck = cursor["cell_id"] + ":" + str(cursor["offset"])
                if not cursor["cell_id"] or cursor["offset"] <= 0 or ck in seen:
                    raise ValueError("系列分頁游標未推進")
                seen.add(ck)
                cell = series_content(self._http, self._load_device(), series_id, cursor)
            valid = [v for v in videos if is_object(v) and int(v.get("season_index") or 0) > 0
                     and int(v.get("episode_cnt") or 0) > 0 and v.get("disable_play") is not True]
            valid.sort(key=lambda v: int(v.get("season_index") or 0))
            out = []
            for v in valid:
                c = self._to_card({"series_id": v.get("series_id_str") or v.get("series_id"),
                                   "series_name": v.get("title"), "series_cover": v.get("cover"),
                                   "episode_cnt": v.get("episode_cnt")})
                if c:
                    out.append(c)
            return out if out else [card]

        return self._cached(key, load)

    def _search_stream(self, keyword, page, want=18):
        key = "search:stream:" + self._owner() + ":" + md5_hex(keyword)
        state = self._cache_get(key)
        if page == 1 or not isinstance(state, dict) or not state.get("cards"):
            r = self._search_page(keyword, {"offset": 0, "searchId": "", "passback": ""})
            cards = [c for c in r["list"] if is_object(c)]
            state = {"cards": cards, "next": r["next"],
                     "seen": [c["vod_id"] for c in cards]}
            self._cache_set(key, state)
        need = page * want
        guard = 0
        while len(state["cards"]) < need and state["next"] and guard < 4:
            guard += 1
            r = self._search_page(keyword, state["next"])
            added = 0
            for card in r["list"]:
                if not is_object(card) or card["vod_id"] in state["seen"]:
                    continue
                state["seen"].append(card["vod_id"])
                state["cards"].append(card)
                added += 1
            moved = r["next"] != state["next"]
            state["next"] = r["next"]
            self._cache_set(key, state)
            if not added and not moved:
                break
        chunk = state["cards"][(page - 1) * want:page * want]
        has_more = bool(state["next"]) or len(state["cards"]) > page * want
        return {"list": chunk, "pagecount": page + 1 if has_more else page}

    def _search_series(self, keyword, cards):
        if not any(self._matches_series(keyword, c["vod_name"]) for c in cards):
            return cards
        out = []
        seen = set()
        for card in cards:
            group = [card]
            if self._matches_series(keyword, card["vod_name"]):
                try:
                    group = self._series_cards(card)
                except Exception:
                    group = [card]
            for entry in group:
                if entry["vod_id"] not in seen:
                    seen.add(entry["vod_id"])
                    out.append(entry)
        return out

    def _get_html(self, url):
        res = self._http(url, method="GET", headers={
            "User-Agent": _WEB_UA,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "zh-CN,zh;q=0.9",
            "Referer": self.siteUrl + "/"})
        if res.get("error"):
            raise ValueError("網路請求失敗：" + str(res["error"]))
        code = int(res.get("code") or 0)
        if not code or code < 200 or code >= 300:
            raise ValueError("HTTP " + str(code) if code else "網路請求失敗")
        html = res.get("content") or ""
        if not html:
            raise ValueError("頁面內容為空")
        return html

    def _router_data(self, html):
        source = str(html or "")
        match = re.search(r"_ROUTER_DATA\s*=\s*", source)
        if not match:
            raise ValueError("頁面缺少資料")
        start = source.find("{", match.end())
        if start < 0:
            raise ValueError("頁面缺少資料")
        depth = 0
        in_string = False
        escaped = False
        for i in range(start, len(source)):
            ch = source[i]
            if in_string:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_string = False
            elif ch == '"':
                in_string = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    data = safe_json(source[start:i + 1])
                    if not data:
                        raise ValueError("頁面資料解析失敗")
                    return data
        raise ValueError("頁面資料不完整")

    def _find_section(self, data, field):
        loaders = data.get("loaderData") if is_object(data) else None
        if is_object(loaders):
            for value in loaders.values():
                if is_object(value) and value.get(field) is not None:
                    return value
        return None

    def _web_detail(self, series_id):
        key = "webdetail:" + self.siteUrl + ":" + series_id
        cached = self._cache_get(key)
        if cached is not None:
            return cached
        try:
            html = self._get_html(self.siteUrl + "/detail?series_id=" + series_id)
            data = self._router_data(html)
            section = self._find_section(data, "seriesDetail") or {}
            web = section.get("seriesDetail") if is_object(section.get("seriesDetail")) else {}
            web = dict(web)
            web["social"] = section.get("seriesSocialInfo") if is_object(section.get("seriesSocialInfo")) else {}
            self._cache_set(key, web)
            return web
        except Exception:
            return {}

    def _detail_tags(self, vd, web):
        out = []
        wt = as_list(web.get("tags"))
        if wt:
            for t in wt:
                t = as_text(t)
                if t:
                    out.append(t)
            return out
        for info in as_list(vd.get("secondary_infos")):
            if is_object(info) and info.get("data_type") == 3:
                c = as_text(info.get("content"))
                if c:
                    out.append(c)
        if out:
            return out
        schema = safe_json(vd.get("category_schema")) if isinstance(vd.get("category_schema"), str) else vd.get("category_schema")
        for entry in as_list(schema):
            n = as_text(entry.get("name")) if is_object(entry) else ""
            if n:
                out.append(n)
        return out

    def _content_text(self, intro, fallback_lines):
        head = ["🦋 红果短剧官方交流群：@tvshare23", "导演：🦋 蝴蝶影视",
                "当前主站：" + self.siteUrl, "━" * 28, "━" * 7]
        if intro:
            return "\n".join(head + [intro])
        return "\n".join(head + fallback_lines)

    def _episode_label(self, v, index):
        title = as_text(v.get("episode_title") or v.get("title") or v.get("name"))
        if title and len(title) <= 24:
            return _safe_label(title)
        n = v.get("vid_index")
        try:
            n = int(n)
        except Exception:
            n = 0
        return "第" + str(n if n > 0 else index + 1) + "集"

    def _audio_book(self, book_id):
        def load():
            book = self._with_device(lambda d: audio_detail(self._http, d, book_id))
            if as_text(book.get("book_id")) != book_id or not as_text(book.get("book_name")):
                raise ValueError("缺少書籍資料")
            return book

        return self._cached("audio-detail:" + self._owner() + ":" + book_id, load)

    def _audio_item(self, book_id):
        book = self._audio_book(book_id)
        chapters = audio_directory(self._http, book_id)
        tone = as_text(book.get("tones")).split(",")[0]
        tone_id = tone if re.match(r"^\d+$", tone) else ("0" if int(book.get("genre_type") or 0) == 1 else "1")
        episodes = []
        for i, chapter in enumerate(chapters):
            if not is_object(chapter):
                continue
            item_id = as_text(chapter.get("itemId"))
            if not re.match(r"^\d{6,}$", item_id) or int(chapter.get("needPay") or 0) > 0:
                continue
            label = _safe_label(as_text(chapter.get("title")) or "第" + str(i + 1) + "章")
            episodes.append(label + "$" + "audio:" + book_id + ":" + item_id + ":" + tone_id)
        if not episodes:
            raise ValueError("沒有可播放的章節")
        intro = as_text(book.get("book_abstract_v2") or book.get("abstract"))
        author = as_text(book.get("author"))
        vod = {
            "vod_id": "audio:" + book_id,
            "vod_name": as_text(book.get("book_name")),
            "vod_actor": (author + ",🦋 TG群: @tvshare23") if author else "🦋 TG群: @tvshare23",
            "vod_director": "🦋 蝴蝶影视",
            "vod_remarks": "蝴蝶影视 | 共 " + str(len(episodes)) + " 章",
            "vod_content": self._content_text(intro, [
                "标题：" + as_text(book.get("book_name")),
                "分类：听书",
                "片源：红果短剧",
                "编号：" + book_id]),
            "vod_play_from": "蝴蝶专线",
            "vod_play_url": "#".join(episodes),
        }
        pic = self._picture(book.get("audio_thumb_url_hd") or book.get("thumb_url"))
        if pic:
            vod["vod_pic"] = pic
            vod["vod_bg"] = pic
            vod["vod_background"] = pic
            vod["vod_banner"] = pic
        return {"list": [vod]}

    def homeContent(self, filter):
        classes = [{"type_id": tid, "type_name": name}
                   for tid, name in zip(_CLASS_IDS + ["audio"], _CLASS_NAMES + ["听书"])]
        result = {"class": classes}
        if filter:
            filters = {}
            for i, tid in enumerate(_CLASS_IDS):
                rows = self._panel_for(_CLASS_SCENES[i])
                groups = []
                for row in rows:
                    if i != 0 and row["key"] == "genre":
                        continue
                    groups.append({
                        "key": row["key"], "name": row["name"], "init": "",
                        "value": [{"n": o["n"], "v": o["v"]} for o in row["value"]]})
                filters[tid] = groups
            result["filters"] = filters
        return result

    def homeVideoContent(self):
        r = self._feed_category(_FEED_TABS["find"], 1)
        return {"list": r["list"]}

    def categoryContent(self, tid, pg, filter, extend):
        try:
            page = int(pg)
        except Exception:
            page = 1
        if page < 1:
            page = 1
        selected = extend if isinstance(extend, dict) else {}
        if tid == "audio":
            r = self._audio_category(page)
            limit = _PAGE_SIZE
        elif tid in _CLASS_IDS:
            r = self._filter_category(_CLASS_IDS.index(tid), page, selected)
            limit = _LANDPAGE_SIZE if r["list"] else _PAGE_SIZE
        else:
            r = self._filter_category(0, page, selected)
            limit = _PAGE_SIZE
        cards = r["list"]
        pagecount = int(r["pagecount"])
        total = page * limit + 100 if pagecount > page else (page - 1) * limit + len(cards)
        return {"list": cards, "page": page, "pagecount": pagecount,
                "limit": len(cards) if cards else limit, "total": total}

    def detailContent(self, ids):
        raw_id = ids[0] if isinstance(ids, (list, tuple)) else str(ids)
        raw = as_text(raw_id)
        audio_match = re.match(r"^audio:(\d{6,})$", raw)
        if audio_match:
            return self._audio_item(audio_match.group(1))
        series_id = _series_id_of(raw)
        if not series_id:
            raise ValueError("無效的劇集 ID")
        vd = self._with_device(lambda d: video_detail(self._http, d, series_id))
        web = self._web_detail(series_id)
        eps = [v for v in as_list(vd.get("video_list")) if is_object(v) and v.get("vid")]
        if not eps:
            raise ValueError("沒有分集")
        title = as_text(vd.get("series_title") or web.get("series_name")) or "紅果短劇"
        episodes = []
        for j, ep in enumerate(eps):
            episodes.append(self._episode_label(ep, j) + "$" + str(ep["vid"]))
        social = web.get("social") if is_object(web.get("social")) else {}
        hot = as_text((social.get("hot_score_data") or {}).get("text")) if is_object(social.get("hot_score_data")) else ""
        if not hot:
            subs = []
            for entry in as_list(vd.get("series_sub_title_list")):
                tx = as_text(entry)
                if tx and not re.match(r"^全\d+集$", tx):
                    subs.append(tx)
            hot = " · ".join(subs)
        remarks_parts = []
        ert = as_text(vd.get("episode_right_text") or web.get("episode_right_text"))
        if ert:
            remarks_parts.append(ert)
        if social.get("rating"):
            remarks_parts.append("評分" + str(social["rating"]))
        if hot:
            remarks_parts.append(hot)
        remarks = " · ".join(remarks_parts)
        tags = self._detail_tags(vd, web)
        intro = as_text(vd.get("series_intro") or web.get("series_intro"))
        actors = []
        for celeb in as_list(web.get("celebrities")):
            nick = as_text(celeb.get("nickname")) if is_object(celeb) else ""
            if nick:
                actors.append(nick)
        vod = {
            "vod_id": series_id,
            "vod_name": title,
            "vod_actor": ",".join(actors + ["🦋 TG群: @tvshare23"]) if actors else "🦋 TG群: @tvshare23",
            "vod_director": "🦋 蝴蝶影视",
            "vod_remarks": "蝴蝶影视 | " + remarks if remarks else "蝴蝶影视",
            "vod_content": self._content_text(intro, [
                "标题：" + title,
                "分类：" + (" / ".join(tags) if tags else "短剧"),
                "片源：红果短剧",
                "编号：" + series_id]),
            "vod_play_from": "蝴蝶专线",
            "vod_play_url": "#".join(episodes),
        }
        if tags:
            vod["vod_class"] = ",".join(tags)
        pic = self._picture(web.get("series_cover") or vd.get("series_cover"))
        if pic:
            vod["vod_pic"] = pic
            vod["vod_bg"] = pic
            vod["vod_background"] = pic
            vod["vod_banner"] = pic
        return {"list": [vod]}

    def searchContent(self, key, quick, pg="1"):
        keyword = str(key or "").strip()
        try:
            page = int(pg)
        except Exception:
            page = 1
        if page < 1:
            page = 1
        if not keyword:
            return {"list": [], "page": page, "pagecount": 1, "limit": _PAGE_SIZE, "total": 0}
        try:
            r = self._search_stream(keyword, page)
        except Exception:
            state_key = "cur:search:" + self._owner() + ":" + md5_hex(keyword)
            r = self._cursor_page(state_key, page, {"offset": 0, "searchId": "", "passback": ""},
                                  lambda cursor: self._search_page(keyword, cursor))
        items = self._search_series(keyword, r["list"])
        pagecount = int(r["pagecount"])
        total = page * _PAGE_SIZE + 100 if pagecount > page else (page - 1) * _PAGE_SIZE + len(items)
        return {"list": items, "page": page, "pagecount": pagecount,
                "limit": len(items) if items else _PAGE_SIZE, "total": total}

    def _web_play_url(self, vid):
        """站點自身放行的簽名直鏈（網頁播放器走的就是這條）"""
        key = "webplay:" + str(vid)
        cached = self._cache_get(key)
        if isinstance(cached, dict):
            url = as_text(cached.get("url"))
            if url and (_now_ms() - int(cached.get("ts") or 0)) < 1200000:
                return url
        body = json.dumps({"item_id": str(vid), "force_refresh": False}, separators=(",", ":"))
        res = self._http("https://hongguoduanju.com/api/video/protected/fallback-play-info?aid=8662",
                         method="POST", headers={
                             "Content-Type": "application/json",
                             "Accept": "application/json, text/plain, */*",
                             "Origin": self.siteUrl,
                             "Referer": self.siteUrl + "/player/" + str(vid),
                             "User-Agent": _WEB_UA}, data=body, retries=0)
        if res.get("error"):
            return ""
        data = safe_json(res.get("content") or "")
        url = as_text(data.get("main_url")) if is_object(data) else ""
        if not re.match(r"^https?://[^/\s]+\S*$", url, re.I):
            return ""
        self._cache_set(key, {"url": url, "ts": _now_ms()})
        return url

    def playerContent(self, flag, id, vipFlags):
        ep_id = as_text(id)
        audio_match = _AUDIO_EPISODE.match(ep_id)
        if audio_match:
            stream = self._with_device(lambda d: audio_stream(
                self._http, d, audio_match.group(1), audio_match.group(2), audio_match.group(3)))
            return {"parse": 0, "jx": 0, "url": stream["url"],
                    "header": {"User-Agent": _APP_UA}}

        vid = ep_id
        if not re.match(r"^\d{6,}$", vid):
            raise ValueError("無效的播放參數")

        url = self._web_play_url(vid)
        if url:
            return {"parse": 0, "jx": 0, "url": url,
                    "header": {"User-Agent": _WEB_UA, "Referer": self.siteUrl + "/"}}

        stream = None
        if _HG_MODEL_MISS["n"] < 2:
            try:
                model = self._with_device(lambda d: video_model(self._http, d, vid))
                quality = as_text(self.options.get("quality"))
                stream = pick_stream(model, quality)
                if stream is None:
                    compatible = compatible_model(self._http, model)
                    if compatible is not None:
                        stream = pick_stream(compatible, quality)
            except Exception:
                stream = None
            if stream is None:
                _HG_MODEL_MISS["n"] += 1
            else:
                _HG_MODEL_MISS["n"] = 0
        if stream is not None:
            result = {"parse": 0, "jx": 0, "url": stream["url"],
                      "header": {"User-Agent": _APP_UA}}
            if stream.get("kid"):
                proxy = ""
                try:
                    proxy = as_text(self.getProxyUrl())
                except Exception:
                    proxy = ""
                if proxy:
                    sep = "&" if "?" in proxy else "?"
                    result["drm"] = {
                        "key": proxy + sep + "type=ck&kid=" + str(stream["kid"]) + "&k=" + str(stream["key"]),
                        "type": "clearkey", "forceKey": True, "header": {}}
            return result
        raise ValueError("該集暫無可用播放源：紅果只開放前幾集，其餘需在 App 內解鎖")

    def action(self, action):
        return {"msg": "ok"}

    def liveContent(self):
        return ""

    def localProxy(self, params):
        if isinstance(params, dict) and params.get("type") == "ck":
            try:
                body = clear_key_license(params.get("kid") or "", params.get("k") or "")
            except Exception as e:
                return [500, "text/plain; charset=utf-8", str(e)]
            return [200, "application/json", body]
        return [404, "text/plain; charset=utf-8", "Proxy not configured"]
