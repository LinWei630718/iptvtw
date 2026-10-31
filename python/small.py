# coding=utf-8
# TVBox Python 爬虫源 —— 小宝影院 (xiaobaotv.com)
# 用法：TVBox / 影视壳 里作为「Python 源」导入本文件即可
# extend 传自定义域名可覆盖默认域名，例如：https://www.xiaobaotv.com

import re
import json
import time
import base64
import urllib.parse

try:
    import requests
    try:
        requests.packages.urllib3.disable_warnings()
    except Exception:
        pass
except Exception:
    requests = None

try:
    from base.spider import Spider as _BaseSpider
except Exception:
    try:
        import base.spider as _base_spider
        _BaseSpider = _base_spider.Spider
    except Exception:
        class _BaseSpider(object):
            pass

BASE = "https://www.xiaobaotv.com"
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"


def js_unescape(s):
    """模拟 JS 的 unescape：%uXXXX 与 %XX"""
    if not s:
        return s
    try:
        s = re.sub(r"%u([0-9a-fA-F]{4})", lambda m: chr(int(m.group(1), 16)), s)
        s = urllib.parse.unquote(s)
    except Exception:
        pass
    return s


def b64decode(s):
    if not s:
        return ""
    s = s.strip().replace("-", "+").replace("_", "/")
    s += "=" * (-len(s) % 4)
    try:
        return base64.b64decode(s).decode("utf-8", "ignore")
    except Exception:
        return ""


def clean(text):
    if not text:
        return ""
    text = re.sub(r"<[^>]+>", "", text)
    text = text.replace("&nbsp;", " ").replace("&amp;", "&").replace("&quot;", '"')
    return re.sub(r"\s+", " ", text).strip()


class Spider(_BaseSpider):

    def getName(self):
        return "小宝影院"

    def init(self, extend=""):
        self.extend = (extend or "").strip()
        self.base = self.extend if self.extend.startswith("http") else BASE
        self.base = self.base.rstrip("/")
        self._sess = None
        try:
            if requests:
                self._sess = requests.Session()
        except Exception:
            self._sess = None

    # ---------------- 网络 ----------------

    def getHtml(self, url, referer=""):
        headers = {
            "User-Agent": UA,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
        }
        if referer:
            headers["Referer"] = referer
        text = ""
        for i in range(4):
            try:
                if requests:
                    if self._sess is None:
                        self._sess = requests.Session()
                    r = self._sess.get(url, headers=headers, timeout=15, verify=False)
                    r.encoding = "utf-8"
                    text = r.text or ""
                else:
                    import urllib.request
                    import ssl
                    req = urllib.request.Request(url, headers=headers)
                    ctx = ssl._create_unverified_context()
                    text = urllib.request.urlopen(req, timeout=15, context=ctx).read().decode("utf-8", "ignore")
            except Exception:
                text = ""
            if text and len(text) > 300 and "Too Many Requests" not in text[:400]:
                return text
            time.sleep(0.8 * (i + 1))
        return text or ""

    # ---------------- 列表解析 ----------------

    def parseList(self, html):
        out = []
        seen = set()
        if not html:
            return out
        for m in re.finditer(r'<a[^>]+href="(/vod/detail/(\d+)\.html)"([^>]*)>', html):
            path, vid, tail = m.group(1), m.group(2), m.group(3)
            if vid in seen:
                continue
            seen.add(vid)
            name = ""
            tag = html[m.start():m.end()]
            tn = re.search(r'title="([^"]*)"', tag) or re.search(r'title="([^"]*)"', tail)
            if tn:
                name = clean(tn.group(1))
            end_a = html.find("</a>", m.end())
            inside = html[m.end(): end_a if end_a > 0 else m.end() + 400]
            if not name:
                # 首页/轮播块的 a 没有 title，标题在后面的 h4 > a 里
                after = html[m.end(): m.end() + 900]
                nm2 = re.search(r'<h4[^>]*>\s*<a[^>]+title="([^"]*)"', after)
                if nm2:
                    name = clean(nm2.group(1))
                else:
                    nm3 = re.search(r'alt="([^"]*)"', inside) or re.search(r'<h4[^>]*>(.*?)</h4>', after, re.S)
                    if nm3:
                        name = clean(nm3.group(1))
            pic = ""
            pm = re.search(r'data-original="([^"]+)"', tail + inside) or re.search(r'src="([^"]+)"', inside)
            if pm:
                pic = pm.group(1)
            if pic.startswith("/"):
                pic = self.base + pic
            end_li = html.find("</li>", m.end())
            seg = html[m.end(): end_li if end_li > 0 else m.end() + 600]
            rk = re.search(r'pic-text[^>]*>\s*([^<]*)<', seg)
            out.append({
                "vod_id": path,
                "vod_name": name,
                "vod_pic": pic,
                "vod_remarks": clean(rk.group(1)) if rk else "",
            })
        return out

    # ---------------- 首页 / 分类 ----------------

    def homeContent(self, filter=False):
        classes = [
            {"type_id": "1", "type_name": "电影"},
            {"type_id": "2", "type_name": "电视剧"},
            {"type_id": "3", "type_name": "动漫"},
            {"type_id": "4", "type_name": "综艺"},
            {"type_id": "11", "type_name": "短剧"},
        ]
        return {"class": classes, "filters": {}, "list": self.homeVideoContent().get("list", [])}

    def homeVideoContent(self):
        html = self.getHtml(self.base + "/")
        return {"list": self.parseList(html)}

    def categoryContent(self, tid, pg, filter, extend):
        try:
            page = int(pg)
        except Exception:
            page = 1
        if page < 1:
            page = 1
        if page == 1:
            url = "%s/vod/type/%s.html" % (self.base, tid)
        else:
            url = "%s/vod/type/%s-%d.html" % (self.base, tid, page)
        html = self.getHtml(url, referer=self.base + "/")
        items = self.parseList(html)
        pagecount = 9999 if items else page
        return {
            "list": items,
            "page": page,
            "pagecount": pagecount,
            "limit": len(items),
            "total": 999999 if items else 0,
        }

    # ---------------- 详情 ----------------

    def _field(self, html, label):
        m = re.search(r'>\s*%s\s*[：:]\s*</span>(.*?)</(?:p|div|span|li)>' % label, html, re.S)
        if m:
            return clean(m.group(1))
        return ""

    def parsePlaylist(self, html):
        froms = []
        urls = []
        tabs = re.findall(r'<a[^>]+href="#playlist(\d+)"[^>]*>([^<]*)</a>', html)
        for pid, pname in tabs:
            m = re.search(r'id="playlist%s"(.*?)</ul>' % re.escape(pid), html, re.S)
            if not m:
                continue
            eps = re.findall(r'href="(/vod/play/[^"]+?\.html)"[^>]*>([^<]*)</a>', m.group(1))
            if not eps:
                continue
            line = []
            for p, n in eps:
                line.append("%s$%s" % (clean(n) or "播放", self.base + p))
            froms.append(clean(pname) or ("线路" + pid))
            urls.append("#".join(line))
        if not froms:
            eps = re.findall(r'href="(/vod/play/(\d+)-(\d+)-(\d+)\.html)"[^>]*>([^<]*)</a>', html)
            groups = {}
            for p, vid, sid, nid, n in eps:
                groups.setdefault(sid, []).append((int(nid), clean(n) or "播放", p))
            for sid in sorted(groups.keys(), key=lambda x: int(x)):
                arr = sorted(groups[sid], key=lambda x: x[0])
                froms.append("线路" + sid)
                urls.append("#".join(["%s$%s" % (n, self.base + p) for _, n, p in arr]))
        return froms, urls

    def detailContent(self, ids):
        url = ids[0] if isinstance(ids, (list, tuple)) else ids
        if not url.startswith("http"):
            url = self.base + url
        html = self.getHtml(url, referer=self.base + "/")

        name = ""
        m = re.search(r'<h1[^>]*class="[^"]*title[^"]*"[^>]*>(.*?)</h1>', html, re.S)
        if m:
            name = clean(m.group(1))
        if not name:
            m = re.search(r'<meta[^>]+property="og:title"[^>]+content="([^"]*)"', html)
            if m:
                name = clean(m.group(1)).split("-")[0].split("_")[0].strip()

        pic = ""
        m = re.search(r'<meta[^>]+property="og:image"[^>]+content="([^"]*)"', html) or \
            re.search(r'data-original="([^"]+)"', html)
        if m:
            pic = m.group(1)
        if pic.startswith("/"):
            pic = self.base + pic

        content = ""
        m = re.search(r'<span class="text-muted">\s*简介\s*[：:]\s*</span>(.*?)</p>', html, re.S)
        if not m:
            m = re.search(r'<div[^>]+class="[^"]*desc[^"]*"[^>]*>(.*?)</div>', html, re.S)
        if m:
            content = clean(m.group(1))

        year = ""
        m = re.search(r'>\s*年份\s*[：:]\s*</span>\s*<a[^>]*>([^<]*)</a>', html) or \
            re.search(r'>\s*年份\s*[：:]\s*</span>([^<]*)<', html)
        if m:
            year = clean(m.group(1))

        area = ""
        m = re.search(r'>\s*地区\s*[：:]\s*</span>([^<]*)<', html)
        if m:
            area = clean(m.group(1))

        actor = self._field(html, "主演")
        director = self._field(html, "导演")
        type_name = self._field(html, "类型")
        remarks = self._field(html, "备注")

        froms, urls = self.parsePlaylist(html)

        vod = {
            "vod_id": ids[0] if isinstance(ids, (list, tuple)) else ids,
            "vod_name": name,
            "vod_pic": pic,
            "type_name": type_name,
            "vod_year": year,
            "vod_area": area,
            "vod_remarks": remarks,
            "vod_actor": actor,
            "vod_director": director,
            "vod_content": content,
            "vod_play_from": "$$$".join(froms),
            "vod_play_url": "$$$".join(urls),
        }
        return {"list": [vod]}

    # ---------------- 搜索 ----------------

    def searchContent(self, key, quick=False, pg="1"):
        kw = urllib.parse.quote(key)
        page = str(pg or "1")
        if page == "1":
            url = "%s/search/%s----------.html" % (self.base, kw)
        else:
            url = "%s/search/%s----------%s---.html" % (self.base, kw, page)
        html = self.getHtml(url, referer=self.base + "/")
        return {"list": self.parseList(html)}

    # ---------------- 播放 ----------------

    def playerContent(self, flag, id, vipFlags=None):
        url = id
        if not url.startswith("http"):
            url = self.base + url
        html = self.getHtml(url, referer=self.base + "/")

        play_url = ""
        m = re.search(r'var\s+player_aaaa\s*=\s*(\{.*?\})\s*</script>', html, re.S)
        if m:
            try:
                data = json.loads(m.group(1))
            except Exception:
                data = {}
            u = (data.get("url") or "").replace("\\/", "/")
            enc = str(data.get("encrypt") if data.get("encrypt") is not None else "0")
            if enc == "1":
                u = js_unescape(u)
            elif enc == "2":
                u = js_unescape(b64decode(u))
            if u.startswith("http"):
                play_url = u

        if not play_url:
            mm = re.search(r'https?://[^\s"\'<>\\]+?\.(?:m3u8|mp4)[^\s"\'<>\\]*', html)
            if mm:
                play_url = mm.group(0)

        header = {"User-Agent": UA, "Referer": self.base + "/"}
        if play_url:
            return {"parse": 0, "playUrl": "", "url": play_url, "header": header}
        # 兜底：交给壳子自行解析播放页
        return {"parse": 1, "playUrl": "", "url": url, "header": header}

    def isVideoFormat(self, url):
        return bool(url and (".m3u8" in url or ".mp4" in url))

    def manualVideoCheck(self):
        return False
