# coding=utf-8
# TVBox Python 爬虫源 —— 极速追剧 (jisuzhuiju.com)
# 用法：TVBox / 影视壳 里作为「Python 源」导入本文件即可
# extend 可传自定义域名覆盖默认：https://jisuzhuiju.com
#
# v2 修复：
# 1. 详情页顶部「立即播放」大按钮不再被当成第一集（只解析分集按钮）
# 2. 线路名显示中文（腾讯官方线路 / 自建线路 / 普通线路一...）
# 3. 播放接口限流(429/500)时自动重试 + 自动切换其它线路
# 4. 播放地址 302 跳转提前解析，兼容不跟跳转的播放器

import re
import json
import time
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

BASE = "https://jisuzhuiju.com"
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"


def clean(text):
    if not text:
        return ""
    text = re.sub(r"<[^>]+>", "", text)
    text = text.replace("&nbsp;", " ").replace("&amp;", "&").replace("&quot;", '"').replace("&#39;", "'")
    return re.sub(r"\s+", " ", text).strip()


class Spider(_BaseSpider):

    def getName(self):
        return "极速追剧"

    def init(self, extend=""):
        self.extend = (extend or "").strip()
        self.base = self.extend if self.extend.startswith("http") else BASE
        self.base = self.base.rstrip("/")
        self._sess = None
        self._play_cache = {}
        self._lines = {}
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
            if text and len(text) > 100 and "Too Many Requests" not in text[:400] and "429" not in text[:200]:
                return text
            time.sleep(0.8 * (i + 1))
        return text or ""

    # ---------------- 列表解析 ----------------

    def parseList(self, html):
        out = []
        seen = set()
        if not html:
            return out
        for m in re.finditer(r'<a\s+href="(/detail/(\d+)\.html)"[^>]*>(.*?)</a>', html, re.S):
            path, vid, seg = m.group(1), m.group(2), m.group(3)
            if vid in seen:
                continue
            name_m = re.search(r'vod-title[^>]*>(.*?)<', seg, re.S)
            if not name_m:
                continue
            seen.add(vid)
            pic = ""
            pm = re.search(r'<img[^>]+src="([^"]+)"', seg)
            if pm:
                pic = pm.group(1)
            if pic.startswith("//"):
                pic = "https:" + pic
            elif pic.startswith("/"):
                pic = self.base + pic
            sub = ""
            sm = re.search(r'vod-subtitle[^>]*>(.*?)<', seg, re.S)
            if sm:
                sub = clean(sm.group(1))
            out.append({
                "vod_id": path,
                "vod_name": clean(name_m.group(1)),
                "vod_pic": pic,
                "vod_remarks": sub,
            })
        return out

    def parseSearch(self, html):
        """搜索结果页是 search-item 卡片结构，跟首页列表不一样"""
        out, seen = [], set()
        if not html:
            return out
        for seg in html.split('<div class="search-item">')[1:]:
            hm = re.search(r'href="(/detail/(\d+)\.html)"', seg)
            if not hm:
                continue
            vid, path = hm.group(2), hm.group(1)
            if vid in seen:
                continue
            nm = re.search(r'class="search-item-title[^"]*"[^>]*>(.*?)</a>', seg, re.S)
            if not nm:
                continue
            seen.add(vid)
            pic = ""
            pm = re.search(r'<img[^>]+src="([^"]+)"', seg)
            if pm:
                pic = pm.group(1)
            if pic.startswith("//"):
                pic = "https:" + pic
            elif pic.startswith("/"):
                pic = self.base + pic
            tp = ""
            tm = re.search(r'class="search-item-type"[^>]*>(.*?)</span>', seg, re.S)
            if tm:
                tp = clean(tm.group(1))
            remark = ""
            mm = re.search(r'类型：</span>\s*<span[^>]*>(.*?)</span>', seg, re.S)
            if mm:
                remark = clean(mm.group(1))
            out.append({
                "vod_id": path,
                "vod_name": clean(nm.group(1)),
                "vod_pic": pic,
                "vod_remarks": remark or tp,
            })
        return out

    # ---------------- 首页 / 分类 ----------------

    def homeContent(self, filter=False):
        classes = [
            {"type_id": "1", "type_name": "电视剧"},
            {"type_id": "2", "type_name": "电影"},
            {"type_id": "3", "type_name": "动漫"},
            {"type_id": "4", "type_name": "综艺"},
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
        url = "%s/filter?channel=%s&page=%d" % (self.base, tid, page)
        html = self.getHtml(url, referer=self.base + "/")
        items = self.parseList(html)
        return {
            "list": items,
            "page": page,
            "pagecount": 9999 if items else page,
            "limit": len(items),
            "total": 999999 if items else 0,
        }

    # ---------------- 详情 ----------------

    def _jsonld(self, html):
        try:
            m = re.search(r'<script type="application/ld\+json">(.*?)</script>', html, re.S)
            if not m:
                return {}
            data = json.loads(m.group(1).strip())
            if isinstance(data, list) and data:
                data = data[0]
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def _tabNames(self, html):
        """播放线路 tab：data-target="source-N" -> 中文线路名"""
        names = {}
        for m in re.finditer(r'<button\b([^>]*)>(.*?)</button>', html, re.S):
            attrs, inner = m.group(1), m.group(2)
            if "source-tab" not in attrs:
                continue
            tm = re.search(r'data-target="(source-\d+)"', attrs)
            if not tm:
                continue
            nm = clean(inner)
            if nm:
                names[tm.group(1)] = nm
        return names

    def _parsePanels(self, html):
        """按线路面板解析分集，返回 [(线路名, [(idx, 集名, playFrom)])]"""
        tab_names = self._tabNames(html)
        parts = re.split(r'<div[^>]*id="(source-\d+)"', html)
        result = []
        for i in range(1, len(parts), 2):
            pid, seg = parts[i], parts[i + 1]
            # 只切到下一个 panel 之前
            cut = re.search(r'<div[^>]*id="source-\d+"', seg)
            if cut:
                seg = seg[:cut.start()]
            eps = []
            for am in re.finditer(r'<a\b([^>]*)>(.*?)</a>', seg, re.S):
                attrs, inner = am.group(1), am.group(2)
                if "episode-btn" not in attrs:
                    continue
                hm = re.search(r'href="(/vodplay/(\d+)-([A-Za-z0-9_]+)-(\d+)\.html)"', attrs)
                if not hm:
                    continue
                eps.append((int(hm.group(4)), clean(inner), hm.group(3)))
            if eps:
                result.append((tab_names.get(pid, ""), eps))
        return result

    def parsePlaylist(self, html):
        """返回 froms, urls；每集 id 形如 jisu|影片id|线路标识|集数"""
        froms, urls = [], []
        panels = self._parsePanels(html)

        # 兜底：没有面板结构时扫全部播放链接（排除顶部「立即播放」大按钮）
        if not panels:
            body = re.sub(r'<a\b[^>]*(?:btn-play-large|id="playBtn")[^>]*>.*?</a>', "", html, flags=re.S)
            groups, order = {}, []
            for am in re.finditer(r'<a\b([^>]*)>(.*?)</a>', body, re.S):
                attrs, inner = am.group(1), am.group(2)
                hm = re.search(r'href="(/vodplay/(\d+)-([A-Za-z0-9_]+)-(\d+)\.html)"', attrs)
                if not hm:
                    continue
                frm = hm.group(3)
                if frm not in groups:
                    groups[frm] = []
                    order.append(frm)
                groups[frm].append((int(hm.group(4)), clean(inner) or ("第%d集" % int(hm.group(4))), frm))
            for frm in order:
                arr = groups[frm]
                if arr:
                    panels.append((frm, arr))

        used = {}
        for name, eps in panels:
            # 同一集去重
            uniq, seen = [], set()
            for idx, nm, frm in eps:
                if idx in seen:
                    continue
                seen.add(idx)
                uniq.append((idx, nm or ("第%d集" % idx), frm))
            if not uniq:
                continue
            uniq.sort(key=lambda x: x[0])
            label = (name or uniq[0][2]).strip()
            if label in used:
                used[label] += 1
                label = "%s%d" % (label, used[label])
            else:
                used[label] = 1
            vid = ""
            line = []
            for idx, nm, frm in uniq:
                line.append("%s$jisu|%s|%s|%d" % (nm, "{vid}", frm, idx))
            froms.append(label)
            urls.append("#".join(line))
        return froms, urls

    def detailContent(self, ids):
        raw = ids[0] if isinstance(ids, (list, tuple)) else ids
        url = raw if raw.startswith("http") else self.base + raw
        html = self.getHtml(url, referer=self.base + "/")

        name = ""
        m = re.search(r'<h1[^>]*>(.*?)</h1>', html, re.S)
        if m:
            name = clean(m.group(1))
        pic = ""
        m = re.search(r'<meta[^>]+property="og:image"[^>]+content="([^"]*)"', html)
        if m:
            pic = m.group(1)
        content = ""
        m = re.search(r'id="synopsisContent"[^>]*>(.*?)</div>', html, re.S)
        if not m:
            m = re.search(r'<meta[^>]+name="description"[^>]+content="([^"]*)"', html)
        if m:
            content = clean(m.group(1))

        ld = self._jsonld(html)
        year = str(ld.get("datePublished") or "")[:4]
        actor = ld.get("actor") or ""
        if isinstance(actor, list):
            actor = ",".join([str(x.get("name", x)) if isinstance(x, dict) else str(x) for x in actor])
        director = ld.get("director") or ""
        if isinstance(director, list):
            director = ",".join([str(x.get("name", x)) if isinstance(x, dict) else str(x) for x in director])
        genre = ld.get("genre") or ""
        if isinstance(genre, list):
            genre = ",".join([str(x) for x in genre])
        area = ld.get("countryOfOrigin") or ""
        if isinstance(area, dict):
            area = area.get("name", "")

        vid = ""
        vm = re.search(r'/detail/(\d+)\.html', url)
        if vm:
            vid = vm.group(1)

        froms, urls = self.parsePlaylist(html)
        final_froms, final_urls = [], []
        for i, f in enumerate(froms):
            line = urls[i].replace("{vid}", vid).split("#") if urls[i] else []
            if not line:
                continue
            final_froms.append(f)
            final_urls.append("#".join(line))
            # 记录该片全部线路，播放失败时自动换线
            frms = []
            for it in line:
                parts = it.split("$", 1)
                if len(parts) == 2:
                    seg = parts[1].split("|")
                    if len(seg) == 4 and seg[2] not in frms:
                        frms.append(seg[2])
            if vid:
                self._lines[vid] = frms

        vod = {
            "vod_id": raw,
            "vod_name": name,
            "vod_pic": pic,
            "type_name": genre,
            "vod_year": year,
            "vod_area": area,
            "vod_remarks": "",
            "vod_actor": actor,
            "vod_director": director,
            "vod_content": content,
            "vod_play_from": "$$$".join(final_froms),
            "vod_play_url": "$$$".join(final_urls),
        }
        return {"list": [vod]}

    # ---------------- 搜索 ----------------

    def searchContent(self, key, quick=False, pg="1"):
        # 站点搜索参数是 keyword（另外 field=all/name/actor），不是 wd
        url = "%s/search?keyword=%s&field=all" % (self.base, urllib.parse.quote(key))
        page = str(pg or "1")
        if page != "1":
            url += "&page=%s" % page
        html = self.getHtml(url, referer=self.base + "/")
        items = self.parseSearch(html)
        if not items:
            items = self.parseList(html)
        # 站内搜索是模糊匹配，把片名命中关键词的排前面
        k = (key or "").strip().lower()
        if k:
            items.sort(key=lambda x: 0 if k in (x.get("vod_name") or "").lower() else 1)
        return {"list": items}

    # ---------------- 播放 ----------------

    def _throttle(self, gap=1.5):
        """同一实例内控制接口请求间隔，避免连点把自己打上限流"""
        last = getattr(self, "_last_api", 0)
        now = time.time()
        if last and (now - last) < gap:
            time.sleep(gap - (now - last))
        self._last_api = time.time()

    def _raw(self, url, referer=""):
        """底层请求，返回 (status, text)；429 交给上层退避"""
        headers = {
            "User-Agent": UA,
            "Accept": "application/json,text/plain,*/*",
            "Referer": referer or (self.base + "/"),
        }
        try:
            if requests:
                if self._sess is None:
                    self._sess = requests.Session()
                r = self._sess.get(url, headers=headers, timeout=12, verify=False)
                r.encoding = "utf-8"
                return r.status_code, (r.text or "")
            import urllib.request
            import ssl
            req = urllib.request.Request(url, headers=headers)
            resp = urllib.request.urlopen(req, timeout=12, context=ssl._create_unverified_context())
            return resp.getcode(), resp.read().decode("utf-8", "ignore")
        except Exception as e:
            code = getattr(getattr(e, "code", None), "__int__", lambda: 0)()
            return int(code or 0), ""

    def _apiPlay(self, vid, frm, idx, fast=False):
        """调播放接口，返回 (直链, mode, 状态)；状态 ok / notfound / rate"""
        referer = "%s/vodplay/%s-%s-%s.html" % (self.base, vid, urllib.parse.quote(frm, safe=""), idx)
        api = "%s/api/play-url?vodId=%s&playFrom=%s&index=%s" % (
            self.base, vid, urllib.parse.quote(frm, safe=""), idx)
        # 逐步退避：限流是站点按 IP 掐的，等一等基本都能过
        waits = (0,) if fast else (0, 2.5, 4.5)
        for wait in waits:
            if wait:
                time.sleep(wait)
            self._throttle()
            status, txt = self._raw(api, referer)
            if not txt:
                continue
            body = txt.lstrip()
            if status == 429 or body.startswith("<"):
                continue
            try:
                data = json.loads(body)
            except Exception:
                continue
            u = (data.get("url") or "").replace("\\/", "/").strip()
            if u.startswith("http"):
                return u, (data.get("mode") or ""), "ok"
            if data.get("code") == 500:
                return "", "", "notfound"
        return "", "", "rate"

    def _resolve(self, url):
        """把 m3u8 的 302 跳转提前解析掉，兼容不跟跳转的播放器"""
        if not requests or not url:
            return url
        try:
            r = self._sess.get(url, headers={"User-Agent": UA}, timeout=5, verify=False,
                               stream=True, allow_redirects=True)
            final = r.url or url
            try:
                r.close()
            except Exception:
                pass
            if final.startswith("http"):
                return final
        except Exception:
            pass
        return url

    def _detailLines(self, vid):
        """取该片的全部线路标识（缓存）"""
        lines = self._lines.get(vid) or []
        if lines:
            return lines
        html = self.getHtml("%s/detail/%s.html" % (self.base, vid), referer=self.base + "/")
        for _, eps in self._parsePanels(html):
            for _, _, f in eps:
                if f not in lines:
                    lines.append(f)
        if lines:
            self._lines[vid] = lines
        return lines

    def playerContent(self, flag, id, vipFlags=None):
        if not isinstance(self._play_cache, dict):
            self._play_cache = {}
        if not isinstance(self._lines, dict):
            self._lines = {}
        hit = self._play_cache.get(id)
        if isinstance(hit, tuple) and len(hit) == 2 and (time.time() - hit[0]) < 120:
            return hit[1]
        if isinstance(hit, dict):
            self._play_cache.pop(id, None)

        header = {"User-Agent": UA, "Referer": self.base + "/"}
        vid, frm, idx = "", "", ""

        m = re.match(r'^jisu\|(\d+)\|([^|]+)\|(\d+)$', id or "")
        if m:
            vid, frm, idx = m.group(1), m.group(2), m.group(3)
        else:
            m = re.search(r'vodId=(\d+).*?playFrom=([^&]+).*?index=(\d+)', id or "")
            if m:
                vid, frm, idx = m.group(1), urllib.parse.unquote(m.group(2)), m.group(3)

        if not vid:
            u = id if id.startswith("http") else self.base + id
            return {"parse": 1, "url": u, "header": header}

        # 1) 当前线路（带退避重试）
        play_url, mode, state = self._apiPlay(vid, frm, idx)

        # 2) 当前线路集数缺失 / 限流失败 -> 换其它线路
        if not play_url:
            lines = self._detailLines(vid)
            alts = [x for x in lines if x != frm]
            # 限流时换线意义不大（同 IP 一起被掐），只在「该集缺失」时才换线
            if state == "notfound":
                for alt in alts[:2]:
                    play_url, mode, state = self._apiPlay(vid, alt, idx, fast=True)
                    if play_url:
                        break

        if play_url:
            if ".m3u8" in play_url.lower() or ".mp4" in play_url.lower() or mode == "native":
                res = {"parse": 0, "url": self._resolve(play_url), "header": header}
            else:
                res = {"parse": 1, "url": play_url, "header": header}
            self._play_cache[id] = (time.time(), res)
            return res

        # 3) 兜底：交给壳子打开真实播放页
        page = "%s/vodplay/%s-%s-%s.html" % (self.base, vid, urllib.parse.quote(frm, safe=""), idx)
        return {"parse": 1, "url": page, "header": header}

    def isVideoFormat(self, url):
        return bool(url and (".m3u8" in url or ".mp4" in url))

    def manualVideoCheck(self):
        return False
