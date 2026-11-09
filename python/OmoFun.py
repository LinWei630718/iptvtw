# -*- coding: utf-8 -*-
"""
OmoFun 动漫 - omoo.tv 发布页系（MacCMS 10 the4 模板）

发布页 https://fb.omoo.tv/ 混淆 JS 解码出 4 个域名（2026-09-23 实测全活）：
    www.omofuns.com / cn.233dm.com / cn.211dm.com / cn.agekkkk.com
源内多域名 failover：请求失败自动切换下一个域名。

关键结论（已实测验证）：
1. 子页面触发「系统安全验证」为 session 级算法验证（无图码，可复现）：
   毫秒时间戳字符串逐字节 XOR 固定 16 字节 key（4e3fa9c2127d88ef55aa0bcddeadbeef）
   → base64 → POST /index.php/ajax/verify_check?type=show，data i=xxx
   → {"code":1,"msg":"ok"}，PHPSESSID 全站放行。
2. 分类 /type/{tid}.html：1日漫 2国漫 5动画 24剧场 4特摄 3美漫
3. 列表 /show/{tid}-----------.html；翻页 /show/{tid}--------{pg}---.html
   卡片 class 名随机混淆（BIaC_xxx），解析锚点只用 href/title/data-original：
   <a class="..." href="/anime/{hash}.html" title="片名" data-original="封面">
   块内 <b>语言/年份</b>...<b>12集</b>（最后一个 b 作备注）
4. 详情 /anime/{hash}.html：
   标题 <h1 class="title">；封面 data-original（upload/vod 路径，avatar/nouser 要排除）；
   简介 .detail-content；元数据 p.data（类型/地区/年份/状态/导演/声优/更新）；
   线路 .channel-tab：<a href="#playlist{sid}">线路名<span>集数</span></a>（sid 直接读 href，不靠顺序对齐）；
   集数 href="/anime/{hash}/play/{sid}/{nid}.html" title="第xx集"
5. 搜索 /search/{wd}-------------.html（关键词后 13 个横杠；10/11/12 横杠均 404）
6. 播放页 /anime/{hash}/play/{sid}/{nid}.html：
   var player_aaaa={"encrypt":1,"url":"%XX...","from":"dyttm3u8","sid":3,"nid":1,...}
   encrypt=1 → unquote →
   - from=dyttm3u8/bfzym3u8/wsym3u8 等：完整 m3u8 直链（vip.dytt-cinema.com 等，parse=0 直播）
   - from=mp4（精品线路）：站内 hash_2 私有标识，浏览器经 iframe
     art.v2player.top:8989/player/?url=...&dmid=... 解出 TikTok CDN 直链；
     源内构造同款 v2player URL 交壳子 WebView 嗅探（dmid 取播放页 d4ddy.dmid）
   封面图床 as.cfhls.top（Cloudflare）宽带直连可达。
"""
import re
import json
import base64
import time
import urllib.parse
import requests

try:
    from base.spider import Spider
except ImportError:
    class Spider:
        def __init__(self):
            pass


class Spider(Spider):
    # ==================== 基础配置 ====================
    name = "OmoFun动漫"
    HOSTS = ["www.omofuns.com", "cn.233dm.com", "cn.211dm.com", "cn.agekkkk.com"]

    searchable = 1
    quickSearch = 1
    filterable = 1
    changeable = 1

    # 分类（站点路由 /type/{tid}.html）
    CATEGORY_NAMES = {
        "1": "日漫", "2": "国漫", "5": "动画", "24": "剧场", "4": "特摄", "3": "美漫",
    }

    VERIFY_KEY = bytes([0x4e, 0x3f, 0xa9, 0xc2, 0x12, 0x7d, 0x88, 0xef,
                        0x55, 0xaa, 0x0b, 0xcd, 0xde, 0xad, 0xbe, 0xef])

    UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
          "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

    play_headers = {
        "User-Agent": UA,
        "Accept": "*/*",
    }

    def __init__(self):
        super().__init__()
        self._sessions = {}          # host -> requests.Session（各域名独立验证）
        self._play_cache = {}
        self._cache_ttl = 1800
        self._last_req_time = 0
        self._min_req_interval = 0.5

        self._re_card = re.compile(
            r'<a[^>]*href="(/anime/[a-f0-9]+\.html)"[^>]*>([\s\S]*?)</a>')
        self._re_b_text = re.compile(r'<b[^>]*>([^<]*)</b>')

    # ==================== 工具方法 ====================
    def _log(self, msg):
        print("[%s] %s" % (self.name, msg))

    def _clean_html(self, text):
        if not text:
            return ""
        text = re.sub(r'<[^>]+>', '', text)
        text = text.replace('&nbsp;', ' ').replace('&amp;', '&')
        text = re.sub(r'\s+', ' ', text).strip()
        return text

    def _verify_token(self):
        f = str(int(time.time() * 1000)).encode()
        return base64.b64encode(
            bytes(b ^ self.VERIFY_KEY[i % len(self.VERIFY_KEY)]
                  for i, b in enumerate(f))).decode()

    def _is_verify(self, html):
        return bool(html) and ("系统安全验证" in html or "mx-mac_msg_jump" in html)

    # ==================== 请求基础（多域名 failover + 验证绕过） ====================
    def _session_for(self, host):
        sess = self._sessions.get(host)
        if sess is None:
            sess = requests.Session()
            sess.headers.update({
                "User-Agent": self.UA,
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                "Accept-Language": "zh-CN,zh;q=0.9",
                "Referer": "https://%s/" % host,
                "Connection": "keep-alive",
            })
            self._sessions[host] = sess
        return sess

    def _pass_verify(self, host, vtype="show"):
        """提交 XOR 时间戳算法验证，对应 type 模块放行"""
        try:
            sess = self._session_for(host)
            r = sess.post("https://%s/index.php/ajax/verify_check?type=%s" % (host, vtype),
                          data={"i": self._verify_token()}, timeout=10)
            ok = '"code":1' in r.text or '"code": 1' in r.text
            self._log("验证提交(%s type=%s): %s" % (host, vtype, r.text[:40]))
            return ok
        except Exception as e:
            self._log("验证提交异常(%s): %s" % (host, e))
            return False

    def _verify_types_for(self, path):
        """按路径推断验证 type 候选序（站点对 show/search 模块独立验证）"""
        if path.startswith("/search/"):
            head = "search"
        elif path.startswith("/show/"):
            head = "show"
        elif "/play/" in path:
            head = "play"
        elif path.startswith("/anime/"):
            head = "detail"
        else:
            head = "show"
        rest = [t for t in ("show", "search", "detail", "play") if t != head]
        return [head] + rest

    def _apply_req_delay(self):
        now = time.time()
        elapsed = now - self._last_req_time
        if 0 < elapsed < self._min_req_interval:
            time.sleep(self._min_req_interval - elapsed)
        self._last_req_time = time.time()

    def _try_get(self, host, path, timeout):
        """单域名请求：验证页自动提交算法并重试一次"""
        sess = self._session_for(host)
        url = "https://%s%s" % (host, path)
        self._apply_req_delay()
        resp = sess.get(url, timeout=timeout)
        html = resp.text
        if self._is_verify(html):
            self._log("触发安全验证(%s): %s" % (host, path))
            for vt in self._verify_types_for(path):
                if self._pass_verify(host, vt):
                    break
            self._apply_req_delay()
            resp = sess.get(url, timeout=timeout)
            html = resp.text
        if self._is_verify(html):
            return ""
        if resp.status_code >= 400 and len(html) < 3000:
            return ""
        return html

    def _get(self, path, max_retry=None, timeout=15):
        """遍历域名 failover 请求，全部失败返回空串"""
        if max_retry is None:
            max_retry = len(self.HOSTS)
        hosts = self.HOSTS[:]
        # 当前首选域名排最前（记录上次成功域名）
        first = getattr(self, "_cur_host", self.HOSTS[0])
        if first in hosts:
            hosts.remove(first)
            hosts.insert(0, first)
        for host in hosts[:max_retry]:
            try:
                html = self._try_get(host, path, timeout)
                if html:
                    self._cur_host = host
                    return html
                self._log("域名无数据(%s): %s" % (host, path))
            except Exception as e:
                self._log("域名请求失败(%s): %s, %s" % (host, path, e))
        return ""

    # ==================== 列表解析 ====================
    def _parse_video_list(self, html):
        """解析 /anime/{hash}.html 卡片（class 随机混淆，锚 href/title/data-original）"""
        videos = []
        if not html:
            return videos
        seen = set()
        for m in self._re_card.finditer(html):
            href, inner = m.group(1), m.group(2)
            vod_id = href.split("/anime/")[-1].split(".")[0]
            if vod_id in seen:
                continue
            tm = re.search(r'title="([^"]*)"', m.group(0))
            pm = re.search(r'data-original="([^"]+)"', m.group(0))
            if not tm:
                # 详情卡片兜底：取 <a> 文本
                tm = re.search(r'>([^<>]{2,60})</a>\s*$', inner.strip())
            title = tm.group(1).strip() if tm else ""
            if not title:
                continue
            pic = pm.group(1) if pm else ""
            if pic.startswith("//"):
                pic = "https:" + pic
            if not pic:
                # 首页 banner 位无真图，跳过
                continue
            bs = self._re_b_text.findall(inner)
            note = bs[-1].strip() if bs else ""
            seen.add(vod_id)
            videos.append({
                "vod_id": vod_id,
                "vod_name": title,
                "vod_pic": pic,
                "vod_remarks": note,
            })
        return videos

    # ==================== 播放源解析（详情页） ====================
    def _parse_play_sources(self, html, vod_id):
        """
        线路：.channel-tab 里 <a href="#playlist{sid}">名<span>集数</span></a>（sid 直接读 href）
        集数：href="/anime/{hash}/play/{sid}/{nid}.html" 按 sid 分组，nid 排序
        """
        line_names = {}
        for m in re.finditer(
                r'<a[^>]*href="#playlist(\d+)"[^>]*>([\s\S]*?)</a>', html):
            sid = m.group(1)
            inner = re.sub(r'<span[^>]*>[^<]*</span>', '', m.group(2))
            inner = re.sub(r'<[^>]+>', '', inner)
            name = re.sub(r'[\s\d]+', '', inner).strip()
            if sid not in line_names and name:
                line_names[sid] = name

        groups = {}
        for m in re.finditer(
                r'href="/anime/([a-f0-9]+)/play/(\d+)/(\d+)\.html"[^>]*>'
                r'(?:\s*<[^>]+>)*\s*([^<>]+?)\s*<', html):
            hid, sid, nid, name = m.groups()
            if hid != vod_id:
                continue
            name = name.strip()
            if not name or "立即" in name or len(name) > 20:
                continue
            groups.setdefault(sid, []).append((int(nid), name))

        if not groups:
            return []

        # 线路顺序按页面 tab 顺序，缺名的补"线路N"
        ordered_sids = [s for s in line_names if s in groups]
        ordered_sids += [s for s in sorted(groups) if s not in ordered_sids]

        sources = []
        for sid in ordered_sids:
            eps = sorted(groups[sid], key=lambda x: x[0])
            name = line_names.get(sid) or "线路%s" % sid
            sources.append({
                "source_name": name,
                "episodes": [
                    {"name": n, "link": "%s-%s-%s" % (vod_id, sid, nid)}
                    for nid, n in eps
                ],
            })

        # 集数多的线路优先
        sources.sort(key=lambda s: -len(s["episodes"]))
        return sources

    # ==================== 播放地址解析 ====================
    def _extract_player_data(self, html):
        """提取 var player_aaaa={...}（括号深度 + 引号转义状态机）"""
        if not html:
            return None
        m = re.search(r'var\s+player_aaaa\s*=\s*', html)
        if not m:
            return None
        start = m.end()
        while start < len(html) and html[start] != '{':
            start += 1
        if start >= len(html):
            return None
        depth = 1
        i = start + 1
        in_string = False
        escape = False
        while i < len(html) and depth > 0:
            c = html[i]
            if in_string:
                if escape:
                    escape = False
                elif c == '\\':
                    escape = True
                elif c == '"':
                    in_string = False
            else:
                if c == '"':
                    in_string = True
                elif c == '{':
                    depth += 1
                elif c == '}':
                    depth -= 1
            i += 1
        if depth == 0:
            try:
                return json.loads(html[start:i])
            except Exception:
                pass
        return None

    def _get_play_url(self, vod_id, sid, nid):
        """返回 dict：{type: direct/webview, url}；失败返回 None"""
        cache_key = "%s-%s-%s" % (vod_id, sid, nid)
        now = time.time()
        if cache_key in self._play_cache:
            meta, ts = self._play_cache[cache_key]
            if now - ts < self._cache_ttl:
                return meta
        play_page = "/anime/%s/play/%s/%s.html" % (vod_id, sid, nid)
        html = self._get(play_page, timeout=15)
        if not html:
            return None
        pd = self._extract_player_data(html)
        if not pd:
            return None
        enc_url = (pd.get("url") or "").strip()
        encrypt = str(pd.get("encrypt", "0"))
        vfrom = (pd.get("from") or "").strip()
        self._log("player encrypt=%s from=%s url=%s..." % (
            encrypt, vfrom, enc_url[:60]))
        if encrypt == "1":
            # 站点用 JS unescape()：%uXXXX（非 ASCII）+ %XX
            enc_url = re.sub(r"%u([0-9a-fA-F]{4})",
                             lambda m: chr(int(m.group(1), 16)), enc_url)
            enc_url = urllib.parse.unquote(enc_url)
        elif encrypt == "2":
            try:
                enc_url = urllib.parse.unquote(base64.b64decode(enc_url).decode("utf-8"))
            except Exception:
                pass
        if not enc_url:
            return None
        meta = {"from": vfrom}
        if enc_url.startswith("http"):
            meta["type"] = "direct"
            meta["url"] = enc_url
        else:
            # mp4 等私有线路：站内 hash_2 标识，走 v2player 解析页（壳子 WebView 嗅探）
            host = getattr(self, "_cur_host", self.HOSTS[0])
            dmid = ""
            dm = re.search(r'"dmid"\s*:\s*"?(\d+)"?', html)
            if dm:
                dmid = dm.group(1)
            vod_data = pd.get("vod_data") or {}
            pic = (vod_data.get("vod_pic") or "").strip()
            vname = (vod_data.get("vod_name") or "").strip()
            link_next = pd.get("link_next") or ""
            meta["type"] = "webview"
            meta["url"] = (
                "https://art.v2player.top:8989/player/?url=%s&dmid=%s&next=%s&name=%s&nid=%s&ph=https://as.cfhls.top/&h=https://%s&pic=%s"
                % (urllib.parse.quote(enc_url), dmid,
                   urllib.parse.quote("https://%s%s" % (host, link_next)) if link_next else "",
                   urllib.parse.quote(vname), nid, host, urllib.parse.quote(pic, safe="")))
        self._play_cache[cache_key] = (meta, now)
        return meta

    # ==================== TVBox 核心方法 ====================
    def init(self, extend=''):
        # extend 传 url= 可覆盖域名（分号分隔多个，按序 failover）
        if extend and isinstance(extend, str):
            m = re.search(r'url=([^&]+)', extend)
            if m:
                hosts = [h.strip().replace("https://", "").strip("/")
                         for h in m.group(1).split(";") if h.strip()]
                if hosts:
                    self.HOSTS = hosts
        self._log("初始化完成 hosts=%s" % self.HOSTS)

    def homeContent(self, filter=False):
        result = {
            "class": [
                {"type_id": tid, "type_name": name}
                for tid, name in self.CATEGORY_NAMES.items()
            ]
        }
        return result

    def homeVideoContent(self):
        try:
            html = self._get("/")
            if not html:
                return {"list": []}
            videos = self._parse_video_list(html)
            return {"list": videos[:30]}
        except Exception as e:
            self._log("homeVideoContent异常: %s" % e)
            return {"list": []}

    def categoryContent(self, tid, pg, filter=False, content=None):
        try:
            pg = max(1, int(pg or 1))
            if str(tid) not in self.CATEGORY_NAMES:
                return {"list": [], "page": pg, "pagecount": 1, "limit": 24, "total": 0}
            if pg == 1:
                path = "/show/%s-----------.html" % tid
            else:
                path = "/show/%s--------%d---.html" % (tid, pg)
            self._log("分类请求: " + path)
            html = self._get(path)
            if not html:
                return {"list": [], "page": pg, "pagecount": 1, "limit": 24, "total": 0}
            videos = self._parse_video_list(html)
            pagecount = 1
            m = re.search(r'共\s*(\d+)\s*页', html) or re.search(r'/(\d+)页', html)
            if m:
                pagecount = int(m.group(1))
            else:
                # 末页探测：翻页条最大页码
                pages = re.findall(r'/show/%s--------(\d+)---\.html' % tid, html)
                if pages:
                    pagecount = max(int(p) for p in pages)
            return {
                "list": videos,
                "page": pg,
                "pagecount": pagecount,
                "limit": 24,
                "total": pagecount * 24,
            }
        except Exception as e:
            self._log("categoryContent异常: %s" % e)
            return {"list": [], "page": pg, "pagecount": 1, "limit": 24, "total": 0}

    def searchContent(self, key, quick=False, pg="1"):
        try:
            try:
                pg = max(1, int(pg or 1))
            except (TypeError, ValueError):
                pg = 1
            keyword = str(key or "").strip()
            if not keyword:
                return {"page": pg, "pagecount": 1, "limit": 0, "total": 0, "list": []}
            if pg > 1:
                path = "/search/%s----%d--------.html" % (urllib.parse.quote(keyword), pg)
            else:
                path = "/search/%s-------------.html" % urllib.parse.quote(keyword)
            self._log("搜索请求: %s quick=%s" % (path, quick))
            html = self._get(path)
            if not html:
                return {"list": [], "page": pg, "pagecount": 1, "limit": 24, "total": 0}
            videos = self._parse_video_list(html)
            if not quick:
                key_lower = keyword.lower()

                def _score(v):
                    name = v.get("vod_name", "").lower()
                    if name == key_lower:
                        return 0
                    if name.startswith(key_lower):
                        return 1
                    if key_lower in name:
                        return 2
                    return 3
                videos = sorted(videos, key=_score)
            return {
                "list": videos,
                "page": pg,
                "pagecount": 9999,
                "limit": 24,
                "total": 999999,
            }
        except Exception as e:
            self._log("searchContent异常: %s" % e)
            return {"list": [], "page": pg, "pagecount": 1, "limit": 24, "total": 0}

    def detailContent(self, ids):
        try:
            vod_id = ids[0] if isinstance(ids, list) else str(ids)
            path = "/anime/%s.html" % vod_id
            self._log("详情请求: " + path)
            html = self._get(path)
            if not html:
                return {"list": []}

            title = re.search(r'<h1[^>]*class="[^"]*title[^"]*"[^>]*>([^<]*)</h1>', html)
            if not title:
                title = re.search(r'<h1[^>]*>([^<]*)</h1>', html)
            vod_name = title.group(1).strip() if title else "未知"

            vod_pic = ""
            pm = re.search(
                r'data-(?:original|src)="(https?://[^"]+/upload/vod/[^"]+\.(?:jpg|png|webp|jpeg)[^"]*)"',
                html, re.I)
            if not pm:
                pm = re.search(r'data-(?:original|src)="(https?://[^"]+)"', html)
            if pm:
                vod_pic = pm.group(1)
            if vod_pic.startswith("//"):
                vod_pic = "https:" + vod_pic

            # 元数据 p.data：类型/地区/年份一行合并；状态/导演/声优/更新独立
            datas = [self._clean_html(x) for x in re.findall(
                r'<p[^>]*class="[^"]*data[^"]*"[^>]*>([\s\S]*?)</p>', html)]
            joined = " | ".join(datas)

            def _field(label):
                m = re.search(label + r'[：:]\s*([^|/]+)', joined)
                return m.group(1).strip() if m else ""

            vod_year = _field("年份")
            vod_area = _field("地区")
            vod_actor = _field("声优") or _field("主演")
            vod_director = _field("导演")
            vod_remarks = _field("状态")
            type_line = _field("类型")
            if type_line:
                type_line = "类型：" + type_line

            desc = re.search(
                r'<span[^>]*class="[^"]*detail-content[^"]*"[^>]*>([\s\S]*?)</span>', html)
            if not desc:
                desc = re.search(
                    r'<span[^>]*class="[^"]*detail-sketch[^"]*"[^>]*>([\s\S]*?)</span>', html)
            vod_content = self._clean_html(desc.group(1)) if desc else ""

            sources = self._parse_play_sources(html, vod_id)
            if not sources:
                self._log("未能解析到播放源")
                return {"list": []}

            from_list = []
            url_list = []
            for src in sources:
                from_list.append(src["source_name"])
                url_list.append("#".join(
                    "%s$%s" % (ep["name"], ep["link"]) for ep in src["episodes"]))

            video = {
                "vod_id": vod_id,
                "vod_name": vod_name,
                "vod_pic": vod_pic,
                "vod_year": vod_year,
                "vod_area": vod_area,
                "vod_actor": vod_actor,
                "vod_director": vod_director,
                "vod_content": vod_content,
                "vod_remarks": vod_remarks,
                "vod_class": type_line,
                "vod_play_from": "$$$".join(from_list),
                "vod_play_url": "$$$".join(url_list),
            }
            self._log("详情解析成功: %s 线路: %s" % (vod_name, "$$$".join(from_list)))
            return {"list": [video]}
        except Exception as e:
            self._log("detailContent异常: %s" % e)
            return {"list": []}

    def playerContent(self, flag, id, vipFlags=None):
        try:
            parts = str(id).split("-")
            if len(parts) != 3:
                return {"parse": 0, "url": "", "header": ""}
            vod_id, sid, nid = parts
            meta = self._get_play_url(vod_id, sid, nid)
            if not meta or not meta.get("url"):
                host = getattr(self, "_cur_host", self.HOSTS[0])
                play_page = "https://%s/anime/%s/play/%s/%s.html" % (host, vod_id, sid, nid)
                return {"parse": 1, "url": play_page, "header": ""}
            url = meta["url"]
            if meta.get("type") == "direct" and re.search(
                    r"\.(m3u8|mp4|flv|ts|mkv)([?#&]|$)", url, re.I):
                h = self.play_headers.copy()
                h["Referer"] = "https://%s/" % getattr(
                    self, "_cur_host", self.HOSTS[0])
                return {"parse": 0, "url": url, "header": h}
            # v2player 解析页 / 外部页面 → 壳子 WebView 嗅探
            return {"parse": 1, "url": url, "header": ""}
        except Exception as e:
            self._log("playerContent异常: %s" % e)
            return {"parse": 0, "url": "", "header": ""}
        except Exception as e:
            self._log("playerContent异常: %s" % e)
            return {"parse": 0, "url": "", "header": ""}

    def getName(self):
        return self.name

    def isVideoFormat(self, url):
        pass

    def manualVideoCheck(self):
        pass

    def destroy(self):
        pass

    def localProxy(self, param):
        pass
