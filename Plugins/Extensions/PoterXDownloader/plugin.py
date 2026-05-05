# -*- coding: utf-8 -*-
from Plugins.Plugin import PluginDescriptor
from Screens.Screen import Screen
from Screens.MessageBox import MessageBox
from Components.Label import Label
from Components.Button import Button
from Components.ActionMap import ActionMap
from Components.ConfigList import ConfigListScreen
from Components.config import (
    config,
    ConfigText,
    ConfigSubsection,
    getConfigListEntry,
    ConfigYesNo,
    ConfigClock,
    ConfigSelection,
    ConfigNothing,
)
from enigma import eDVBDB, quitMainloop, eTimer, getDesktop
import os
import sys
import json
from datetime import datetime
import re
import tarfile
import zipfile
import io
import hashlib
import subprocess
import threading

# Virtual keyboard (availability depends on image)
try:
    from Screens.VirtualKeyBoard import VirtualKeyBoard
except Exception:
    VirtualKeyBoard = None

# --- WERSJA WTYCZKI ---
VERSION = "3.5.3"

# --- ADRESY ---
UPDATE_BASE_URL = "http://poterx.me/update"
PICONS_URL_TEMPLATE = UPDATE_BASE_URL + "/picons_%s.tar.gz"  # np. picons_220x132.tar.gz
TRACKER_URL = "http://poterx.me/tracker.php"
_CHANNEL_LIST_URL = "http://poterx.me/lista.zip"

# --- SCIEZKI ---
PLUGIN_PATH = "/usr/lib/enigma2/python/Plugins/Extensions/PoterXDownloader"
ICON_PATH = PLUGIN_PATH + "/plugin.png"
TARGET_PICON_PATH = "/usr/share/enigma2/picon"

# --- Kompatybilnosc Python 2 i 3 ---
PY3 = sys.version_info[0] == 3
if PY3:
    from urllib.request import urlopen, Request
    from urllib.error import HTTPError
    def to_str(b): return b.decode('utf-8', errors='ignore') if isinstance(b, bytes) else b
else:
    from urllib2 import urlopen, Request, HTTPError
    def to_str(b): return b

# --- Utils ---
def _parse_version(v):
    # "3.4.10" should be > "3.4.3" (string compare would be wrong).
    parts = []
    for p in re.split(r"[^0-9]+", (v or "").strip()):
        if not p:
            continue
        try:
            parts.append(int(p))
        except Exception:
            parts.append(0)
    return tuple(parts or [0])

def _sanitize_host(host):
    host = (host or "").strip()
    if not host:
        host = "http://potertv.ddns.me:80"
    if not host.startswith("http"):
        host = "http://" + host
    return host.rstrip("/")

def _encode_url_minimal(url):
    # Match your bash script: encode just the characters E2 bouquet parsing often chokes on.
    # Keep "/" intact (e.g. http%3a//example).
    s = url or ""
    s = s.replace(":", "%3A").replace("&", "%26").replace("?", "%3F").replace("=", "%3D")
    return s

def _decode_url_minimal(s):
    t = s or ""
    # reverse of _encode_url_minimal (case-insensitive for %3a)
    t = re.sub("(?i)%3a", ":", t)
    t = t.replace("%26", "&").replace("%3F", "?").replace("%3D", "=")
    return t

def _normalize_name(s):
    s = (s or "").strip().lower()
    # Usun prefiksy krajowe: "PL:", "PL |", "PL -", "UK:", "DE:", itp.
    s = re.sub(r"^[a-z]{2,3}\s*[:\|\-]\s*", "", s)
    # Usun "hd", "fhd", "uhd", "4k", "sd" tylko jako osobne slowa (nie w srodku nazwy)
    s = re.sub(r"\b(fhd|uhd|4k|sd)\b", "", s)
    s = re.sub(r"\bhd\b", "", s)
    # Usun znaki specjalne zostawiajac litery, cyfry, spacje
    s = re.sub(r"[^\w\s]", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s

def _slugify_filename(s, max_len=40):
    s = (s or "").lower().strip()
    s = re.sub(r"[^a-z0-9]+", "_", s)
    s = re.sub(r"_+", "_", s).strip("_")
    if not s:
        s = "kategoria"
    return s[:max_len]

def _name_to_picon_filename(name):
    """
    Service Name Picon (SNP) — generuje nazwe pliku picona z nazwy kanalu.
    Identyczne podejscie jak Bouquet_Maker_Xtream w trybie SNP:
      - lowercase, usun znaki specjalne, zostaw a-z0-9
    Przyklad: "CANAL+ Sport HD" → "canalsport.png"
    """
    s = (name or "").strip()
    s = s.replace("&", "and").replace("+", "plus").replace("*", "star")
    s = s.lower()
    s = re.sub(r"[^a-z0-9]", "", s)
    if not s:
        return ""
    return s + ".png"

def _xml_escape(s):
    s = s or ""
    return (
        s.replace("&", "&amp;")
         .replace("<", "&lt;")
         .replace(">", "&gt;")
         .replace('"', "&quot;")
         .replace("'", "&apos;")
    )

def _to_ascii_pl(s):
    table = {
        u"ą": "a", u"ć": "c", u"ę": "e", u"ł": "l", u"ń": "n", u"ó": "o", u"ś": "s", u"ż": "z", u"ź": "z",
        u"Ą": "a", u"Ć": "c", u"Ę": "e", u"Ł": "l", u"Ń": "n", u"Ó": "o", u"Ś": "s", u"Ż": "z", u"Ź": "z",
    }
    out = []
    for ch in (s or ""):
        out.append(table.get(ch, ch))
    return "".join(out)

def _canonical_key(s):
    s = _to_ascii_pl((s or "").lower())
    s = re.sub(r"[^a-z0-9]+", "", s)
    return s

def _parse_int_auto(s):
    v = (s or "").strip()
    if not v:
        return None
    try:
        return int(v)
    except Exception:
        pass
    try:
        return int(v, 16)
    except Exception:
        return None

def _parse_extinf_attrs(extinf_line):
    # EXTINF example: #EXTINF:-1 tvg-id="..." group-title="Sport",Channel Name
    attrs = {}
    try:
        for m in re.finditer(r'([a-zA-Z0-9_-]+)=\"([^\"]*)\"', extinf_line or ""):
            attrs[m.group(1)] = m.group(2)
    except Exception:
        pass
    return attrs

def _read_first_name_line(path):
    try:
        with open(path, "r") as f:
            first = f.readline().strip()
        if first.startswith("#NAME"):
            return first[5:].strip()
    except Exception:
        pass
    return ""

def _list_tv_bouquet_files():
    """
    Zwraca liste (filename, filepath) plikow bouquet TV.
    Rekursywnie sledzi FROM BOUQUET w pod-bouquetach (np. BMX-style).
    Kolejnosc: najpierw pliki z bouquets.tv, potem rekurencyjnie ich dzieci.
    Fallback: wszystkie userbouquet.*.tv z /etc/enigma2/.
    """
    base = "/etc/enigma2"
    idx = os.path.join(base, "bouquets.tv")
    out = []
    seen = set()

    def _collect_from_file(filepath):
        try:
            with open(filepath, "r") as f:
                for line in f:
                    m = re.search(r'FROM BOUQUET "([^"]+)"', line)
                    if not m:
                        continue
                    fn = m.group(1)
                    if fn in seen:
                        continue
                    seen.add(fn)
                    fp = os.path.join(base, fn)
                    out.append((fn, fp))
                    # Rekurencja – sprawdz czy pod-bouquet sam ma FROM BOUQUET
                    if os.path.exists(fp):
                        _collect_from_file(fp)
        except Exception:
            pass

    try:
        if os.path.exists(idx):
            _collect_from_file(idx)
    except Exception:
        pass

    if out:
        return out

    # Fallback: scan filesystem
    try:
        for fn in sorted(os.listdir(base)):
            if fn.startswith("userbouquet.") and fn.endswith(".tv"):
                if fn not in seen:
                    fp = os.path.join(base, fn)
                    out.append((fn, fp))
    except Exception:
        pass
    return out

# CANAL+ service refs (z Twojego skryptu) - uzywamy ich do auto-wykrywania listy Bzyk83 oraz podmiany.
_CANAL_SERVICES = [
    "1:0:1:32DC:190:13E:820000:0:0:0",
    "1:0:1:13ED:5DC:13E:820000:0:0:0",
    "1:0:1:3779:44C:13E:820000:0:0:0",
    "1:0:19:3782:44C:13E:820000:0:0:0",
    "1:0:1:377A:44C:13E:820000:0:0:0",
    "1:0:1:32DE:190:13E:820000:0:0:0",
    "1:0:1:13EE:5DC:13E:820000:0:0:0",
    "1:0:1:3AA0:514:13E:820000:0:0:0",
    "1:0:1:3AA1:514:13E:820000:0:0:0",
    "1:0:1:32E1:190:13E:820000:0:0:0",
    "1:0:1:37B5:44C:13E:820000:0:0:0",
    "1:0:1:3315:190:13E:820000:0:0:0",
    "1:0:1:32E4:190:13E:820000:0:0:0",
    "1:0:1:32CD:190:13E:820000:0:0:0",
]

def _score_bouquet_for_canal(path):
    try:
        with open(path, "r") as f:
            data = f.read()
    except Exception:
        return 0
    score = 0
    for ref in _CANAL_SERVICES:
        if ("#SERVICE " + ref) in data:
            score += 1
    return score

def _auto_detect_source_bouquet_path():
    candidates = _list_tv_bouquet_files()
    if not candidates:
        return ""

    best_path = ""
    best_score = -1
    for fn, fp in candidates:
        title = (_read_first_name_line(fp) or "").lower()
        bonus = 0
        if "bzyk" in title:
            bonus += 2
        if "polskie" in title:
            bonus += 1
        score = _score_bouquet_for_canal(fp) * 10 + bonus
        if score > best_score:
            best_score = score
            best_path = fp
    return best_path

# --- Konfiguracja ---
config.plugins.poterx = ConfigSubsection()
config.plugins.poterx.host = ConfigText(default="http://potertv.ddns.me:80", fixed_size=False)
config.plugins.poterx.username = ConfigText(default="", fixed_size=False)
try:
    from Components.config import ConfigPassword
    config.plugins.poterx.password = ConfigPassword(default="", fixed_size=False)
except Exception:
    config.plugins.poterx.password = ConfigText(default="", fixed_size=False)
config.plugins.poterx.auto_update = ConfigYesNo(default=False)
config.plugins.poterx.auto_update_time = ConfigClock(default=14400) # 04:00
# Niebieski przycisk: wybór akcji
config.plugins.poterx.blue_action = ConfigSelection(
    choices=[
        ("update", "Sprawdz aktualizacje wtyczki"),
        ("bzyk", "Podmień moje kanały IPTV"),
        ("hotbird", "Pobierz moja liste + Podmien Canal+"),
        ("epg", "Importuj EPG bezposrednio"),
    ],
    default="bzyk",
)

# Podmiana Bzyk83 (domyslne wartosci jak w Twoim skrypcie)
config.plugins.poterx.bzyk_source_bouquet = ConfigSelection(
    choices=[("", "Auto")],
    default="",
)
# Na starszych image (np. OpenPLi 8.3) czasem ConfigSelection nie umie dynamicznie pokazac listy.
# Pozwalamy wtedy wpisac sciezke recznie.
config.plugins.poterx.bzyk_source_path = ConfigText(default="", fixed_size=False)
config.plugins.poterx.bzyk_custom_title = ConfigText(default="Moja lista", fixed_size=False)
config.plugins.poterx.bzyk_custom_bouquet = ConfigText(default="userbouquet.mojalista.tv", fixed_size=False)
config.plugins.poterx.bzyk_insert_first = ConfigYesNo(default=True)

# Tryb: kopiuj do nowego bouquet (domyslnie) albo modyfikuj w miejscu (jak w starszych wersjach).
config.plugins.poterx.bzyk_target_mode = ConfigSelection(
    choices=[
        ("copy", "Tworz nowy bouquet (zachowaj oryginal)"),
        ("inplace", "Podmien w oryginalnym bouquet"),
    ],
    default="copy",
)

# Opcjonalnie: dodatkowy bouquet z "pozostalymi" kanalami z M3U (osobna lista w bouquets.tv)
config.plugins.poterx.bzyk_extra_enable = ConfigYesNo(default=False)
config.plugins.poterx.bzyk_extra_title = ConfigText(default="IPTV - Pozostale", fixed_size=False)
config.plugins.poterx.bzyk_extra_bouquet = ConfigText(default="userbouquet.iptv_pozostale.tv", fixed_size=False)

# Pobieranie listy z serwera i podmiana Canal+
config.plugins.poterx.hotbird_insert_first = ConfigYesNo(default=True)

# Picony – zrodlo i rozdzielczosc
config.plugins.poterx.picon_source = ConfigSelection(
    choices=[
        ("panel", "Z panelu IPTV (stream_icon z API)"),
        ("server", "Z serwera PoterX (paczka tar.gz)"),
    ],
    default="panel",
)
config.plugins.poterx.picon_size = ConfigSelection(
    choices=[
        ("50x30",   "50x30   (mini)"),
        ("100x60",  "100x60  (male)"),
        ("220x94",  "220x94  (xpicons slim)"),
        ("220x132", "220x132 (xpicons - standard)"),
        ("330x198", "330x198 (zpicons)"),
        ("400x170", "400x170 (szerokie)"),
        ("400x240", "400x240 (zzzpicons - duze)"),
    ],
    default="220x132",
)
config.plugins.poterx.picon_path = ConfigSelection(
    choices=[
        ("/usr/share/enigma2/picon", "/usr/share/enigma2/picon"),
        ("/media/hdd/picon", "/media/hdd/picon"),
        ("/media/usb/picon", "/media/usb/picon"),
        ("/data/picon", "/data/picon"),
    ],
    default="/usr/share/enigma2/picon",
)

def send_tracking_ping():
    try:
        mac = "unknown"
        if os.path.exists('/sys/class/net/eth0/address'):
            mac = open('/sys/class/net/eth0/address').read().strip()
        elif os.path.exists('/sys/class/net/wlan0/address'):
            mac = open('/sys/class/net/wlan0/address').read().strip()
        url = "{}?mac={}&ver={}".format(TRACKER_URL, mac, VERSION)
        req = Request(url)
        req.add_header('User-Agent', 'Enigma2-PoterX')
        urlopen(req, timeout=2)
    except: pass

# --- CLEANUP ---
def remove_old_configs():
    try:
        if hasattr(config.plugins, "serviceapp"):
            config.plugins.serviceapp.enigma2_impl.value = "enigma2"
            if hasattr(config.plugins.serviceapp.servicemp3, "gst_bufferlimit"):
                 config.plugins.serviceapp.servicemp3.gst_bufferlimit.value = 0
            if hasattr(config.plugins.serviceapp.servicemp3, "gst_buffertime"):
                 config.plugins.serviceapp.servicemp3.gst_buffertime.value = 0
            config.plugins.serviceapp.save()
            config.save()
    except: pass

# --- CORE POBIERANIA ---
def perform_playlist_update(silent=False, session=None):
    host = config.plugins.poterx.host.value
    user = config.plugins.poterx.username.value
    password = config.plugins.poterx.password.value

    remove_old_configs()
    send_tracking_ping()

    if not user or not password:
        if not silent and session: session.open(MessageBox, "Brak danych logowania!", MessageBox.TYPE_ERROR)
        return False

    host = _sanitize_host(host)
    
    url = "{}/playlist/{}/{}/dreambox?output=".format(host, user, password)

    try:
        req = Request(url)
        req.add_header('User-Agent', 'Enigma2-Plugin')
        response = urlopen(req, timeout=45)
        raw_data = response.read()
        
        if len(raw_data) < 100:
            if not silent and session: session.open(MessageBox, "Błąd: Pusty plik listy.", MessageBox.TYPE_ERROR)
            return False

        content = to_str(raw_data)
        lines = content.splitlines()
        new_lines = []
        target_name = "#NAME IPTV | PoterX"
        name_set = False
        
        for line in lines:
            line = line.strip()
            if line.startswith("#NAME"):
                new_lines.append(target_name)
                name_set = True
            elif line.startswith("#DESCRIPTION"):
                new_lines.append(line)
            elif line.startswith("#SERVICE"):
                # Upewniamy sie ze to standard DVB (1)
                if "#SERVICE 4097" not in line and "#SERVICE 500" not in line:
                     line = re.sub(r'^#SERVICE \d+:', '#SERVICE 1:', line)
                new_lines.append(line)
            else:
                new_lines.append(line)
        
        if not name_set: new_lines.insert(0, target_name)

        bouquet_filename = "userbouquet.canal_poterx.tv"
        bouquet_path = "/etc/enigma2/" + bouquet_filename
        with open(bouquet_path, "w") as f: f.write("\n".join(new_lines))

        index_path = "/etc/enigma2/bouquets.tv"
        entry_line = '#SERVICE 1:7:1:0:0:0:0:0:0:0:FROM BOUQUET "{}" ORDER BY bouquet'.format(bouquet_filename)
        if os.path.exists(index_path):
            try:
                with open(index_path, "r") as f: lines = f.readlines()
                lines = [line for line in lines if bouquet_filename not in line]
                if lines and not lines[-1].endswith('\n'): lines[-1] += '\n'
                if len(lines) > 0 and lines[0].startswith("#NAME"): lines.insert(1, entry_line + '\n')
                else: lines.insert(0, entry_line + '\n')
                with open(index_path, "w") as f: f.writelines(lines)
            except: pass

        eDVBDB.getInstance().reloadBouquets()
        eDVBDB.getInstance().reloadServicelist()
        
        return True

    except Exception as e:
        if not silent and session: session.open(MessageBox, "Błąd pobierania: " + str(e), MessageBox.TYPE_ERROR)
        return False

# --- AUTOMATYCZNA AKTUALIZACJA ---
class AutoUpdateCheck:
    def __init__(self):
        self.timer = eTimer()
        self.timer.callback.append(self.check)
        self.timer.start(60000, False)
        self.last_run_day = -1

    def check(self):
        if not config.plugins.poterx.auto_update.value: return
        now = datetime.now()
        target_ts = config.plugins.poterx.auto_update_time.value
        
        if self.last_run_day == now.day: return

        if now.hour == target_ts[0] and now.minute == target_ts[1]:
            success = perform_playlist_update(silent=True)
            if success:
                self.last_run_day = now.day
                quitMainloop(3) # Auto restart GUI po automacie

auto_update_instance = AutoUpdateCheck()

# --- AUTOMATYCZNY ODSWIEZACZ EPG (co 4h, jak satelitarny EIT) ---
class EPGAutoRefresh:
    """
    Periodycznie uruchamia EPGImport dla zrodla PoterX.
    Dziala w tle, jak EIT na satelicie – EPG zawsze aktualne.
    """
    _INTERVAL_MS = 4 * 3600 * 1000  # 4 godziny
    _INITIAL_DELAY_MS = 120 * 1000   # 2 minuty po starcie (zeby E2 zdazyl wstac)

    def __init__(self):
        self._timer = eTimer()
        self._timer.callback.append(self._run)
        self._timer.start(self._INITIAL_DELAY_MS, True)  # True = jednorazowy (initial)

    def _run(self):
        # Po pierwszym uruchomieniu przelacz na cykliczny timer
        self._timer.stop()
        self._timer.start(self._INTERVAL_MS, False)  # False = powtarzaj

        # Sprawdz czy mamy pliki EPG
        sources = "/etc/epgimport/poterx_iptv.sources.xml"
        channels = "/etc/epgimport/poterx_iptv.channels.xml"
        if not os.path.exists(sources) or not os.path.exists(channels):
            return

        # Probuj EPGImport
        epgimport_dir = "/usr/lib/enigma2/python/Plugins/Extensions/EPGImport"
        if os.path.isdir(epgimport_dir):
            try:
                from enigma import eEPGCache
                from Plugins.Extensions.EPGImport.EPGImport import EPGImport as EpgCls
                from Plugins.Extensions.EPGImport.EPGConfig import enumSourcesFile
                # channelFilter=None → importuj WSZYSTKO (nie odrzucaj)
                epg = EpgCls(eEPGCache.getInstance(), None)
                epg.onDone = lambda reboot=False, epgfile="": None
                src_list = list(enumSourcesFile(sources))
                if src_list:
                    epg.sources = src_list
                    epg.beginImport(longDescUntil=24 * 3600)
                    return  # OK, EPGImport ogarnia
            except Exception:
                pass

        # Fallback: bezposredni import XMLTV → eEPGCache (bez EPGImport)
        try:
            _direct_epg_import_standalone()
        except Exception:
            pass

def _direct_epg_import_standalone():
    """
    Standalone wersja bezposredniego importu EPG (do uzytku z timera).
    Czyta channels.xml + XMLTV → wstrzykuje do eEPGCache.
    """
    ch_path = "/etc/epgimport/poterx_iptv.channels.xml"
    if not os.path.exists(ch_path):
        return

    # Odczytaj mapowanie epg_id → service_ref z channels.xml
    epgid_to_sref = {}
    try:
        with open(ch_path, "r") as f:
            for line in f:
                m = re.search(r'<channel\s+id="([^"]+)">([^<]+)</channel>', line)
                if m:
                    eid = m.group(1).strip()
                    sref = m.group(2).strip()
                    if eid and sref and eid not in epgid_to_sref:
                        epgid_to_sref[eid] = sref
    except Exception:
        return
    if not epgid_to_sref:
        return

    host = _sanitize_host(config.plugins.poterx.host.value)
    user = config.plugins.poterx.username.value
    password = config.plugins.poterx.password.value
    if not user or not password:
        return

    xmltv_url = "%s/xmltv.php?username=%s&password=%s" % (host, user, password)
    try:
        req = Request(xmltv_url)
        req.add_header("User-Agent", "Enigma2-PoterX")
        xmltv_raw = to_str(urlopen(req, timeout=120).read())
    except Exception:
        return

    import time as _time
    try:
        from enigma import eEPGCache, eServiceReference
    except ImportError:
        return

    epgcache = eEPGCache.getInstance()
    has_importEvents = hasattr(epgcache, "importEvents")
    has_importEvent = hasattr(epgcache, "importEvent")
    if not has_importEvents and not has_importEvent:
        return

    imported = 0
    cur_channel = ""
    cur_start = 0
    cur_end = 0
    cur_title = ""
    cur_desc = ""
    in_programme = False

    def _parse_ts(s):
        s = (s or "").strip()[:14]
        try:
            return int(_time.mktime(_time.strptime(s, "%Y%m%d%H%M%S")))
        except Exception:
            return 0

    for line in xmltv_raw.splitlines():
        line = line.strip()
        if "<programme " in line:
            mc = re.search(r'channel="([^"]+)"', line)
            ms = re.search(r'start="([^"]+)"', line)
            me = re.search(r'stop="([^"]+)"', line)
            if mc and ms:
                cur_channel = mc.group(1).strip()
                cur_start = _parse_ts(ms.group(1))
                cur_end = _parse_ts(me.group(1)) if me else cur_start + 3600
                cur_title = ""
                cur_desc = ""
                in_programme = True
                tm = re.search(r'<title[^>]*>(.*?)</title>', line)
                if tm:
                    cur_title = re.sub(r'<[^>]+>', '', tm.group(1)).strip()
            continue

        if in_programme:
            tm = re.search(r'<title[^>]*>(.*?)</title>', line)
            if tm:
                cur_title = re.sub(r'<[^>]+>', '', tm.group(1)).strip()
            dm = re.search(r'<desc[^>]*>(.*?)</desc>', line)
            if dm:
                cur_desc = re.sub(r'<[^>]+>', '', dm.group(1)).strip()

        if "</programme>" in line and in_programme:
            in_programme = False
            sref_str = epgid_to_sref.get(cur_channel, "")
            if sref_str and cur_start and cur_title:
                try:
                    sref = eServiceReference(sref_str)
                    duration = max(cur_end - cur_start, 60)
                    evt = (cur_start, duration, cur_title, cur_desc[:200] if cur_desc else "", cur_desc or "")
                    if has_importEvents:
                        epgcache.importEvents(sref, [evt])
                    elif has_importEvent:
                        epgcache.importEvent(sref, evt)
                    imported += 1
                except Exception:
                    pass

    if imported > 0:
        try:
            epgcache.save()
        except Exception:
            pass

epg_refresh_instance = EPGAutoRefresh()

# --- GLOWNY EKRAN ---
class PoterXScreen(ConfigListScreen, Screen):
    # ── Wykrywanie rozdzielczości ────────────────────────────────────────────
    _DESKTOP_W = 720
    try:
        _DESKTOP_W = int(getDesktop(0).size().width())
    except Exception:
        _DESKTOP_W = 720

    # ZASADA RENDEROWANIA ENIGMA2:
    # eLabel zawsze renderuje się NAD widgetami tego samego zPosition=0.
    # Rozwiązanie: zPosition="5" na KAŻDYM widgecie tekstowym (header, config,
    # status, help, key_*) + transparent="1" by eLabel tło było widoczne.
    # Widget "config" BEZ transparent — system default background zawsze działa.

    if _DESKTOP_W >= 1920:
        # ── FHD 1920×1080 ──────────────────────────────────────────────────
        # eLabel=z0 (tlo), widget=z5 (tekst zawsze na wierzchu)
        skin = """
        <screen position="center,center" size="1280,720" title="PoterX Downloader">

            <eLabel position="0,0"     size="1280,720" backgroundColor="#0D1117" zPosition="0" />

            <!-- NAGLOWEK -->
            <eLabel position="0,0"     size="1280,76"  backgroundColor="#161B22" zPosition="0" />
            <eLabel position="0,0"     size="5,76"     backgroundColor="#1F6FEB" zPosition="0" />
            <eLabel position="0,74"    size="1280,3"   backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="header"      position="22,14" size="780,48"
                    font="Regular;32"  halign="left" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="820,20"  size="435,36"   backgroundColor="#1A2744" zPosition="0" />
            <eLabel position="820,20"  size="3,36"     backgroundColor="#1F6FEB" zPosition="0" />
            <eLabel position="1252,20" size="3,36"     backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="ver_label"   position="823,20" size="429,36"
                    font="Regular;22"  halign="center" valign="center"
                    foregroundColor="#60A5FA" transparent="1" zPosition="5" />

            <!-- CONFIG -->
            <eLabel position="0,78"    size="5,508"    backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="config"      position="6,78"  size="1268,508"
                    scrollbarMode="showOnDemand" zPosition="5" />

            <!-- POMOC -->
            <eLabel position="0,590"   size="1280,1"   backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="help"        position="14,594" size="1252,28"
                    font="Regular;20"  halign="left" valign="center"
                    foregroundColor="#64748B" transparent="1" zPosition="5" />

            <!-- STATUS -->
            <eLabel position="0,626"   size="1280,2"   backgroundColor="#334155" zPosition="0" />
            <eLabel position="0,628"   size="1280,44"  backgroundColor="#161B22" zPosition="0" />
            <eLabel position="14,638"  size="4,22"     backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="status"      position="26,628" size="1240,44"
                    font="Regular;22"  halign="left" valign="center"
                    foregroundColor="#94A3B8" transparent="1" zPosition="5" />

            <!-- PRZYCISKI -->
            <eLabel position="0,674"   size="1280,2"   backgroundColor="#21262D" zPosition="0" />
            <eLabel position="0,676"   size="1280,44"  backgroundColor="#0A0A14" zPosition="0" />
            <eLabel position="20,681"  size="295,34"   backgroundColor="#7F1D1D" zPosition="0" />
            <widget name="key_red"     position="20,681" size="295,34"
                    font="Regular;22"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="325,681" size="295,34"   backgroundColor="#14532D" zPosition="0" />
            <widget name="key_green"   position="325,681" size="295,34"
                    font="Regular;22"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="630,681" size="295,34"   backgroundColor="#713F12" zPosition="0" />
            <widget name="key_yellow"  position="630,681" size="295,34"
                    font="Regular;22"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="935,681" size="325,34"   backgroundColor="#1E3A8A" zPosition="0" />
            <widget name="key_blue"    position="935,681" size="325,34"
                    font="Regular;22"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
        </screen>"""

    elif _DESKTOP_W >= 1280:
        # ── HD 1280×720 ────────────────────────────────────────────────────
        skin = """
        <screen position="center,center" size="1100,580" title="PoterX Downloader">

            <eLabel position="0,0"     size="1100,580" backgroundColor="#0D1117" zPosition="0" />

            <!-- NAGLOWEK -->
            <eLabel position="0,0"     size="1100,66"  backgroundColor="#161B22" zPosition="0" />
            <eLabel position="0,0"     size="4,66"     backgroundColor="#1F6FEB" zPosition="0" />
            <eLabel position="0,64"    size="1100,3"   backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="header"      position="16,12" size="676,42"
                    font="Regular;28"  halign="left" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="706,18"  size="372,30"   backgroundColor="#1A2744" zPosition="0" />
            <eLabel position="706,18"  size="3,30"     backgroundColor="#1F6FEB" zPosition="0" />
            <eLabel position="1075,18" size="3,30"     backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="ver_label"   position="709,18" size="366,30"
                    font="Regular;20"  halign="center" valign="center"
                    foregroundColor="#60A5FA" transparent="1" zPosition="5" />

            <!-- CONFIG -->
            <eLabel position="0,68"    size="4,404"    backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="config"      position="5,68"  size="1090,404"
                    scrollbarMode="showOnDemand" zPosition="5" />

            <!-- POMOC -->
            <eLabel position="0,476"   size="1100,1"   backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="help"        position="10,480" size="1080,24"
                    font="Regular;18"  halign="left" valign="center"
                    foregroundColor="#64748B" transparent="1" zPosition="5" />

            <!-- STATUS -->
            <eLabel position="0,508"   size="1100,2"   backgroundColor="#334155" zPosition="0" />
            <eLabel position="0,510"   size="1100,38"  backgroundColor="#161B22" zPosition="0" />
            <eLabel position="10,520"  size="4,18"     backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="status"      position="22,510" size="1066,38"
                    font="Regular;20"  halign="left" valign="center"
                    foregroundColor="#94A3B8" transparent="1" zPosition="5" />

            <!-- PRZYCISKI -->
            <eLabel position="0,550"   size="1100,2"   backgroundColor="#21262D" zPosition="0" />
            <eLabel position="0,552"   size="1100,28"  backgroundColor="#0A0A14" zPosition="0" />
            <eLabel position="12,554"  size="254,24"   backgroundColor="#7F1D1D" zPosition="0" />
            <widget name="key_red"     position="12,554" size="254,24"
                    font="Regular;18"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="274,554" size="254,24"   backgroundColor="#14532D" zPosition="0" />
            <widget name="key_green"   position="274,554" size="254,24"
                    font="Regular;18"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="536,554" size="254,24"   backgroundColor="#713F12" zPosition="0" />
            <widget name="key_yellow"  position="536,554" size="254,24"
                    font="Regular;18"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="798,554" size="290,24"   backgroundColor="#1E3A8A" zPosition="0" />
            <widget name="key_blue"    position="798,554" size="290,24"
                    font="Regular;18"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
        </screen>"""

    else:
        # ── SD 720×576 ─────────────────────────────────────────────────────
        skin = """
        <screen position="center,center" size="660,430" title="PoterX Downloader">

            <eLabel position="0,0"     size="660,430"  backgroundColor="#0D1117" zPosition="0" />

            <!-- NAGLOWEK -->
            <eLabel position="0,0"     size="660,54"   backgroundColor="#161B22" zPosition="0" />
            <eLabel position="0,0"     size="4,54"     backgroundColor="#1F6FEB" zPosition="0" />
            <eLabel position="0,52"    size="660,2"    backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="header"      position="12,8"  size="418,38"
                    font="Regular;22"  halign="left" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="436,12"  size="212,30"   backgroundColor="#1A2744" zPosition="0" />
            <eLabel position="436,12"  size="3,30"     backgroundColor="#1F6FEB" zPosition="0" />
            <eLabel position="645,12"  size="3,30"     backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="ver_label"   position="439,12" size="206,30"
                    font="Regular;17"  halign="center" valign="center"
                    foregroundColor="#60A5FA" transparent="1" zPosition="5" />

            <!-- CONFIG -->
            <eLabel position="0,55"    size="4,272"    backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="config"      position="5,55"  size="650,272"
                    scrollbarMode="showOnDemand" zPosition="5" />

            <!-- POMOC -->
            <eLabel position="0,330"   size="660,1"    backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="help"        position="8,334" size="644,20"
                    font="Regular;16"  halign="left" valign="center"
                    foregroundColor="#64748B" transparent="1" zPosition="5" />

            <!-- STATUS -->
            <eLabel position="0,358"   size="660,2"    backgroundColor="#334155" zPosition="0" />
            <eLabel position="0,360"   size="660,36"   backgroundColor="#161B22" zPosition="0" />
            <eLabel position="8,369"   size="3,16"     backgroundColor="#1F6FEB" zPosition="0" />
            <widget name="status"      position="18,360" size="632,36"
                    font="Regular;17"  halign="left" valign="center"
                    foregroundColor="#94A3B8" transparent="1" zPosition="5" />

            <!-- PRZYCISKI -->
            <eLabel position="0,398"   size="660,2"    backgroundColor="#21262D" zPosition="0" />
            <eLabel position="0,400"   size="660,30"   backgroundColor="#0A0A14" zPosition="0" />
            <eLabel position="10,403"  size="148,24"   backgroundColor="#7F1D1D" zPosition="0" />
            <widget name="key_red"     position="10,403" size="148,24"
                    font="Regular;16"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="166,403" size="148,24"   backgroundColor="#14532D" zPosition="0" />
            <widget name="key_green"   position="166,403" size="148,24"
                    font="Regular;16"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="322,403" size="148,24"   backgroundColor="#713F12" zPosition="0" />
            <widget name="key_yellow"  position="322,403" size="148,24"
                    font="Regular;16"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />
            <eLabel position="478,403" size="172,24"   backgroundColor="#1E3A8A" zPosition="0" />
            <widget name="key_blue"    position="478,403" size="172,24"
                    font="Regular;16"  halign="center" valign="center"
                    foregroundColor="#FFFFFF" transparent="1" zPosition="5" />

            <eLabel position="168,401" size="150,26" backgroundColor="#14532D" />
            <widget name="key_green"
                    position="168,401" size="150,26"
                    font="Regular;17" halign="center" valign="center"
                    foregroundColor="#BBF7D0" backgroundColor="#14532D" />

        </screen>"""

    def __init__(self, session):
        Screen.__init__(self, session)
        self.session = session
        self.list = []

        self._refresh_bouquet_choices()

        # ── Sekcja 1: Konto ─────────────────────────────────────────────────
        self.list.append(getConfigListEntry(" >> KONTO IPTV", ConfigNothing()))
        self.list.append(getConfigListEntry("    Uzytkownik", config.plugins.poterx.username))
        self.list.append(getConfigListEntry("    Haslo", config.plugins.poterx.password))
        self.list.append(getConfigListEntry("    Auto aktualizacja", config.plugins.poterx.auto_update))
        self.list.append(getConfigListEntry("    Godzina auto", config.plugins.poterx.auto_update_time))
        self.list.append(getConfigListEntry("    Akcja niebieskiego", config.plugins.poterx.blue_action))

        # ── Sekcja 2: Podmiana kanałów ───────────────────────────────────────
        self.list.append(getConfigListEntry(" >> PODMIANA KANALOW", ConfigNothing()))
        self.list.append(getConfigListEntry("    Zrodlo (lista)", config.plugins.poterx.bzyk_source_bouquet))
        self.list.append(getConfigListEntry("    Zrodlo (sciezka recznie)", config.plugins.poterx.bzyk_source_path))
        self.list.append(getConfigListEntry("    Tryb zapisu", config.plugins.poterx.bzyk_target_mode))
        self.list.append(getConfigListEntry("    Tytul nowej listy", config.plugins.poterx.bzyk_custom_title))
        self.list.append(getConfigListEntry("    Plik nowej listy", config.plugins.poterx.bzyk_custom_bouquet))
        self.list.append(getConfigListEntry("    Wstaw na 1 miejscu", config.plugins.poterx.bzyk_insert_first))

        # ── Sekcja 3: Dodatkowa lista ────────────────────────────────────────
        self.list.append(getConfigListEntry(" >> DODATKOWA LISTA IPTV", ConfigNothing()))
        self.list.append(getConfigListEntry("    Utworz liste z reszta", config.plugins.poterx.bzyk_extra_enable))
        self.list.append(getConfigListEntry("    Tytul listy", config.plugins.poterx.bzyk_extra_title))
        self.list.append(getConfigListEntry("    Plik listy", config.plugins.poterx.bzyk_extra_bouquet))

        # ── Sekcja 3b: Moja lista z serwera ─────────────────────────────────
        self.list.append(getConfigListEntry(" >> MOJA LISTA Z SERWERA", ConfigNothing()))
        self.list.append(getConfigListEntry("    Wstaw na 1 miejscu", config.plugins.poterx.hotbird_insert_first))

        # ── Sekcja 4: Picony ─────────────────────────────────────────────────
        self.list.append(getConfigListEntry(" >> PICONY", ConfigNothing()))
        self.list.append(getConfigListEntry("    Zrodlo piconow", config.plugins.poterx.picon_source))
        self.list.append(getConfigListEntry("    Rozdzielczosc", config.plugins.poterx.picon_size))
        self.list.append(getConfigListEntry("    Katalog docelowy", config.plugins.poterx.picon_path))
        
        ConfigListScreen.__init__(self, self.list, session=self.session)
        title_full = "PoterX Downloader v%s" % VERSION
        self.setTitle(title_full)          # pasek tytułu okna (niezależny od skinu)
        self["header"] = Label("PoterX Downloader")
        try:
            self["ver_label"] = Label("v%s" % VERSION)
        except Exception:
            pass
        self["status"] = Label("Inicjalizacja...")
        self["help"] = Label("Klawisz 0 = Diagnostyka EPG")

        self["key_red"]    = Button("Wyjscie")
        self["key_green"]  = Button("Pobierz IPTV")
        self["key_yellow"] = Button("Pobierz picony")
        self["key_blue"]   = Button("Podmien kanaly")
        self._refresh_key_labels()
        
        self["setupActions"] = ActionMap(["SetupActions", "ColorActions", "NumberActions"], {
            "green": self.download_direct,
            "red": self.cancel,
            "cancel": self.cancel,
            "blue": self.blue_action,
            "yellow": self.ask_picons,
            "ok": self.ok_pressed,
            "0": self.run_epg_diagnostic,
        }, -2)
        
        self.onLayoutFinish.append(self.auto_check_update)
        try:
            self["config"].onSelectionChanged.append(self._on_selection_changed)
        except Exception:
            pass
        self.onLayoutFinish.append(self._on_selection_changed)

    def _refresh_key_labels(self):
        action = config.plugins.poterx.blue_action.value
        if action == "bzyk":
            self["key_blue"].setText("Podmien kanaly")
        elif action == "hotbird":
            self["key_blue"].setText("Pobierz+Canal+")
        elif action == "epg":
            self["key_blue"].setText("Importuj EPG")
        else:
            self["key_blue"].setText("Sprawdz aktualizacje")

    def ok_pressed(self):
        cur = None
        try:
            cur = self["config"].getCurrent()
        except Exception:
            cur = None

        if not cur or len(cur) < 2:
            return

        label, cfg = cur[0], cur[1]

        # Full-screen virtual keyboard for text inputs.
        if VirtualKeyBoard is not None and hasattr(cfg, "value"):
            try:
                val = cfg.value
            except Exception:
                val = None
            if isinstance(val, str):
                title = "Wpisz: %s" % (label or "")
                self.session.openWithCallback(lambda txt: self._vk_cb(cfg, txt), VirtualKeyBoard, title=title, text=val)
                return

        # For other config types, OK cycles forward.
        try:
            self.keyRight()
        except Exception:
            pass

    def _vk_cb(self, cfg, txt):
        if txt is None:
            return
        try:
            cfg.value = txt
            cfg.save()
        except Exception:
            pass
        try:
            self["config"].invalidateCurrent()
        except Exception:
            pass
        self._on_selection_changed()

    def _on_selection_changed(self):
        # Etykiety musza pasowac DOKLADNIE do nazw w self.list (ASCII, bez polskich znakow).
        try:
            cur = self["config"].getCurrent()
            label = (cur[0] or "").strip() if cur else ""
        except Exception:
            label = ""

        help_txt = ""
        if "Uzytkownik" in label or "Haslo" in label:
            help_txt = "Dane do logowania IPTV. OK = klawiatura ekranowa."
        elif "Auto aktualizacja" in label or "Godzina auto" in label:
            help_txt = "Automatyczne odswiezanie listy i restart GUI o wybranej godzinie."
        elif "Akcja niebieskiego" in label:
            if config.plugins.poterx.blue_action.value == "bzyk":
                help_txt = "Niebieski: podmienia CANAL+ w liscie Bzyk83."
            else:
                help_txt = "Niebieski: sprawdza aktualizacje wtyczki."
        elif "Zrodlo (lista)" in label or "Zrodlo (sciezka" in label:
            help_txt = "Wybierz bukiet zrodlowy. Jesli lista pusta, wpisz recznie sciezke z /etc/enigma2."
        elif "Tryb zapisu" in label:
            help_txt = "Copy: tworzy nowa liste (bezpieczne). Inplace: podmienia oryginalna (robi backup)."
        elif "Tytul nowej listy" in label or "Plik nowej listy" in label:
            help_txt = "Dotyczy tylko trybu Copy (nowa lista)."
        elif "Wstaw na 1 miejscu" in label:
            help_txt = "Tak: nowa lista pojawi sie jako pierwsza na liscie buketow."
        elif "Utworz liste z reszta" in label:
            help_txt = "Dodatkowy buket z pozostalymi kanalami IPTV (poza podmienionymi)."
        elif "Tytul listy" in label or "Plik listy" in label:
            help_txt = "Nazwa i plik dodatkowego buketu z reszta kanalow IPTV."
        elif "Zrodlo piconow" in label:
            help_txt = "Panel: pobiera loga z API (stream_icon). Serwer: gotowa paczka tar.gz z PoterX."
        elif "Rozdzielczosc" in label:
            help_txt = "Rozmiar piconow. 220x132 = standard (xpicons). 400x240 = duze (zzzpicons)."
        elif "Katalog docelowy" in label:
            help_txt = "Gdzie zapisac picony. Domyslnie /usr/share/enigma2/picon."

        self["help"].setText(help_txt)
        self._refresh_key_labels()

    def _refresh_bouquet_choices(self):
        bouquets = _list_tv_bouquet_files()
        choices = [("", "Auto (wybierz pozniej)")]
        for fn, fp in bouquets:
            title = _read_first_name_line(fp) or fn
            choices.append((fn, title))
        try:
            config.plugins.poterx.bzyk_source_bouquet.setChoices(choices, default=config.plugins.poterx.bzyk_source_bouquet.value)
        except Exception:
            # Older images may not have setChoices; keep default list.
            pass

    def save(self):
        for x in self["config"].list: x[1].save()
        config.save()
        self.download_direct()

    def cancel(self):
        self.close()

    def auto_check_update(self):
        remove_old_configs()
        self["status"].setText("Sprawdzanie wersji wtyczki...")
        try:
            req = Request("{}/version.txt".format(UPDATE_BASE_URL))
            req.add_header('User-Agent', 'Enigma2-PoterX')
            response = urlopen(req, timeout=3)
            new_version = to_str(response.read()).strip()
            if _parse_version(new_version) > _parse_version(VERSION):
                self.session.openWithCallback(self.auto_update_callback, MessageBox, 
                    "Dostępna nowa wersja: %s\nZaktualizować?" % new_version, MessageBox.TYPE_YESNO)
            else:
                self.check_account_info()
        except:
            self.check_account_info()

    def auto_update_callback(self, confirm):
        if confirm: self.do_update(True)
        else: self.check_account_info()

    def check_account_info(self):
        host = config.plugins.poterx.host.value
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        
        if not user or not password:
            self["status"].setText("Wpisz login i hasło.")
            return

        host = _sanitize_host(host)

        api_url = "{}/player_api.php?username={}&password={}".format(host, user, password)
        self["status"].setText("Weryfikacja...")
        
        try:
            req = Request(api_url)
            req.add_header('User-Agent', 'Enigma2-Plugin')
            response = urlopen(req, timeout=5)
            data = response.read()
            json_data = json.loads(to_str(data))
            user_info = json_data.get('user_info', {})
            
            if user_info.get('auth', 0) == 0:
                self["status"].setText("BŁĄD: Złe dane logowania!")
                return
            
            exp_date = user_info.get('exp_date')
            if exp_date is None or exp_date == "null": expiry_str = "Bez limitu"
            else:
                try: expiry_str = datetime.fromtimestamp(int(exp_date)).strftime('%d-%m-%Y')
                except: expiry_str = "Nieznana"

            self["status"].setText("Konto aktywne do: %s" % expiry_str)
        except:
            self["status"].setText("Gotowy.")

    def manual_check_update(self):
        self["status"].setText("Sprawdzanie aktualizacji...")
        try:
            req = Request("{}/version.txt".format(UPDATE_BASE_URL))
            req.add_header('User-Agent', 'Enigma2-PoterX')
            new_version = to_str(urlopen(req, timeout=10).read()).strip()
            if _parse_version(new_version) > _parse_version(VERSION):
                self.session.openWithCallback(self.do_update, MessageBox,
                    "Dostepna nowa wersja: %s\nZaktualizowac?" % new_version, MessageBox.TYPE_YESNO)
            else:
                self["status"].setText("Wersja aktualna.")
                self.session.open(MessageBox, "Masz najnowsza wersje wtyczki (%s)." % VERSION, MessageBox.TYPE_INFO)
                self.check_account_info()
        except Exception as e:
            self["status"].setText("Blad sprawdzania aktualizacji.")
            self.session.open(MessageBox, "Blad sprawdzania aktualizacji: " + str(e), MessageBox.TYPE_ERROR)

    def blue_action(self):
        action = config.plugins.poterx.blue_action.value
        if action == "bzyk":
            self.run_bzyk_replace()
        elif action == "hotbird":
            self.ask_download_hotbird()
        elif action == "epg":
            self.run_epg_import_threaded()
        else:
            self.manual_check_update()

    # ══════════════════════════════════════════════════════════════════════════
    #  BEZPOSREDNI IMPORT EPG – niebieski przycisk (akcja "epg")
    #  Pobiera XMLTV w watku z postepem MB, parsuje, wstrzykuje do eEPGCache
    #  w glownym watku (przez eTimer) – thread-safe.
    # ══════════════════════════════════════════════════════════════════════════

    def run_epg_import_threaded(self):
        """Start background EPG import with real-time MB progress."""
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        if not user or not password:
            self.session.open(MessageBox, "Brak danych logowania (uzytkownik/haslo).", MessageBox.TYPE_ERROR)
            return

        # Guard: don't start twice
        if getattr(self, "_epg_import_running", False):
            self["status"].setText("Import EPG jest juz uruchomiony...")
            return

        self._epg_import_running = True
        self._epg_import_result  = None          # set by thread when done
        self._epg_import_status  = "Inicjalizacja..."
        self._epg_pending_events = {}            # sref_str -> [evt, ...]
        self._epg_channel_count  = 0

        host = _sanitize_host(config.plugins.poterx.host.value)
        self["status"].setText("EPG: uruchamianie...")

        t = threading.Thread(target=self._epg_import_thread, args=(host, user, password))
        t.daemon = True
        t.start()

        self._epg_import_timer = eTimer()
        self._epg_import_timer.callback.append(self._epg_import_poll_check)
        self._epg_import_timer.start(500, False)   # poll every 500 ms

    def _epg_import_thread(self, host, user, password):
        """
        Background worker:
          1. get_live_streams → build epg_channel_id → service_ref map
          2. Download xmltv.php with chunk-by-chunk MB progress
          3. Parse <programme> tags into events list
        No Enigma2 API calls here – all injection happens in the main thread.
        """
        import time as _time

        def _parse_xmltv_time(s):
            s = (s or "").strip()
            ts_part = s[:14] if len(s) >= 14 else s
            try:
                return int(_time.mktime(_time.strptime(ts_part, "%Y%m%d%H%M%S")))
            except Exception:
                return 0

        try:
            # ── Step 1: get_live_streams ─────────────────────────────────────
            self._epg_import_status = "Pobieranie listy kanalow z API panelu..."
            streams_url = "%s/player_api.php?username=%s&password=%s&action=get_live_streams" % (
                host, user, password
            )
            req = Request(streams_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            raw = to_str(urlopen(req, timeout=60).read())
            streams = json.loads(raw)

            if not isinstance(streams, list) or not streams:
                self._epg_import_result = (False, "API nie zwrocilo listy kanalow.")
                return

            # ── Step 2: match stream epg_channel_id to bouquet service refs ──
            self._epg_import_status = "Mapowanie %d kanalow..." % len(streams)
            bouquet_by_stream, bouquet_by_norm, bouquet_by_canon = self._collect_bouquet_channel_maps()

            epgid_to_refs = {}   # epg_channel_id -> [sref_str, ...]
            for stream in streams:
                epg_id = (
                    str(stream.get("epg_channel_id") or "").strip()
                    or str(stream.get("tvg_id") or "").strip()
                )
                if not epg_id:
                    continue
                stream_id = str(stream.get("stream_id") or "").strip()
                name      = str(stream.get("name") or "").strip()

                pair = None
                if stream_id and stream_id in bouquet_by_stream:
                    pair = bouquet_by_stream[stream_id]
                if not pair and name:
                    for v in self._name_variants(name):
                        if v in bouquet_by_norm:
                            pair = bouquet_by_norm[v]
                            break
                if not pair and name:
                    for v in self._name_variants(name):
                        ck = _canonical_key(v)
                        if ck in bouquet_by_canon:
                            pair = bouquet_by_canon[ck]
                            break

                if pair:
                    refs = self._service_ref_variants("", pair[1])
                    if refs:
                        epgid_to_refs[epg_id] = refs

            if not epgid_to_refs:
                self._epg_import_result = (
                    False,
                    "Nie zmatchowano zadnego kanalu EPG.\n"
                    "Sprawdz czy kanaly IPTV sa w bouquetach Enigma2."
                )
                return

            self._epg_channel_count = len(epgid_to_refs)

            # ── Step 3: Download XMLTV with chunk-by-chunk MB progress ───────
            xmltv_url = "%s/xmltv.php?username=%s&password=%s" % (host, user, password)
            req = Request(xmltv_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            response = urlopen(req, timeout=150)

            content_length = 0
            try:
                content_length = int(response.headers.get("Content-Length") or 0)
            except Exception:
                pass
            total_mb = content_length / (1024.0 * 1024.0) if content_length > 0 else 0

            chunks    = []
            downloaded = 0
            last_mb   = -1

            while True:
                chunk = response.read(65536)
                if not chunk:
                    break
                chunks.append(chunk)
                downloaded += len(chunk)
                current_mb = downloaded // (1024 * 1024)
                if current_mb != last_mb:
                    last_mb = current_mb
                    if content_length > 0:
                        pct = int(downloaded * 100 / content_length)
                        self._epg_import_status = (
                            "Pobieranie XMLTV: %.1f / %.1f MB (%d%%)" % (current_mb, total_mb, pct)
                        )
                    else:
                        self._epg_import_status = "Pobieranie XMLTV: %.1f MB..." % current_mb

            xmltv_raw = to_str(b"".join(chunks))
            chunks = None   # free memory

            # ── Step 4: Parse <programme> tags ───────────────────────────────
            self._epg_import_status = "Parsowanie XMLTV..."
            lines       = xmltv_raw.splitlines()
            xmltv_raw   = None   # free memory
            total_lines = len(lines)

            events_by_ref = {}   # sref_str -> [(start, dur, title, short_desc, long_desc), ...]
            total_parsed  = 0

            in_prog   = False
            cur_ch    = ""
            cur_start = 0
            cur_end   = 0
            cur_title = ""
            cur_desc  = ""

            for i, line in enumerate(lines):
                line = line.strip()

                # Update status every ~20 000 lines
                if (i % 20000) == 0 and total_lines > 0:
                    self._epg_import_status = (
                        "Parsowanie XMLTV: %.0f%% (%d eventow)..." % (
                            i * 100.0 / total_lines, total_parsed
                        )
                    )

                if "<programme " in line:
                    mc = re.search(r'channel="([^"]+)"', line)
                    ms = re.search(r'start="([^"]+)"', line)
                    me = re.search(r'stop="([^"]+)"', line)
                    if mc and ms:
                        cur_ch    = mc.group(1).strip()
                        cur_start = _parse_xmltv_time(ms.group(1))
                        cur_end   = _parse_xmltv_time(me.group(1)) if me else cur_start + 3600
                        cur_title = ""
                        cur_desc  = ""
                        in_prog   = True
                        tm = re.search(r'<title[^>]*>(.*?)</title>', line)
                        if tm:
                            cur_title = re.sub(r'<[^>]+>', '', tm.group(1)).strip()
                    continue

                if in_prog:
                    tm = re.search(r'<title[^>]*>(.*?)</title>', line)
                    if tm:
                        cur_title = re.sub(r'<[^>]+>', '', tm.group(1)).strip()
                    dm = re.search(r'<desc[^>]*>(.*?)</desc>', line)
                    if dm:
                        cur_desc = re.sub(r'<[^>]+>', '', dm.group(1)).strip()

                if "</programme>" in line and in_prog:
                    in_prog = False
                    refs = epgid_to_refs.get(cur_ch)
                    if refs and cur_start and cur_title:
                        duration = max(cur_end - cur_start, 60)
                        evt = (
                            cur_start,
                            duration,
                            cur_title,
                            cur_desc[:200] if cur_desc else "",
                            cur_desc or "",
                        )
                        for sref_str in refs:
                            events_by_ref.setdefault(sref_str, []).append(evt)
                        total_parsed += 1

            lines = None  # free memory

            self._epg_import_status = (
                "Przygotowano %d eventow dla %d referencji. Wstrzykiwanie..." % (
                    total_parsed, len(events_by_ref)
                )
            )
            self._epg_pending_events = events_by_ref
            # Signal the poll timer: ready to inject (main thread)
            self._epg_import_result = (True, total_parsed)

        except Exception as ex:
            self._epg_import_result = (False, "Blad importu EPG: %s" % str(ex))

    def _epg_import_poll_check(self):
        """
        eTimer callback – runs in the Enigma2 main thread.
        While the worker is running: update status label.
        When done: inject events into eEPGCache (thread-safe here).
        """
        if self._epg_import_result is None:
            # Worker still running – show its latest status message
            self["status"].setText(getattr(self, "_epg_import_status", "EPG import..."))
            return

        # Worker finished – stop polling
        self._epg_import_timer.stop()
        self._epg_import_running = False

        ok, data = self._epg_import_result

        if not ok:
            self["status"].setText("Blad importu EPG.")
            self.session.open(MessageBox, "Blad importu EPG:\n%s" % data, MessageBox.TYPE_ERROR)
            self._epg_pending_events = {}
            return

        total_parsed  = data
        events_by_ref = getattr(self, "_epg_pending_events", {})

        if not events_by_ref:
            self["status"].setText("Brak eventow EPG do wstrzykniecia.")
            self.session.open(
                MessageBox,
                "Parsowanie OK (%d eventow), ale brak zmapowanych referencji." % total_parsed,
                MessageBox.TYPE_INFO,
            )
            return

        # ── Inject events into eEPGCache (main thread – safe) ────────────────
        self["status"].setText("Wstrzykiwanie %d eventow EPG..." % total_parsed)
        try:
            from enigma import eEPGCache, eServiceReference
            epgcache         = eEPGCache.getInstance()
            has_importEvents = hasattr(epgcache, "importEvents")
            has_importEvent  = hasattr(epgcache, "importEvent")

            if not has_importEvents and not has_importEvent:
                self.session.open(
                    MessageBox,
                    "eEPGCache nie ma importEvents/importEvent.\nStary lub niekompatybilny image.",
                    MessageBox.TYPE_ERROR,
                )
                return

            injected = 0
            for sref_str, events in events_by_ref.items():
                try:
                    sref = eServiceReference(sref_str)
                    if has_importEvents:
                        epgcache.importEvents(sref, events)
                    else:
                        for evt in events:
                            epgcache.importEvent(sref, evt)
                    injected += len(events)
                except Exception:
                    pass

            try:
                epgcache.save()
            except Exception:
                pass

            ch_count = getattr(self, "_epg_channel_count", 0)
            msg = (
                "Import EPG zakonczony!\n\n"
                "Wstrzyknietych eventow: %d\n"
                "Kanalow zmapowanych:    %d\n"
                "Referencji serwisow:    %d\n\n"
                "EPG bedzie widoczne w przewodniku."
            ) % (injected, ch_count, len(events_by_ref))

            self["status"].setText("EPG OK: %d eventow." % injected)
            self.session.open(MessageBox, msg, MessageBox.TYPE_INFO)

        except ImportError:
            self.session.open(
                MessageBox, "Brak enigma (eEPGCache). Niekompatybilny image.", MessageBox.TYPE_ERROR
            )
        except Exception as ex:
            self.session.open(
                MessageBox, "Blad wstrzykiwania EPG: %s" % str(ex), MessageBox.TYPE_ERROR
            )
        finally:
            self._epg_pending_events = {}

    # ══════════════════════════════════════════════════════════════════════════
    #  DIAGNOSTYKA EPG – klawisz 0
    # ══════════════════════════════════════════════════════════════════════════
    def run_epg_diagnostic(self):
        """
        Pelna diagnostyka EPG – sprawdza kazdy krok i pokazuje wynik.
        Uruchamiane klawiszem 0.
        """
        self["status"].setText("Diagnostyka EPG...")
        diag = []

        host = _sanitize_host(config.plugins.poterx.host.value)
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value

        # ── 1. Dane logowania ──────────────────────────────────────────────
        if not user or not password:
            diag.append("[BLAD] Brak danych logowania (uzytkownik/haslo).")
            self.session.open(MessageBox, "\n".join(diag), MessageBox.TYPE_ERROR)
            return
        diag.append("[OK] Login: %s" % user)

        # ── 2. EPGImport zainstalowany? ────────────────────────────────────
        epgi_dir = "/usr/lib/enigma2/python/Plugins/Extensions/EPGImport"
        if os.path.isdir(epgi_dir):
            diag.append("[OK] EPGImport: ZAINSTALOWANY")
        else:
            diag.append("[BLAD] EPGImport: NIEZAINSTALOWANY!")
            diag.append("   >> opkg install enigma2-plugin-extensions-epgimport")

        # ── 3. Pliki EPG istnieja? ─────────────────────────────────────────
        ch_path = "/etc/epgimport/poterx_iptv.channels.xml"
        src_path = "/etc/epgimport/poterx_iptv.sources.xml"
        if os.path.exists(ch_path):
            try:
                with open(ch_path, "r") as f:
                    ch_content = f.read()
                ch_count = ch_content.count("<channel ")
                diag.append("[OK] channels.xml: %d kanalow" % ch_count)
                if ch_count == 0:
                    diag.append("   >> PUSTY! Uruchom 'Pobierz IPTV' aby wygenerowac.")
            except Exception as e:
                diag.append("[BLAD] channels.xml: nie mozna odczytac: %s" % str(e))
        else:
            diag.append("[BLAD] channels.xml: NIE ISTNIEJE")
            diag.append("   >> Uruchom 'Pobierz IPTV' (zielony) aby wygenerowac pliki EPG.")

        if os.path.exists(src_path):
            diag.append("[OK] sources.xml: istnieje")
        else:
            diag.append("[BLAD] sources.xml: NIE ISTNIEJE")

        # ── 4. XMLTV feed dziala? ─────────────────────────────────────────
        xmltv_url = "%s/xmltv.php?username=%s&password=%s" % (host, user, password)
        diag.append("")
        diag.append("--- TEST XMLTV ---")
        try:
            req = Request(xmltv_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            resp = urlopen(req, timeout=15)
            # Czytaj tylko poczatek (max 4KB) zeby nie zaladowac calego pliku
            chunk = to_str(resp.read(4096))
            if "<tv" in chunk or "<channel" in chunk:
                # Policz kanaly w przykladzie
                sample_channels = chunk.count("<channel ")
                diag.append("[OK] XMLTV feed dziala (>=%d kanalow w probie)" % sample_channels)
            elif "<?xml" in chunk:
                diag.append("[OK] XMLTV feed odpowiada XML, ale brak tagow <tv>/<channel>")
                diag.append("   >> Moze puste dane EPG na panelu.")
            else:
                diag.append("[BLAD] XMLTV feed nie zwraca XML!")
                diag.append("   >> Pierwsze 200 zn: %s" % chunk[:200])
        except Exception as e:
            diag.append("[BLAD] XMLTV feed niedostepny: %s" % str(e))

        # ── 5. Bouquety – ile kanalow, ile z #DESCRIPTION ──────────────────
        diag.append("")
        diag.append("--- BOUQUETY ---")
        bouquet_list = _list_tv_bouquet_files()
        diag.append("Znalezione pliki bouquet: %d" % len(bouquet_list))
        # Pokaz pierwsze 5 nazw plikow
        for fn, fp in bouquet_list[:5]:
            diag.append("  >> %s [%s]" % (fn, "OK" if os.path.exists(fp) else "BRAK"))
        if len(bouquet_list) > 5:
            diag.append("  ... i %d wiecej" % (len(bouquet_list) - 5))

        total_srv = 0
        total_desc = 0
        total_stream = 0
        bouquet_names_sample = []
        first_file_shown = False
        for fn, fp in bouquet_list:
            try:
                with open(fp, "r") as f:
                    blines = [l.strip() for l in f.readlines()]
                srv_count = sum(1 for l in blines if l.startswith("#SERVICE ") and "FROM BOUQUET" not in l.upper())
                desc_count = sum(1 for l in blines if l.startswith("#DESCRIPTION"))
                sub_count = sum(1 for l in blines if "FROM BOUQUET" in l.upper())
                total_srv += srv_count
                total_desc += desc_count
                # Policz stream_id w URLach
                for bl in blines:
                    if bl.startswith("#SERVICE ") and "FROM BOUQUET" not in bl.upper():
                        srv_ref = bl[len("#SERVICE "):].strip()
                        sid = self._extract_stream_id_from_service(srv_ref)
                        if sid:
                            total_stream += 1
                if srv_count > 0 or sub_count > 0:
                    diag.append("  %s: %d kanalow, %d opisow, %d sub-bouquet" % (fn, srv_count, desc_count, sub_count))
                # Pierwsze linie pierwszego pliku z kanalami (debug)
                if srv_count > 0 and not first_file_shown:
                    first_file_shown = True
                    diag.append("  Przyklad linii z '%s':" % fn)
                    shown = 0
                    for bl in blines:
                        if bl.startswith("#SERVICE ") and "FROM BOUQUET" not in bl.upper():
                            diag.append("    %s" % bl[:100])
                            shown += 1
                            if shown >= 2:
                                break
                # Zbierz przykladowe nazwy
                if len(bouquet_names_sample) < 5:
                    for bl in blines:
                        if bl.startswith("#DESCRIPTION") and len(bouquet_names_sample) < 5:
                            bouquet_names_sample.append(bl[len("#DESCRIPTION"):].strip())
            except Exception as ex:
                diag.append("  [BLAD] %s: %s" % (fn, str(ex)))
        diag.append("RAZEM: %d kanalow, %d opisow, %d z URL/stream_id" % (total_srv, total_desc, total_stream))
        if total_srv == 0:
            diag.append("[UWAGA] Brak kanalow w bouquetach! Uruchom 'Pobierz IPTV' (zielony).")
        elif total_desc == 0 and total_stream == 0:
            diag.append("[UWAGA] Brak #DESCRIPTION i URL – matchowanie EPG niemozliwe!")
        elif total_desc == 0:
            diag.append("[INFO] Brak #DESCRIPTION – EPG bedie matchowany po stream_id z URL (%d kanalow)." % total_stream)

        # ── 6. API get_live_streams – proba matchowania ────────────────────
        diag.append("")
        diag.append("--- MATCHOWANIE ---")
        try:
            streams_url = "%s/player_api.php?username=%s&password=%s&action=get_live_streams" % (host, user, password)
            req = Request(streams_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            raw = to_str(urlopen(req, timeout=30).read())
            streams = json.loads(raw)
            if isinstance(streams, list):
                with_epg_id = sum(1 for s in streams if (s.get("epg_channel_id") or "").strip())
                diag.append("API: %d kanalow, %d z epg_channel_id" % (len(streams), with_epg_id))

                # Probne matchowanie – dokladnie ta sama logika co generator EPG.
                bmap_stream, bmap, bmap_c = self._collect_bouquet_channel_maps()

                matched = 0
                matched_stream = 0
                matched_name = 0
                unmatched_samples = []
                for s in streams:
                    epg_id = str(s.get("epg_channel_id") or s.get("tvg_id") or "").strip()
                    if not epg_id:
                        continue
                    stream_id = str(s.get("stream_id") or "").strip()
                    name = str(s.get("name") or "").strip()
                    found = False

                    if stream_id and stream_id in bmap_stream:
                        found = True
                        matched_stream += 1

                    if not found:
                        for v in self._name_variants(name):
                            if v in bmap:
                                found = True
                                matched_name += 1
                                break
                    if not found:
                        for v in self._name_variants(name):
                            ck = _canonical_key(v)
                            if ck in bmap_c:
                                found = True
                                matched_name += 1
                                break
                    if found:
                        matched += 1
                    else:
                        if len(unmatched_samples) < 5:
                            unmatched_samples.append("%s (sid=%s)" % (name or "?", stream_id or "?"))

                diag.append("Zmatchowano: %d / %d (z epg_id)" % (matched, with_epg_id))
                diag.append("  po stream_id: %d" % matched_stream)
                diag.append("  po nazwie:    %d" % matched_name)
                if unmatched_samples:
                    diag.append("Przyklad NIEZMATCHOWANYCH:")
                    for u in unmatched_samples:
                        diag.append("  API: '%s'" % u)
                if bouquet_names_sample:
                    diag.append("Przyklad nazw z BOUQUETU:")
                    for b in bouquet_names_sample[:3]:
                        norm = _normalize_name(b)
                        diag.append("  BQ: '%s' → norm: '%s'" % (b, norm))
            else:
                diag.append("[BLAD] API nie zwrocilo listy kanalow.")
        except Exception as e:
            diag.append("[BLAD] API get_live_streams: %s" % str(e))

        # ── 7. EPGImport config ────────────────────────────────────────────
        diag.append("")
        diag.append("--- EPGIMPORT CONFIG ---")
        pickle_path = "/etc/enigma2/epgimport.conf"
        if os.path.exists(pickle_path):
            try:
                import pickle
                with open(pickle_path, "rb") as f:
                    cfg = pickle.load(f)
                if isinstance(cfg, dict):
                    our_key = "poterx_iptv.sources.xml"
                    if cfg.get(our_key) is True:
                        diag.append("[OK] Zrodlo PoterX WLACZONE w EPGImport config")
                    else:
                        diag.append("[BLAD] Zrodlo PoterX WYLACZONE w EPGImport config!")
                        diag.append("   >> Wlacz recznie: EPGImport → Sources → PoterX IPTV")
                        diag.append("   >> Lub nacisniej 0 ponownie (auto-wlaczy)")
                        # Proba automatycznego wlaczenia
                        cfg[our_key] = True
                        with open(pickle_path, "wb") as f:
                            pickle.dump(cfg, f)
                        diag.append("   >> NAPRAWIONO: zrodlo wlaczone automatycznie!")
                else:
                    diag.append("[INFO] epgimport.conf nie jest dict (format: %s)" % type(cfg).__name__)
            except Exception as e:
                diag.append("[INFO] Nie mozna odczytac epgimport.conf: %s" % str(e))
        else:
            diag.append("[INFO] Brak /etc/enigma2/epgimport.conf (normalne przy pierwszym uzyciu)")

        # ── 8. eEPGCache API check ─────────────────────────────────────────
        diag.append("")
        diag.append("--- eEPGCache API ---")
        try:
            from enigma import eEPGCache
            ec = eEPGCache.getInstance()
            diag.append("[OK] eEPGCache dostepny")
            diag.append("  importEvents: %s" % ("TAK" if hasattr(ec, "importEvents") else "NIE"))
            diag.append("  importEvent: %s" % ("TAK" if hasattr(ec, "importEvent") else "NIE"))
            diag.append("  save: %s" % ("TAK" if hasattr(ec, "save") else "NIE"))
        except Exception as e:
            diag.append("[BLAD] eEPGCache: %s" % str(e))

        # ── 9. Proba importu EPG ──────────────────────────────────────────
        diag.append("")
        diag.append("--- PROBA IMPORTU ---")
        if os.path.exists(ch_path):
            trig_ok, trig_msg = self._trigger_epgimport()
            if trig_ok:
                diag.append("[OK] %s" % trig_msg)
            else:
                diag.append("[BLAD] %s" % trig_msg)
            # Pokaz logi bledow jesli istnieja
            err_path = "/tmp/poterx_epg_errors.txt"
            if os.path.exists(err_path):
                try:
                    with open(err_path, "r") as f:
                        errs = f.read().strip()
                    if errs:
                        diag.append("Szczegoly bledow:")
                        for el in errs.splitlines()[:5]:
                            diag.append("  %s" % el)
                except Exception:
                    pass
        else:
            diag.append("[POMINIETY] Brak EPGImport lub plikow EPG.")

        # ── Pokaz wynik ───────────────────────────────────────────────────
        result = "\n".join(diag)
        # Zapisz tez do pliku (uzytkownik moze przeslac SSH)
        try:
            with open("/tmp/poterx_epg_diag.txt", "w") as f:
                f.write(result + "\n")
        except Exception:
            pass

        self["status"].setText("Diagnostyka EPG: gotowe. Wynik w /tmp/poterx_epg_diag.txt")
        self.session.open(MessageBox, result, MessageBox.TYPE_INFO)

    def _build_m3u_url(self):
        host = _sanitize_host(config.plugins.poterx.host.value)
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        return "{}/get.php?username={}&password={}&type=m3u&output=ts".format(host, user, password)

    def _build_dreambox_url(self):
        host = _sanitize_host(config.plugins.poterx.host.value)
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        return "{}/playlist/{}/{}/dreambox?output=".format(host, user, password)

    def _build_player_api_url(self, action):
        host = _sanitize_host(config.plugins.poterx.host.value)
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        return "{}/player_api.php?username={}&password={}&action={}".format(host, user, password, action)

    def _fetch_url_text(self, url, timeout=45):
        last = None
        for _ in range(2):
            try:
                req = Request(url)
                req.add_header("User-Agent", "Enigma2-PoterX")
                return to_str(urlopen(req, timeout=timeout).read())
            except Exception as e:
                last = e
        if last:
            raise last
        return ""

    def _parse_dreambox_playlist(self, content):
        # Parse Enigma2 dreambox playlist into entries with original #SERVICE references from the panel.
        # Returns list of dicts: {"name": str, "norm": str, "service": "#SERVICE ...", "description": "#DESCRIPTION ..."}
        entries = []
        if not content:
            return entries
        lines = content.splitlines()
        i = 0
        while i < len(lines):
            line = (lines[i] or "").strip()
            if not line.startswith("#SERVICE"):
                i += 1
                continue

            service_line = line
            desc_line = ""
            name = ""
            if i + 1 < len(lines):
                nxt = (lines[i + 1] or "").strip()
                if nxt.startswith("#DESCRIPTION"):
                    desc_line = nxt
                    name = nxt[len("#DESCRIPTION"):].strip()
                    i += 2
                else:
                    i += 1
            else:
                i += 1

            if not name:
                # Fallback: last field after ":" is usually the display name.
                try:
                    name = service_line.split(":")[-1].strip()
                except Exception:
                    name = ""

            norm = _normalize_name(name)
            if not desc_line and name:
                desc_line = "#DESCRIPTION %s" % name

            if service_line and norm:
                entries.append({"name": name, "norm": norm, "service": service_line, "description": desc_line})

        return entries

    def _dreambox_entries_to_url_map(self, entries):
        m = {}
        for e in entries:
            name = (e.get("name") or "").strip()
            srv = (e.get("service") or "").strip()
            if not name or not srv.startswith("#SERVICE "):
                continue
            # In dreambox format URL is appended after first 10 fields.
            s = srv[len("#SERVICE "):]
            parts = s.split(":")
            if len(parts) < 11:
                continue
            enc_url = ":".join(parts[10:]).strip()
            if not enc_url:
                continue
            url = _decode_url_minimal(enc_url)
            if not url.startswith("http"):
                continue
            norm = _normalize_name(name)
            if norm and norm not in m:
                m[norm] = url
        return m

    def _build_panel_ref_map_from_dreambox(self, entries):
        # Build name->service_core map from panel-assigned dreambox references.
        by_variant = {}
        by_canon = {}
        for e in (entries or []):
            srv_line = (e.get("service") or "").strip()
            if not srv_line.startswith("#SERVICE "):
                continue
            srv = srv_line[len("#SERVICE "):].strip()
            core = self._extract_ref_core(srv)
            if not core:
                continue
            # Keep TV service-type for compatibility with bouquets/EPGImport.
            core = self._force_service_type_1(core)
            if not self._is_mappable_service_core(core):
                continue
            name = (e.get("name") or "").strip()
            if not name:
                continue
            for v in self._name_variants(name):
                if v and v not in by_variant:
                    by_variant[v] = core
                ck = _canonical_key(v)
                if ck and ck not in by_canon:
                    by_canon[ck] = core
        return by_variant, by_canon

    def _resolve_source_bouquet_path(self):
        base = "/etc/enigma2"
        manual = (config.plugins.poterx.bzyk_source_path.value or "").strip()
        if manual:
            return manual
        fn = config.plugins.poterx.bzyk_source_bouquet.value
        if not fn:
            detected = _auto_detect_source_bouquet_path()
            if detected:
                return detected
            lst = _list_tv_bouquet_files()
            return lst[0][1] if lst else ""
        if fn.startswith("/"):
            return fn
        return os.path.join(base, fn)

    def _resolve_custom_bouquet_path(self):
        base = "/etc/enigma2"
        fn = (config.plugins.poterx.bzyk_custom_bouquet.value or "").strip()
        if not fn:
            fn = "userbouquet.mojalista.tv"
        if not fn.startswith("userbouquet."):
            fn = "userbouquet." + fn
        if not fn.endswith(".tv"):
            fn = fn + ".tv"
        return os.path.join(base, fn), fn

    def _parse_m3u(self, content):
        # Return:
        # - name_to_url: {normalized_channel_name: url}
        # - entries: list of dicts: {"name": raw, "norm": norm, "url": url, "group": group_title}
        name_to_url = {}
        entries = []
        if not content:
            return name_to_url, entries
        lines = content.splitlines()
        i = 0
        while i < len(lines):
            line = (lines[i] or "").strip()
            if line.startswith("#EXTINF"):
                raw_name = line.split(",")[-1].strip()
                n = _normalize_name(raw_name)
                attrs = _parse_extinf_attrs(line)
                group_title = (attrs.get("group-title") or "").strip()
                if i + 1 < len(lines):
                    url = (lines[i + 1] or "").strip().replace("\r", "")
                    if n and url and not url.startswith("#"):
                        name_to_url[n] = url
                        entries.append({"name": raw_name, "norm": n, "url": url, "group": group_title})
                i += 2
                continue
            i += 1
        return name_to_url, entries

    def _replace_in_bouquet(self, src_path, dst_path, m3u_map, force_title=True, title_override=None):
        # Channel list copied from your bash script; we keep the same service refs to preserve picons/EPG etc.
        channels = [
            ("1:0:1:32DC:190:13E:820000:0:0:0", ["canal+ premium"], "CANAL+ PREMIUM HD"),
            ("1:0:1:13ED:5DC:13E:820000:0:0:0", ["canal+ 1", "canal+1"], "CANAL+1 HD"),
            ("1:0:1:3779:44C:13E:820000:0:0:0", ["canal+ film"], "CANAL+ FILM HD"),
            ("1:0:19:3782:44C:13E:820000:0:0:0", ["canal+ seriale"], "CANAL+ SERIALE HD"),
            ("1:0:1:377A:44C:13E:820000:0:0:0", ["canal+ dokument"], "CANAL+ DOKUMENT HD"),
            ("1:0:1:32DE:190:13E:820000:0:0:0", ["canal+ sport 1", "canal+ sport"], "CANAL+ SPORT HD"),
            ("1:0:1:13EE:5DC:13E:820000:0:0:0", ["canal+ sport 2"], "CANAL+ SPORT 2 HD"),
            ("1:0:1:3AA0:514:13E:820000:0:0:0", ["canal+ sport 3"], "CANAL+ SPORT 3 HD"),
            ("1:0:1:3AA1:514:13E:820000:0:0:0", ["canal+ sport 4"], "CANAL+ SPORT 4 HD"),
            ("1:0:1:32E1:190:13E:820000:0:0:0", ["canal+ extra 1"], "CANAL+ EXTRA 1"),
            ("1:0:1:37B5:44C:13E:820000:0:0:0", ["canal+ extra 2"], "CANAL+ EXTRA 2"),
            ("1:0:1:3315:190:13E:820000:0:0:0", ["canal+ extra 3"], "CANAL+ EXTRA 3"),
            ("1:0:1:32E4:190:13E:820000:0:0:0", ["canal+ extra 4"], "CANAL+ EXTRA 4"),
            ("1:0:1:32CD:190:13E:820000:0:0:0", ["canal+ now"], "CANAL+ NOW"),
        ]

        with open(src_path, "r") as f:
            in_lines = [l.rstrip("\n") for l in f.readlines()]

        out_lines = []
        replaced = 0
        i = 0
        while i < len(in_lines):
            line = in_lines[i]
            m = None
            for service_ref, keys, disp in channels:
                if line.startswith("#SERVICE " + service_ref):
                    m = (service_ref, keys, disp)
                    break
            if not m:
                out_lines.append(line)
                i += 1
                continue

            service_ref, keys, disp = m
            url = ""
            for k in keys:
                url = m3u_map.get(_normalize_name(k), "") or ""
                if url:
                    break
            if not url:
                out_lines.append(line)
                i += 1
                continue

            enc = _encode_url_minimal(url)
            out_lines.append("#SERVICE %s:%s:%s" % (service_ref, enc, disp))
            out_lines.append("#DESCRIPTION %s" % disp)
            replaced += 1

            # If next line is old description, skip it to avoid duplicates.
            if i + 1 < len(in_lines) and in_lines[i + 1].startswith("#DESCRIPTION"):
                i += 2
            else:
                i += 1

        if force_title:
            # Force first line to custom title (only for "copy" mode).
            title = (title_override or "").strip() or (config.plugins.poterx.bzyk_custom_title.value or "").strip() or "Moja lista"
            if out_lines:
                if out_lines[0].startswith("#NAME"):
                    out_lines[0] = "#NAME " + title
                else:
                    out_lines.insert(0, "#NAME " + title)
            else:
                out_lines = ["#NAME " + title]

        with open(dst_path, "w") as f:
            f.write("\n".join(out_lines) + "\n")

        return replaced

    def _backup_file(self, path):
        try:
            ts = datetime.now().strftime("%Y%m%d-%H%M%S")
            bkp = "%s.bak-%s" % (path, ts)
            with open(path, "rb") as src:
                data = src.read()
            with open(bkp, "wb") as dst:
                dst.write(data)
            return bkp
        except Exception:
            return ""

    def _ensure_bouquet_link_first(self, bouquet_filename):
        self._ensure_bouquet_link(bouquet_filename, position=2)

    def _ensure_bouquet_link(self, bouquet_filename, position=2):
        # position is 1-based "slot" right after #NAME (so 2 means first bouquet on the list)
        if not bouquet_filename:
            return
        idx = "/etc/enigma2/bouquets.tv"
        entry = '#SERVICE 1:7:1:0:0:0:0:0:0:0:FROM BOUQUET "%s" ORDER BY bouquet' % bouquet_filename
        try:
            lines = []
            if os.path.exists(idx):
                with open(idx, "r") as f:
                    lines = [l.rstrip("\n") for l in f.readlines()]
            lines = [l for l in lines if bouquet_filename not in l]
            if not lines:
                lines = ["#NAME User - bouquets (TV)"]
            base_at = 1 if lines[0].startswith("#NAME") else 0
            # Keep #NAME on top, clamp insert index.
            insert_at = max(base_at, min(len(lines), position - 1))
            if lines[0].startswith("#NAME") and insert_at == 0:
                insert_at = 1
            lines.insert(insert_at, entry)
            with open(idx, "w") as f:
                f.write("\n".join(lines) + "\n")
        except Exception:
            pass

    def _resolve_extra_bouquet_path(self):
        base = "/etc/enigma2"
        fn = (config.plugins.poterx.bzyk_extra_bouquet.value or "").strip()
        if not fn:
            fn = "userbouquet.iptv_pozostale.tv"
        if not fn.startswith("userbouquet."):
            fn = "userbouquet." + fn
        if not fn.endswith(".tv"):
            fn = fn + ".tv"
        return os.path.join(base, fn), fn

    def _write_extra_iptv_bouquet_from_dreambox(self, dst_path, title, entries, used_norm_names):
        # Create a separate IPTV bouquet with the remaining channels, using service references
        # fetched from the Xtream UI panel (dreambox playlist), like in older versions.
        limit = 2000  # hard cap

        out = ["#NAME %s" % ((title or "").strip() or "IPTV - Pozostale")]
        count = 0
        for e in entries:
            if e.get("norm") in used_norm_names:
                continue

            srv = (e.get("service") or "").strip()
            desc = (e.get("description") or "").strip()
            if not srv:
                continue

            # Prefer default player (service type 1) while keeping the original reference intact.
            srv = re.sub(r"^#SERVICE\s+4097:", "#SERVICE 1:", srv)

            out.append(srv)
            if desc:
                out.append(desc)
            count += 1
            if count >= limit:
                break

        with open(dst_path, "w") as f:
            f.write("\n".join(out) + "\n")

        return count

    def _name_variants(self, name):
        # Generuje warianty nazwy do fuzzy matchowania.
        base = _normalize_name(name)
        out = set([base])
        # Wariant BEZ prefiksu krajowego (gdyby _normalize_name nie zlapalo)
        raw_lower = (name or "").strip().lower()
        no_prefix = re.sub(r"^[a-z]{2,3}\s*[:\|\-]\s*", "", raw_lower)
        if no_prefix != raw_lower:
            out.add(_normalize_name(no_prefix))
        x = base
        x = x.replace("canal+", "canal plus")
        x = x.replace("+", " plus ")
        x = re.sub(r"\s+", " ", x).strip()
        out.add(x)
        # Wariant "canal" bez "plus" (np. "canal sport" matchuje "canal+ sport")
        cp = x.replace("canal plus", "canal")
        cp = re.sub(r"\s+", " ", cp).strip()
        out.add(cp)
        # remove some common suffix tokens
        y = re.sub(r"\b(fhd|uhd|4k|sd)\b", " ", x)
        y = re.sub(r"\s+", " ", y).strip()
        out.add(y)
        # compact variant: "tvp 2" -> "tvp2"
        z = y.replace(" ", "")
        out.add(z)
        # drop separators often used by providers
        w = re.sub(r"[\[\]\(\)\|/_-]+", " ", y)
        w = re.sub(r"\s+", " ", w).strip()
        out.add(w)
        out.add(_canonical_key(w))
        return [v for v in out if v]

    def _extract_ref_core(self, srv):
        # Return first 10 fields of service ref (without URL/display tail).
        parts = (srv or "").split(":")
        if len(parts) < 10:
            return ""
        core = ":".join(parts[:10])
        return core

    def _extract_service_url(self, srv):
        # Extract encoded stream URL from IPTV service ref and decode it.
        parts = (srv or "").split(":")
        if len(parts) < 11:
            return ""
        enc_url = ":".join(parts[10:]).strip()
        if not enc_url:
            return ""
        url = _decode_url_minimal(enc_url)
        return url if url.startswith("http") else ""

    def _extract_stream_id_from_url(self, url):
        s = (url or "").strip()
        if not s:
            return ""
        patterns = [
            r"/live/[^/]+/[^/]+/([0-9]+)(?:\.[A-Za-z0-9]+)?(?:$|[/?#])",
            r"/([0-9]+)(?:\.[A-Za-z0-9]+)?(?:$|[?#])",
            r"[?&]stream(?:_id)?=([0-9]+)(?:$|[&#])",
        ]
        for pat in patterns:
            m = re.search(pat, s)
            if m:
                return m.group(1)
        return ""

    def _extract_stream_id_from_service(self, srv):
        return self._extract_stream_id_from_url(self._extract_service_url(srv))

    def _service_ref_variants(self, full_ref, core):
        # Return unique ref variants that may exist on different images/players.
        refs = []
        seen = set()

        def _add(ref):
            ref = (ref or "").strip()
            if not ref:
                return
            if not ref.endswith(":"):
                ref += ":"
            if ref not in seen:
                seen.add(ref)
                refs.append(ref)

        full_ref = (full_ref or "").strip()
        core = (core or "").strip()

        _add(full_ref)
        _add(core)

        parts = core.split(":")
        if len(parts) >= 10:
            alt_1 = list(parts)
            alt_1[0] = "1"
            _add(":".join(alt_1[:10]))

            alt_4097 = list(parts)
            alt_4097[0] = "4097"
            _add(":".join(alt_4097[:10]))

        return refs

    def _collect_bouquet_channel_maps(self):
        # Collect multiple lookup maps from local bouquets for robust EPG matching.
        by_stream_id = {}  # stream_id -> (full_ref, core, name)
        by_norm = {}       # normalized name -> (full_ref, core, name)
        by_canon = {}      # canonical name -> (full_ref, core, name)

        for fn, fp in _list_tv_bouquet_files():
            try:
                with open(fp, "r") as f:
                    blines = [l.strip() for l in f.readlines()]
            except Exception:
                continue
            i = 0
            while i < len(blines):
                line = blines[i]
                if line.startswith("#SERVICE ") and "FROM BOUQUET" not in line.upper():
                    full_ref = line[len("#SERVICE "):].strip()
                    core = self._extract_ref_core(full_ref)
                    if core:
                        name = ""
                        if i + 1 < len(blines) and blines[i + 1].startswith("#DESCRIPTION"):
                            name = blines[i + 1][len("#DESCRIPTION"):].strip()
                        if not name:
                            parts = full_ref.split(":")
                            if len(parts) > 11:
                                tail = parts[-1].strip()
                                if tail and not tail.startswith("http") and not tail.startswith("/"):
                                    name = tail
                        pair = (full_ref, core, name)
                        stream_id = self._extract_stream_id_from_service(full_ref)
                        if stream_id and stream_id not in by_stream_id:
                            by_stream_id[stream_id] = pair
                        if name:
                            for v in self._name_variants(name):
                                if v and v not in by_norm:
                                    by_norm[v] = pair
                                ck = _canonical_key(v)
                                if ck and ck not in by_canon:
                                    by_canon[ck] = pair
                i += 1

        return by_stream_id, by_norm, by_canon

    def _is_mappable_service_core(self, core):
        # Accept only TV-like DVB service references (exclude markers/radio/sub-bouquet).
        parts = (core or "").split(":")
        if len(parts) < 10:
            return False
        if parts[0] != "1":
            return False
        stype = _parse_int_auto(parts[1])
        if stype is None:
            return False
        if stype in (2, 7, 10, 64, 832):
            return False
        return True

    def _safe_service_name(self, name):
        # Keep #SERVICE tail parser-safe; display name is still taken from #DESCRIPTION.
        s = (name or "").replace("\r", " ").replace("\n", " ").replace(":", " - ")
        s = re.sub(r"\s+", " ", s).strip()
        return s or "Kanał IPTV"

    def _is_urlish_service(self, srv):
        s = (srv or "").lower()
        return ("http%3a//" in s) or ("https%3a//" in s)

    def _pseudo_service_core(self, stream_id, category_id, name):
        # Stable pseudo-reference for IPTV-only channels (no DVB equivalent).
        # Deterministic by stream_id/category/name so EPG/picon filenames stay stable.
        raw = "%s|%s|%s" % (stream_id or "", category_id or "", name or "")
        h = hashlib.md5(raw.encode("utf-8")).hexdigest()
        sid = int(h[0:4], 16) or 1
        tsid = int(h[4:8], 16) or 1
        onid = int(h[8:12], 16) or 1
        ns = int(h[12:20], 16) or 1
        return "1:0:1:%X:%X:%X:%X:0:0:0" % (sid, tsid, onid, ns)

    def _service_core_to_picon_name(self, core):
        return (core or "").replace(":", "_") + ".png"

    def _force_ref_type_1(self, ref):
        parts = (ref or "").split(":")
        if len(parts) < 10:
            return ref or ""
        parts[0] = "1"
        return ":".join(parts)

    def _force_service_type_1(self, core):
        parts = (core or "").split(":")
        if len(parts) < 10:
            return core or ""
        parts[2] = "1"
        return ":".join(parts[:10])

    def _custom_sid_to_core(self, custom_sid):
        cs = (custom_sid or "").strip()
        if not cs or cs in ("0", "None", "null"):
            return ""
        try:
            if cs and cs[0].isdigit():
                cs = "1" + cs[1:]
            elif cs.startswith(":0"):
                cs = "1" + cs
            core = ":".join(cs.split(":")[:10])
            if len(core.split(":")) < 10:
                core = ":".join(cs.split(":")[:7]) + ":0:0:0"
            if not self._is_mappable_service_core(core):
                return ""
            return core
        except Exception:
            return ""

    def _picon_exists(self, picon_filename):
        if not picon_filename:
            return False
        paths = [
            TARGET_PICON_PATH,
            "/media/hdd/picon",
            "/media/usb/picon",
            "/picon",
        ]
        for p in paths:
            try:
                if os.path.exists(os.path.join(p, picon_filename)):
                    return True
            except Exception:
                pass
        return False

    # ══════════════════════════════════════════════════════════════════════════
    #  EPG SIMPLE – czyta referencje WPROST z bouquetow, jak satelita
    # ══════════════════════════════════════════════════════════════════════════

    def _build_epg_simple(self):
        """
        EPG jak satelita – czyta referencje WPROST z bouquetow,
        matchuje z epg_channel_id z API panelu, pisze channels.xml + sources.xml.
        KLUCZOWE: wpisuje PELNA referencje z bouquetu (z URL) + sam core,
        dzieki czemu EPGImport matchuje IPTV i DVB jednoczesnie.
        Zwraca (ok: bool, komunikat: str).
        """
        EPG_DIR = "/etc/epgimport"
        CHANNELS_FN = "poterx_iptv.channels.xml"
        SOURCES_FN = "poterx_iptv.sources.xml"

        # 1. Katalog /etc/epgimport
        if not os.path.isdir(EPG_DIR):
            try:
                os.makedirs(EPG_DIR)
            except Exception as e:
                return False, "Nie mozna utworzyc /etc/epgimport: %s" % str(e)

        host = _sanitize_host(config.plugins.poterx.host.value)
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        if not user or not password:
            return False, "Brak danych logowania."

        # 2. Czytaj WSZYSTKIE bouquety – zbierz mapowanie po stream_id i nazwach.
        bouquet_by_stream, bouquet_by_norm, bouquet_by_canon = self._collect_bouquet_channel_maps()

        if not bouquet_by_stream and not bouquet_by_norm:
            return False, "Brak kanalow w bouquetach Enigma2."

        # 3. Pobierz epg_channel_id z API panelu
        streams_url = "%s/player_api.php?username=%s&password=%s&action=get_live_streams" % (host, user, password)
        try:
            req = Request(streams_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            raw = to_str(urlopen(req, timeout=60).read())
            streams = json.loads(raw)
        except Exception as e:
            return False, "Blad API get_live_streams: %s" % str(e)

        if not isinstance(streams, list) or not streams:
            return False, "API zwrocilo pusta liste kanalow."

        # 4. Matchuj i buduj channels.xml
        #    KLUCZOWE: wpisujemy WIELE wariantow referencji dla kazdego kanalu:
        #    - pelna ref z bouquetu (z URL) → matchuje usluge IPTV
        #    - sam core (10 pol) → matchuje usluge DVB (satelita)
        #    - core z roznymi service type (1, 4097) → matchuje rozne playery
        #    Dzieki temu EPGImport trafi ZAWSZE, niezaleznie od tego
        #    czy kabel satelitarny jest podlaczony czy nie.
        ch_lines = ['<?xml version="1.0" encoding="utf-8"?>', "<channels>"]
        mapped = 0
        seen = set()

        def _add_channel(eid, sref):
            if sref and sref not in seen:
                seen.add(sref)
                ch_lines.append('  <channel id="%s">%s</channel>' % (eid, _xml_escape(sref)))
                return True
            return False

        for stream in streams:
            epg_id = (
                str(stream.get("epg_channel_id") or "").strip()
                or str(stream.get("tvg_id") or "").strip()
            )
            if not epg_id:
                continue
            stream_id = str(stream.get("stream_id") or "").strip()
            name = str(stream.get("name") or "").strip()

            # Najpierw probuj po stream_id z URL, bo to jest stabilniejsze niz nazwa.
            pair = None
            if stream_id and stream_id in bouquet_by_stream:
                pair = bouquet_by_stream[stream_id]
            if not pair and name:
                for v in self._name_variants(name):
                    if v in bouquet_by_norm:
                        pair = bouquet_by_norm[v]
                        break
            if not pair and name:
                for v in self._name_variants(name):
                    ck = _canonical_key(v)
                    if ck in bouquet_by_canon:
                        pair = bouquet_by_canon[ck]
                        break

            if not pair:
                continue

            full_ref, core, _pair_name = pair
            if not core:
                continue

            eid = _xml_escape(epg_id)
            added = False

            # Dodaj komplet wariantow referencji: oryginal, 1:..., 4097:...
            for sref in self._service_ref_variants(full_ref, core):
                if _add_channel(eid, sref):
                    added = True

            if added:
                mapped += 1

        ch_lines.append("</channels>")

        if mapped == 0:
            return False, "Nie udalo sie zmapowac zadnego kanalu EPG."

        # 5. Zapisz channels.xml
        channels_path = os.path.join(EPG_DIR, CHANNELS_FN)
        try:
            with open(channels_path, "w") as f:
                f.write("\n".join(ch_lines) + "\n")
        except Exception as e:
            return False, "Blad zapisu channels.xml: %s" % str(e)

        # 6. Zapisz sources.xml
        xmltv_url = "%s/xmltv.php?username=%s&password=%s" % (host, user, password)
        sources_path = os.path.join(EPG_DIR, SOURCES_FN)
        src_lines = [
            '<?xml version="1.0" encoding="utf-8"?>',
            "<sources>",
            '  <sourcecat sourcecatname="PoterX IPTV EPG">',
            '    <source type="gen_xmltv" nocheck="1" channels="%s">' % CHANNELS_FN,
            "      <description>PoterX IPTV</description>",
            "      <url><![CDATA[%s]]></url>" % xmltv_url,
            "    </source>",
            "  </sourcecat>",
            "</sources>",
        ]
        try:
            with open(sources_path, "w") as f:
                f.write("\n".join(src_lines) + "\n")
        except Exception as e:
            return False, "Blad zapisu sources.xml: %s" % str(e)

        # 7. Auto-wlacz zrodlo w EPGImport
        self._auto_enable_epgimport_source(SOURCES_FN)

        epgimport_installed = os.path.isdir(
            "/usr/lib/enigma2/python/Plugins/Extensions/EPGImport"
        )
        note = (
            "EPGImport zainstalowany – pliki gotowe."
            if epgimport_installed else
            "EPGImport NIEZAINSTALOWANY – pliki zapisane, po instalacji EPG ruszy od razu."
        )
        return True, "EPG: %d kanalow zmapowanych.\n%s" % (mapped, note)

    def _auto_enable_epgimport_source(self, sources_fn):
        """
        Wlacza zrodlo PoterX w konfiguracji EPGImport.
        EPGImport przechowuje config jako pickle w /etc/enigma2/epgimport.conf.
        Probujemy kilka formatow (pickle, tekst) zeby wspierac rozne wersje.
        """
        # Format 1: pickle (wiekszosc wersji EPGImport)
        pickle_path = "/etc/enigma2/epgimport.conf"
        try:
            import pickle
            cfg = {}
            if os.path.exists(pickle_path):
                with open(pickle_path, "rb") as f:
                    cfg = pickle.load(f)
            if not isinstance(cfg, dict):
                cfg = {}
            # Klucz to nazwa pliku sources.xml
            if cfg.get(sources_fn) is True:
                return  # juz wlaczone
            cfg[sources_fn] = True
            with open(pickle_path, "wb") as f:
                pickle.dump(cfg, f)
            return
        except Exception:
            pass

        # Format 2: tekst (niektore forki EPGImport)
        txt_path = "/etc/epgimport/epgimport.conf"
        try:
            content = ""
            if os.path.exists(txt_path):
                with open(txt_path, "r") as f:
                    content = f.read()
            if sources_fn in content:
                return
            with open(txt_path, "a") as f:
                f.write("%s=enabled\n" % sources_fn)
        except Exception:
            pass

    def _direct_epg_import(self):
        """
        Bezposredni import EPG z XMLTV do eEPGCache – NIE wymaga EPGImport.
        Pobiera xmltv.php, parsuje <programme>, wstrzykuje eventy do cache.
        Fallback gdy EPGImport nie jest zainstalowany lub nie dziala.
        Zwraca (ok: bool, msg: str).
        """
        host = _sanitize_host(config.plugins.poterx.host.value)
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        if not user or not password:
            return False, "Brak danych logowania."

        # 1. Zbuduj mape bouquetow po stream_id i nazwach.
        bouquet_by_stream, bouquet_by_norm, bouquet_by_canon = self._collect_bouquet_channel_maps()

        # 2. Pobierz epg_channel_id z API → zbuduj mape channel_id → core_ref
        streams_url = "%s/player_api.php?username=%s&password=%s&action=get_live_streams" % (host, user, password)
        try:
            req = Request(streams_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            raw = to_str(urlopen(req, timeout=60).read())
            streams = json.loads(raw)
        except Exception as e:
            return False, "Blad API: %s" % str(e)

        # channel_id → core service ref
        epgid_to_core = {}
        for stream in (streams if isinstance(streams, list) else []):
            epg_id = (str(stream.get("epg_channel_id") or "").strip()
                      or str(stream.get("tvg_id") or "").strip())
            if not epg_id:
                continue
            stream_id = str(stream.get("stream_id") or "").strip()
            name = str(stream.get("name") or "").strip()
            pair = None
            if stream_id and stream_id in bouquet_by_stream:
                pair = bouquet_by_stream[stream_id]
            if not pair and name:
                for v in self._name_variants(name):
                    if v in bouquet_by_norm:
                        pair = bouquet_by_norm[v]
                        break
            if not pair:
                if name:
                    for v in self._name_variants(name):
                        ck = _canonical_key(v)
                        if ck in bouquet_by_canon:
                            pair = bouquet_by_canon[ck]
                            break
            if pair:
                epgid_to_core[epg_id] = pair[1]  # core ref

        if not epgid_to_core:
            return False, "Nie zmatchowano zadnego kanalu."

        # 3. Pobierz XMLTV i parsuj <programme>
        xmltv_url = "%s/xmltv.php?username=%s&password=%s" % (host, user, password)
        try:
            req = Request(xmltv_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            xmltv_raw = to_str(urlopen(req, timeout=120).read())
        except Exception as e:
            return False, "Blad XMLTV: %s" % str(e)

        # 4. Parsuj <programme> i wstrzykuj do eEPGCache
        try:
            from enigma import eEPGCache, eServiceReference
        except ImportError:
            return False, "Brak eEPGCache (niekompatybilny image)."

        epgcache = eEPGCache.getInstance()

        # Wykryj dostepne API do importu eventow
        has_importEvents = hasattr(epgcache, "importEvents")
        has_importEvent = hasattr(epgcache, "importEvent")
        if not has_importEvents and not has_importEvent:
            return False, "eEPGCache nie ma importEvents/importEvent (stary image?)."

        imported = 0
        errors = 0
        import time as _time
        cur_channel = ""
        cur_start = 0
        cur_end = 0
        cur_title = ""
        cur_desc = ""
        in_programme = False

        def _parse_xmltv_time(s):
            """Parsuje czas XMLTV: '20260413120000 +0200' → unix timestamp"""
            s = (s or "").strip()
            # Odetnij timezone offset (parsujemy jako localtime)
            ts_part = s[:14] if len(s) >= 14 else s
            try:
                return int(_time.mktime(_time.strptime(ts_part, "%Y%m%d%H%M%S")))
            except Exception:
                return 0

        def _inject_event(channel_id, start, end, title, desc):
            """Wstrzykuje event do eEPGCache. Probuje rozne API."""
            core = epgid_to_core.get(channel_id, "")
            if not core or not start or not title:
                return False
            duration = max(end - start, 60)
            evt = (start, duration, title, desc[:200] if desc else "", desc or "")
            for sref_str in self._service_ref_variants("", core):
                try:
                    sref = eServiceReference(sref_str)
                    if has_importEvents:
                        epgcache.importEvents(sref, [evt])
                    elif has_importEvent:
                        epgcache.importEvent(sref, evt)
                    return True
                except Exception:
                    continue
            return False

        for line in xmltv_raw.splitlines():
            line = line.strip()

            # <programme> — atrybuty moga byc w dowolnej kolejnosci
            if "<programme " in line:
                mc = re.search(r'channel="([^"]+)"', line)
                ms = re.search(r'start="([^"]+)"', line)
                me = re.search(r'stop="([^"]+)"', line)
                if mc and ms:
                    cur_channel = mc.group(1).strip()
                    cur_start = _parse_xmltv_time(ms.group(1))
                    cur_end = _parse_xmltv_time(me.group(1)) if me else cur_start + 3600
                    cur_title = ""
                    cur_desc = ""
                    in_programme = True
                    # Tytul moze byc na tej samej linii
                    tm = re.search(r'<title[^>]*>(.*?)</title>', line)
                    if tm:
                        cur_title = re.sub(r'<[^>]+>', '', tm.group(1)).strip()
                continue

            if in_programme:
                tm = re.search(r'<title[^>]*>(.*?)</title>', line)
                if tm:
                    cur_title = re.sub(r'<[^>]+>', '', tm.group(1)).strip()
                dm = re.search(r'<desc[^>]*>(.*?)</desc>', line)
                if dm:
                    cur_desc = re.sub(r'<[^>]+>', '', dm.group(1)).strip()

            if "</programme>" in line and in_programme:
                in_programme = False
                if _inject_event(cur_channel, cur_start, cur_end, cur_title, cur_desc):
                    imported += 1
                else:
                    errors += 1

        if imported > 0:
            try:
                epgcache.save()
            except Exception:
                pass
            return True, "Bezposredni import EPG: %d eventow (bledy: %d)." % (imported, errors)
        return False, "XMLTV sparsowany ale 0 eventow zaimportowanych (bledy: %d, kanalow w mapie: %d)." % (errors, len(epgid_to_core))

    def _download_picon(self, icon_url, picon_filename):
        if not icon_url or not picon_filename:
            return False
        icon_url = (icon_url or "").strip()
        if not (icon_url.startswith("http://") or icon_url.startswith("https://")):
            return False
        try:
            if not os.path.isdir(TARGET_PICON_PATH):
                os.makedirs(TARGET_PICON_PATH)
        except Exception:
            return False
        out_path = os.path.join(TARGET_PICON_PATH, picon_filename)
        try:
            req = Request(icon_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            data = urlopen(req, timeout=20).read()
            if not data or len(data) < 16:
                return False
            with open(out_path, "wb") as f:
                f.write(data)
            return True
        except Exception:
            return False

    def _load_local_service_map(self):
        # Build local service map from existing bouquets for EPG/picon mapping.
        # Return: {normalized_name: "1:..."} (service ref without "#SERVICE ")
        m = {}
        canon = {}
        for fn, fp in _list_tv_bouquet_files():
            # skip generated IPTV category bouquets to avoid self-mapping
            if fn.startswith("userbouquet.iptv_kat_"):
                continue
            try:
                with open(fp, "r") as f:
                    lines = [l.strip() for l in f.readlines()]
            except Exception:
                continue
            i = 0
            while i < len(lines):
                line = lines[i]
                if not line.startswith("#SERVICE "):
                    i += 1
                    continue
                # take only local DVB refs for mapping (service type 1 and not URL-ish tail)
                srv = line[len("#SERVICE "):].strip()
                if not srv.startswith("1:"):
                    i += 1
                    continue
                if "FROM BOUQUET" in srv.upper():
                    i += 1
                    continue
                if self._is_urlish_service(srv):
                    i += 1
                    continue
                core = self._extract_ref_core(srv)
                if not core:
                    i += 1
                    continue
                if not self._is_mappable_service_core(core):
                    i += 1
                    continue
                name = ""
                if i + 1 < len(lines) and lines[i + 1].startswith("#DESCRIPTION"):
                    name = lines[i + 1][len("#DESCRIPTION"):].strip()
                if name:
                    for v in self._name_variants(name):
                        if v and v not in m:
                            m[v] = core
                        ck = _canonical_key(v)
                        if ck and ck not in canon:
                            canon[ck] = core
                i += 1
        return m, canon

    def _load_lamedb_service_map(self):
        # Build mapping from /etc/enigma2/lamedb (all DVB services, not only user bouquets).
        # Returns maps like _load_local_service_map: (by_variant, by_canonical)
        m = {}
        canon = {}
        for lamedb in ("/etc/enigma2/lamedb", "/etc/enigma2/lamedb5"):
            if not os.path.exists(lamedb):
                continue
            try:
                with open(lamedb, "r") as f:
                    lines = [l.rstrip("\n") for l in f.readlines()]
            except Exception:
                continue

            in_services = False
            i = 0
            while i < len(lines):
                line = lines[i].strip()
                if not in_services:
                    if line == "services":
                        in_services = True
                    i += 1
                    continue
                if line == "end":
                    break
                # Expected service block:
                # 1) sid:ns:tsid:onid:stype:...
                # 2) service name
                # 3) provider/cached meta
                svc_line = line
                if i + 1 >= len(lines):
                    break
                name = (lines[i + 1] or "").strip()
                i += 3

                parts = svc_line.split(":")
                if len(parts) < 5:
                    continue
                sid, ns, tsid, onid, stype = parts[0], parts[1], parts[2], parts[3], parts[4]
                stype_i = _parse_int_auto(stype)
                if stype_i is None or stype_i in (2, 7, 10, 64, 832):
                    continue
                try:
                    core = "1:0:%X:%X:%X:%X:%X:0:0:0" % (
                        stype_i, int(sid, 16), int(tsid, 16), int(onid, 16), int(ns, 16)
                    )
                except Exception:
                    continue
                if not self._is_mappable_service_core(core):
                    continue
                if not name:
                    continue
                for v in self._name_variants(name):
                    if v and v not in m:
                        m[v] = core
                    ck = _canonical_key(v)
                    if ck and ck not in canon:
                        canon[ck] = core
        return m, canon

    def _load_xui_json(self, action, timeout=45):
        url = self._build_player_api_url(action)
        text = self._fetch_url_text(url, timeout=timeout)
        data = json.loads(text)
        if isinstance(data, list):
            return data
        return []

    def _cleanup_generated_xui_bouquets(self):
        base = "/etc/enigma2"
        idx = os.path.join(base, "bouquets.tv")
        prefix = "userbouquet.iptv_kat_"
        try:
            lines = []
            if os.path.exists(idx):
                with open(idx, "r") as f:
                    lines = [l.rstrip("\n") for l in f.readlines()]
            lines = [l for l in lines if ('FROM BOUQUET "' + prefix) not in l]
            if lines:
                with open(idx, "w") as f:
                    f.write("\n".join(lines) + "\n")
        except Exception:
            pass
        try:
            for fn in os.listdir(base):
                if fn.startswith(prefix) and fn.endswith(".tv"):
                    try:
                        os.remove(os.path.join(base, fn))
                    except Exception:
                        pass
        except Exception:
            pass

    def run_xui_full_import(self):
        # Legacy stable mode (3.4.4 line): heavy full XUI import disabled.
        self.session.open(
            MessageBox,
            "Ta funkcja jest wyłączona w trybie stabilnym 3.4.4.\nUżyj: Pobierz IPTV lub Podmień kanały.",
            MessageBox.TYPE_INFO,
        )
        return

        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        host = _sanitize_host(config.plugins.poterx.host.value)
        safe_mode = False
        if not user or not password:
            self.session.open(MessageBox, "Brak danych logowania (użytkownik/hasło).", MessageBox.TYPE_ERROR)
            return

        self._set_progress(2, "Łączenie z panelem...")
        self["status"].setText("Pobieranie kategorii z panelu...")
        try:
            categories = self._load_xui_json("get_live_categories", timeout=30)
            self._set_progress(7, "Pobrano kategorie, pobieranie kanałów LIVE...")
            streams = self._load_xui_json("get_live_streams", timeout=60)
            self._set_progress(10, "Pobieranie referencji kanałów z playlisty dreambox...")
            dreambox_text = self._fetch_url_text(self._build_dreambox_url(), timeout=60)
            dreambox_entries = self._parse_dreambox_playlist(dreambox_text)
        except Exception as e:
            self.session.open(MessageBox, "Błąd API panelu: %s" % str(e), MessageBox.TYPE_ERROR)
            self["status"].setText("Błąd API.")
            self._reset_progress()
            return

        if not streams:
            self.session.open(MessageBox, "Brak kanałów LIVE w panelu.", MessageBox.TYPE_ERROR)
            self["status"].setText("Brak danych.")
            self._reset_progress()
            return

        cat_name_by_id = {}
        cat_order = []
        for c in categories:
            cid = str(c.get("category_id", "")).strip()
            name = (c.get("category_name", "") or "").strip() or "Inne"
            if not cid:
                continue
            cat_name_by_id[cid] = name
            cat_order.append(cid)

        grouped = {}
        for s in streams:
            sid = str(s.get("stream_id", "")).strip()
            if not sid:
                continue
            cid = str(s.get("category_id", "")).strip()
            cname = cat_name_by_id.get(cid, "Inne")
            grouped.setdefault(cname, []).append(s)

        if not grouped:
            self.session.open(MessageBox, "Brak poprawnych kanałów do importu.", MessageBox.TYPE_ERROR)
            self["status"].setText("Brak danych.")
            self._reset_progress()
            return

        self._set_progress(14, "Przygotowanie mapowania referencji DVB...")
        self["status"].setText("Tworzenie bukietów...")
        self._cleanup_generated_xui_bouquets()
        panel_map, panel_canon = self._build_panel_ref_map_from_dreambox(dreambox_entries)
        local_map, local_canon = self._load_local_service_map()
        lamedb_map, lamedb_canon = self._load_lamedb_service_map()

        # Build stable category order: API order first, then unknown categories.
        ordered_cats = []
        used = set()
        for cid in cat_order:
            name = cat_name_by_id.get(cid, "")
            if name and name in grouped and name not in used:
                ordered_cats.append(name)
                used.add(name)
        for name in sorted(grouped.keys()):
            if name not in used:
                ordered_cats.append(name)

        created = 0
        imported = 0
        mapped = 0
        picons_downloaded = 0
        picon_cap = 250 if safe_mode else 1200
        used_files = set()
        total_items = 0
        for cname in ordered_cats:
            total_items += len(grouped.get(cname, []))
        if total_items <= 0:
            total_items = 1
        done_items = 0
        for idx_cat, cname in enumerate(ordered_cats, 1):
            items = grouped.get(cname, [])
            if not items:
                continue
            self._set_progress(15 + int((done_items * 70) / total_items), "Mapowanie: %s (%d/%d)" % (cname, idx_cat, len(ordered_cats)))
            slug = _slugify_filename(cname, max_len=28)
            fn = "userbouquet.iptv_kat_%03d_%s.tv" % (idx_cat, slug)
            if fn in used_files:
                fn = "userbouquet.iptv_kat_%03d_%s_%d.tv" % (idx_cat, slug, idx_cat)
            used_files.add(fn)
            path = os.path.join("/etc/enigma2", fn)
            out = ["#NAME IPTV | %s" % cname]

            for st in items:
                sid = str(st.get("stream_id", "")).strip()
                if not sid:
                    continue
                name = (st.get("name", "") or "").strip() or ("Kanał %s" % sid)
                ext = (st.get("container_extension", "") or "").strip().lower() or "ts"
                url = "%s/live/%s/%s/%s.%s" % (host, user, password, sid, ext)
                enc = _encode_url_minimal(url)
                safe_name = self._safe_service_name(name)
                ref = ""
                # 1) Priorytet: reference ustawione w panelu XUI (dreambox playlist).
                for v in self._name_variants(name):
                    if v in panel_map:
                        ref = panel_map[v]
                        break
                if not ref:
                    for v in self._name_variants(name):
                        ck = _canonical_key(v)
                        if ck in panel_canon:
                            ref = panel_canon[ck]
                            break
                # 2) Fallback: lokalne mapowanie (bouquets/lamedb).
                for v in self._name_variants(name):
                    if ref:
                        break
                    if v in local_map:
                        ref = local_map[v]
                        break
                if not ref:
                    for v in self._name_variants(name):
                        if v in lamedb_map:
                            ref = lamedb_map[v]
                            break
                if not ref:
                    # Canonical exact fallback
                    for v in self._name_variants(name):
                        ck = _canonical_key(v)
                        if ck in local_canon:
                            ref = local_canon[ck]
                            break
                if not ref:
                    for v in self._name_variants(name):
                        ck = _canonical_key(v)
                        if ck in lamedb_canon:
                            ref = lamedb_canon[ck]
                            break
                if not ref:
                    # Canonical loose fallback (contains), guarded by minimum length.
                    target = _canonical_key(name)
                    if len(target) >= 5:
                        for ck, core in local_canon.items():
                            if len(ck) < 5:
                                continue
                            if ck in target or target in ck:
                                ref = core
                                break
                if not ref:
                    target = _canonical_key(name)
                    if len(target) >= 5:
                        for ck, core in lamedb_canon.items():
                            if len(ck) < 5:
                                continue
                            if ck in target or target in ck:
                                ref = core
                                break
                if ref:
                    ref = self._force_service_type_1(ref)
                    # Mapped to local reference: better chance for EPG/picon.
                    out.append("#SERVICE %s:%s:%s" % (ref, enc, safe_name))
                    mapped += 1
                    ref_core = ref
                    ref_full = "%s:%s:%s" % (ref, enc, safe_name)
                    # Dociagnij picon rowniez dla zmapowanych, jesli lokalnie brak.
                    pfn = self._service_core_to_picon_name(ref_core)
                    if picons_downloaded < picon_cap and not self._picon_exists(pfn):
                        if self._download_picon(st.get("stream_icon", ""), pfn):
                            picons_downloaded += 1
                else:
                    custom_core = self._custom_sid_to_core(st.get("custom_sid", ""))
                    if custom_core:
                        ref_core = custom_core
                    else:
                        ref_core = self._pseudo_service_core(sid, st.get("category_id"), name)
                    out.append("#SERVICE %s:%s:%s" % (ref_core, enc, safe_name))
                    ref_full = "%s:%s:%s" % (ref_core, enc, safe_name)
                    # For IPTV-only channels fetch icon from panel stream_icon.
                    if picons_downloaded < picon_cap:
                        pfn = self._service_core_to_picon_name(ref_core)
                        if (not self._picon_exists(pfn)) and self._download_picon(st.get("stream_icon", ""), pfn):
                            picons_downloaded += 1
                out.append("#DESCRIPTION %s" % name)
                imported += 1
                done_items += 1
                if (done_items % 8) == 0:
                    self._set_progress(15 + int((done_items * 70) / total_items), "Mapowanie kanałów: %d/%d" % (done_items, total_items))

            try:
                with open(path, "w") as f:
                    f.write("\n".join(out) + "\n")
                self._ensure_bouquet_link(fn, position=9999)
                created += 1
            except Exception:
                pass

        self._set_progress(90, "Odświeżanie list kanałów w Enigma2...")
        try:
            eDVBDB.getInstance().reloadBouquets()
            eDVBDB.getInstance().reloadServicelist()
        except Exception:
            pass

        self._set_progress(95, "Tworzenie plików EPG...")
        epg_ok = False
        epg_msg = ""
        try:
            epg_ok, epg_msg = self._build_epg_simple()
        except Exception:
            epg_ok = False
            epg_msg = "Blad generowania EPG."

        # Auto-trigger EPGImport
        if epg_ok:
            try:
                self._trigger_epgimport()
            except Exception:
                pass

        self._set_progress(100, "Zakończono import.")
        self["status"].setText("Gotowy.")
        self.session.open(
            MessageBox,
            "Import IPTV zakończony.\nKategorie: %d\nKanały: %d\nZmapowane DVB (EPG/picon): %d\nPobrane picony: %d\n\n%s" % (
                created, imported, mapped, picons_downloaded, epg_msg
            ),
            MessageBox.TYPE_INFO,
        )

    # ══════════════════════════════════════════════════════════════════════════
    #  POBIERANIE LISTY HOTBIRD + PODMIANA CANAL+
    # ══════════════════════════════════════════════════════════════════════════

    def ask_download_hotbird(self):
        """Potwierdź operację przed pobraniem listy z serwera."""
        url = _CHANNEL_LIST_URL
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        if not user or not password:
            self.session.open(MessageBox, "Brak danych logowania IPTV (uzytkownik/haslo).", MessageBox.TYPE_ERROR)
            return
        self.session.openWithCallback(
            self._do_download_hotbird,
            MessageBox,
            "Pobrac liste kanalow z serwera i podmienic kanaly Canal+ na IPTV?\n\nIstniejace pliki bouquet zostana nadpisane (z backupem).",
            MessageBox.TYPE_YESNO,
        )

    def _do_download_hotbird(self, confirmed):
        if not confirmed:
            self["status"].setText("Anulowano.")
            return
        self["status"].setText("Pobieranie listy z serwera...")
        try:
            self._run_download_hotbird_and_replace()
        except Exception as e:
            self["status"].setText("Blad.")
            self.session.open(MessageBox, "Blad pobierania listy:\n%s" % str(e), MessageBox.TYPE_ERROR)

    def _fetch_url_bytes(self, url, timeout=60):
        """Pobierz URL jako bajty (binary)."""
        last = None
        for _ in range(2):
            try:
                req = Request(url)
                req.add_header("User-Agent", "Enigma2-PoterX")
                return urlopen(req, timeout=timeout).read()
            except Exception as e:
                last = e
        if last:
            raise last
        return b""

    def _download_channel_list(self, url):
        """
        Pobiera liste kanalow z URL i zapisuje bezpiecznie do /etc/enigma2/.

        ZIP moze zawierac kompletny backup Enigma2 (bouquets.tv, lamedb, settings...).
        Wyciagamy TYLKO pliki userbouquet.*.tv + bouquets.tv.
        Pliki systemowe (lamedb, settings, satellites.xml itp.) sa pomijane.
        Zwraca slownik:
          {
            "userbouquets": [(fn, fp), ...],   # zapisane userbouquet.*.tv
            "bouquets_tv":  str or None,        # zawartosc bouquets.tv z ZIP (tekst)
          }
        """
        ENIGMA2_DIR = "/etc/enigma2"

        self["status"].setText("Pobieranie listy kanalow...")
        raw_bytes = self._fetch_url_bytes(url, timeout=90)
        if not raw_bytes:
            raise Exception("Serwer zwrocil pusta odpowiedz.")

        result = {"userbouquets": [], "bouquets_tv": None}

        # ── ZIP ──────────────────────────────────────────────────────────────
        if raw_bytes[:2] == b"PK":
            self["status"].setText("Rozpakowywanie ZIP...")
            try:
                zf = zipfile.ZipFile(io.BytesIO(raw_bytes))
            except zipfile.BadZipFile:
                raise Exception("Plik nie jest poprawnym archiwum ZIP.")

            all_names = zf.namelist()

            # Wyciagnij bouquets.tv (kolejnosc list) – tylko do odczytu, nie nadpisujemy
            for zname in all_names:
                if os.path.basename(zname).lower() == "bouquets.tv":
                    try:
                        result["bouquets_tv"] = zf.read(zname).decode("utf-8", errors="ignore")
                    except Exception:
                        pass
                    break

            # Zapisz TYLKO userbouquet.*.tv (pomijamy bouquets.tv, lamedb, settings itd.)
            ub_files = [n for n in all_names
                        if os.path.basename(n).lower().startswith("userbouquet.")
                        and os.path.basename(n).lower().endswith(".tv")]

            if not ub_files:
                raise Exception("ZIP nie zawiera plikow userbouquet.*.tv.")

            for zname in ub_files:
                fn = os.path.basename(zname)
                if not fn:
                    continue
                dst = os.path.join(ENIGMA2_DIR, fn)
                if os.path.exists(dst):
                    self._backup_file(dst)
                data = zf.read(zname)
                with open(dst, "wb") as f:
                    f.write(data)
                result["userbouquets"].append((fn, dst))

        # ── Bezposredni plik .tv ─────────────────────────────────────────────
        else:
            fn = os.path.basename(url.split("?")[0]) or "userbouquet.moja_lista.tv"
            fn = fn.lower()
            if not fn.endswith(".tv"):
                fn += ".tv"
            if not fn.startswith("userbouquet."):
                fn = "userbouquet." + fn
            dst = os.path.join(ENIGMA2_DIR, fn)
            if os.path.exists(dst):
                self._backup_file(dst)
            with open(dst, "wb") as f:
                f.write(raw_bytes)
            result["userbouquets"].append((fn, dst))

        return result

    def _apply_bouquets_tv_from_zip(self, bouquets_tv_content, saved_fns):
        """
        Aktualizuje lokalny /etc/enigma2/bouquets.tv na podstawie bouquets.tv z ZIP.
        Zachowuje kolejnosc z ZIP, ale tylko dla plikow ktore faktycznie zostaly pobrane.
        Nie usuwa istniejacych wpisow ktore nie sa w ZIP.
        """
        ENIGMA2_DIR = "/etc/enigma2"
        idx = os.path.join(ENIGMA2_DIR, "bouquets.tv")

        # Pliki ktore wlasnie zapisalismy
        saved_set = set(fn.lower() for fn in saved_fns)

        # Kolejnosc z ZIP
        zip_order = []
        for line in (bouquets_tv_content or "").splitlines():
            m = re.search(r'FROM BOUQUET "([^"]+)"', line)
            if m:
                fn = m.group(1)
                if fn.lower() in saved_set:
                    zip_order.append(fn)

        if not zip_order:
            # Nie udalo sie ustalic kolejnosci – dodaj po kolei
            for fn in saved_fns:
                self._ensure_bouquet_link(fn, position=9999)
            return

        # Wczytaj istniejacy bouquets.tv
        existing_lines = []
        try:
            if os.path.exists(idx):
                with open(idx, "r") as f:
                    existing_lines = [l.rstrip("\n") for l in f.readlines()]
        except Exception:
            existing_lines = ["#NAME User - bouquets (TV)"]

        if not existing_lines:
            existing_lines = ["#NAME User - bouquets (TV)"]

        # Usun stare wpisy dla plikow ktore pobieramy (bedziemy je wstawic w nowej kolejnosci)
        existing_lines = [l for l in existing_lines
                          if not any(fn in l for fn in saved_fns)]

        # Ustal pozycje wstawienia
        insert_first = config.plugins.poterx.hotbird_insert_first.value
        base_at = 1 if existing_lines and existing_lines[0].startswith("#NAME") else 0
        insert_pos = base_at if insert_first else len(existing_lines)

        # Wstaw nowe wpisy w kolejnosci z ZIP
        for i, fn in enumerate(zip_order):
            entry = '#SERVICE 1:7:1:0:0:0:0:0:0:0:FROM BOUQUET "%s" ORDER BY bouquet' % fn
            existing_lines.insert(insert_pos + i, entry)

        self._backup_file(idx)
        with open(idx, "w") as f:
            f.write("\n".join(existing_lines) + "\n")

    def _run_download_hotbird_and_replace(self):
        """
        Pelny flow:
        1. Pobierz userbouquet.*.tv z URL (ZIP lub plik .tv)
        2. Zaktualizuj bouquets.tv
        3. Pobierz URL-e Canal+ z panelu IPTV
        4. Podmien Canal+ we WSZYSTKICH plikach ktore maja te referencje
        5. Jeden reload na koncu
        6. Generuj EPG
        """
        url = _CHANNEL_LIST_URL

        # 1. Pobierz i zapisz bezpiecznie
        dl = self._download_channel_list(url)
        saved = dl["userbouquets"]
        if not saved:
            raise Exception("Nie zapisano zadnego pliku bouquet.")

        # 2. Zaktualizuj bouquets.tv
        self["status"].setText("Aktualizacja bouquets.tv...")
        saved_fns = [fn for fn, _ in saved]
        if dl["bouquets_tv"]:
            self._apply_bouquets_tv_from_zip(dl["bouquets_tv"], saved_fns)
        else:
            insert_first = config.plugins.poterx.hotbird_insert_first.value
            for i, fn in enumerate(saved_fns):
                pos = (2 + i) if insert_first else 9999
                self._ensure_bouquet_link(fn, position=pos)

        # 3. Pobierz URL-e kanalow IPTV – probuj dreambox, fallback M3U
        m3u_map = {}
        m3u_source = ""
        self["status"].setText("Pobieranie listy IPTV...")
        try:
            db_content = self._fetch_url_text(self._build_dreambox_url(), timeout=30)
            db_entries = self._parse_dreambox_playlist(db_content)
            m3u_map = self._dreambox_entries_to_url_map(db_entries)
            if m3u_map:
                m3u_source = "dreambox"
        except Exception:
            pass
        if not m3u_map:
            try:
                content = self._fetch_url_text(self._build_m3u_url(), timeout=60)
                m3u_map, _ = self._parse_m3u(content)
                if m3u_map:
                    m3u_source = "m3u"
            except Exception as e:
                m3u_source = "BLAD: %s" % str(e)

        # 4. Podmien Canal+ we WSZYSTKICH plikach z bouqueta ktore maja Canal+ referencje
        #    (nie tylko w jednym – lista moze byc podzielona na wiele plikow)
        replaced_total = 0
        replaced_files = []
        if m3u_map:
            self["status"].setText("Podmiana kanalow Canal+...")
            for fn, fp in saved:
                score = _score_bouquet_for_canal(fp)
                if score == 0:
                    continue  # ten plik nie ma Canal+ – pomijamy
                try:
                    n = self._replace_in_bouquet(fp, fp, m3u_map, force_title=False)
                    if n > 0:
                        replaced_total += n
                        replaced_files.append("%s (%d)" % (fn, n))
                except Exception:
                    pass

        # 5. Jeden reload na koncu (po wszystkich zmianach)
        self["status"].setText("Przeladowanie list kanalow...")
        try:
            eDVBDB.getInstance().reloadBouquets()
            eDVBDB.getInstance().reloadServicelist()
        except Exception:
            pass

        # 6. EPG
        epg_msg = ""
        try:
            self["status"].setText("Generowanie EPG...")
            epg_ok, epg_msg = self._build_epg_simple()
            if epg_ok:
                self._trigger_epgimport()
        except Exception:
            epg_msg = ""

        self["status"].setText("Gotowy.")

        # Buduj czytelny raport
        if not m3u_map:
            canal_msg = "UWAGA: Nie udalo sie pobrac listy IPTV!\nSprawdz polaczenie z serwerem.\nCanal+ NIE zostalo podmienione."
        elif replaced_total == 0:
            canal_msg = "UWAGA: Lista IPTV pobrana (%s), ale\nnie znaleziono kanalow Canal+ do podmiany.\nSprawdz nazwy kanalow Canal+ w panelu IPTV." % m3u_source
        else:
            files_list = ", ".join(replaced_files)
            canal_msg = "Podmieniono %d kanalow Canal+ (zrodlo: %s)\nPliki: %s" % (replaced_total, m3u_source, files_list)

        epg_line = ("\n\n%s" % epg_msg) if epg_msg else ""

        self.session.open(
            MessageBox,
            "Lista kanalow zainstalowana!\nPobrano plikow: %d\n\n%s%s" % (len(saved), canal_msg, epg_line),
            MessageBox.TYPE_INFO,
        )

    def run_bzyk_replace(self):
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        if not user or not password:
            self.session.open(MessageBox, "Brak danych logowania (uzytkownik/haslo).", MessageBox.TYPE_ERROR)
            return

        src = self._resolve_source_bouquet_path()
        if not src or not os.path.exists(src):
            self.session.open(MessageBox, "Nie znaleziono zrodla bouquet (lista Bzyk83).", MessageBox.TYPE_ERROR)
            return

        mode = config.plugins.poterx.bzyk_target_mode.value
        if mode == "inplace":
            dst_path = src
            dst_fn = os.path.basename(src)
        else:
            dst_path, dst_fn = self._resolve_custom_bouquet_path()
            if os.path.abspath(src) == os.path.abspath(dst_path):
                self.session.open(MessageBox, "Zrodlo i cel to ten sam plik bouquet.", MessageBox.TYPE_ERROR)
                return

        # Faster path: take URLs directly from dreambox playlist.
        m3u_map = {}
        db_entries = []
        self["status"].setText("Pobieranie listy dreambox...")
        try:
            db_content = self._fetch_url_text(self._build_dreambox_url(), timeout=30)
            db_entries = self._parse_dreambox_playlist(db_content)
            m3u_map = self._dreambox_entries_to_url_map(db_entries)
        except Exception:
            m3u_map = {}

        # Fallback to full M3U only if dreambox map is empty.
        if not m3u_map:
            url = self._build_m3u_url()
            self["status"].setText("Pobieranie M3U...")
            try:
                content = self._fetch_url_text(url, timeout=45)
            except Exception as e:
                self.session.open(MessageBox, "Blad pobierania M3U: %s" % str(e), MessageBox.TYPE_ERROR)
                self["status"].setText("Blad M3U.")
                return
            m3u_map, _m3u_entries = self._parse_m3u(content)
            if not m3u_map:
                self.session.open(MessageBox, "M3U puste albo niepoprawne.", MessageBox.TYPE_ERROR)
                self["status"].setText("Blad M3U.")
                return

        self["status"].setText("Tworzenie listy...")
        try:
            bkp = ""
            if mode == "inplace":
                bkp = self._backup_file(src)
            replaced = self._replace_in_bouquet(src, dst_path, m3u_map, force_title=(mode != "inplace"))
        except Exception as e:
            self.session.open(MessageBox, "Blad podmiany bouquet: %s" % str(e), MessageBox.TYPE_ERROR)
            self["status"].setText("Blad.")
            return

        extra_fn = ""
        extra_count = 0
        if config.plugins.poterx.bzyk_extra_enable.value:
            extra_path, extra_fn = self._resolve_extra_bouquet_path()
            # Names used for CANAL+ mapping, so we don't duplicate them in "reszta" bouquet
            used = set([
                _normalize_name("canal+ premium"),
                _normalize_name("canal+ 1"),
                _normalize_name("canal+1"),
                _normalize_name("canal+ film"),
                _normalize_name("canal+ seriale"),
                _normalize_name("canal+ dokument"),
                _normalize_name("canal+ sport 1"),
                _normalize_name("canal+ sport"),
                _normalize_name("canal+ sport 2"),
                _normalize_name("canal+ sport 3"),
                _normalize_name("canal+ sport 4"),
                _normalize_name("canal+ extra 1"),
                _normalize_name("canal+ extra 2"),
                _normalize_name("canal+ extra 3"),
                _normalize_name("canal+ extra 4"),
                _normalize_name("canal+ now"),
            ])
            try:
                extra_title = (config.plugins.poterx.bzyk_extra_title.value or "").strip() or "IPTV - Pozostale"
                # Reuse already-fetched db_entries; avoid second download.
                if db_entries:
                    extra_count = self._write_extra_iptv_bouquet_from_dreambox(extra_path, extra_title, db_entries, used)
                else:
                    extra_count = 0
            except Exception:
                extra_count = 0

        if mode != "inplace":
            if config.plugins.poterx.bzyk_insert_first.value:
                self._ensure_bouquet_link(dst_fn, position=2)
                if extra_fn and extra_count > 0:
                    self._ensure_bouquet_link(extra_fn, position=3)
            else:
                # Do not reorder bouquets list; just make sure the bouquets are visible.
                self._ensure_bouquet_link(dst_fn, position=9999)
                if extra_fn and extra_count > 0:
                    self._ensure_bouquet_link(extra_fn, position=9999)
        else:
            # In-place: bouquet juz jest w bouquets.tv; ewentualnie tylko dopinamy extra.
            if extra_fn and extra_count > 0:
                self._ensure_bouquet_link(extra_fn, position=9999)

        try:
            eDVBDB.getInstance().reloadBouquets()
            eDVBDB.getInstance().reloadServicelist()
        except Exception:
            pass

        # EPG – generuj pliki EPGImport (czyta referencje wprost z bouquetow)
        epg_msg = ""
        try:
            self["status"].setText("Generowanie EPG...")
            epg_ok, epg_msg = self._build_epg_simple()
            if epg_ok:
                self._trigger_epgimport()
        except Exception:
            epg_msg = ""

        self["status"].setText("Gotowy.")
        extra_msg = ""
        if extra_fn and extra_count > 0:
            extra_msg = "\nDodatkowy bouquet: %s (%d kanalow)" % (extra_fn, extra_count)
        bkp_msg = ""
        if mode == "inplace" and bkp:
            bkp_msg = "\nBackup: %s" % os.path.basename(bkp)
        epg_line = ""
        if epg_msg:
            epg_line = "\n\n%s" % epg_msg
        self.session.open(
            MessageBox,
            "Zrobione.\nCel: %s\nPodmieniono kanalow: %d%s%s%s" % (dst_fn, replaced, extra_msg, bkp_msg, epg_line),
            MessageBox.TYPE_INFO,
        )

    def do_update(self, confirm):
        if not confirm:
            self["status"].setText("Aktualizacja anulowana.")
            self.check_account_info()
            return
        self["status"].setText("Pobieranie aktualizacji...")
        try:
            code = urlopen("{}/plugin.py".format(UPDATE_BASE_URL), timeout=20).read()
            with open(PLUGIN_PATH + "/plugin.py", "wb") as f: f.write(code)
            try:
                img = urlopen("{}/plugin.png".format(UPDATE_BASE_URL), timeout=10).read()
                with open(PLUGIN_PATH + "/plugin.png", "wb") as f: f.write(img)
            except: pass
            self.session.openWithCallback(self.restart_gui, MessageBox, "Zaktualizowano! Restart GUI...", MessageBox.TYPE_INFO)
        except Exception as e:
            self.session.open(MessageBox, "Błąd: " + str(e), MessageBox.TYPE_ERROR)

    def restart_gui(self, confirmed=True):
        if confirmed:
            quitMainloop(3)
        else:
            self["status"].setText("Gotowy (bez restartu).")
            self.check_account_info()

    # ══════════════════════════════════════════════════════════════════════════
    #  PICONY — żółty przycisk
    # ══════════════════════════════════════════════════════════════════════════

    def ask_picons(self):
        for x in self["config"].list:
            x[1].save()
        config.save()

        source  = config.plugins.poterx.picon_source.value   # "panel" | "server"
        size    = config.plugins.poterx.picon_size.value      # np. "220x132"
        dest    = config.plugins.poterx.picon_path.value      # katalog docelowy

        if source == "server":
            self.session.openWithCallback(
                self._do_picons_from_server, MessageBox,
                "Pobrac picony z serwera PoterX?\n\n"
                "Rozdzielczosc: %s\n"
                "Katalog: %s\n\n"
                "Kontynuowac?" % (size, dest),
                MessageBox.TYPE_YESNO,
            )
        else:
            user     = config.plugins.poterx.username.value
            password = config.plugins.poterx.password.value
            if not user or not password:
                self.session.open(MessageBox, "Brak danych logowania (uzytkownik/haslo).", MessageBox.TYPE_ERROR)
                return
            self.session.openWithCallback(
                self._do_picons_from_panel, MessageBox,
                "Pobrac picony z panelu IPTV?\n\n"
                "Zrodlo: stream_icon z API panelu\n"
                "Rozdzielczosc: %s (resize przez PIL)\n"
                "Katalog: %s\n\n"
                "Kontynuowac?" % (size, dest),
                MessageBox.TYPE_YESNO,
            )

    # ── Źródło: serwer PoterX (tar.gz) ──────────────────────────────────────

    def _do_picons_from_server(self, confirm):
        """Pobiera paczkę piconów z serwera PoterX (tar.gz z wybraną rozdzielczością)."""
        if not confirm:
            return
        size = config.plugins.poterx.picon_size.value
        dest = config.plugins.poterx.picon_path.value
        picons_url = PICONS_URL_TEMPLATE % size   # np. picons_220x132.tar.gz

        self["status"].setText("Pobieranie paczki piconow %s..." % size)
        self._picon_total  = 0
        self._picon_done   = 0
        self._picon_result = None

        t = threading.Thread(target=self._picon_server_thread, args=(picons_url, dest))
        t.daemon = True
        t.start()

        self._picon_poll_timer = eTimer()
        self._picon_poll_timer.callback.append(self._picon_poll_check)
        self._picon_poll_timer.start(500, False)

    def _picon_server_thread(self, url, dest):
        """Watek: pobiera i rozpakowuje tar.gz z piconami z serwera."""
        tmp_file = "/tmp/picons.tar.gz"
        try:
            # Pobierz plik
            req = Request(url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            response = urlopen(req, timeout=180)
            with open(tmp_file, "wb") as f:
                while True:
                    chunk = response.read(16384)
                    if not chunk:
                        break
                    f.write(chunk)

            if not tarfile.is_tarfile(tmp_file):
                self._picon_result = (0, 1, "Plik nie jest prawidlowym archiwum TAR")
                return

            # Stworz katalog docelowy
            if not os.path.isdir(dest):
                os.makedirs(dest)

            # Rozpakuj – plaskie (ignoruj podkatalogi w archiwum)
            count = 0
            with tarfile.open(tmp_file, "r:gz") as tar:
                members = []
                for member in tar.getmembers():
                    if member.isfile() and member.name.endswith(".png"):
                        member.name = os.path.basename(member.name)
                        members.append(member)
                        count += 1
                tar.extractall(path=dest, members=members)

            # Usun tmp
            try:
                os.remove(tmp_file)
            except Exception:
                pass

            # Picon linker: 1_0_1_ → symlink 4097_0_1_
            self._create_picon_symlinks(dest)

            self._picon_result = (count, 0, "")
        except Exception as ex:
            try:
                os.remove(tmp_file)
            except Exception:
                pass
            self._picon_result = (0, 1, str(ex))

    # ── Źródło: panel IPTV (stream_icon z API) ──────────────────────────────

    def _do_picons_from_panel(self, confirm):
        """Pobiera picony z panelu XUI.one (stream_icon z get_live_streams)."""
        if not confirm:
            return
        self["status"].setText("Picony: pobieranie listy kanalow z API...")
        host     = _sanitize_host(config.plugins.poterx.host.value)
        user     = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        dest     = config.plugins.poterx.picon_path.value
        size_str = config.plugins.poterx.picon_size.value   # np. "220x132"

        # Parsuj rozdzielczosc
        try:
            tw, th = [int(x) for x in size_str.split("x")]
        except Exception:
            tw, th = 220, 132

        # ── 1. Pobierz liste kanalow z API ───────────────────────────────────
        streams_url = "{}/player_api.php?username={}&password={}&action=get_live_streams".format(
            host, user, password
        )
        try:
            req = Request(streams_url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            raw     = to_str(urlopen(req, timeout=60).read())
            streams = json.loads(raw)
        except Exception as e:
            self.session.open(MessageBox, "Blad API: %s" % str(e), MessageBox.TYPE_ERROR)
            self["status"].setText("Blad.")
            return

        if not isinstance(streams, list) or not streams:
            self.session.open(MessageBox, "API zwrocilo pusta liste kanalow.", MessageBox.TYPE_ERROR)
            return

        # ── 2. Zbierz referencje z WSZYSTKICH zrodel ─────────────────────────
        self["status"].setText("Picony: zbieranie referencji...")
        bouquet_ref_map = {}   # norm_name → core_ref

        # 2a. Z playlisty dreambox (API panelu)
        try:
            db_text    = self._fetch_url_text(self._build_dreambox_url(), timeout=40)
            db_entries = self._parse_dreambox_playlist(db_text)
            for e in db_entries:
                sline = (e.get("service") or "").strip()
                if not sline.startswith("#SERVICE "):
                    continue
                core = self._extract_ref_core(sline[len("#SERVICE "):].strip())
                norm = (e.get("norm") or "").strip()
                if norm and core:
                    bouquet_ref_map[norm] = core
        except Exception:
            pass

        # 2b. Z lokalnych bouquetow Enigma2 (wlacznie z IPTV 4097)
        # Dzieki temu kanaly PPV ktore sa w bouquecie tez dostana picony.
        try:
            for fn, fp in _list_tv_bouquet_files():
                try:
                    with open(fp, "r") as f:
                        blines = [l.strip() for l in f.readlines()]
                except Exception:
                    continue
                i = 0
                while i < len(blines):
                    line = blines[i]
                    if line.startswith("#SERVICE ") and "FROM BOUQUET" not in line.upper():
                        srv = line[len("#SERVICE "):].strip()
                        core = self._extract_ref_core(srv)
                        if core:
                            # Szukaj nazwy w #DESCRIPTION
                            bname = ""
                            if i + 1 < len(blines) and blines[i + 1].startswith("#DESCRIPTION"):
                                bname = blines[i + 1][len("#DESCRIPTION"):].strip()
                            if bname:
                                bnorm = _normalize_name(bname)
                                if bnorm and bnorm not in bouquet_ref_map:
                                    bouquet_ref_map[bnorm] = core
                    i += 1
        except Exception:
            pass

        # ── 3. Zbuduj listę [picon_filename, icon_url] ──────────────────────
        # Generujemy DWA typy piconow:
        #   SRP (Service Reference Picon) — nazwa pliku z service ref (priorytet)
        #   SNP (Service Name Picon) — nazwa pliku z nazwy kanalu (fallback dla PPV itp.)
        # Dzieki temu kanaly PPV i niestandardowe tez dostana picony.
        picon_list = []
        seen = set()
        for stream in streams:
            icon_url = str(stream.get("stream_icon") or "").strip()
            if not icon_url or not icon_url.startswith("http"):
                continue
            name       = str(stream.get("name") or "").strip()
            sid_raw    = str(stream.get("stream_id") or "").strip()
            custom_sid = str(stream.get("custom_sid") or "").strip()
            norm       = _normalize_name(name)

            # Optymalizacja URL – mniejszy rozmiar obrazka
            for big in ("1920px", "1280px", "1200px", "2000px", "728px"):
                icon_url = icon_url.replace(big, "400px")

            # SRP: picon z service reference
            core = bouquet_ref_map.get(norm, "")
            if not core and sid_raw:
                core = self._pseudo_service_core(sid_raw, stream.get("category_id"), name)
            if core:
                picon_fn = self._service_core_to_picon_name(core)
                if picon_fn not in seen and not os.path.exists(os.path.join(dest, picon_fn)):
                    seen.add(picon_fn)
                    picon_list.append((picon_fn, icon_url))

            # SNP: picon z nazwy kanalu (fallback — dla PPV, eventow, niestandardowych)
            snp_fn = _name_to_picon_filename(name)
            if snp_fn and snp_fn not in seen and not os.path.exists(os.path.join(dest, snp_fn)):
                seen.add(snp_fn)
                picon_list.append((snp_fn, icon_url))

        if not picon_list:
            self.session.open(MessageBox,
                "Wszystkie picony sa juz pobrane (%d kanalow sprawdzonych)." % len(streams),
                MessageBox.TYPE_INFO)
            self["status"].setText("Gotowy.")
            return

        # ── 5. Uruchom wielowątkowe pobieranie w tle ─────────────────────────
        self["status"].setText("Picony: pobieranie %d ikon..." % len(picon_list))
        self._picon_total  = len(picon_list)
        self._picon_done   = 0
        self._picon_result = None

        t = threading.Thread(
            target=self._picon_panel_thread,
            args=(picon_list, dest, tw, th),
        )
        t.daemon = True
        t.start()

        self._picon_poll_timer = eTimer()
        self._picon_poll_timer.callback.append(self._picon_poll_check)
        self._picon_poll_timer.start(500, False)

    def _picon_panel_thread(self, picon_list, dest, tw, th):
        """Watek: pobiera picony z panelu wielowatkowo (max 10 watkow)."""
        try:
            if not os.path.isdir(dest):
                os.makedirs(dest)
        except Exception:
            self._picon_result = (0, len(picon_list), "Nie mozna utworzyc katalogu")
            return

        lock = threading.Lock()

        def download_one(item):
            picon_fn, icon_url = item
            out_path = os.path.join(dest, picon_fn)
            success = False
            try:
                req = Request(icon_url)
                req.add_header("User-Agent", "Enigma2-PoterX")
                resp = urlopen(req, timeout=10)
                data = resp.read()
                if not data or len(data) < 32:
                    return False

                # Sprawdz magic bytes (PNG lub JPEG)
                if data[:4] != b'\x89PNG' and data[:2] != b'\xff\xd8':
                    return False

                # Sprobuj resize przez PIL
                try:
                    from PIL import Image
                    import io
                    img = Image.open(io.BytesIO(data))
                    img = img.convert("RGBA")
                    img.thumbnail((tw, th), Image.LANCZOS)
                    canvas = Image.new("RGBA", (tw, th), (0, 0, 0, 0))
                    x = (tw - img.width) // 2
                    y = (th - img.height) // 2
                    canvas.paste(img, (x, y), img)
                    canvas.save(out_path, "PNG", optimize=True)
                    success = True
                except ImportError:
                    with open(out_path, "wb") as f:
                        f.write(data)
                    success = True
            except Exception:
                success = False

            with lock:
                self._picon_done = getattr(self, "_picon_done", 0) + 1
            return success

        # Wielowatkowe pobieranie
        try:
            from concurrent.futures import ThreadPoolExecutor
            with ThreadPoolExecutor(max_workers=10) as pool:
                results = list(pool.map(download_one, picon_list))
            ok_count   = sum(1 for r in results if r)
            fail_count = len(results) - ok_count
        except ImportError:
            ok_count = fail_count = 0
            for item in picon_list:
                if download_one(item):
                    ok_count += 1
                else:
                    fail_count += 1

        # Picon linker
        self._create_picon_symlinks(dest)

        self._picon_result = (ok_count, fail_count, "")

    # ── Wspólne: symlinki + poll timer ───────────────────────────────────────

    def _create_picon_symlinks(self, dest):
        """Tworzy symlinki 4097_0_1_... → 1_0_1_... dla IPTV service type."""
        try:
            for fn in os.listdir(dest):
                if fn.startswith("1_0_1_") and fn.endswith(".png"):
                    link_name = "4097_0_1_" + fn[6:]
                    link_path = os.path.join(dest, link_name)
                    if not os.path.exists(link_path):
                        try:
                            os.symlink(fn, link_path)
                        except Exception:
                            pass
        except Exception:
            pass

    def _picon_poll_check(self):
        """Timer: sprawdza czy watek pobierania piconow skonczyl."""
        if self._picon_result is None:
            done  = getattr(self, "_picon_done", 0)
            total = getattr(self, "_picon_total", 0)
            if total > 0:
                self["status"].setText("Picony: %d / %d..." % (done, total))
            else:
                dots = getattr(self, "_picon_dots", 0) + 1
                self._picon_dots = dots
                self["status"].setText("Pobieranie piconow%s" % ("." * (dots % 4 + 1)))
            return

        self._picon_poll_timer.stop()
        ok, fail = self._picon_result[0], self._picon_result[1]
        err_msg  = self._picon_result[2] if len(self._picon_result) > 2 else ""
        dest     = config.plugins.poterx.picon_path.value

        if err_msg:
            self.session.open(MessageBox,
                "Blad piconow: %s" % err_msg, MessageBox.TYPE_ERROR)
            self["status"].setText("Blad piconow.")
            return

        total = ok + fail
        self.session.openWithCallback(
            self.restart_gui, MessageBox,
            "Picony pobrane!\n\n"
            "Pobrano: %d / %d\n"
            "Bledy: %d\n"
            "Katalog: %s\n\n"
            "Zrestartowac GUI?" % (ok, total, fail, dest),
            MessageBox.TYPE_YESNO,
        )
        self["status"].setText("Picony OK: %d pobrano." % ok)

    def _trigger_epgimport(self):
        """
        Uruchamia EPGImport automatycznie po wygenerowaniu plikow.
        Probuje kilka metod (rozne wersje EPGImport maja rozne API).
        KLUCZOWE: channelFilter MUSI zwracac True (nie None!) zeby
        EPGImport nie odrzucil kanalow.
        Zwraca (ok: bool, info: str).
        """
        epgimport_dir = "/usr/lib/enigma2/python/Plugins/Extensions/EPGImport"
        if not os.path.isdir(epgimport_dir):
            # EPGImport nie zainstalowany – probuj bezposredni import
            try:
                ok, msg = self._direct_epg_import()
                if ok:
                    return True, msg
            except Exception:
                pass
            return False, (
                "EPGImport nie jest zainstalowany.\n"
                "Zainstaluj: opkg install enigma2-plugin-extensions-epgimport\n"
                "Lub uzyj bezposredniego importu (klawisz 0)."
            )

        _errors = []

        # Metoda 1: EPGImport z wlasnym zrodlem (najlepsza kontrola)
        try:
            from enigma import eEPGCache
            from Plugins.Extensions.EPGImport.EPGImport import EPGImport as EpgCls
            from Plugins.Extensions.EPGImport.EPGConfig import enumSourcesFile
            src_path = "/etc/epgimport/poterx_iptv.sources.xml"
            if os.path.exists(src_path):
                sources = list(enumSourcesFile(src_path))
                if sources:
                    # channelFilter=None → brak filtra → importuj WSZYSTKO
                    epg = EpgCls(eEPGCache.getInstance(), None)
                    epg.sources = sources
                    epg.onDone = lambda reboot=False, epgfile="": None
                    epg.beginImport(longDescUntil=24 * 3600)
                    return True, "EPGImport uruchomiony (PoterX IPTV)."
        except Exception as e:
            _errors.append("M1: %s" % str(e))

        # Metoda 2: EPGImport z innym importem modulu
        try:
            from enigma import eEPGCache
            from Plugins.Extensions.EPGImport import EPGImport as epgimp
            if hasattr(epgimp, "EPGImport"):
                obj = epgimp.EPGImport(eEPGCache.getInstance(), None)
                obj.onDone = lambda reboot=False, epgfile="": None
                obj.beginImport(longDescUntil=24 * 3600)
                return True, "EPGImport uruchomiony automatycznie."
        except Exception as e:
            _errors.append("M2: %s" % str(e))

        # Metoda 3: plugin.autostart
        try:
            from Plugins.Extensions.EPGImport import plugin as epg_plugin
            if hasattr(epg_plugin, "autostart"):
                epg_plugin.autostart(reason=0, session=self.session)
                return True, "EPGImport uruchomiony (autostart)."
        except Exception as e:
            _errors.append("M3: %s" % str(e))

        # Metoda 4: Bezposredni import XMLTV → eEPGCache (nie wymaga EPGImport)
        try:
            ok, msg = self._direct_epg_import()
            if ok:
                return True, msg
            _errors.append("M4-direct: %s" % msg)
        except Exception as e:
            _errors.append("M4: %s" % str(e))

        # Zapisz bledy do loga diagnostycznego
        try:
            with open("/tmp/poterx_epg_errors.txt", "w") as f:
                f.write("\n".join(_errors) + "\n")
        except Exception:
            pass

        return False, (
            "Nie udalo sie zaimportowac EPG.\n"
            "Bledy: %s\n"
            "Log: /tmp/poterx_epg_errors.txt" % "; ".join(_errors[:3])
        )

    # ══════════════════════════════════════════════════════════════════════════
    #  POBIERZ IPTV – zielony przycisk
    #  Pobiera WSZYSTKIE kanaly LIVE (bez VOD) z get_live_streams API,
    #  buduje bukiet "IPTV | PoterX" w tle z widocznym postepem.
    # ══════════════════════════════════════════════════════════════════════════

    def download_direct(self):
        for x in self["config"].list:
            x[1].save()
        config.save()

        user     = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        if not user or not password:
            self.session.open(MessageBox, "Brak danych logowania (uzytkownik/haslo).", MessageBox.TYPE_ERROR)
            return

        if getattr(self, "_dl_running", False):
            self["status"].setText("Pobieranie jest juz uruchomione...")
            return

        self._dl_running = True
        self._dl_result  = None
        self._dl_status  = "Inicjalizacja..."

        host = _sanitize_host(config.plugins.poterx.host.value)
        self["status"].setText("Pobieranie IPTV: uruchamianie...")

        t = threading.Thread(target=self._dl_iptv_thread, args=(host, user, password))
        t.daemon = True
        t.start()

        self._dl_timer = eTimer()
        self._dl_timer.callback.append(self._dl_poll_check)
        self._dl_timer.start(500, False)

    def _dl_iptv_thread(self, host, user, password):
        """
        Watek tla:
          1. Pobiera get_live_streams (tylko TV, zero VOD)
          2. Buduje userbouquet.canal_poterx.tv z nazwa 'IPTV | PoterX'
        Bez zadnych wywolan Enigma2 API – wszystko w glownym watku.
        """
        try:
            # ── Krok 1: get_live_streams ─────────────────────────────────────
            self._dl_status = "Pobieranie listy kanalow LIVE z panelu..."
            url = "%s/player_api.php?username=%s&password=%s&action=get_live_streams" % (
                host, user, password
            )
            req = Request(url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            raw     = to_str(urlopen(req, timeout=60).read())
            streams = json.loads(raw)

            if not isinstance(streams, list) or not streams:
                self._dl_result = (False, "API nie zwrocilo listy kanalow LIVE.")
                return

            total = len(streams)
            self._dl_status = "Budowanie bukietu: %d kanalow..." % total

            # ── Krok 2: buduj wpisy bouquet ──────────────────────────────────
            out = ["#NAME IPTV | PoterX"]
            added = 0
            for i, stream in enumerate(streams):
                sid = str(stream.get("stream_id") or "").strip()
                if not sid:
                    continue
                name = (stream.get("name") or "").strip() or ("Kanal %s" % sid)
                ext  = ((stream.get("container_extension") or "").strip().lower()) or "ts"

                stream_url = "%s/live/%s/%s/%s.%s" % (host, user, password, sid, ext)
                enc        = _encode_url_minimal(stream_url)
                safe_name  = self._safe_service_name(name)

                # Stabilna pseudo-referencja oparta o stream_id (unikalna per kanal)
                core = self._pseudo_service_core(sid, stream.get("category_id"), name)

                out.append("#SERVICE %s:%s:%s" % (core, enc, safe_name))
                out.append("#DESCRIPTION %s" % safe_name)
                added += 1

                if (i % 50) == 0:
                    self._dl_status = "Budowanie bukietu: %d / %d kanalow..." % (i + 1, total)

            if added == 0:
                self._dl_result = (False, "Brak kanalow do zapisania.")
                return

            # ── Krok 3: zapisz plik bouquet ──────────────────────────────────
            bouquet_fn   = "userbouquet.canal_poterx.tv"
            bouquet_path = "/etc/enigma2/" + bouquet_fn

            with open(bouquet_path, "w") as f:
                f.write("\n".join(out) + "\n")

            self._dl_result = (True, added, bouquet_fn)

        except Exception as ex:
            self._dl_result = (False, "Blad pobierania: %s" % str(ex))

    def _dl_poll_check(self):
        """
        eTimer callback – glowny watek.
        Aktualizuje status; po zakonczeniu watku:
          * dodaje bouquet do bouquets.tv
          * przeladowuje listy kanalow
          * generuje pliki EPG i odpala EPGImport
        """
        if self._dl_result is None:
            self["status"].setText(getattr(self, "_dl_status", "Pobieranie..."))
            return

        self._dl_timer.stop()
        self._dl_running = False

        ok = self._dl_result[0]

        if not ok:
            self["status"].setText("Blad pobierania IPTV.")
            self.session.open(MessageBox, self._dl_result[1], MessageBox.TYPE_ERROR)
            return

        count, bouquet_fn = self._dl_result[1], self._dl_result[2]

        # ── Dodaj bouquet na 1. miejscu bouquets.tv ───────────────────────────
        self["status"].setText("Aktualizacja bouquets.tv...")
        self._ensure_bouquet_link_first(bouquet_fn)

        # ── Przeladuj listy kanalow ───────────────────────────────────────────
        self["status"].setText("Przeladowanie list kanalow...")
        try:
            eDVBDB.getInstance().reloadBouquets()
            eDVBDB.getInstance().reloadServicelist()
        except Exception:
            pass

        # ── Generuj pliki EPG i odpala EPGImport ─────────────────────────────
        self["status"].setText("Generowanie EPG...")
        epg_ok  = False
        epg_msg = ""
        try:
            epg_ok, epg_msg = self._build_epg_simple()
            if epg_ok:
                self._trigger_epgimport()
        except Exception:
            epg_msg = "Blad generowania EPG."

        epg_line = ("\n\n%s" % epg_msg) if epg_msg else ""
        self["status"].setText("Gotowy – %d kanalow LIVE." % count)
        self.session.openWithCallback(
            self.restart_gui,
            MessageBox,
            "Bukiet IPTV | PoterX gotowy!\n\n"
            "Kanalow LIVE (bez VOD): %d\n"
            "Plik: %s"
            "%s\n\n"
            "Zrestartowac GUI?" % (count, bouquet_fn, epg_line),
            MessageBox.TYPE_YESNO,
        )

    def _on_ask_install_epgimport(self, confirmed):
        """Callback po pytaniu o instalację EPGImport."""
        epg_msg = getattr(self, "_pending_epg_msg", "")
        if confirmed:
            self._install_epgimport(epg_msg)
        else:
            self._finish_download_direct(True, epg_msg, "\n\n>> EPGImport nie zainstalowany. Mozesz go zainstalowac pozniej przez Menedzer Oprogramowania.")

    def _install_epgimport(self, epg_msg=""):
        """
        Instaluje EPGImport przez opkg w osobnym watku (subprocess.Popen).
        eTimer co 500ms sprawdza czy watek sie skonczyl.
        Dzieki temu GUI nie zamarza i mamy pelny log z opkg.
        """
        self._epg_install_epg_msg = epg_msg
        self._epg_install_result  = None   # (retval, output) – wypelnia watek
        self["status"].setText("Instalowanie EPGImport (opkg update + install)...")

        # Uruchom instalacje w watku
        t = threading.Thread(target=self._epg_install_thread)
        t.daemon = True
        t.start()

        # Timer sprawdza co 500ms czy watek skonczyl
        self._epg_poll_timer = eTimer()
        self._epg_poll_timer.callback.append(self._epg_poll_check)
        self._epg_poll_timer.start(500, False)   # False = powtarzaj

    def _epg_install_thread(self):
        """Watek: czysci cache + opkg update + opkg install. Zapisuje wynik w self._epg_install_result."""
        full_log = []
        try:
            # Krok 0: Wyczysc uszkodzony cache opkg (pliki 0 bajtow)
            try:
                cache_dir = "/var/cache/opkg"
                if os.path.isdir(cache_dir):
                    removed = 0
                    for fn in os.listdir(cache_dir):
                        fp = os.path.join(cache_dir, fn)
                        try:
                            if os.path.isfile(fp) and os.path.getsize(fp) == 0:
                                os.remove(fp)
                                removed += 1
                        except Exception:
                            pass
                    if removed:
                        full_log.append("=== Usunieto %d uszkodzonych plikow z cache ===\n" % removed)
            except Exception:
                pass

            # Krok 1: opkg update
            try:
                p1 = subprocess.Popen(
                    ["opkg", "update"],
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT
                )
                out1, _ = p1.communicate(timeout=120)
                full_log.append("=== opkg update (kod: %d) ===\n" % p1.returncode)
                full_log.append(to_str(out1) if out1 else "")
            except Exception as e1:
                full_log.append("=== opkg update BLAD: %s ===\n" % str(e1))

            # Krok 2: opkg install
            try:
                p2 = subprocess.Popen(
                    ["opkg", "install", "enigma2-plugin-extensions-epgimport"],
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT
                )
                out2, _ = p2.communicate(timeout=120)
                full_log.append("\n=== opkg install (kod: %d) ===\n" % p2.returncode)
                full_log.append(to_str(out2) if out2 else "")
                self._epg_install_result = (p2.returncode, "".join(full_log))
            except Exception as e2:
                full_log.append("\n=== opkg install BLAD: %s ===\n" % str(e2))
                self._epg_install_result = (1, "".join(full_log))
        except Exception as ex:
            self._epg_install_result = (1, "Blad ogolny: %s" % str(ex))

    def _epg_poll_check(self):
        """Timer: sprawdza czy watek instalacji skonczyl prace."""
        if self._epg_install_result is None:
            # Jeszcze trwa – pokaz animacje
            dots = getattr(self, "_epg_dots", 0) + 1
            self._epg_dots = dots
            self["status"].setText("Instalowanie EPGImport%s" % ("." * (dots % 4 + 1)))
            return

        # Watek skonczyl – zatrzymaj timer
        self._epg_poll_timer.stop()

        retval, output = self._epg_install_result
        epg_msg = getattr(self, "_epg_install_epg_msg", "")
        last_log = output.strip()[-600:] if output.strip() else "(brak logu)"

        if retval == 0:
            trig_ok, trig_msg = self._trigger_epgimport()
            self._finish_download_direct(
                True, epg_msg,
                "\n\n>> EPGImport zainstalowany pomyslnie!\n>> %s" % trig_msg,
            )
        else:
            self._finish_download_direct(
                True, epg_msg,
                (
                    "\n\n>> Blad instalacji EPGImport (kod: %d)\n\n"
                    "Log opkg:\n%s\n\n"
                    "Aby zainstalowac recznie przez SSH:\n"
                    "  opkg update\n"
                    "  opkg install enigma2-plugin-extensions-epgimport"
                ) % (retval, last_log),
            )

    def _finish_download_direct(self, epg_ok, epg_msg, epg_trigger_info=""):
        """Pokazuje podsumowanie po zakończeniu download_direct."""
        self.check_account_info()

        if epg_ok:
            summary = (
                "Playlista pobrana pomyslnie!\n\n"
                "%s"
                "%s\n\n"
                "Zrestartowac GUI?"
            ) % (epg_msg, epg_trigger_info)
        else:
            summary = (
                "Playlista pobrana pomyslnie!\n\n"
                "Blad EPG: %s\n\n"
                "Zrestartowac GUI?" % epg_msg
            )

        self.session.openWithCallback(
            self.restart_gui, MessageBox, summary, MessageBox.TYPE_YESNO
        )
        self["status"].setText("Gotowy.")

def main(session, **kwargs):
    session.open(PoterXScreen)

def AutoStart(reason, **kwargs): 
    if reason == 0: send_tracking_ping()

def Plugins(**kwargs):
    return [
        PluginDescriptor(name="PoterX Downloader", description="Prosty Panel IPTV", where=PluginDescriptor.WHERE_PLUGINMENU, icon="plugin.png", fnc=main),
        PluginDescriptor(where=PluginDescriptor.WHERE_AUTOSTART, fnc=AutoStart)
    ]
