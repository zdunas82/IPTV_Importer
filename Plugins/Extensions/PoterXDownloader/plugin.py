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

# --- WERSJA WTYCZKI ---
VERSION = "3.5.2"

# --- ADRESY ---
UPDATE_BASE_URL = "http://poterx.me/update"
PICONS_URL = UPDATE_BASE_URL + "/picons.tar.gz"
TRACKER_URL = "http://poterx.me/tracker.php"

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

def _normalize_name(s):
    s = (s or "").strip().lower()
    s = s.replace("hd", "")
    s = re.sub(r"\s+", " ", s).strip()
    return s

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
    # Prefer bouquets.tv entries, fallback to filesystem scan.
    base = "/etc/enigma2"
    idx = os.path.join(base, "bouquets.tv")
    out = []
    seen = set()
    try:
        if os.path.exists(idx):
            with open(idx, "r") as f:
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
    except Exception:
        pass
    if out:
        return out
    try:
        for fn in sorted(os.listdir(base)):
            if fn.startswith("userbouquet.") and fn.endswith(".tv"):
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
config.plugins.poterx.password = ConfigText(default="", fixed_size=False)
config.plugins.poterx.auto_update = ConfigYesNo(default=False)
config.plugins.poterx.auto_update_time = ConfigClock(default=14400) # 04:00

# Niebieski przycisk: wybór akcji
config.plugins.poterx.blue_action = ConfigSelection(
    choices=[
        ("update", "Sprawdz aktualizacje wtyczki"),
        ("bzyk", "Podmien moje IPTV w liscie Bzyk83"),
    ],
    default="update",
)

# Podmiana Bzyk83 (domyslne wartosci jak w Twoim skrypcie)
config.plugins.poterx.bzyk_source_bouquet = ConfigSelection(
    choices=[("", "Auto (wybierz pozniej)")],
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
        target_name = "#NAME CANAL+ | PoterX"
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

# --- GLOWNY EKRAN ---
class PoterXScreen(ConfigListScreen, Screen):
    _DESKTOP_W = 720
    try:
        _DESKTOP_W = int(getDesktop(0).size().width())
    except Exception:
        _DESKTOP_W = 720

        if _DESKTOP_W >= 1280:
            skin = """
            <screen position="center,center" size="1100,660" title="PoterX Downloader">
            <eLabel position="0,0" size="1100,70" backgroundColor="#202020" />
            <widget name="header" position="24,14" size="1050,40" font="Regular;34" foregroundColor="#ffffff" transparent="1" />

            <widget name="config" position="24,90" size="1052,400" scrollbarMode="showOnDemand" />
            <widget name="help" position="24,498" size="1052,30" font="Regular;20" foregroundColor="#cfcfcf" transparent="1" />
            <eLabel position="24,532" size="1052,2" backgroundColor="#404040" />
            <widget name="status" position="24,536" size="1052,54" font="Regular;24" halign="center" valign="center" />

            <eLabel position="0,600" size="1100,60" backgroundColor="#101010" />
                <eLabel position="24,610" size="250,40" backgroundColor="#9f1313" />
                <eLabel position="300,610" size="250,40" backgroundColor="#1f771f" />
                <eLabel position="576,610" size="250,40" backgroundColor="#dbbf00" />
                <eLabel position="852,610" size="224,40" backgroundColor="#003a88" />
                <widget name="key_red" position="24,610" size="250,40" font="Regular;24" foregroundColor="#ffffff" halign="center" valign="center" zPosition="5" transparent="1" />
                <widget name="key_green" position="300,610" size="250,40" font="Regular;24" foregroundColor="#ffffff" halign="center" valign="center" zPosition="5" transparent="1" />
                <widget name="key_yellow" position="576,610" size="250,40" font="Regular;24" foregroundColor="#000000" halign="center" valign="center" zPosition="5" transparent="1" />
                <widget name="key_blue" position="852,610" size="224,40" font="Regular;24" foregroundColor="#ffffff" halign="center" valign="center" zPosition="5" transparent="1" />
            </screen>"""
        else:
            skin = """
            <screen position="center,center" size="660,460" title="PoterX Downloader">
            <eLabel position="0,0" size="660,54" backgroundColor="#202020" />
            <widget name="header" position="18,10" size="624,32" font="Regular;26" foregroundColor="#ffffff" transparent="1" />

            <widget name="config" position="18,68" size="624,250" scrollbarMode="showOnDemand" />
            <widget name="help" position="18,322" size="624,24" font="Regular;18" foregroundColor="#cfcfcf" transparent="1" />
            <eLabel position="18,350" size="624,2" backgroundColor="#404040" />
            <widget name="status" position="18,356" size="624,44" font="Regular;20" halign="center" valign="center" />

            <eLabel position="0,410" size="660,50" backgroundColor="#101010" />
                <eLabel position="18,418" size="150,30" backgroundColor="#9f1313" />
                <eLabel position="182,418" size="170,30" backgroundColor="#1f771f" />
                <eLabel position="366,418" size="140,30" backgroundColor="#dbbf00" />
                <eLabel position="520,418" size="122,30" backgroundColor="#003a88" />
                <widget name="key_red" position="18,418" size="150,30" font="Regular;18" foregroundColor="#ffffff" halign="center" valign="center" zPosition="5" transparent="1" />
                <widget name="key_green" position="182,418" size="170,30" font="Regular;18" foregroundColor="#ffffff" halign="center" valign="center" zPosition="5" transparent="1" />
                <widget name="key_yellow" position="366,418" size="140,30" font="Regular;18" foregroundColor="#000000" halign="center" valign="center" zPosition="5" transparent="1" />
                <widget name="key_blue" position="520,418" size="122,30" font="Regular;18" foregroundColor="#ffffff" halign="center" valign="center" zPosition="5" transparent="1" />
            </screen>"""

    def __init__(self, session):
        Screen.__init__(self, session)
        self.session = session
        self.list = []

        self._refresh_bouquet_choices()
        
        self.list.append(getConfigListEntry("--- Konto IPTV ---", ConfigNothing()))
        self.list.append(getConfigListEntry("Uzytkownik", config.plugins.poterx.username))
        self.list.append(getConfigListEntry("Haslo", config.plugins.poterx.password))
        self.list.append(getConfigListEntry("Auto aktualizacja", config.plugins.poterx.auto_update))
        self.list.append(getConfigListEntry("Godzina auto", config.plugins.poterx.auto_update_time))
        self.list.append(getConfigListEntry("Niebieski przycisk", config.plugins.poterx.blue_action))

        self.list.append(getConfigListEntry("--- CANAL+ w liscie Bzyk83 ---", ConfigNothing()))
        self.list.append(getConfigListEntry("Zrodlo (lista)", config.plugins.poterx.bzyk_source_bouquet))
        self.list.append(getConfigListEntry("Zrodlo (sciezka, opcjonalnie)", config.plugins.poterx.bzyk_source_path))
        self.list.append(getConfigListEntry("Tryb", config.plugins.poterx.bzyk_target_mode))
        self.list.append(getConfigListEntry("Tytul (nowa lista)", config.plugins.poterx.bzyk_custom_title))
        self.list.append(getConfigListEntry("Plik (nowa lista)", config.plugins.poterx.bzyk_custom_bouquet))
        self.list.append(getConfigListEntry("Wstaw na 1 miejscu", config.plugins.poterx.bzyk_insert_first))

        self.list.append(getConfigListEntry("--- Dodatkowa lista IPTV ---", ConfigNothing()))
        self.list.append(getConfigListEntry("Utworz liste z reszta", config.plugins.poterx.bzyk_extra_enable))
        self.list.append(getConfigListEntry("Tytul (reszta)", config.plugins.poterx.bzyk_extra_title))
        self.list.append(getConfigListEntry("Plik (reszta)", config.plugins.poterx.bzyk_extra_bouquet))
        
        ConfigListScreen.__init__(self, self.list, session=self.session)
            header = "PoterX Downloader v%s" % VERSION
            self.setTitle(header)  # title bar (skin-independent)
            self["header"] = Label(header)
            self["status"] = Label("Gotowy.")
            self["help"] = Label("")

            # Opisy w kolorowych polach (w praktyce: najbardziej kompatybilne na image/skinach).
            self["key_red"] = Button("CZERWONY: Wyjscie")
            self["key_green"] = Button("ZIELONY: Pobierz")
            self["key_yellow"] = Button("ZOLTY: Picony")
            self["key_blue"] = Button("NIEBIESKI: Akcja")
            self._refresh_key_labels()
        
        self["setupActions"] = ActionMap(["SetupActions", "ColorActions"], {
            "green": self.download_direct,
            "red": self.cancel,
            "cancel": self.cancel,
            "blue": self.blue_action,
            "yellow": self.ask_picons,
            "ok": self.save,
        }, -2)
        
            self.onLayoutFinish.append(self.auto_check_update)
            try:
                self["config"].onSelectionChanged.append(self._on_selection_changed)
            except Exception:
                pass
            self.onLayoutFinish.append(self._on_selection_changed)

        def _refresh_key_labels(self):
            try:
                action = config.plugins.poterx.blue_action.value
            except Exception:
                action = "update"
            if action == "bzyk":
                self["key_blue"].setText("NIEBIESKI: Podmiana")
            else:
                self["key_blue"].setText("NIEBIESKI: Update")

    def _on_selection_changed(self):
        # Proste podpowiedzi - bez "slopa", zeby UI bylo czytelne na roznych image.
        try:
            cur = self["config"].getCurrent()
            label = (cur[0] or "") if cur else ""
        except Exception:
            label = ""

        help_txt = ""
        if "Uzytkownik" in label or "Haslo" in label:
            help_txt = "Dane do logowania IPTV (Xtream)."
        elif "Auto aktualizacja" in label or "Godzina auto" in label:
            help_txt = "Automatyczne odswiezanie listy i restart GUI o wybranej godzinie."
        elif "Niebieski przycisk" in label:
            if config.plugins.poterx.blue_action.value == "bzyk":
                help_txt = "Niebieski: podmienia CANAL+ w liscie Bzyk83."
            else:
                help_txt = "Niebieski: sprawdza aktualizacje wtyczki."
        elif "Zrodlo (lista)" in label or "Zrodlo (sciezka" in label:
            help_txt = "Wybierz bukiet Bzyk83. Jesli lista pusta, wpisz recznie sciezke z /etc/enigma2."
        elif label == "Tryb":
            help_txt = "Copy: tworzy nowa liste. Inplace: podmienia w oryginalnej liscie (robi backup)."
        elif "Tytul (nowa lista)" in label or "Plik (nowa lista)" in label:
            help_txt = "Dotyczy tylko trybu Copy (nowa lista)."
            elif "Utworz liste z reszta" in label:
                help_txt = "Dodatkowy bukiet z pozostalymi kanalami IPTV (bez CANAL+ z mapowania)."
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
        self["status"].setText("Łączenie...")
        try:
            req = Request("{}/version.txt".format(UPDATE_BASE_URL))
            req.add_header('User-Agent', 'Enigma2-PoterX')
            new_version = to_str(urlopen(req, timeout=10).read()).strip()
            if _parse_version(new_version) > _parse_version(VERSION):
                self.session.openWithCallback(self.do_update, MessageBox, "Nowa wersja: %s\nAktualizować?" % new_version, MessageBox.TYPE_YESNO)
            else:
                self.session.open(MessageBox, "Wersja aktualna.", MessageBox.TYPE_INFO)
                self.check_account_info()
        except Exception as e:
            self.session.open(MessageBox, "Błąd: " + str(e), MessageBox.TYPE_ERROR)

    def blue_action(self):
        action = config.plugins.poterx.blue_action.value
        if action == "bzyk":
            self.run_bzyk_replace()
        else:
            self.manual_check_update()

    def _build_m3u_url(self):
        host = _sanitize_host(config.plugins.poterx.host.value)
        user = config.plugins.poterx.username.value
        password = config.plugins.poterx.password.value
        return "{}/get.php?username={}&password={}&type=m3u&output=ts".format(host, user, password)

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

    def _write_extra_iptv_bouquet(self, dst_path, title, entries, used_norm_names):
        # Create a separate IPTV bouquet with the remaining channels.
        # Hard cap to avoid huge bouquets on weaker boxes.
        limit = 2000

        out = ["#NAME %s" % ((title or "").strip() or "IPTV - Pozostale")]
        count = 0
        for e in entries:
            if e.get("norm") in used_norm_names:
                continue
            url = e.get("url") or ""
            name = e.get("name") or ""
            if not url or not name:
                continue
            enc = _encode_url_minimal(url)
            out.append("#SERVICE 4097:0:1:0:0:0:0:0:0:0:%s:%s" % (enc, name))
            out.append("#DESCRIPTION %s" % name)
            count += 1
            if count >= limit:
                break

        with open(dst_path, "w") as f:
            f.write("\n".join(out) + "\n")

        return count

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

        url = self._build_m3u_url()
        self["status"].setText("Pobieranie M3U...")
        try:
            req = Request(url)
            req.add_header("User-Agent", "Enigma2-PoterX")
            content = to_str(urlopen(req, timeout=45).read())
        except Exception as e:
            self.session.open(MessageBox, "Blad pobierania M3U: %s" % str(e), MessageBox.TYPE_ERROR)
            self["status"].setText("Blad M3U.")
            return

        m3u_map, m3u_entries = self._parse_m3u(content)
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
                extra_count = self._write_extra_iptv_bouquet(extra_path, extra_title, m3u_entries, used)
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

        self["status"].setText("Gotowy.")
        extra_msg = ""
        if extra_fn and extra_count > 0:
            extra_msg = "\nDodatkowy bouquet: %s (%d kanalow)" % (extra_fn, extra_count)
        bkp_msg = ""
        if mode == "inplace" and bkp:
            bkp_msg = "\nBackup: %s" % os.path.basename(bkp)
        self.session.open(
            MessageBox,
            "Zrobione.\nCel: %s\nPodmieniono kanalow: %d%s%s" % (dst_fn, replaced, extra_msg, bkp_msg),
            MessageBox.TYPE_INFO,
        )

    def do_update(self, confirm):
        if not confirm: return
        self["status"].setText("Pobieranie...")
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
        quitMainloop(3)

    def ask_picons(self):
        self.session.openWithCallback(self.do_picons_download, MessageBox, 
            "Pobrać picony do: %s?" % TARGET_PICON_PATH, MessageBox.TYPE_YESNO)

    def do_picons_download(self, confirm):
        if not confirm: return
        self["status"].setText("Pobieranie picons...")
        tmp_file = "/tmp/picons.tar.gz"
        try:
            req = Request(PICONS_URL)
            req.add_header('User-Agent', 'Enigma2-PoterX')
            response = urlopen(req, timeout=120)
            with open(tmp_file, "wb") as f:
                while True:
                    chunk = response.read(8192)
                    if not chunk: break
                    f.write(chunk)
            
            if not os.path.exists(TARGET_PICON_PATH):
                try: os.makedirs(TARGET_PICON_PATH)
                except: return

            self["status"].setText("Rozpakowywanie...")
            if not tarfile.is_tarfile(tmp_file):
                raise Exception("Błąd archiwum TAR")

            # --- POPRAWKA: PŁASKIE WYPAKOWYWANIE (IGNORUJE FOLDER PICONS) ---
            with tarfile.open(tmp_file, "r:gz") as tar:
                members = []
                for member in tar.getmembers():
                    if member.isfile():
                        # Usuwamy sciezke (np. picons/1_0_1...) zostawiajac sama nazwe pliku
                        member.name = os.path.basename(member.name)
                        members.append(member)
                tar.extractall(path=TARGET_PICON_PATH, members=members)
            # ----------------------------------------------------------------

            if os.path.exists(tmp_file): os.remove(tmp_file)
            
            # Picon Linker (Dla bezpieczenstwa)
            try:
                for filename in os.listdir(TARGET_PICON_PATH):
                    if filename.startswith("1_0_1_"):
                        new_name = filename.replace("1_0_", "4097_0_", 1)
                        if not os.path.exists(os.path.join(TARGET_PICON_PATH, new_name)):
                            os.symlink(os.path.join(TARGET_PICON_PATH, filename), os.path.join(TARGET_PICON_PATH, new_name))
            except: pass

            self.session.openWithCallback(self.restart_gui, MessageBox, "Picony pobrane! Restart GUI wymagany.", MessageBox.TYPE_INFO)
            self["status"].setText("Picony OK.")
        except Exception as e:
            self.session.open(MessageBox, "Błąd picon: " + str(e), MessageBox.TYPE_ERROR)
            self["status"].setText("Błąd.")

    def download_direct(self):
        self["status"].setText("Pobieranie listy...")
        for x in self["config"].list: x[1].save()
        config.save()
        
        if perform_playlist_update(silent=False, session=self.session):
            self.check_account_info()
            # TUTAJ ZAPYTANIE O RESTART
            self.session.openWithCallback(self.restart_gui, MessageBox, "Lista pobrana pomyślnie!\nZrestartować GUI?", MessageBox.TYPE_YESNO)
            self["status"].setText("Gotowy.")
        else:
            self["status"].setText("Błąd pobierania.")

def main(session, **kwargs):
    session.open(PoterXScreen)

def AutoStart(reason, **kwargs): 
    if reason == 0: send_tracking_ping()

def Plugins(**kwargs):
    return [
        PluginDescriptor(name="PoterX Downloader", description="Prosty Panel IPTV", where=PluginDescriptor.WHERE_PLUGINMENU, icon="plugin.png", fnc=main),
        PluginDescriptor(where=PluginDescriptor.WHERE_AUTOSTART, fnc=AutoStart)
    ]
