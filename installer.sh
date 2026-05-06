#!/bin/sh
# PoterX Downloader – Instalator dla Enigma2
# Wymaga OpenATV 6.4+ lub odpowiednika (Python3)

PLUGIN_NAME="PoterX Downloader"
PLUGIN_DIR="/usr/lib/enigma2/python/Plugins/Extensions/PoterXDownloader"
REPO_ZIP_URL="https://github.com/zdunas82/IPTV_Importer/archive/refs/heads/main.zip"
TMP_ZIP="/tmp/poterx_install.zip"
TMP_EXTRACT="/tmp/poterx_extract"

echo ""
echo "============================================="
echo "  $PLUGIN_NAME - Instalator"
echo "============================================="
echo ""

# Sprawdz Python3
if ! command -v python3 >/dev/null 2>&1; then
    echo "[BLAD] Python3 nie jest dostepny."
    echo "       Wymagany OpenATV 6.4+ lub nowszy."
    exit 1
fi
echo "[OK] Python3 dostepny: $(python3 --version 2>&1)"

# Pobierz archiwum
echo ""
echo "[INFO] Pobieranie wtyczki..."

DL_OK=0
if command -v wget >/dev/null 2>&1; then
    wget --no-check-certificate -q -O "$TMP_ZIP" "$REPO_ZIP_URL" && DL_OK=1
fi
if [ "$DL_OK" -eq 0 ] && command -v curl >/dev/null 2>&1; then
    curl -k -L -s -o "$TMP_ZIP" "$REPO_ZIP_URL" && DL_OK=1
fi

if [ "$DL_OK" -eq 0 ] || [ ! -f "$TMP_ZIP" ] || [ ! -s "$TMP_ZIP" ]; then
    echo "[BLAD] Nie udalo sie pobrac archiwum."
    echo "       Sprawdz polaczenie z internetem."
    exit 1
fi
echo "[OK] Archiwum pobrane."

# Wypakuj
echo "[INFO] Rozpakowywanie..."
rm -rf "$TMP_EXTRACT"
mkdir -p "$TMP_EXTRACT"

if command -v unzip >/dev/null 2>&1; then
    unzip -q "$TMP_ZIP" -d "$TMP_EXTRACT" 2>/dev/null
else
    echo "[BLAD] Brak narzedzia 'unzip'. Zainstaluj: opkg install unzip"
    rm -f "$TMP_ZIP"
    exit 1
fi

# Znajdz katalog z plugin.py w archiwum
SRC_DIR=$(find "$TMP_EXTRACT" -name "plugin.py" 2>/dev/null | head -1 | xargs dirname 2>/dev/null)

if [ -z "$SRC_DIR" ] || [ ! -d "$SRC_DIR" ]; then
    echo "[BLAD] Nie znaleziono plugin.py w archiwum."
    rm -f "$TMP_ZIP"
    rm -rf "$TMP_EXTRACT"
    exit 1
fi

# Usun poprzednia instalacje
echo "[INFO] Usuwanie poprzedniej wersji..."
rm -rf "$PLUGIN_DIR"
mkdir -p "$PLUGIN_DIR"

# Kopiuj pliki
echo "[INFO] Instalowanie plikow..."
cp -r "$SRC_DIR"/. "$PLUGIN_DIR/"

# Ustaw uprawnienia
chmod -R 755 "$PLUGIN_DIR"

# Sprzatanie
rm -f "$TMP_ZIP"
rm -rf "$TMP_EXTRACT"

echo ""
echo "============================================="
echo "  [OK] Instalacja zakonczona!"
echo "  Katalog: $PLUGIN_DIR"
echo ""
echo "  Zrestartuj GUI Enigmy:"
echo "  Menu -> Informacje -> Uruchom ponownie GUI"
echo "============================================="
echo ""
