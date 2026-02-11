
from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from urllib.parse import unquote, urljoin, urlparse

os.environ.setdefault("QT_OPENGL", "software")
os.environ["QSG_RHI_BACKEND"] = "opengl"
os.environ.setdefault("QT_ANGLE_PLATFORM", "swiftshader")
os.environ.setdefault(
    "QTWEBENGINE_CHROMIUM_FLAGS",
    "--disable-gpu --disable-gpu-compositing --disable-gpu-rasterization "
    "--use-angle=swiftshader --disable-features=Vulkan,UseSkiaRenderer --enable-logging=stderr --log-level=3"
)
os.environ.setdefault("QT_LOGGING_RULES", "qt.webenginecontext.warning=false;qt.webenginecontext.info=false")

# Network backend
try:
    from curl_cffi import requests as cf_requests
except Exception:
    print("FATAL: Missing dependency. Install with: pip install curl-cffi")
    sys.exit(1)

try:
    from playwright.sync_api import sync_playwright, TimeoutError as PWTimeoutError
except Exception:
    print("FATAL: Missing dependency. Install with:")
    print("  pip install playwright")
    print("  playwright install chromium")
    sys.exit(1)

from bs4 import BeautifulSoup

from PySide6.QtCore import QObject, QThread, Qt, Signal, QTimer, QUrl, QSize, QPointF, QCoreApplication
from PySide6.QtGui import QColor, QPainter, QLinearGradient, QRadialGradient, QFont, QIcon, QPixmap
from PySide6.QtWidgets import (
    QApplication,
    QDialog,
    QFrame,
    QGraphicsDropShadowEffect,
    QHBoxLayout,
    QLabel,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QProgressBar,
    QTextEdit,
    QVBoxLayout,
    QWidget,
)

try:
    from PySide6.QtWebEngineWidgets import QWebEngineView
    WEBENGINE_AVAILABLE = True
except Exception:
    WEBENGINE_AVAILABLE = False
    QWebEngineView = None

SEED_URL = "https://jmail.world/drive"

FOLDER_MIN = 1
FOLDER_MAX = 12
REVERSE_ORDER = True
WORKER_ID = ""
FILES_DIR_NAME = "files_rev"
STATE_FILE_NAME = "jdrive_download_state_rev.json"
MANIFEST_FILE_NAME = "manifest_rev.jsonl"
ROOT_URL = f"https://jmail.world/drive/folder/doj/vol{FOLDER_MAX}"


def _bool_env(name: str, default: bool = False) -> bool:
    v = os.getenv(name)
    if v is None:
        return default
    return str(v).strip().lower() in {"1", "true", "yes", "y", "on"}


def _sanitize_worker_id(raw: str) -> str:
    val = re.sub(r"[^a-zA-Z0-9_-]+", "", (raw or "").strip())
    return val[:48]


def apply_runtime_config_from_args() -> None:
    """Apply config from CLI/env before UI starts.

    Examples:
      python download_Epstein_files_Mirror.py
      python download_Epstein_files_Mirror.py --worker-id B --start-vol 7 --end-vol 12
    """
    global FOLDER_MIN, FOLDER_MAX, REVERSE_ORDER, WORKER_ID
    global FILES_DIR_NAME, STATE_FILE_NAME, MANIFEST_FILE_NAME, ROOT_URL

    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--worker-id", default=os.getenv("JD_WORKER_ID", ""))
    # Mirror variant: aqui corre do volN -> vol1
    parser.add_argument("--reverse", action="store_true", default=True)
    parser.add_argument("--start-vol", type=int, default=int(os.getenv("JD_START_VOL", "1")))
    parser.add_argument("--end-vol", type=int, default=int(os.getenv("JD_END_VOL", "12")))
    parser.add_argument("--state-file", default=os.getenv("JD_STATE_FILE", "").strip())
    parser.add_argument("--manifest-file", default=os.getenv("JD_MANIFEST_FILE", "").strip())
    parser.add_argument("--files-dir", default=os.getenv("JD_FILES_DIR", "").strip())

    args, remaining = parser.parse_known_args(sys.argv[1:])
    sys.argv = [sys.argv[0], *remaining]

    start = int(args.start_vol)
    end = int(args.end_vol)
    start = max(1, min(9999, start))
    end = max(1, min(9999, end))
    lo, hi = (start, end) if start <= end else (end, start)

    FOLDER_MIN = lo
    FOLDER_MAX = hi
    REVERSE_ORDER = True

    WORKER_ID = _sanitize_worker_id(args.worker_id)
    suffix = f"_{WORKER_ID}" if WORKER_ID else "_rev"

    default_files_dir = f"files{suffix}"
    default_state = f"jdrive_download_state{suffix}.json"
    default_manifest = f"manifest{suffix}.jsonl"

    FILES_DIR_NAME = args.files_dir or default_files_dir
    STATE_FILE_NAME = args.state_file or default_state
    MANIFEST_FILE_NAME = args.manifest_file or default_manifest

    anchor_vol = FOLDER_MAX
    ROOT_URL = f"https://jmail.world/drive/folder/doj/vol{anchor_vol}"


def folder_span_label() -> str:
    if REVERSE_ORDER:
        return f"vol{FOLDER_MAX}..vol{FOLDER_MIN} (reverse)"
    return f"vol{FOLDER_MIN}..vol{FOLDER_MAX}"

NO_PROGRESS_SCROLL_LIMIT = 500
MAX_SCROLLS = 100000
PAGE_RETRIES = 3
FILE_RETRIES = 3

try:
    MAX_CONSECUTIVE_ITEM_FAILURES = max(1, int(os.getenv("JD_MAX_CONSEC_FAILS", "20")))
except Exception:
    MAX_CONSECUTIVE_ITEM_FAILURES = 20

ENABLE_GENERIC_TOKEN_EXPANSION = _bool_env("JD_ENABLE_GENERIC_TOKEN_EXPANSION", True)

PAGE_SLEEP_RANGE = (0.20, 0.55)
FILE_SLEEP_RANGE = (0.10, 0.28)

# Padrões de páginas de documento JDrive.
# Variantes /drive/vol00012-xxxx-pdf e também /drive/001-pdf.
DOC_SLUG_RE = re.compile(r"(?:vol\d{1,6}-)?[a-z0-9][a-z0-9_\-]{0,220}-pdf", re.I)
ABS_DOC_RE = re.compile(r"https?://[^\"' ]+/drive/(?:vol\d{1,6}-)?[a-z0-9][a-z0-9_\-]{0,220}-pdf", re.I)
DOC_PATH_RE = re.compile(r"/drive/(?:vol\d{1,6}-)?[a-z0-9][a-z0-9_\-]{0,220}-pdf", re.I)
# URLs PDF diretos (com ou sem querystring)
ABS_PDF_RE = re.compile(r"https?://[^\"'\s]+?\.pdf(?:\?[^\"'\s]*)?", re.I)
REL_PDF_TOKEN_RE = re.compile(r"(?<![a-z0-9_\-])(?:[a-z]{2,16}\d[a-z0-9_\-]{0,240}|(?:doj|court|file)[a-z0-9_\-]{0,240})\.pdf(?![a-z0-9_\-])", re.I)
GENERIC_PDF_TOKEN_RE = re.compile(r"(?<![a-z0-9_\-])([a-z0-9][a-z0-9_\-]{0,220})\.pdf(?![a-z0-9_\-])", re.I)
PDF_URL_RE = re.compile(r"\.pdf($|\?)", re.I)

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:126.0) Gecko/20100101 Firefox/126.0",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
]


def build_folder_urls() -> List[str]:
    if REVERSE_ORDER:
        seq = range(FOLDER_MAX, FOLDER_MIN - 1, -1)
    else:
        seq = range(FOLDER_MIN, FOLDER_MAX + 1)
    return [f"https://jmail.world/drive/folder/doj/vol{i}" for i in seq]


def extract_volume_name(url: str, fallback_idx: int = 1) -> str:
    m = re.search(r"/(vol\d+)(?:/)?$", str(url).strip(), re.I)
    if m:
        return m.group(1).lower()
    return f"vol{max(1, int(fallback_idx))}"


def runtime_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def files_dir() -> Path:
    base = Path(FILES_DIR_NAME)
    d = base if base.is_absolute() else (runtime_dir() / base)
    d.mkdir(parents=True, exist_ok=True)
    return d


def state_file() -> Path:
    p = Path(STATE_FILE_NAME)
    return p if p.is_absolute() else (runtime_dir() / p)


def manifest_file() -> Path:
    p = Path(MANIFEST_FILE_NAME)
    return p if p.is_absolute() else (files_dir() / p)


def resource_path(name: str) -> Path:
    if getattr(sys, "frozen", False):
        base = Path(getattr(sys, "_MEIPASS", runtime_dir()))
    else:
        base = runtime_dir()
    return base / name


def pick_existing_resource(*names: str) -> Optional[Path]:
    for n in names:
        p = resource_path(n)
        if p.exists():
            return p
    return None


def normalize_url(url: str) -> str:
    p = urlparse(url)
    return f"{p.scheme}://{p.netloc}{p.path}"


def sanitize_filename(name: str) -> str:
    name = re.sub(r'[<>:"/\\|?*]+', "_", name).strip(" .")
    return name or "document.pdf"


def safe_filename_from_url(url: str) -> str:
    parsed = urlparse(url)
    raw_name = unquote(Path(parsed.path).name.strip())
    if not raw_name:
        raw_name = f"file_{hashlib.md5(url.encode('utf-8')).hexdigest()[:12]}.pdf"
    raw_name = sanitize_filename(raw_name)
    if not raw_name.lower().endswith(".pdf"):
        raw_name += ".pdf"
    return raw_name


def code_from_doc_url(doc_url: str) -> Optional[str]:
    slug = doc_url.rstrip("/").split("/")[-1]
    m = re.match(r"vol\d{1,6}-([a-z0-9_\-]+)-pdf$", slug, re.I)
    if not m:
        return None
    return f"{m.group(1).upper()}.pdf"


def load_state() -> Optional[dict]:
    p = state_file()
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return None


def save_state(data: dict) -> None:
    p = state_file()
    tmp = p.with_suffix(p.suffix + ".tmp")
    try:
        tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(p)
    except Exception:
        pass


def clear_state() -> None:
    p = state_file()
    try:
        if p.exists():
            p.unlink()
    except Exception:
        pass


def append_manifest_row(row: dict) -> None:
    p = manifest_file()
    try:
        with p.open("a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
    except Exception:
        pass


def extract_candidates_from_text_blob(text: str, base_url: str) -> Tuple[Set[str], Set[str]]:
    doc_urls: Set[str] = set()
    pdf_urls: Set[str] = set()
    if not text:
        return doc_urls, pdf_urls

    # 1) URLs absolutas... páginas de documento... de PDF
    for u in ABS_DOC_RE.findall(text):
        doc_urls.add(normalize_url(u))
    for u in ABS_PDF_RE.findall(text):
        pdf_urls.add(u)

    # 2) Caiminhos relativos /drive/...-pdf
    for rel in DOC_PATH_RE.findall(text):
        doc_urls.add(normalize_url(urljoin(base_url, rel)))

    # 3) Slugs soltos eventualmente ...-pdf sem /drive
    for slug in DOC_SLUG_RE.findall(text):
        doc_urls.add(normalize_url(urljoin(base_url, f"/drive/{slug}")))

    # 4) Tokens de ficheiros PDF que às vezes aparecem no JSON sem URL completa
    for tok in REL_PDF_TOKEN_RE.findall(text):
        cand = urljoin(base_url, f"/{tok}")
        pdf_urls.add(cand)

    # 5) Tokens *.pdf sem URL completa.
    #    Mantemos esta expansão ativa por omissão, mas com filtro anti-lixo
    #    para não inflacionar com nomes de assets JS/CSS.
    if ENABLE_GENERIC_TOKEN_EXPANSION:
        for stem in GENERIC_PDF_TOKEN_RE.findall(text):
            if not stem:
                continue
            if not looks_likely_document_stem(stem):
                continue
            tok = f"{stem}.pdf"
            pdf_urls.add(urljoin(base_url, f"/{tok}"))
            doc_urls.add(normalize_url(urljoin(base_url, f"/drive/{stem}-pdf")))

    return doc_urls, pdf_urls


def extract_candidates_from_html(html: str, base_url: str) -> Tuple[Set[str], Set[str]]:
    soup = BeautifulSoup(html, "html.parser")
    doc_urls: Set[str] = set()
    pdf_urls: Set[str] = set()

    attrs = ("href", "src", "data", "data-href", "data-url")
    for el in soup.find_all(True):
        for a in attrs:
            v = el.get(a)
            if not v:
                continue
            u = urljoin(base_url, v)
            if "/drive/" in u and DOC_SLUG_RE.search(u):
                doc_urls.add(normalize_url(u))
            if PDF_URL_RE.search(u):
                pdf_urls.add(u)

    d2, p2 = extract_candidates_from_text_blob(html, base_url)
    doc_urls |= d2
    pdf_urls |= p2

    for sc in soup.find_all("script"):
        t = sc.string or sc.get_text(" ", strip=False) or ""
        if not t:
            continue
        d3, p3 = extract_candidates_from_text_blob(t, base_url)
        doc_urls |= d3
        pdf_urls |= p3

    return doc_urls, pdf_urls


def looks_blocked(text: str) -> bool:
    t = (text or "").lower()
    markers = [
        "captcha",
        "verify you are human",
        "access denied",
        "cloudflare",
        "forbidden",
        "request blocked",
        "please sign in",
        "login required",
    ]
    return any(m in t for m in markers)


_ASSET_WORD_HINTS = {
    "bootstrap", "jquery", "react", "vue", "angular", "polyfill", "polyfills",
    "runtime", "vendor", "bundle", "chunk", "webpack", "favicon", "font", "icons",
    "style", "styles", "theme", "script", "analytics", "tracking", "pixel", "logo",
    "image", "sprite", "manifest", "serviceworker", "sw", "worker", "hot-update",
}


def looks_likely_document_stem(stem: str) -> bool:
    s = (stem or "").strip().lower().strip("._-")
    if len(s) < 3:
        return False

    # Fortes sinais de documento real
    if re.search(r"\d{3,}", s):
        return True
    if re.match(r"(?:doj|court|file|efta|usao|fbi|irs|sec|case|exhibit|evidence|vol)", s):
        return True
    if re.search(r"\d", s) and len(s) >= 5:
        return True

    # Sem dígitos + palavra típica de asset web => lixo
    if not re.search(r"\d", s):
        if any(w in s for w in _ASSET_WORD_HINTS):
            return False
        # tokens alfabéticos curtos raramente são PDFs de evidência
        if re.fullmatch(r"[a-z]{1,5}", s):
            return False

    # fallback conservador
    return len(s) >= 8 and not any(w in s for w in _ASSET_WORD_HINTS)


def file_name_from_headers_or_url(resp, fallback: str) -> str:
    cd = (resp.headers.get("content-disposition") or "")
    if "filename=" in cd.lower():
        part = cd.split("filename=", 1)[1].strip().strip('"').strip("'")
        name = sanitize_filename(part)
        if name:
            return name

    name = Path(urlparse(resp.url).path).name
    if name:
        name = sanitize_filename(name)
        if name:
            return name
    return sanitize_filename(fallback)


class SharedCookieStore:
    """Thread-safe cookie snapshot from QWebEngine cookie store."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._cookies: Dict[Tuple[str, str, str], dict] = {}

    def set_all(self, cookies: List[dict]) -> None:
        with self._lock:
            self._cookies.clear()
            for c in cookies or []:
                name = c.get("name", "")
                domain = c.get("domain", "")
                path = c.get("path", "/")
                if not name:
                    continue
                self._cookies[(name, domain, path)] = dict(c)

    def merge(self, cookies: List[dict]) -> int:
        added = 0
        with self._lock:
            for c in cookies or []:
                name = c.get("name", "")
                domain = c.get("domain", "")
                path = c.get("path", "/")
                if not name:
                    continue
                key = (name, domain, path)
                prev = self._cookies.get(key)
                if prev != c:
                    self._cookies[key] = dict(c)
                    added += 1
        return added

    def get_all(self) -> List[dict]:
        with self._lock:
            return [dict(v) for v in self._cookies.values()]

    def count(self) -> int:
        with self._lock:
            return len(self._cookies)


@dataclass
class DownloadResult:
    ok: bool
    reason: str = ""
    permanent_skip: bool = False


class DownloaderWorker(QObject):
    log = Signal(str)
    progress = Signal(int, int)
    progress_total = Signal(int, int)
    volume_update = Signal(int, int, int, str, str, str)
    finished = Signal(int, int, int, str)
    auth_required = Signal(str, int, int)

    def __init__(
        self,
        output_dir: Path,
        resume_state: Optional[dict],
        cookie_store: SharedCookieStore,
        folder_urls: Optional[List[str]] = None,
    ):
        super().__init__()
        self.output_dir = output_dir
        self.resume_state = resume_state or {}
        self.folder_urls = [u for u in (folder_urls or build_folder_urls()) if str(u).strip()]
        if not self.folder_urls:
            self.folder_urls = build_folder_urls()
        self.folder_url = self.folder_urls[0]
        self.cookie_store = cookie_store
        self._stop = False

        self.session = cf_requests.Session(impersonate="chrome124")
        self.session.headers.update(
            {
                "User-Agent": random.choice(USER_AGENTS),
                "Accept-Language": "en-US,en;q=0.9,pt-PT;q=0.8",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                "Connection": "keep-alive",
                "Cache-Control": "no-cache",
            }
        )

    def request_stop(self) -> None:
        self._stop = True

    def start(self) -> None:
        self.run()

    def _checkpoint(
        self,
        status: str,
        phase: str,
        processed: Set[str],
        discovered: Set[str],
        doc_pages: List[str],
        current_index: int,
        downloaded: int,
        skipped: int,
        failed: int,
        fail_reason: str = "",
        current_folder_idx: int = 0,
    ) -> None:
        state = {
            "version": 4,
            "status": status,
            "phase": phase,
            "folder_urls": list(self.folder_urls),
            "folder_url": self.folder_url,
            "current_folder_idx": int(current_folder_idx),
            "processed": sorted(processed),
            "discovered": sorted(discovered),
            "doc_pages": list(doc_pages),
            "current_index": int(current_index),
            "downloaded": int(downloaded),
            "skipped": int(skipped),
            "failed": int(failed),
            "fail_reason": fail_reason,
            "updated_at_epoch": int(time.time()),
        }
        save_state(state)

    def _merge_cookies_into_session(self) -> int:
        merged = 0
        for c in self.cookie_store.get_all():
            name = c.get("name")
            value = c.get("value", "")
            domain = (c.get("domain") or "").lstrip(".")
            path = c.get("path", "/")
            if not name:
                continue
            if domain:
                self.session.cookies.set(name, value, domain=domain, path=path)
            else:
                self.session.cookies.set(name, value, path=path)
            merged += 1
        return merged

    def _cookies_for_playwright(self) -> List[dict]:
        out = []
        for c in self.cookie_store.get_all():
            name = c.get("name")
            value = c.get("value", "")
            domain = c.get("domain", "")
            path = c.get("path", "/")
            if not name:
                continue
            row = {"name": name, "value": value, "path": path}
            if domain:
                row["domain"] = domain
            else:
                row["url"] = self.folder_url
            out.append(row)
        return out

    def _emit_progress(self, processed_count: int, discovered_count: int, total_indexed: int) -> None:
        discovered_safe = max(1, int(discovered_count))
        self.progress.emit(int(processed_count), discovered_safe)

        total = max(1, int(total_indexed or discovered_safe))
        self.progress_total.emit(int(processed_count), total)

    def _emit_volume_update(
        self,
        current_volume_zero_based: int,
        total_volumes: int,
        percent: int,
        volume_name: str,
        state: str,
        completed_volumes_zero_based: Set[int],
    ) -> None:
        total_volumes = max(1, int(total_volumes))
        current_ui = max(1, min(total_volumes, int(current_volume_zero_based) + 1))
        pct = max(0, min(100, int(percent)))
        completed_csv = ",".join(str(i + 1) for i in sorted(completed_volumes_zero_based))
        self.volume_update.emit(current_ui, total_volumes, pct, str(volume_name), str(state), completed_csv)

    def _request_page_html(self, url: str, retries: int = PAGE_RETRIES) -> Tuple[Optional[str], str]:
        last_reason = "unknown error"
        backoff = 1.4
        for attempt in range(1, retries + 1):
            if self._stop:
                return None, "stopped by user"
            try:
                self._merge_cookies_into_session()
                resp = self.session.get(url, timeout=35, allow_redirects=True)
                code = int(resp.status_code)
                text = resp.text or ""
                try:
                    resp.close()
                except Exception:
                    pass

                if code in (401, 403):
                    last_reason = f"HTTP {code} (authorization/login likely required)"
                    self.log.emit(f"Attempt {attempt}/{retries} failed: {url} -> {last_reason}")
                    time.sleep(backoff + random.uniform(0.2, 0.8))
                    backoff *= 1.5
                    continue

                if code in (429, 500, 502, 503, 504):
                    last_reason = f"HTTP {code}"
                    self.log.emit(f"Attempt {attempt}/{retries} failed: {url} -> {last_reason}")
                    time.sleep(backoff + random.uniform(0.2, 0.8))
                    backoff *= 1.5
                    continue

                if code >= 400:
                    return None, f"HTTP {code}"

                return text, ""
            except Exception as e:
                last_reason = str(e)
                self.log.emit(f"Attempt {attempt}/{retries} failed: {url} -> {e}")
                time.sleep(backoff + random.uniform(0.2, 0.8))
                backoff *= 1.5

        return None, last_reason

    def _collect_doc_pages(self, page, discovered: Set[str], processed: Set[str], downloaded: int, skipped: int, failed: int) -> Tuple[List[str], bool]:
        self.log.emit(f"Scanning folder: {self.folder_url}")
        blocked = False
        local_items: Set[str] = set()

        try:
            page.goto(self.folder_url, wait_until="domcontentloaded", timeout=120000)
        except Exception as e:
            self.log.emit(f"Failed to open folder URL: {e}")
            return [], True

        page.wait_for_timeout(2200)

        # Captura respostas de rede (JSON/HTML/JS)... isto para dar a volta a itens não estão no DOM inicial.
        def on_response(resp):
            nonlocal blocked
            try:
                ctype = (resp.headers.get("content-type") or "").lower()
            except Exception:
                ctype = ""
            if not any(x in ctype for x in ("json", "javascript", "html", "text")):
                return
            try:
                txt = resp.text()
            except Exception:
                return
            if not txt:
                return
            if looks_blocked(txt):
                blocked = True
            d, p = extract_candidates_from_text_blob(txt, resp.url or self.folder_url)
            if d or p:
                for u in d:
                    local_items.add(u)
                    discovered.add(u)
                for u in p:
                    nu = normalize_url(u)
                    local_items.add(nu)
                    discovered.add(nu)

        try:
            page.on("response", on_response)
        except Exception:
            pass

        stagnant = 0
        for i in range(1, MAX_SCROLLS + 1):
            if self._stop:
                break

            html = ""
            try:
                html = page.content()
            except Exception:
                html = ""

            if i == 1 and looks_blocked(html):
                blocked = True

            before_local = len(local_items)
            before_global = len(discovered)

            doc_urls, pdf_urls = extract_candidates_from_html(html, page.url)
            for u in doc_urls:
                local_items.add(u)
                discovered.add(u)
            for u in pdf_urls:
                nu = normalize_url(u)
                local_items.add(nu)
                discovered.add(nu)

            try:
                body_text = page.inner_text("body")
                d4, p4 = extract_candidates_from_text_blob(body_text, page.url)
                for u in d4:
                    local_items.add(u)
                    discovered.add(u)
                for u in p4:
                    nu = normalize_url(u)
                    local_items.add(nu)
                    discovered.add(nu)
            except Exception:
                pass

            if len(local_items) == before_local and len(discovered) == before_global:
                stagnant += 1
            else:
                stagnant = 0
                self.log.emit(f"Discovery: local={len(local_items)} | global={len(discovered)} items")
                self._emit_progress(len(processed), max(len(discovered), 1), max(len(discovered), 1))
                self._checkpoint(
                    status="running",
                    phase="discover",
                    processed=processed,
                    discovered=discovered,
                    doc_pages=sorted(local_items),
                    current_index=0,
                    downloaded=downloaded,
                    skipped=skipped,
                    failed=failed,
                )

            if stagnant >= NO_PROGRESS_SCROLL_LIMIT:
                self.log.emit(f"Discovery stalled ({NO_PROGRESS_SCROLL_LIMIT} scrolls without new items).")
                break

            # Scroll robusto: contentor principal + teclado + wheel
            try:
                page.evaluate(
                    """(amt) => {
                        const root = document.scrollingElement || document.documentElement;
                        let best = root;
                        let bestScore = (root.scrollHeight || 0) - (root.clientHeight || 0);
                        const nodes = Array.from(document.querySelectorAll('*'));
                        for (const el of nodes) {
                            const sh = el.scrollHeight || 0;
                            const ch = el.clientHeight || 0;
                            const score = sh - ch;
                            if (score > bestScore + 20) {
                                best = el;
                                bestScore = score;
                            }
                        }
                        try { best.scrollBy(0, amt); } catch(e) {}
                    }""",
                    2200,
                )
            except Exception:
                pass

            try:
                page.keyboard.press("PageDown")
            except Exception:
                pass
            if i % 8 == 0:
                try:
                    page.keyboard.press("End")
                except Exception:
                    pass
            try:
                page.mouse.wheel(0, 24000)
            except Exception:
                pass

            page.wait_for_timeout(700)

        try:
            page.remove_listener("response", on_response)
        except Exception:
            pass

        return sorted(local_items), blocked


    def _resolve_pdf_url_with_page(self, page, doc_url: str) -> Tuple[Optional[str], str]:
        found_pdf: Optional[str] = None
        reason = ""

        def on_response(resp):
            nonlocal found_pdf
            if found_pdf:
                return
            try:
                ctype = (resp.headers.get("content-type") or "").lower()
            except Exception:
                ctype = ""
            ru = resp.url
            if "application/pdf" in ctype or PDF_URL_RE.search(ru):
                found_pdf = ru

        page.on("response", on_response)
        try:
            page.goto(doc_url, wait_until="domcontentloaded", timeout=120000)
            page.wait_for_timeout(2000)
        except PWTimeoutError:
            reason = "timeout while opening document page"
        except Exception as e:
            reason = str(e)

        if not found_pdf:
            try:
                html = page.content()
                _, pdf_urls = extract_candidates_from_html(html, page.url)
                if pdf_urls:
                    found_pdf = sorted(pdf_urls)[0]
            except Exception:
                pass

        if not found_pdf:
            try:
                candidates = page.evaluate(
                    """() => {
                        const out = [];
                        const sels = ['a[href]','iframe[src]','embed[src]','object[data]','source[src]','link[href]'];
                        for (const sel of sels) {
                            for (const el of document.querySelectorAll(sel)) {
                                const v = el.getAttribute('href') || el.getAttribute('src') || el.getAttribute('data');
                                if (v) out.push(new URL(v, location.origin).href);
                            }
                        }
                        return out;
                    }"""
                )
                pdf_candidates = [u for u in candidates if re.search(r"\\.pdf($|\\?)", u, re.I)]
                if pdf_candidates:
                    found_pdf = sorted(set(pdf_candidates))[0]
            except Exception:
                pass

        if not reason and not found_pdf:
            reason = "pdf_url_not_found"

        return found_pdf, reason

    def _resolve_pdf_url(self, context, doc_url: str) -> Tuple[Optional[str], List[dict], str]:
        html, reason = self._request_page_html(doc_url, retries=2)
        if html:
            _, pdf_urls = extract_candidates_from_html(html, doc_url)
            if pdf_urls:
                try:
                    cookies = context.cookies()
                except Exception:
                    cookies = []
                return sorted(pdf_urls)[0], cookies, ""

        page = context.new_page()
        try:
            pdf_url, reason2 = self._resolve_pdf_url_with_page(page, doc_url)
            try:
                cookies = context.cookies()
            except Exception:
                cookies = []
            return pdf_url, cookies, reason2 or reason
        finally:
            try:
                page.close()
            except Exception:
                pass

    def _download_pdf(self, url: str, target: Path, referer: str) -> DownloadResult:
        temp = target.with_suffix(target.suffix + ".part")
        last_reason = "unknown"

        for attempt in range(1, FILE_RETRIES + 1):
            if self._stop:
                return DownloadResult(False, "stopped by user", permanent_skip=True)

            resp = None
            try:
                self._merge_cookies_into_session()
                headers = {
                    "Referer": referer,
                    "User-Agent": random.choice(USER_AGENTS),
                    "Accept": "application/pdf,application/octet-stream;q=0.9,*/*;q=0.8",
                }
                resp = self.session.get(url, stream=True, timeout=(20, 140), headers=headers, allow_redirects=True)
                code = int(resp.status_code)

                if code in (401, 403):
                    last_reason = f"HTTP {code} (authorization/login likely required)"
                    self.log.emit(f"Attempt {attempt}/{FILE_RETRIES} failed for {url}: {last_reason}")
                    time.sleep(1.1 + attempt * 0.7 + random.uniform(0.1, 0.6))
                    continue

                if code == 404:
                    return DownloadResult(False, "HTTP 404 (file missing)", permanent_skip=True)

                if code in (429, 500, 502, 503, 504):
                    last_reason = f"HTTP {code}"
                    self.log.emit(f"Attempt {attempt}/{FILE_RETRIES} failed for {url}: {last_reason}")
                    time.sleep(1.0 + attempt * 0.7 + random.uniform(0.1, 0.6))
                    continue

                if code >= 400:
                    return DownloadResult(False, f"HTTP {code}", permanent_skip=True)

                fallback_name = target.name
                final_name = file_name_from_headers_or_url(resp, fallback_name)
                final_target = target.parent / sanitize_filename(final_name)
                if not final_target.name.lower().endswith(".pdf"):
                    final_target = final_target.with_suffix(".pdf")

                with open(temp, "wb") as f:
                    wrote = 0
                    for chunk in resp.iter_content(chunk_size=1024 * 128):
                        if self._stop:
                            return DownloadResult(False, "stopped by user", permanent_skip=True)
                        if not chunk:
                            continue
                        f.write(chunk)
                        wrote += len(chunk)

                if wrote < 256:
                    try:
                        temp.unlink(missing_ok=True)
                    except TypeError:
                        if temp.exists():
                            temp.unlink()
                    return DownloadResult(False, "downloaded file too small/invalid", permanent_skip=True)

                temp.replace(final_target)
                return DownloadResult(True, reason=str(final_target))

            except Exception as e:
                last_reason = str(e)
                self.log.emit(f"Attempt {attempt}/{FILE_RETRIES} failed for {url}: {e}")
                try:
                    if temp.exists():
                        temp.unlink()
                except Exception:
                    pass
                time.sleep(1.0 + attempt * 0.7 + random.uniform(0.1, 0.6))
            finally:
                try:
                    if resp is not None:
                        resp.close()
                except Exception:
                    pass

        return DownloadResult(False, last_reason, permanent_skip=True)

    
    def run(self) -> None:
        downloaded = int(self.resume_state.get("downloaded") or 0)
        skipped = int(self.resume_state.get("skipped") or 0)
        failed = int(self.resume_state.get("failed") or 0)

        processed: Set[str] = set(self.resume_state.get("processed") or [])
        discovered: Set[str] = set(self.resume_state.get("discovered") or [])
        doc_pages: List[str] = list(self.resume_state.get("doc_pages") or [])
        current_index = int(self.resume_state.get("current_index") or 0)
        phase = (self.resume_state.get("phase") or "discover").lower()

        saved_folder_urls = self.resume_state.get("folder_urls") or []
        if saved_folder_urls:
            self.folder_urls = [str(u).strip() for u in saved_folder_urls if str(u).strip()]
        if not self.folder_urls:
            self.folder_urls = build_folder_urls()

        current_folder_idx = int(self.resume_state.get("current_folder_idx") or 0)
        current_folder_idx = max(0, min(current_folder_idx, max(0, len(self.folder_urls) - 1)))

        self._merge_cookies_into_session()
        self.log.emit(f"Using {self.cookie_store.count()} cookies from browser session.")

        if self.resume_state:
            self.log.emit(
                f"Resume mode active: folder {current_folder_idx + 1}/{len(self.folder_urls)}, "
                f"phase={phase}, item={current_index + 1}."
            )
        else:
            self.log.emit(f"Starting fresh. Folder range: {folder_span_label()}")

        self._emit_progress(len(processed), max(len(discovered), 1), max(len(discovered), len(processed), 1))

        try:
            with sync_playwright() as pw:
                browser = pw.chromium.launch(headless=True)
                context = browser.new_context(user_agent=random.choice(USER_AGENTS), locale="en-US")

                seed_cookies = self._cookies_for_playwright()
                if seed_cookies:
                    try:
                        context.add_cookies(seed_cookies)
                    except Exception as e:
                        self.log.emit(f"Warning: could not inject browser cookies into Playwright context: {e}")

                seed_page = context.new_page()
                try:
                    self.log.emit(f"Seed page: {SEED_URL}")
                    seed_page.goto(SEED_URL, wait_until="domcontentloaded", timeout=90000)
                    seed_page.wait_for_timeout(1200)
                except Exception:
                    pass
                try:
                    seed_page.close()
                except Exception:
                    pass

                folder_page = context.new_page()
                folder_count = len(self.folder_urls)
                completed_volumes: Set[int] = set(range(max(0, current_folder_idx)))

                current_volume_name = extract_volume_name(
                    self.folder_urls[current_folder_idx] if self.folder_urls else "",
                    current_folder_idx + 1,
                )
                self._emit_volume_update(
                    current_folder_idx,
                    folder_count,
                    0,
                    current_volume_name,
                    "processing",
                    completed_volumes,
                )

                for fidx in range(current_folder_idx, folder_count):
                    current_folder_idx = fidx
                    self.folder_url = self.folder_urls[fidx]

                    if self._stop:
                        self._checkpoint(
                            status="stopped",
                            phase=phase,
                            processed=processed,
                            discovered=discovered,
                            doc_pages=doc_pages,
                            current_index=current_index,
                            downloaded=downloaded,
                            skipped=skipped,
                            failed=failed,
                            current_folder_idx=fidx,
                        )
                        try:
                            folder_page.close()
                        except Exception:
                            pass
                        browser.close()
                        self.finished.emit(downloaded, skipped, failed, "stopped")
                        return

                    self.log.emit(f"Scanning folder {fidx + 1}/{folder_count}: {self.folder_url}")
                    volume_name = extract_volume_name(self.folder_url, fidx + 1)
                    self._emit_volume_update(
                        fidx,
                        folder_count,
                        0,
                        volume_name,
                        "processing",
                        completed_volumes,
                    )

                    resumed_this_folder = (phase == "download" and fidx == current_folder_idx and len(doc_pages) > 0)

                    if not resumed_this_folder:
                        phase = "discover"
                        current_index = 0
                        doc_pages = []

                        self.log.emit(
                            f"Step 1/2 (folder {fidx + 1}/{folder_count}): Discovering items (doc pages + direct PDFs)..."
                        )
                        self._emit_volume_update(
                            fidx,
                            folder_count,
                            1,
                            volume_name,
                            "discovering",
                            completed_volumes,
                        )
                        doc_pages, blocked = self._collect_doc_pages(
                            folder_page,
                            discovered=discovered,
                            processed=processed,
                            downloaded=downloaded,
                            skipped=skipped,
                            failed=failed,
                        )

                        if blocked and not doc_pages:
                            self.log.emit(
                                "No items discovered and page looked protected/challenged. "
                                "Trying next folder instead of aborting."
                            )

                        if not doc_pages:
                            self.log.emit(f"No items found in folder {fidx + 1}. Moving to next folder.")
                            completed_volumes.add(fidx)
                            self._emit_volume_update(
                                fidx,
                                folder_count,
                                100,
                                volume_name,
                                "completed (no items)",
                                completed_volumes,
                            )
                            self._checkpoint(
                                status="running",
                                phase="discover",
                                processed=processed,
                                discovered=discovered,
                                doc_pages=[],
                                current_index=0,
                                downloaded=downloaded,
                                skipped=skipped,
                                failed=failed,
                                current_folder_idx=fidx + 1,
                            )
                            continue

                        phase = "download"
                        current_index = 0
                        self.log.emit(
                            f"Folder {fidx + 1}/{folder_count}: discovered {len(doc_pages)} items. "
                            "Starting download immediately."
                        )
                        self._checkpoint(
                            status="running",
                            phase="download",
                            processed=processed,
                            discovered=discovered,
                            doc_pages=doc_pages,
                            current_index=current_index,
                            downloaded=downloaded,
                            skipped=skipped,
                            failed=failed,
                            current_folder_idx=fidx,
                        )
                        self._emit_volume_update(
                            fidx,
                            folder_count,
                            5,
                            volume_name,
                            "processing",
                            completed_volumes,
                        )
                    else:
                        self.log.emit(
                            f"Resume download in folder {fidx + 1}/{folder_count}: "
                            f"continuing at item {current_index + 1}/{len(doc_pages)}."
                        )
                        resume_total = max(1, len(doc_pages))
                        resume_pct = 5 + int((max(0, current_index) / resume_total) * 95)
                        self._emit_volume_update(
                            fidx,
                            folder_count,
                            resume_pct,
                            volume_name,
                            "processing",
                            completed_volumes,
                        )

                    total_docs = len(doc_pages)
                    self._emit_progress(
                        len(processed),
                        max(len(discovered), total_docs, 1),
                        max(len(discovered), len(processed), total_docs, 1),
                    )
                    self.log.emit(f"Step 2/2 (folder {fidx + 1}/{folder_count}): Resolving and downloading PDFs...")
                    consecutive_item_failures = 0
                    folder_short_circuited = False

                    for idx in range(current_index, total_docs):
                        if self._stop:
                            stop_total = max(1, total_docs)
                            stop_pct = 5 + int((max(0, idx) / stop_total) * 95)
                            self._emit_volume_update(
                                fidx,
                                folder_count,
                                stop_pct,
                                volume_name,
                                "stopping",
                                completed_volumes,
                            )
                            self._checkpoint(
                                status="stopped",
                                phase="download",
                                processed=processed,
                                discovered=discovered,
                                doc_pages=doc_pages,
                                current_index=idx,
                                downloaded=downloaded,
                                skipped=skipped,
                                failed=failed,
                                current_folder_idx=fidx,
                            )
                            try:
                                folder_page.close()
                            except Exception:
                                pass
                            browser.close()
                            self.finished.emit(downloaded, skipped, failed, "stopped")
                            return

                        doc_url = doc_pages[idx]
                        if doc_url in processed:
                            self._emit_progress(
                                len(processed),
                                max(len(discovered), total_docs, 1),
                                max(len(discovered), len(processed), total_docs, 1),
                            )
                            done_pct = 5 + int(((idx + 1) / max(1, total_docs)) * 95)
                            self._emit_volume_update(
                                fidx,
                                folder_count,
                                done_pct,
                                volume_name,
                                "processing",
                                completed_volumes,
                            )
                            continue

                        self.log.emit(f"[F{fidx + 1} {idx + 1}/{total_docs}] Resolving PDF URL: {doc_url}")
                        pdf_url: Optional[str] = None
                        reason = ""

                        try:
                            if PDF_URL_RE.search(doc_url):
                                pdf_url = doc_url
                                pw_cookies = []
                            else:
                                pdf_url, pw_cookies, reason = self._resolve_pdf_url(context, doc_url)

                            if pw_cookies:
                                merged = self.cookie_store.merge(
                                    [
                                        {
                                            "name": c.get("name", ""),
                                            "value": c.get("value", ""),
                                            "domain": c.get("domain", ""),
                                            "path": c.get("path", "/"),
                                        }
                                        for c in pw_cookies
                                    ]
                                )
                                if merged > 0:
                                    self._merge_cookies_into_session()
                        except Exception as e:
                            reason = str(e)

                        row = {
                            "folder": self.folder_url,
                            "doc_url": doc_url,
                            "status": "error",
                            "pdf_url": None,
                            "file": None,
                            "error": None,
                            "ts": int(time.time()),
                        }
                        item_failed = False

                        if not pdf_url:
                            failed += 1
                            processed.add(doc_url)
                            row["error"] = reason or "pdf_url_not_found"
                            self.log.emit(f"[SKIP-FAILED] Could not resolve PDF ({row['error']}).")
                            item_failed = True
                        else:
                            fallback_name = code_from_doc_url(doc_url) or safe_filename_from_url(pdf_url)
                            target = self.output_dir / fallback_name

                            if target.exists():
                                skipped += 1
                                processed.add(doc_url)
                                row["status"] = "exists"
                                row["pdf_url"] = pdf_url
                                row["file"] = str(target)
                                self.log.emit(f"[EXISTS] {target.name}")
                            else:
                                res = self._download_pdf(pdf_url, target, referer=doc_url)
                                processed.add(doc_url)

                                if res.ok:
                                    downloaded += 1
                                    saved_path = res.reason if res.reason else str(target)
                                    row["status"] = "ok"
                                    row["pdf_url"] = pdf_url
                                    row["file"] = saved_path
                                    self.log.emit(f"[OK] {Path(saved_path).name}")
                                else:
                                    failed += 1
                                    row["status"] = "error"
                                    row["pdf_url"] = pdf_url
                                    row["error"] = res.reason
                                    self.log.emit(
                                        f"[SKIP-FAILED] Download failed after {FILE_RETRIES} attempts ({res.reason})."
                                    )
                                    item_failed = True

                        append_manifest_row(row)
                        self._emit_progress(
                            len(processed),
                            max(len(discovered), total_docs, 1),
                            max(len(discovered), len(processed), total_docs, 1),
                        )
                        done_pct = 5 + int(((idx + 1) / max(1, total_docs)) * 95)
                        self._emit_volume_update(
                            fidx,
                            folder_count,
                            done_pct,
                            volume_name,
                            "processing",
                            completed_volumes,
                        )

                        self._checkpoint(
                            status="running",
                            phase="download",
                            processed=processed,
                            discovered=discovered,
                            doc_pages=doc_pages,
                            current_index=idx + 1,
                            downloaded=downloaded,
                            skipped=skipped,
                            failed=failed,
                            fail_reason=row.get("error") or "",
                            current_folder_idx=fidx,
                        )

                        if item_failed:
                            consecutive_item_failures += 1
                        else:
                            consecutive_item_failures = 0

                        if consecutive_item_failures >= MAX_CONSECUTIVE_ITEM_FAILURES:
                            folder_short_circuited = True
                            remaining = max(0, total_docs - (idx + 1))
                            self.log.emit(
                                f"[CIRCUIT-BREAK] {consecutive_item_failures} consecutive failures. "
                                f"Skipping remaining {remaining} items in this folder and moving on."
                            )
                            self._checkpoint(
                                status="running",
                                phase="download",
                                processed=processed,
                                discovered=discovered,
                                doc_pages=doc_pages,
                                current_index=idx + 1,
                                downloaded=downloaded,
                                skipped=skipped,
                                failed=failed,
                                fail_reason=f"consecutive_failures>={MAX_CONSECUTIVE_ITEM_FAILURES}",
                                current_folder_idx=fidx,
                            )
                            break

                        time.sleep(random.uniform(*FILE_SLEEP_RANGE))

                    # Folder finished -> move immediately to next folder.
                    if folder_short_circuited:
                        self.log.emit(
                            f"Folder {fidx + 1}/{folder_count} skipped after "
                            f"{MAX_CONSECUTIVE_ITEM_FAILURES} consecutive failures."
                        )
                        volume_status = "skipped (consecutive failures)"
                    else:
                        self.log.emit(f"Folder {fidx + 1}/{folder_count} completed.")
                        volume_status = "completed"

                    completed_volumes.add(fidx)
                    self._emit_volume_update(
                        fidx,
                        folder_count,
                        100,
                        volume_name,
                        volume_status,
                        completed_volumes,
                    )
                    phase = "discover"
                    current_index = 0
                    doc_pages = []

                    self._checkpoint(
                        status="running",
                        phase="discover",
                        processed=processed,
                        discovered=discovered,
                        doc_pages=doc_pages,
                        current_index=0,
                        downloaded=downloaded,
                        skipped=skipped,
                        failed=failed,
                        current_folder_idx=fidx + 1,
                    )

                try:
                    folder_page.close()
                except Exception:
                    pass
                browser.close()

            clear_state()
            if self.folder_urls:
                last_idx = max(0, len(self.folder_urls) - 1)
                self._emit_volume_update(
                    last_idx,
                    len(self.folder_urls),
                    100,
                    extract_volume_name(self.folder_urls[last_idx], last_idx + 1),
                    "completed",
                    set(range(len(self.folder_urls))),
                )
            self.log.emit(f"Completed all folders ({folder_span_label()}).")
            self.finished.emit(downloaded, skipped, failed, "completed")

        except Exception as e:
            self.log.emit(f"Unexpected error: {type(e).__name__}: {e}")
            try:
                self._emit_volume_update(
                    current_folder_idx,
                    max(1, len(self.folder_urls)),
                    0,
                    extract_volume_name(self.folder_urls[current_folder_idx], current_folder_idx + 1) if self.folder_urls else "vol1",
                    "error",
                    set(range(max(0, current_folder_idx))),
                )
            except Exception:
                pass
            self._checkpoint(
                status="error",
                phase=phase,
                processed=processed,
                discovered=discovered,
                doc_pages=doc_pages,
                current_index=current_index,
                downloaded=downloaded,
                skipped=skipped,
                failed=failed,
                fail_reason=str(e),
                current_folder_idx=current_folder_idx,
            )
            self.finished.emit(downloaded, skipped, failed, "error")


class AgeGateDialog(QDialog):
    confirmed = Signal()

    def __init__(self, parent=None, target_url: str = ROOT_URL):
        super().__init__(parent)
        self.setWindowTitle("Manual Access Confirmation")
        self.setMinimumSize(1024, 760)

        self._cookie_map: Dict[Tuple[str, str, str], dict] = {}

        layout = QVBoxLayout(self)
        info = QLabel(
            "Open the page below and complete any login/CAPTCHA/age check if required.\n"
            "If none is required, just click:\n"
            "'I Confirmed, Start Download'."
        )
        info.setWordWrap(True)
        layout.addWidget(info)

        if not WEBENGINE_AVAILABLE:
            label = QLabel("PySide6 WebEngine is not available. The app can still continue without browser cookies.")
            label.setWordWrap(True)
            layout.addWidget(label)
            self.web = None
        else:
            self.web = QWebEngineView(self)
            self.web.load(QUrl(target_url))
            layout.addWidget(self.web, 1)

            store = self.web.page().profile().cookieStore()
            store.cookieAdded.connect(self._on_cookie_added)

        self.cookie_count_lbl = QLabel("Cookies captured: 0")
        layout.addWidget(self.cookie_count_lbl)

        row = QHBoxLayout()
        self.btn_reload = QPushButton("Reload Page")
        self.btn_reload.clicked.connect(self._reload)
        row.addWidget(self.btn_reload)

        row.addStretch(1)

        self.btn_confirm = QPushButton("I Confirmed, Start Download")
        self.btn_confirm.clicked.connect(self._confirm)
        row.addWidget(self.btn_confirm)
        layout.addLayout(row)

    def _reload(self):
        if self.web:
            self.web.reload()

    def _on_cookie_added(self, cookie):
        try:
            name = bytes(cookie.name()).decode("utf-8", errors="ignore")
            value = bytes(cookie.value()).decode("utf-8", errors="ignore")
            domain = cookie.domain() or ""
            path = cookie.path() or "/"
            if not name:
                return
            key = (name, domain, path)
            self._cookie_map[key] = {"name": name, "value": value, "domain": domain, "path": path}
            self.cookie_count_lbl.setText(f"Cookies captured: {len(self._cookie_map)}")
        except Exception:
            pass

    def export_cookies(self) -> List[dict]:
        return list(self._cookie_map.values())

    def _confirm(self):
        self.confirmed.emit()
        self.accept()


class HackerBackground(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._t = 0.0
        self._mouse = QPointF(-9999, -9999)
        self._inside = False
        self._timer = QTimer(self)
        self._timer.timeout.connect(self._tick)
        self._timer.start(33)
        self.setMouseTracking(True)

    def _tick(self):
        self._t += 0.033
        self.update()

    def mouseMoveEvent(self, event):
        self._inside = True
        self._mouse = event.position()
        super().mouseMoveEvent(event)

    def leaveEvent(self, event):
        self._inside = False
        super().leaveEvent(event)

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.setRenderHint(QPainter.TextAntialiasing, True)

        w, h = self.width(), self.height()

        g = QLinearGradient(0, 0, 0, h)
        g.setColorAt(0.0, QColor(2, 8, 4))
        g.setColorAt(0.55, QColor(3, 14, 7))
        g.setColorAt(1.0, QColor(1, 5, 3))
        p.fillRect(self.rect(), g)

        p.setFont(QFont("Consolas", 10))
        for x in range(0, w, 14):
            y = int((self._t * 80 + x * 1.7) % (h + 120)) - 60
            p.setPen(QColor(65, 255, 140, 85))
            p.drawText(x, y, random.choice("01"))

        if self._inside:
            rg = QRadialGradient(self._mouse, 120)
            rg.setColorAt(0.0, QColor(90, 255, 170, 60))
            rg.setColorAt(0.5, QColor(40, 190, 120, 30))
            rg.setColorAt(1.0, QColor(0, 0, 0, 0))
            p.setPen(Qt.NoPen)
            p.setBrush(rg)
            p.drawEllipse(self._mouse, 120, 120)

        v = QRadialGradient(w / 2, h / 2, max(w, h) * 0.9)
        v.setColorAt(0.7, QColor(0, 0, 0, 0))
        v.setColorAt(1.0, QColor(0, 0, 0, 140))
        p.fillRect(self.rect(), v)
        p.end()


class GlowFrame(QFrame):
    def __init__(self, parent=None):
        super().__init__(parent)
        sh = QGraphicsDropShadowEffect(self)
        sh.setOffset(0, 0)
        sh.setBlurRadius(22)
        sh.setColor(QColor(45, 255, 200, 110))
        self.setGraphicsEffect(sh)
        self._shadow = sh


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("ARIADNE • Dataset Downloader")
        self.setMinimumSize(1060, 740)

        ico = pick_existing_resource("logo_adriadne.ico", "logo_ariadne.ico")
        if ico:
            self.setWindowIcon(QIcon(str(ico)))

        self.cookie_store = SharedCookieStore()
        self.age_dialog: Optional[AgeGateDialog] = None

        self.worker_thread: Optional[QThread] = None
        self.worker: Optional[DownloaderWorker] = None
        self._last_total_indexed: int = 0
        self._volume_total: int = max(1, FOLDER_MAX - FOLDER_MIN + 1)
        self._volume_current: int = 1
        self._volume_completed: Set[int] = set()

        self._build_ui()
        self._apply_style()

    def _build_ui(self):
        bg = HackerBackground(self)
        self.setCentralWidget(bg)

        root = QVBoxLayout(bg)
        root.setContentsMargins(20, 20, 20, 20)

        header = GlowFrame()
        header.setObjectName("headerCard")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(14, 10, 14, 10)

        logo = QLabel()
        logo.setFixedSize(QSize(84, 84))
        png = pick_existing_resource("logo_adriadne.png", "logo_ariadne.png")
        if png:
            pm = QPixmap(str(png))
            if not pm.isNull():
                logo.setPixmap(pm.scaled(80, 80, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        hl.addWidget(logo)

        titles = QVBoxLayout()
        t1 = QLabel("ARIADNE Downloader")
        t1.setObjectName("title")
        t2 = QLabel("Download files from JDrive folder to output directory")
        t2.setObjectName("subtitle")
        titles.addWidget(t1)
        titles.addWidget(t2)
        hl.addLayout(titles, 1)

        self.btn_start = QPushButton("Start")
        self.btn_stop = QPushButton("Stop")
        self.btn_stop.setEnabled(False)
        self.btn_start.clicked.connect(self.start_clicked)
        self.btn_stop.clicked.connect(self.stop_clicked)

        hl.addWidget(self.btn_start)
        hl.addWidget(self.btn_stop)

        root.addWidget(header)

        info = GlowFrame()
        info.setObjectName("infoCard")
        il = QHBoxLayout(info)
        il.setContentsMargins(12, 8, 12, 8)
        il.addWidget(QLabel("Output:"))
        self.lbl_output = QLabel(str(files_dir()))
        self.lbl_output.setObjectName("path")
        self.lbl_output.setTextInteractionFlags(Qt.TextSelectableByMouse)
        il.addWidget(self.lbl_output, 1)
        root.addWidget(info)

        self.progress_volume = QProgressBar()
        self.progress_volume.setRange(0, 100)
        self.progress_volume.setValue(0)
        root.addWidget(self.progress_volume)

        self.lbl_volume_status = QLabel("Volume: 1/1 (0%) • vol1 • waiting.")
        self.lbl_volume_status.setObjectName("volumeStatus")
        root.addWidget(self.lbl_volume_status)

        self.lbl_volume_list = QLabel("")
        self.lbl_volume_list.setObjectName("volumeList")
        self.lbl_volume_list.setTextFormat(Qt.RichText)
        self.lbl_volume_list.setWordWrap(True)
        root.addWidget(self.lbl_volume_list)
        self.lbl_volume_list.setText(self._render_volume_list(self._volume_total, self._volume_current, self._volume_completed))

        self.progress = QProgressBar()
        self.progress.setRange(0, 100)
        self.progress.setValue(0)
        root.addWidget(self.progress)

        self.lbl_status = QLabel("Processed / Discovered: 0 / 0 (0%)")
        self.lbl_status.setObjectName("status")
        root.addWidget(self.lbl_status)

        self.progress_total = QProgressBar()
        self.progress_total.setRange(0, 100)
        self.progress_total.setValue(0)
        root.addWidget(self.progress_total)

        self.lbl_status_total = QLabel("Processed / Total indexed files: 0 / 0 (0%)")
        self.lbl_status_total.setObjectName("status")
        root.addWidget(self.lbl_status_total)

        self.log_box = QTextEdit()
        self.log_box.setObjectName("logBox")
        self.log_box.setReadOnly(True)
        root.addWidget(self.log_box, 1)

    def _apply_style(self):
        self.setStyleSheet(
            """
            QWidget {
                color: #d8ffee;
                font-family: Segoe UI, Arial, sans-serif;
                font-size: 13px;
            }
            #headerCard, #infoCard {
                background: rgba(8, 20, 24, 214);
                border: 1px solid rgba(95, 255, 220, 95);
                border-radius: 14px;
            }
            #title {
                font-size: 25px;
                font-weight: 800;
                color: #f0fff9;
            }
            #subtitle {
                color: #9bffd5;
                font-size: 13px;
            }
            #path {
                color: #9affdf;
                font-weight: 600;
            }
            #status {
                color: #9fe6ff;
                font-weight: 600;
                padding-left: 2px;
            }
            #volumeStatus {
                color: #b8ffe8;
                font-weight: 700;
                padding-left: 2px;
            }
            #volumeList {
                color: #a1d7cf;
                font-weight: 600;
                padding-left: 2px;
                min-height: 24px;
            }
            QPushButton {
                background: rgba(10, 40, 45, 225);
                border: 1px solid rgba(110, 255, 220, 130);
                border-radius: 10px;
                padding: 10px 14px;
                font-weight: 700;
                min-width: 120px;
            }
            QPushButton:hover {
                background: rgba(16, 56, 64, 245);
            }
            QPushButton:disabled {
                background: rgba(30, 40, 45, 180);
                color: #96b8b0;
                border: 1px solid rgba(90, 120, 110, 90);
            }
            QProgressBar {
                border: 1px solid rgba(80, 255, 210, 120);
                border-radius: 9px;
                background: rgba(10, 24, 26, 210);
                height: 21px;
                text-align: center;
                font-weight: 700;
                color: #e8fff5;
            }
            QProgressBar::chunk {
                background: qlineargradient(x1:0, y1:0, x2:1, y2:0,
                    stop:0 rgba(55, 230, 150, 230),
                    stop:1 rgba(60, 200, 255, 235));
                border-radius: 8px;
            }
            #logBox {
                background: rgba(4, 16, 18, 226);
                border: 1px solid rgba(100, 255, 220, 110);
                border-radius: 12px;
                padding: 8px;
                selection-background-color: rgba(20, 120, 95, 180);
            }

            QMessageBox {
                background: #ffffff;
                color: #111111;
            }
            QMessageBox QLabel {
                color: #111111;
                font-size: 13px;
            }
            QMessageBox QPushButton {
                color: #111111;
                background: #f0f0f0;
                border: 1px solid #999;
                border-radius: 6px;
                min-width: 110px;
                padding: 6px 10px;
            }
            QMessageBox QPushButton:hover {
                background: #e4e4e4;
            }
            """
        )

    def append_log(self, text: str):
        now = time.strftime("%H:%M:%S")
        self.log_box.append(f"[{now}] {text}")
        sb = self.log_box.verticalScrollBar()
        sb.setValue(sb.maximum())

    def _ask_resume(self) -> Optional[dict]:
        st = load_state()
        if not st:
            return None

        status = (st.get("status") or "").lower()
        if status not in {"running", "stopped", "failed", "error", "auth_required"}:
            return None

        idx = int(st.get("current_index") or 0)
        total = len(st.get("doc_pages") or [])
        phase = st.get("phase") or "unknown"
        reason = st.get("fail_reason") or ""
        folder_urls = st.get("folder_urls") or build_folder_urls()
        fidx = int(st.get("current_folder_idx") or 0)
        fidx = max(0, min(fidx, max(0, len(folder_urls) - 1)))

        msg = QMessageBox(self)
        msg.setIcon(QMessageBox.Question)
        msg.setWindowTitle("Resume previous session")
        msg.setText(
            "A checkpoint was found.\n"
            "Do you want to resume or start over?\n\n"
            f"Folder: {fidx + 1}/{len(folder_urls)}\n"
            f"Phase: {phase}\n"
            f"Item: {idx}/{total}\n"
            f"Reason: {reason or 'n/a'}"
        )
        btn_resume = msg.addButton("Resume", QMessageBox.AcceptRole)
        btn_restart = msg.addButton("Start Over", QMessageBox.DestructiveRole)
        btn_cancel = msg.addButton("Cancel", QMessageBox.RejectRole)
        msg.exec()

        clicked = msg.clickedButton()
        if clicked == btn_resume:
            return st
        if clicked == btn_restart:
            clear_state()
            return None
        return {"__cancel__": True}


    def _open_age_dialog(self, target_url: str = SEED_URL) -> bool:
        if not WEBENGINE_AVAILABLE:
            self.append_log("WebEngine not available. Continuing without browser cookie capture.")
            QMessageBox.information(
                self,
                "WebEngine not available",
                "PySide6 WebEngine is not installed.\n\n"
                "The downloader will continue without browser cookies.\n"
                "If access is blocked, install PySide6-Addons and retry."
            )
            return True

        self.age_dialog = AgeGateDialog(self, target_url=target_url)
        self.append_log("Optional manual step: complete login/CAPTCHA/access if needed, then click 'I Confirmed, Start Download'.")
        ok = self.age_dialog.exec() == QDialog.Accepted
        if not ok:
            return False

        cookies = self.age_dialog.export_cookies()
        if cookies:
            self.cookie_store.set_all(cookies)
            self.append_log(f"Cookie snapshot captured: {self.cookie_store.count()} cookies.")
        else:
            self.append_log("No cookies captured. Proceeding without browser cookies.")

        return True

    def start_clicked(self):
        resume_state = self._ask_resume()
        if isinstance(resume_state, dict) and resume_state.get("__cancel__"):
            self.append_log("Startup canceled.")
            return

        target_url = SEED_URL
        folder_urls = build_folder_urls()
        if resume_state:
            folder_urls = resume_state.get("folder_urls") or folder_urls
            docs = resume_state.get("doc_pages") or []
            idx = int(resume_state.get("current_index") or 0)
            fidx = int(resume_state.get("current_folder_idx") or 0)
            if 0 <= idx < len(docs):
                target_url = docs[idx]
            else:
                if 0 <= fidx < len(folder_urls):
                    target_url = folder_urls[fidx]
                else:
                    target_url = SEED_URL

        if not self._open_age_dialog(target_url=target_url):
            self.append_log("Manual confirmation canceled.")
            return

        self.progress.setValue(0)
        self.progress_total.setValue(0)
        self.progress_volume.setValue(0)
        self._last_total_indexed = 0
        self._volume_total = max(1, len(folder_urls))
        start_volume = 1
        if resume_state:
            start_volume = max(1, min(self._volume_total, int(resume_state.get("current_folder_idx") or 0) + 1))
            self._volume_completed = set(range(1, start_volume))
        else:
            self._volume_completed = set()
        self._volume_current = start_volume
        start_volume_name = extract_volume_name(folder_urls[start_volume - 1], start_volume) if folder_urls else "vol1"
        self.lbl_status.setText("Processed / Discovered: 0 / 0 (0%)")
        self.lbl_status_total.setText("Processed / Total indexed files: 0 / 0 (0%)")
        self.lbl_volume_status.setText(
            f"Volume: {start_volume}/{self._volume_total} (0%) • {start_volume_name} • processing."
        )
        self.lbl_volume_list.setText(
            self._render_volume_list(self._volume_total, self._volume_current, self._volume_completed)
        )
        self.append_log("Session setup...")
        self.append_log(
            f"Worker config: id='{WORKER_ID or 'default'}' | range={folder_span_label()} | "
            f"state={state_file().name} | manifest={manifest_file().name} | output={files_dir().name}"
        )

        self.btn_start.setEnabled(False)
        self.btn_stop.setEnabled(True)

        out = files_dir()
        self.lbl_output.setText(str(out))

        self.worker_thread = QThread(self)
        self.worker = DownloaderWorker(
            out,
            resume_state=resume_state,
            cookie_store=self.cookie_store,
            folder_urls=folder_urls,
        )
        self.worker.moveToThread(self.worker_thread)

        runner = getattr(self.worker, "run", None)
        if not callable(runner):
            runner = getattr(self.worker, "start", None)
        if not callable(runner):
            self.append_log("FATAL: DownloaderWorker has no callable run/start method.")
            self.btn_start.setEnabled(True)
            self.btn_stop.setEnabled(False)
            QMessageBox.critical(self, "ARIADNE", "Internal error: worker entrypoint not found (run/start).")
            return

        self.worker_thread.started.connect(runner)
        self.worker.log.connect(self.append_log)
        self.worker.progress.connect(self.on_progress)
        self.worker.progress_total.connect(self.on_progress_total)
        self.worker.volume_update.connect(self.on_volume_update)
        self.worker.finished.connect(self.on_finished)
        self.worker.auth_required.connect(self.on_auth_required)

        self.worker.finished.connect(self.worker_thread.quit)
        self.worker_thread.finished.connect(self.worker_thread.deleteLater)

        self.worker_thread.start()


    def stop_clicked(self):
        if self.worker:
            self.worker.request_stop()
            self.append_log("Stop requested...")
            self.lbl_status.setText("Stopping...")

    def _render_volume_list(self, total: int, current: int, completed: Set[int]) -> str:
        total = max(1, int(total))
        current = max(1, min(total, int(current)))
        parts: List[str] = []
        for i in range(1, total + 1):
            label = f"{i}/{total}"
            is_done = i in completed
            is_current = i == current

            if is_done:
                item = f"✓ {label}"
                base_style = "color:#7dffb9; font-weight:700;"
            else:
                item = label
                base_style = "color:#98d9cc;"

            if is_current:
                base_style += (
                    " background: rgba(80, 195, 255, 0.22);"
                    " border: 1px solid rgba(130, 225, 255, 0.65);"
                    " border-radius: 8px;"
                    " padding: 2px 7px;"
                    " font-weight: 800;"
                    " color:#e7fbff;"
                )
            else:
                base_style += " padding: 1px 2px;"

            parts.append(f'<span style="{base_style}">{item}</span>')
        return " · ".join(parts)

    def on_volume_update(
        self,
        current_volume: int,
        total_volumes: int,
        percent: int,
        volume_name: str,
        state: str,
        completed_csv: str,
    ):
        total_volumes = max(1, int(total_volumes))
        current_volume = max(1, min(total_volumes, int(current_volume)))
        percent = max(0, min(100, int(percent)))

        completed: Set[int] = set()
        if completed_csv:
            for tok in completed_csv.split(","):
                tok = tok.strip()
                if tok.isdigit():
                    val = int(tok)
                    if 1 <= val <= total_volumes:
                        completed.add(val)

        self._volume_total = total_volumes
        self._volume_current = current_volume
        self._volume_completed = completed

        self.progress_volume.setValue(percent)
        self.lbl_volume_status.setText(
            f"Volume: {current_volume}/{total_volumes} ({percent}%) • {volume_name} • {state}."
        )
        self.lbl_volume_list.setText(self._render_volume_list(total_volumes, current_volume, completed))

    def on_progress(self, current: int, total: int):
        if total <= 0:
            pct = 0
        else:
            pct = int((current / total) * 100)
            pct = max(0, min(100, pct))
        self.progress.setValue(pct)
        self.lbl_status.setText(f"Processed / Discovered: {current} / {total} ({pct}%)")

    def on_progress_total(self, current: int, total_indexed: int):
        total_indexed = max(0, int(total_indexed))
        self._last_total_indexed = total_indexed

        if total_indexed <= 0:
            self.progress_total.setValue(0)
            self.lbl_status_total.setText(f"Processed / Total indexed files: {current} / 0 (0%)")
            return

        pct = int((current / total_indexed) * 100)
        pct = max(0, min(100, pct))
        self.progress_total.setValue(pct)
        self.lbl_status_total.setText(
            f"Processed / Total indexed files: {current} / {total_indexed} ({pct}%)"
        )

    def on_auth_required(self, url: str, idx: int, total: int):
        self.append_log(
            f"Session likely blocked at index {idx}/{total}. "
            "Re-open Start and complete manual access in browser if required."
        )

    def on_finished(self, downloaded: int, skipped: int, failed: int, status: str):
        self.btn_start.setEnabled(True)
        self.btn_stop.setEnabled(False)

        processed_final = downloaded + skipped + failed
        if self._last_total_indexed > 0:
            pct2 = int((processed_final / self._last_total_indexed) * 100)
            pct2 = max(0, min(100, pct2))
            self.progress_total.setValue(pct2)
            self.lbl_status_total.setText(
                f"Processed / Total indexed files: {processed_final} / {self._last_total_indexed} ({pct2}%)"
            )

        if status == "completed":
            self.progress_volume.setValue(100)
            self._volume_completed = set(range(1, self._volume_total + 1))
            self.lbl_volume_list.setText(
                self._render_volume_list(self._volume_total, self._volume_total, self._volume_completed)
            )
            self.lbl_volume_status.setText(
                f"Volume: {self._volume_total}/{self._volume_total} (100%) • "
                f"{extract_volume_name(self.worker.folder_url if self.worker else '', self._volume_total)} • completed."
            )
            headline = f"Completed. New: {downloaded} | Existing: {skipped} | Failed: {failed}"
            detail = (
                "Download completed.\n\n"
                f"New: {downloaded}\nExisting: {skipped}\nFailed: {failed}\n\n"
                f"Folder: {files_dir()}\n"
                f"Manifest: {manifest_file()}"
            )
        elif status == "stopped":
            self.lbl_volume_status.setText(
                f"Volume: {self._volume_current}/{self._volume_total} ({self.progress_volume.value()}%) • "
                f"{extract_volume_name(self.worker.folder_url if self.worker else '', self._volume_current)} • stopped."
            )
            headline = f"Stopped by user. New: {downloaded} | Existing: {skipped} | Failed: {failed}"
            detail = (
                "Download stopped by user.\n\n"
                f"New: {downloaded}\nExisting: {skipped}\nFailed: {failed}\n\n"
                "Checkpoint saved for resume."
            )
        elif status == "auth_required":
            self.lbl_volume_status.setText(
                f"Volume: {self._volume_current}/{self._volume_total} ({self.progress_volume.value()}%) • "
                f"{extract_volume_name(self.worker.folder_url if self.worker else '', self._volume_current)} • blocked."
            )
            headline = f"Access blocked. New: {downloaded} | Existing: {skipped} | Failed: {failed}"
            detail = (
                "Access appears blocked by login/CAPTCHA/authorization gate.\n\n"
                "Click Start, complete manual access in the browser window, and resume."
            )
        else:
            self.lbl_volume_status.setText(
                f"Volume: {self._volume_current}/{self._volume_total} ({self.progress_volume.value()}%) • "
                f"{extract_volume_name(self.worker.folder_url if self.worker else '', self._volume_current)} • {status}."
            )
            headline = f"Finished with status '{status}'. New: {downloaded} | Existing: {skipped} | Failed: {failed}"
            detail = (
                "Run finished with unexpected status.\n\n"
                f"Status: {status}\nNew: {downloaded}\nExisting: {skipped}\nFailed: {failed}"
            )

        self.lbl_status.setText(headline)
        self.append_log(headline)
        QMessageBox.information(self, "ARIADNE", detail)

    def closeEvent(self, event):
        try:
            if self.worker:
                self.worker.request_stop()
            if self.worker_thread and self.worker_thread.isRunning():
                self.worker_thread.quit()
                self.worker_thread.wait(1500)
        except Exception:
            pass
        super().closeEvent(event)


def main():
    apply_runtime_config_from_args()

    QCoreApplication.setAttribute(Qt.AA_UseSoftwareOpenGL, True)
    QCoreApplication.setAttribute(Qt.AA_ShareOpenGLContexts, True)

    app = QApplication(sys.argv)
    app.setStyle("Fusion")

    w = MainWindow()
    w.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
