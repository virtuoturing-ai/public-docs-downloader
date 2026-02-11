from __future__ import annotations

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
from typing import Dict, List, Optional, Tuple
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

from bs4 import BeautifulSoup

from PySide6.QtCore import QObject, QThread, Qt, Signal, QTimer, QUrl, QSize, QPointF, QCoreApplication
from PySide6.QtGui import QColor, QPainter, QLinearGradient, QRadialGradient, QPen, QFont, QIcon, QPixmap
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

ROOT_URL = "https://www.justice.gov/epstein"
STATE_FILE_NAME = "epstein_download_state.json"
FILES_PER_PAGE_OBJECTIVE = 50
TOTAL_EPSTEIN_FILES = 804_650  
DATASET_MIN = 1
DATASET_MAX = 12

DATASET_PAGE_COUNTS = {
    1: 63,
    2: 12,
    3: 2,
    4: 4,
    5: 3,
    6: 1,
    7: 1,
    8: 220,
    9: 9276,
    10: 1,
    11: 6507,
    12: 3,
}

# Stop current dataset after too many consecutive page-level failures
NO_PROGRESS_PAGE_LIMIT = 20

PAGE_RETRIES = 3
FILE_RETRIES = 3

PAGE_SLEEP_RANGE = (0.6, 1.3)
FILE_SLEEP_RANGE = (0.12, 0.32)

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:126.0) Gecko/20100101 Firefox/126.0",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
]


def runtime_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def files_dir() -> Path:
    d = runtime_dir() / "files"
    d.mkdir(parents=True, exist_ok=True)
    return d


def state_file() -> Path:
    return runtime_dir() / STATE_FILE_NAME


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


def safe_filename_from_url(url: str) -> str:
    parsed = urlparse(url)
    raw_name = unquote(Path(parsed.path).name.strip())
    if not raw_name:
        raw_name = f"file_{hashlib.md5(url.encode('utf-8')).hexdigest()[:12]}.pdf"
    raw_name = re.sub(r'[<>:"/\\|?*]+', "_", raw_name).strip(" .")
    if not raw_name.lower().endswith(".pdf"):
        raw_name += ".pdf"
    return raw_name


def normalize_url(url: str) -> str:
    p = urlparse(url)
    return f"{p.scheme}://{p.netloc}{p.path}"


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
    dataset_info = Signal(int, int, int, int)  
    finished = Signal(int, int, int, str) 
    auth_required = Signal(str, int, int)  

    def __init__(self, output_dir: Path, resume_state: Optional[dict], cookie_store: SharedCookieStore):
        super().__init__()
        self.output_dir = output_dir
        self.resume_state = resume_state or {}
        self.total_epstein = int(TOTAL_EPSTEIN_FILES)
        self._dataset_processed_counts: Dict[int, int] = {}
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

    def _checkpoint(
        self,
        status: str,
        dataset_idx: int,
        page_idx: int,
        processed: set[str],
        discovered: set[str],
        downloaded: int,
        skipped: int,
        failed: int,
        no_progress_pages: int = 0,
        fail_reason: str = "",
    ) -> None:
        state = {
            "version": 1,
            "status": status,
            "dataset_idx": dataset_idx,
            "page_idx": page_idx,
            "processed": sorted(processed),
            "discovered": sorted(discovered),
            "downloaded": downloaded,
            "skipped": skipped,
            "failed": failed,
            "no_progress_pages": no_progress_pages,
            "fail_reason": fail_reason,
            "updated_at_epoch": int(time.time()),
            "total_epstein": int(self.total_epstein or 0),
            "dataset_processed_counts": {str(k): int(v) for k, v in sorted(self._dataset_processed_counts.items())},
        }
        save_state(state)

    def _merge_cookies_into_session(self) -> int:
        merged = 0
        for c in self.cookie_store.get_all():
            name = c.get("name")
            value = c.get("value", "")
            domain = c.get("domain", "")
            path = c.get("path", "/")
            if not name:
                continue
            self.session.cookies.set(name, value, domain=domain, path=path)
            merged += 1
        return merged

    def _emit_progress(self, dataset_processed: int, dataset_target: int, global_processed: int, dataset_idx: int) -> None:
        dataset_target_safe = max(1, int(dataset_target))
        dataset_processed_safe = max(0, int(dataset_processed))
        self.progress.emit(dataset_processed_safe, dataset_target_safe)
        self.dataset_info.emit(int(dataset_idx), int(DATASET_MAX), dataset_processed_safe, dataset_target_safe)

        total = max(1, int(self.total_epstein or 0))
        global_processed_safe = max(0, int(global_processed))
        self.progress_total.emit(global_processed_safe, total)

    def _estimate_total_epstein_files(self, already_known: set[str]) -> int:
        _ = already_known
        return int(TOTAL_EPSTEIN_FILES)

    def _request_page_html(self, url: str, retries: int = PAGE_RETRIES) -> Tuple[Optional[str], str]:
        last_reason = "unknown error"
        backoff = 2.0
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
                    last_reason = f"HTTP {code} (authorization/age gate likely required)"
                    self.log.emit(f"Attempt {attempt}/{retries} failed: {url} -> {last_reason}")
                    time.sleep(backoff + random.uniform(0.2, 0.9))
                    backoff *= 1.6
                    continue

                if code in (429, 500, 502, 503, 504):
                    last_reason = f"HTTP {code}"
                    self.log.emit(f"Attempt {attempt}/{retries} failed: {url} -> {last_reason}")
                    time.sleep(backoff + random.uniform(0.2, 0.9))
                    backoff *= 1.6
                    continue

                if code >= 400:
                    return None, f"HTTP {code}"

                return text, ""
            except Exception as e:
                last_reason = str(e)
                self.log.emit(f"Attempt {attempt}/{retries} failed: {url} -> {e}")
                time.sleep(backoff + random.uniform(0.2, 0.9))
                backoff *= 1.6

        return None, last_reason

    @staticmethod
    def _extract_pdf_links(html: str, page_url: str) -> List[str]:
        soup = BeautifulSoup(html, "html.parser")
        out: List[str] = []
        seen = set()
        for a in soup.find_all("a", href=True):
            href = (a.get("href") or "").strip()
            if not href:
                continue
            full = urljoin(page_url, href)
            norm = normalize_url(full)
            p = urlparse(norm)
            path = p.path.lower()

            if "/epstein/files/" not in path:
                continue
            if not path.endswith(".pdf"):
                continue
            if norm in seen:
                continue
            seen.add(norm)
            out.append(norm)
        return out

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
                    last_reason = f"HTTP {code} (authorization/age gate likely required)"
                    self.log.emit(f"Attempt {attempt}/{FILE_RETRIES} failed for {url}: {last_reason}")
                    time.sleep(1.4 + attempt * 0.8 + random.uniform(0.2, 0.9))
                    continue

                if code == 404:
                    return DownloadResult(False, "HTTP 404 (link exists but file missing)", permanent_skip=True)

                if code in (429, 500, 502, 503, 504):
                    last_reason = f"HTTP {code}"
                    self.log.emit(f"Attempt {attempt}/{FILE_RETRIES} failed for {url}: {last_reason}")
                    time.sleep(1.2 + attempt * 0.7 + random.uniform(0.2, 0.9))
                    continue

                if code >= 400:
                    return DownloadResult(False, f"HTTP {code}", permanent_skip=True)

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
                    return DownloadResult(False, "downloaded file is too small / invalid", permanent_skip=True)

                temp.replace(target)
                return DownloadResult(True)

            except Exception as e:
                last_reason = str(e)
                self.log.emit(f"Attempt {attempt}/{FILE_RETRIES} failed for {url}: {e}")
                try:
                    if temp.exists():
                        temp.unlink()
                except Exception:
                    pass
                time.sleep(1.2 + attempt * 0.7 + random.uniform(0.2, 0.9))
            finally:
                try:
                    if resp is not None:
                        resp.close()
                except Exception:
                    pass

        return DownloadResult(False, last_reason, permanent_skip=True)

    @staticmethod
    def _page_url(ds: int, page: int) -> str:
        base = f"https://www.justice.gov/epstein/doj-disclosures/data-set-{ds}-files"
        if page <= 1:
            return base
        # justice.gov uses zero-based pagination in the query string
        return f"{base}?page={page - 1}"

    def run(self) -> None:
        downloaded = int(self.resume_state.get("downloaded") or 0)
        skipped = int(self.resume_state.get("skipped") or 0)
        failed = int(self.resume_state.get("failed") or 0)

        processed: set[str] = set(self.resume_state.get("processed") or [])
        discovered: set[str] = set(self.resume_state.get("discovered") or [])

        start_ds = int(self.resume_state.get("dataset_idx") or DATASET_MIN)
        start_page = int(self.resume_state.get("page_idx") or 1)

        self._merge_cookies_into_session()
        self.log.emit(f"Using {self.cookie_store.count()} cookies from browser session.")

        if self.resume_state:
            self.log.emit(f"Resume mode active: continuing from dataset {start_ds}, page {start_page}.")
        else:
            self.log.emit("Starting fresh: dataset 1, page 1.")

        self.total_epstein = int(TOTAL_EPSTEIN_FILES)
        self.log.emit(f"Using fixed global objective: {self.total_epstein} files.")

        plan_str = ", ".join(
            f"DS{ds}:{DATASET_PAGE_COUNTS.get(ds, 1)}"
            for ds in range(DATASET_MIN, DATASET_MAX + 1)
        )
        self.log.emit(f"Hardcoded page plan -> {plan_str}")

        raw_counts = self.resume_state.get("dataset_processed_counts") or {}
        try:
            self._dataset_processed_counts = {int(k): int(v) for k, v in raw_counts.items()}
        except Exception:
            self._dataset_processed_counts = {}

        # Initial UI state
        current_ds_for_ui = max(DATASET_MIN, min(DATASET_MAX, start_ds))
        current_ds_target = max(1, int(DATASET_PAGE_COUNTS.get(current_ds_for_ui, 1)) * FILES_PER_PAGE_OBJECTIVE)
        current_ds_processed = int(self._dataset_processed_counts.get(current_ds_for_ui, 0))
        if current_ds_processed <= 0 and start_page > 1 and current_ds_for_ui == start_ds:
            current_ds_processed = min((start_page - 1) * FILES_PER_PAGE_OBJECTIVE, current_ds_target)

        global_processed0 = len(processed)
        self._emit_progress(current_ds_processed, current_ds_target, global_processed0, current_ds_for_ui)

        try:
            for ds in range(start_ds, DATASET_MAX + 1):
                if self._stop:
                    self._checkpoint(
                        status="stopped",
                        dataset_idx=ds,
                        page_idx=1,
                        processed=processed,
                        discovered=discovered,
                        downloaded=downloaded,
                        skipped=skipped,
                        failed=failed,
                    )
                    self.finished.emit(downloaded, skipped, failed, "stopped")
                    return

                max_pages = int(DATASET_PAGE_COUNTS.get(ds, 1))
                page = start_page if ds == start_ds else 1
                ds_target_files = max(1, max_pages * FILES_PER_PAGE_OBJECTIVE)
                ds_processed_files = int(self._dataset_processed_counts.get(ds, 0))
                if ds_processed_files <= 0 and ds == start_ds and page > 1:
                    ds_processed_files = min((page - 1) * FILES_PER_PAGE_OBJECTIVE, ds_target_files)

                self._emit_progress(ds_processed_files, ds_target_files, len(processed), ds)

                if page > max_pages:
                    self.log.emit(
                        f"Data Set {ds}: resume page {page} is beyond hardcoded max page {max_pages}. "
                        "Skipping dataset."
                    )
                    start_page = 1
                    continue

                no_progress_pages = int(self.resume_state.get("no_progress_pages") or 0) if ds == start_ds else 0

                self.log.emit(f"Starting Data Set {ds} at page {page}/{max_pages} (hardcoded).")

                while (not self._stop) and (page <= max_pages):
                    page_url = self._page_url(ds, page)
                    self.log.emit(f"Scanning Data Set {ds}, page {page}/{max_pages}: {page_url}")

                    html, reason = self._request_page_html(page_url, retries=PAGE_RETRIES)
                    if html is None:
                        failed += 1
                        no_progress_pages += 1
                        self.log.emit(
                            f"Data Set {ds}, page {page}/{max_pages}: failed ({reason}). "
                            f"Failure streak: {no_progress_pages}/{NO_PROGRESS_PAGE_LIMIT}."
                        )

                        if "authorization/age gate" in reason.lower() and page == 1:
                            self._checkpoint(
                                status="auth_required",
                                dataset_idx=ds,
                                page_idx=page,
                                processed=processed,
                                discovered=discovered,
                                downloaded=downloaded,
                                skipped=skipped,
                                failed=failed,
                                no_progress_pages=no_progress_pages,
                                fail_reason=reason,
                            )
                            self.auth_required.emit(page_url, ds, page)
                            self.finished.emit(downloaded, skipped, failed, "auth_required")
                            return

                        next_page = min(page + 1, max_pages + 1)
                        self._checkpoint(
                            status="running",
                            dataset_idx=ds,
                            page_idx=next_page,
                            processed=processed,
                            discovered=discovered,
                            downloaded=downloaded,
                            skipped=skipped,
                            failed=failed,
                            no_progress_pages=no_progress_pages,
                            fail_reason=reason,
                        )

                        if no_progress_pages >= NO_PROGRESS_PAGE_LIMIT:
                            remaining = max_pages - page + 1
                            self.log.emit(
                                f"Data Set {ds}: reached failure streak limit ({NO_PROGRESS_PAGE_LIMIT}). "
                                f"Skipping remaining {remaining} page(s) in this dataset."
                            )
                            break

                        page += 1
                        time.sleep(random.uniform(*PAGE_SLEEP_RANGE))
                        continue

                    no_progress_pages = 0

                    links = self._extract_pdf_links(html, page_url)
                    for u in links:
                        discovered.add(u)

                    if not links:
                        self.log.emit(f"Data Set {ds}, page {page}/{max_pages}: no PDF links on this page.")
                    else:
                        new_links = [u for u in links if u not in processed]
                        self.log.emit(
                            f"Data Set {ds}, page {page}/{max_pages}: found {len(links)} links ({len(new_links)} new)."
                        )

                        for pdf_url in new_links:
                            if self._stop:
                                break

                            file_name = safe_filename_from_url(pdf_url)
                            target = self.output_dir / file_name

                            if target.exists():
                                skipped += 1
                                processed.add(pdf_url)
                                ds_processed_files += 1
                                self._dataset_processed_counts[ds] = ds_processed_files
                                self._emit_progress(ds_processed_files, ds_target_files, len(processed), ds)
                                self.log.emit(f"[DS{ds} {ds_processed_files}/{ds_target_files}] EXISTS: {file_name}")
                                continue

                            res = self._download_pdf(pdf_url, target, referer=page_url)

                            if res.ok:
                                downloaded += 1
                                processed.add(pdf_url)
                                ds_processed_files += 1
                                self._dataset_processed_counts[ds] = ds_processed_files
                                self._emit_progress(ds_processed_files, ds_target_files, len(processed), ds)
                                self.log.emit(f"[DS{ds} {ds_processed_files}/{ds_target_files}] OK: {file_name}")
                            else:
                                failed += 1
                                processed.add(pdf_url)
                                ds_processed_files += 1
                                self._dataset_processed_counts[ds] = ds_processed_files
                                self._emit_progress(ds_processed_files, ds_target_files, len(processed), ds)
                                self.log.emit(
                                    f"[SKIP-FAILED] {pdf_url} failed after {FILE_RETRIES} attempts "
                                    f"({res.reason}). Skipping this file and continuing."
                                )

                            self._checkpoint(
                                status="running",
                                dataset_idx=ds,
                                page_idx=page,
                                processed=processed,
                                discovered=discovered,
                                downloaded=downloaded,
                                skipped=skipped,
                                failed=failed,
                                no_progress_pages=no_progress_pages,
                            )
                            time.sleep(random.uniform(*FILE_SLEEP_RANGE))

                    next_page = min(page + 1, max_pages + 1)
                    self._checkpoint(
                        status="running",
                        dataset_idx=ds,
                        page_idx=next_page,
                        processed=processed,
                        discovered=discovered,
                        downloaded=downloaded,
                        skipped=skipped,
                        failed=failed,
                        no_progress_pages=no_progress_pages,
                    )

                    page += 1
                    time.sleep(random.uniform(*PAGE_SLEEP_RANGE))

                if self._stop:
                    self._checkpoint(
                        status="stopped",
                        dataset_idx=ds,
                        page_idx=page,
                        processed=processed,
                        discovered=discovered,
                        downloaded=downloaded,
                        skipped=skipped,
                        failed=failed,
                        no_progress_pages=no_progress_pages,
                    )
                    self.finished.emit(downloaded, skipped, failed, "stopped")
                    return

                self.log.emit(f"Data Set {ds}: completed hardcoded range 1..{max_pages}.")
                start_page = 1

            clear_state()
            self.log.emit("Completed all datasets (1..12).")
            self.finished.emit(downloaded, skipped, failed, "completed")

        except Exception as e:
            self.log.emit(f"Unexpected error: {type(e).__name__}: {e}")
            self._checkpoint(
                status="error",
                dataset_idx=start_ds,
                page_idx=start_page,
                processed=processed,
                discovered=discovered,
                downloaded=downloaded,
                skipped=skipped,
                failed=failed,
                fail_reason=str(e),
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
            "Open the page below, complete any age/access confirmation, then click:\n"
            "'I Confirmed, Start Download'."
        )
        info.setWordWrap(True)
        layout.addWidget(info)

        if not WEBENGINE_AVAILABLE:
            label = QLabel("PySide6 WebEngine is not available. Install: pip install PySide6-Addons")
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
        self._last_total_epstein: int = TOTAL_EPSTEIN_FILES
        self._last_global_processed_files: int = 0

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
        t2 = QLabel("Download files to the folder /files")
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

        self.lbl_dataset_info = QLabel(f"Extracting Data Set: 0/{DATASET_MAX}")
        self.lbl_dataset_info.setObjectName("status")
        root.addWidget(self.lbl_dataset_info)

        self.progress = QProgressBar()
        self.progress.setRange(0, 100)
        self.progress.setValue(0)
        root.addWidget(self.progress)

        self.lbl_status = QLabel("Current Data Set files: 0 / 0 (0%)")
        self.lbl_status.setObjectName("status")
        root.addWidget(self.lbl_status)

        self.progress_total = QProgressBar()
        self.progress_total.setRange(0, 100)
        self.progress_total.setValue(0)
        root.addWidget(self.progress_total)

        self.lbl_status_total = QLabel(f"Global files objective: 0 / {TOTAL_EPSTEIN_FILES} (0%)")
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

        ds = int(st.get("dataset_idx") or 1)
        pg = int(st.get("page_idx") or 1)
        reason = st.get("fail_reason") or ""

        msg = QMessageBox(self)
        msg.setIcon(QMessageBox.Question)
        msg.setWindowTitle("Resume previous session")
        msg.setText(
            "A checkpoint was found.\n"
            "Do you want to resume or start over?\n\n"
            f"Last position: Data Set {ds}, page {pg}\n"
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

    def _open_age_dialog(self, target_url: str = ROOT_URL) -> bool:
        if not WEBENGINE_AVAILABLE:
            QMessageBox.critical(
                self,
                "Missing dependency",
                "PySide6 WebEngine is required.\nInstall:\n\npip install PySide6-Addons"
            )
            return False

        self.age_dialog = AgeGateDialog(self, target_url=target_url)
        self.append_log("Manual step required: confirm age/access in the browser window, then click 'I Confirmed, Start Download'.")
        ok = self.age_dialog.exec() == QDialog.Accepted
        if not ok:
            return False

        cookies = self.age_dialog.export_cookies()
        if not cookies:
            QMessageBox.warning(
                self,
                "No cookies captured",
                "No browser cookies were captured.\nConfirm age/access in the page and click again."
            )
            return False

        self.cookie_store.set_all(cookies)
        self.append_log(f"Cookie snapshot captured: {self.cookie_store.count()} cookies.")
        return True

    def start_clicked(self):
        resume_state = self._ask_resume()
        if isinstance(resume_state, dict) and resume_state.get("__cancel__"):
            self.append_log("Startup canceled.")
            return

        target_url = ROOT_URL
        if resume_state:
            ds = int(resume_state.get("dataset_idx") or 1)
            pg = int(resume_state.get("page_idx") or 1)
            target_url = DownloaderWorker._page_url(ds, pg)

        if not self._open_age_dialog(target_url=target_url):
            self.append_log("Age confirmation canceled or incomplete.")
            return

        self.progress.setValue(0)
        self.progress_total.setValue(0)
        self._last_total_epstein = TOTAL_EPSTEIN_FILES
        self._last_global_processed_files = 0
        self.lbl_dataset_info.setText(f"Extracting Data Set: 0/{DATASET_MAX}")
        self.lbl_status.setText("Current Data Set files: 0 / 0 (0%)")
        self.lbl_status_total.setText(f"Global files objective: 0 / {TOTAL_EPSTEIN_FILES} (0%)")
        self.append_log("Session setup...")

        self.btn_start.setEnabled(False)
        self.btn_stop.setEnabled(True)

        out = files_dir()
        self.lbl_output.setText(str(out))

        self.worker_thread = QThread(self)
        self.worker = DownloaderWorker(out, resume_state=resume_state, cookie_store=self.cookie_store)
        self.worker.moveToThread(self.worker_thread)

        self.worker_thread.started.connect(self.worker.run)
        self.worker.log.connect(self.append_log)
        self.worker.progress.connect(self.on_progress)
        self.worker.progress_total.connect(self.on_progress_total)
        self.worker.dataset_info.connect(self.on_dataset_info)
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

    def on_progress(self, current: int, total: int):
        total = max(0, int(total))
        current = max(0, int(current))
        if total <= 0:
            pct = 0
        else:
            pct = int((current / total) * 100)
            pct = max(0, min(100, pct))
        self.progress.setValue(pct)
        self.lbl_status.setText(f"Current Data Set files: {current} / {total} ({pct}%)")

    def on_progress_total(self, current: int, total_epstein: int):
        current = max(0, int(current))
        total_epstein = max(0, int(total_epstein))
        self._last_total_epstein = total_epstein
        self._last_global_processed_files = current

        if total_epstein <= 0:
            self.progress_total.setValue(0)
            self.lbl_status_total.setText(f"Global files objective: {current} / 0 (0%)")
            return

        pct = int((current / total_epstein) * 100)
        pct = max(0, min(100, pct))
        self.progress_total.setValue(pct)
        self.lbl_status_total.setText(
            f"Global files objective: {current} / {total_epstein} ({pct}%)"
        )

    def on_dataset_info(self, dataset_idx: int, total_datasets: int, dataset_processed: int, dataset_target: int):
        dataset_idx = max(DATASET_MIN, min(DATASET_MAX, int(dataset_idx)))
        total_datasets = max(DATASET_MAX, int(total_datasets))
        dataset_processed = max(0, int(dataset_processed))
        dataset_target = max(1, int(dataset_target))
        pct = int((dataset_processed / dataset_target) * 100)
        pct = max(0, min(100, pct))
        self.lbl_dataset_info.setText(f"Extracting Data Set: {dataset_idx}/{total_datasets}")

    def on_auth_required(self, url: str, ds: int, pg: int):
        self.append_log(
            f"Session likely expired at Data Set {ds}, page {pg}. "
            "Re-confirm age/access and resume."
        )

    def on_finished(self, downloaded: int, skipped: int, failed: int, status: str):
        self.btn_start.setEnabled(True)
        self.btn_stop.setEnabled(False)

        processed_final = max(self._last_global_processed_files, 0)
        if self._last_total_epstein > 0:
            pct2 = int((processed_final / self._last_total_epstein) * 100)
            pct2 = max(0, min(100, pct2))
            self.progress_total.setValue(pct2)
            self.lbl_status_total.setText(
                f"Global files objective: {processed_final} / {self._last_total_epstein} ({pct2}%)"
            )

        if status == "completed":
            headline = f"Completed. New: {downloaded} | Existing: {skipped} | Failed: {failed}"
            detail = (
                "Download completed.\n\n"
                f"New: {downloaded}\nExisting: {skipped}\nFailed: {failed}\n\n"
                f"Folder: {files_dir()}"
            )
        elif status == "stopped":
            headline = f"Stopped by user. New: {downloaded} | Existing: {skipped} | Failed: {failed}"
            detail = (
                "Download stopped by user.\n\n"
                f"New: {downloaded}\nExisting: {skipped}\nFailed: {failed}\n\n"
                "Checkpoint saved for resume."
            )
        elif status == "auth_required":
            headline = f"Session expired/blocked. New: {downloaded} | Existing: {skipped} | Failed: {failed}"
            detail = (
                "Session appears blocked by authorization/age gate.\n\n"
                "Please click Start, reconfirm in browser, and resume from checkpoint."
            )
        else:
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
    # must be set before QApplication
    QCoreApplication.setAttribute(Qt.AA_UseSoftwareOpenGL, True)
    QCoreApplication.setAttribute(Qt.AA_ShareOpenGLContexts, True)

    app = QApplication(sys.argv)
    app.setStyle("Fusion")

    w = MainWindow()
    w.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()