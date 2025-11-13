import logging
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Literal, Optional, TextIO

RESET = "\033[0m"
COLORS = {
    logging.DEBUG: "\033[36m",     # Cyan
    logging.INFO: "\033[32m",      # Green
    logging.WARNING: "\033[33m",   # Yellow
    logging.ERROR: "\033[31m",     # Red
    logging.CRITICAL: "\033[41m",  # Red background
}

LOG_DIR = Path(__file__).resolve().parent.parent / "cache" / "logs"

_configured = False
_console_handler: Optional[logging.StreamHandler] = None
_file_handler: Optional[logging.FileHandler] = None
_log_file_path: Optional[Path] = None


class ColorFormatter(logging.Formatter):
    def __init__(
        self,
        fmt: Optional[str] = None,
        datefmt: Optional[str] = None,
        style: Literal["%", "{", "$"] = "%",
        stream: Optional[TextIO] = None,
    ):
        super().__init__(fmt=fmt, datefmt=datefmt, style=style)
        self.stream = stream or sys.stdout
        self.use_color = self._stream_supports_color(self.stream) and self._colors_enabled()

    @staticmethod
    def _colors_enabled() -> bool:
        return os.environ.get("NO_COLOR") is None

    @staticmethod
    def _stream_supports_color(stream: Optional[TextIO]) -> bool:
        if stream is None:
            return False
        if hasattr(stream, "isatty") and stream.isatty():
            return True
        if "PYCHARM_HOSTED" in os.environ:
            return True
        return False

    def format(self, record: logging.LogRecord) -> str:
        message = super().format(record)
        if not self.use_color:
            return message
        color = COLORS.get(record.levelno)
        if color:
            return f"{color}{message}{RESET}"
        return message


def configure_logging(
    level: int = logging.INFO,
    fmt: str = "%(asctime)s - %(levelname)s - %(message)s",
    datefmt: Optional[str] = "%Y-%m-%d %H:%M:%S",
    stream: Optional[TextIO] = None,
) -> None:
    global _configured, _console_handler, _file_handler, _log_file_path
    root_logger = logging.getLogger()
    effective_stream = stream or sys.stdout
    LOG_DIR.mkdir(parents=True, exist_ok=True)

    if _log_file_path is None:
        timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        _log_file_path = LOG_DIR / f"{timestamp}.log"

    if (
        _console_handler is None
        or not isinstance(_console_handler, logging.StreamHandler)
        or _console_handler.stream is not effective_stream
    ):
        _console_handler = logging.StreamHandler(effective_stream)

    if _file_handler is None or getattr(_file_handler, "baseFilename", None) != str(_log_file_path):
        _file_handler = logging.FileHandler(_log_file_path, encoding="utf-8")

    _console_handler.setLevel(level)
    _file_handler.setLevel(level)

    console_formatter = ColorFormatter(fmt=fmt, datefmt=datefmt, stream=effective_stream)
    file_formatter = logging.Formatter(fmt=fmt, datefmt=datefmt)
    _console_handler.setFormatter(console_formatter)
    _file_handler.setFormatter(file_formatter)

    if _configured:
        root_logger.setLevel(level)
        for handler in list(root_logger.handlers):
            root_logger.removeHandler(handler)
    else:
        root_logger.handlers.clear()
        root_logger.setLevel(level)

    root_logger.addHandler(_console_handler)
    root_logger.addHandler(_file_handler)
    _configured = True

