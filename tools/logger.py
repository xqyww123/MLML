import logging
import os
import sys
from typing import Optional, TextIO

RESET = "\033[0m"
COLORS = {
    logging.DEBUG: "\033[36m",     # Cyan
    logging.INFO: "\033[32m",      # Green
    logging.WARNING: "\033[33m",   # Yellow
    logging.ERROR: "\033[31m",     # Red
    logging.CRITICAL: "\033[41m",  # Red background
}

_configured = False


class ColorFormatter(logging.Formatter):
    def __init__(
        self,
        fmt: Optional[str] = None,
        datefmt: Optional[str] = None,
        style: str = "%",
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
    global _configured
    root_logger = logging.getLogger()
    effective_stream = stream or sys.stdout
    if _configured:
        root_logger.setLevel(level)
        for handler in root_logger.handlers:
            handler.setLevel(level)
            if isinstance(handler, logging.StreamHandler) and handler.stream is effective_stream:
                handler.setFormatter(ColorFormatter(fmt=fmt, datefmt=datefmt, stream=effective_stream))
        return

    handler = logging.StreamHandler(effective_stream)
    handler.setLevel(level)
    formatter = ColorFormatter(fmt=fmt, datefmt=datefmt, stream=effective_stream)
    handler.setFormatter(formatter)

    root_logger.handlers.clear()
    root_logger.setLevel(level)
    root_logger.addHandler(handler)
    _configured = True

