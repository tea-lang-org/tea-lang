
from dataclasses import dataclass
from tea.logging.logging_target import LoggingTarget
from typing import Optional
import logging


@dataclass
class TeaLoggerConfiguration:
    logging_level: int = logging.INFO
    logging_target: LoggingTarget = LoggingTarget.STDOUT
    logging_file_target: Optional[str] = None
