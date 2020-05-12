from __future__ import annotations
from tea.logging.tea_logger_configuration import TeaLoggerConfiguration
from tea.logging.logging_target import LoggingTarget

import logging
import sys


class TeaLogger:
    __logger_instance: TeaLogger = None

    def __init__(self, logging_level: int, logging_handler: logging.StreamHandler):
        self.__logger = logging.getLogger('tea_logger')
        self.__logger.addHandler(logging_handler)
        self.__logger.setLevel(logging_level)

    @staticmethod
    def initialize_logger(config: TeaLoggerConfiguration) -> TeaLogger:
        if config.logging_target == LoggingTarget.FILE:
            if config.logging_file_target is not None:
                logging_handler = logging.FileHandler(config.logging_file_target)
            else:
                raise AttributeError('When configuring file handler, logging_file_target field is required')
        else:
            logging_handler = logging.StreamHandler(sys.stdout)
        tea_logger = TeaLogger(config.logging_level, logging_handler)
        TeaLogger.__logger_instance = tea_logger
        return tea_logger

    @staticmethod
    def get_logger() -> TeaLogger:
        if TeaLogger.__logger_instance is None:
            default_config = TeaLoggerConfiguration()
            TeaLogger.initialize_logger(default_config)
            TeaLogger.__logger_instance.log_info('Logger was initialized with default configuration.\nUse TeaLogger.initialize_logger to change it.')
        return TeaLogger.__logger_instance

    def log_debug(self, message: str):
        self.__logger.debug(message)

    def log_info(self, message: str):
        self.__logger.info(message)
