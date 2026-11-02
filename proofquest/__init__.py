"""proofquest: deterministic lean4game generator from leanblueprint projects."""

from importlib.metadata import PackageNotFoundError, version

try:
    __version__ = version("proofquest")
except PackageNotFoundError:
    # Package is not installed; fallback to a placeholder for development
    __version__ = "0.0.0-dev"
