"""Small shared helpers for TNLean's plasTeX packages."""

from __future__ import annotations

from typing import Any


def stringify_tex_item(obj: Any) -> str:
    """Extract a stable string from a plasTeX token/list item."""

    return getattr(obj, "source", getattr(obj, "textContent", str(obj))).strip()
