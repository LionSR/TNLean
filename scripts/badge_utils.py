#!/usr/bin/env python3
"""Shared helpers for badge endpoint generators."""

from __future__ import annotations


def count_color(
    count: int,
    *,
    warning_at: int = 1,
    danger_at: int | None = None,
) -> str:
    """Color a nonnegative count using inclusive escalation thresholds."""
    if count == 0:
        return "brightgreen"
    if count < warning_at:
        return "yellow"
    if danger_at is not None and count >= danger_at:
        return "red"
    return "orange"


def sorries_color(count: int) -> str:
    """Color the shared sorries endpoint."""
    return count_color(count, warning_at=10, danger_at=50)


def axioms_color(count: int) -> str:
    """Color the shared axioms endpoint."""
    return "brightgreen" if count == 0 else "red"
