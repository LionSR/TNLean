#!/usr/bin/env python3
"""Regression tests for shared badge count-color thresholds."""

import generate_badges
import write_badges
from badge_utils import count_color


def test_generators_share_count_color() -> None:
    assert generate_badges.count_color is count_color
    assert write_badges.count_color is count_color


def test_count_color_boundaries() -> None:
    colors = {
        count: count_color(count, warning_at=100, danger_at=300)
        for count in (0, 1, 99, 100, 299, 300)
    }
    assert colors == {
        0: "brightgreen",
        1: "yellow",
        99: "yellow",
        100: "orange",
        299: "orange",
        300: "red",
    }


if __name__ == "__main__":
    test_generators_share_count_color()
    test_count_color_boundaries()
    print("Badge color tests passed.")
