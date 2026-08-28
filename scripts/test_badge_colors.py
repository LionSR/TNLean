#!/usr/bin/env python3
"""Regression tests for shared badge count-color thresholds."""

import generate_badges
import write_badges
from badge_utils import axioms_color, count_color, sorries_color


def test_generators_share_count_color() -> None:
    assert generate_badges.count_color is count_color
    assert write_badges.count_color is count_color
    assert generate_badges.sorries_color is sorries_color
    assert write_badges.sorries_color is sorries_color
    assert generate_badges.axioms_color is axioms_color
    assert write_badges.axioms_color is axioms_color


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


def test_endpoint_color_agreement() -> None:
    for count, expected in ((10, "orange"), (50, "red")):
        generated = generate_badges.badge_count_colors(count, 0)["sorries"]
        written = write_badges.badge_count_colors(count, 0)["sorries"]
        assert generated == written == expected

    for count, expected in ((0, "brightgreen"), (1, "red")):
        generated = generate_badges.badge_count_colors(0, count)["axioms"]
        written = write_badges.badge_count_colors(0, count)["axioms"]
        assert generated == written == expected


if __name__ == "__main__":
    test_generators_share_count_color()
    test_count_color_boundaries()
    test_endpoint_color_agreement()
    print("Badge color tests passed.")
