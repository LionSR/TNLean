"""Small shared helpers for TNLean's plasTeX packages.

This module keeps no plasTeX import of its own, so the generated-page
regression can read the row-break rule below without loading -- and thereby
patching -- a renderer it is meant to be checking.
"""

from __future__ import annotations

import re
from typing import Any


# The named lengths a row break may be given.  A control word outside this
# list is a mathematical symbol, not a dimension: \alpha and \sum open a row,
# they do not measure the gap above it.
_NAMED_LENGTHS = (
    "jot",
    "baselineskip",
    "lineskip",
    "parskip",
    "smallskipamount",
    "medskipamount",
    "bigskipamount",
    "abovedisplayskip",
    "belowdisplayskip",
    "abovedisplayshortskip",
    "belowdisplayshortskip",
    "topsep",
    "arraycolsep",
    "tabcolsep",
    "arrayrulewidth",
    "doublerulesep",
    "textwidth",
    "textheight",
    "linewidth",
    "columnwidth",
    "parindent",
    "fboxsep",
    "fboxrule",
    "extrarowheight",
)

# What may stand in brackets after a row break and mean the gap to the next
# row: a number with a unit, or one of the named lengths with an optional
# factor in front of it.  Anything else there is mathematics, and reading it
# as a gap turns the row into an error box.
ROW_BREAK_LENGTH = re.compile(
    r"""\s*[-+]?\s*(
          (\d+(\.\d*)?|\.\d+)\s*(pt|pc|in|bp|cm|mm|dd|cc|sp|ex|em|mu)
        | ((\d+(\.\d*)?|\.\d+)\s*)?\\(""" + "|".join(_NAMED_LENGTHS) + r""")
        )\s*$""",
    re.VERBOSE,
)


def stringify_tex_item(obj: Any) -> str:
    """Extract a stable string from a plasTeX token/list item."""

    return getattr(obj, "source", getattr(obj, "textContent", str(obj))).strip()
