#!/usr/bin/env python3
"""Reject new pass-through declarations: one statement under a second name.

A pass-through is a declaration whose whole body applies another declaration
to its own arguments in order.  ``docs/many_body_circuit_architecture.md``
forbids them: the caller uses the original name.

The rule is lexical and deliberately narrow.  A declaration is reported exactly
when all of the following hold, after Lean comments are removed.

1. It is a ``theorem``, ``lemma``, ``def`` or ``abbrev`` that starts in the
   first column of a module below ``TNLean/`` and outside ``TNLean/Archive``,
   after any attributes and the modifiers ``private``, ``protected``,
   ``public``, ``noncomputable`` and ``nonrec``.  An ``instance``, an
   ``example``, a structure field and a declaration nested in a ``where`` block
   are never reported.
2. Between its name and its ``:=`` there are only bracketed binders and an
   optional type.  It has at least one explicit binder ``(x y : T)``, no binder
   has a default value, and it is not followed by ``where``,
   ``termination_by`` or ``decreasing_by``.
3. Its body is ``F x₁ … xₙ``, ``by exact F x₁ … xₙ`` or
   ``by simpa using F x₁ … xₙ``, where ``x₁ … xₙ`` are exactly the names of
   its explicit binders, all of them, in the order they are bound, and
   nothing else follows.
4. ``F`` is a name with a namespace, such as ``Kraus.blockPhysDim``, written
   without ``@``.  Its last component is the last component of the name of
   the declaration, and each earlier component begins with a capital letter
   and is neither a binder of the declaration nor bound by a ``variable``
   command of the module.  So ``F`` names a declaration of another namespace,
   not a field or a consequence of a hypothesis such as ``h.trans x``.

Hence a declaration that reorders, drops, repeats or transforms an argument,
supplies a named or implicit argument, uses a section variable as an argument,
or does anything besides the one application, is not a pass-through here.
Neither is a lemma about a definition that is proved by one application of a
differently named fact about what the definition unfolds to, nor a definition
that gives a new name to an application of another one: only the same name in
a second namespace is reported, the form a declaration takes when its content
has moved to another namespace and a forwarding copy is left behind.  The
check does not compare the two statements.

An entry is the full name of the declaration, built from the enclosing
``namespace`` commands, so that moving a module does not change it.

``PASS_THROUGH`` is a ratchet.  It lists the pass-throughs present when the
check was introduced.  A new pass-through fails, and so does an entry that is
no longer one: remove it in the change that deletes the declaration.  With
``--base-ref`` the set is also compared with its value at the merge base, and
an added entry fails, so a new pass-through cannot be admitted by recording
it.
"""

from __future__ import annotations

import argparse
import re
from collections.abc import Iterator, Mapping
from pathlib import Path

from check_import_layers import ratchet_errors, records_at_merge_base, tracked_sources
from lean_import_syntax import strip_lean_comments

CHECKER_PATH = "scripts/check_pass_through_declarations.py"

IDENT = r"[^\W\d][\w'!?]*"
NAME = rf"{IDENT}(?:\.{IDENT})*"
ATTRIBUTES = r"(?:@\[[^\]]*\]\s*)*"
DECLARATION_RE = re.compile(
    rf"{ATTRIBUTES}(?:(?:private|protected|public|noncomputable|nonrec)\s+)*"
    rf"(?:theorem|lemma|def|abbrev)\s+({NAME})(?=[\s(\[{{⦃:])"
)
NAMESPACE_RE = re.compile(rf"namespace\s+({NAME})\s*$")
SCOPE_RE = re.compile(
    rf"{ATTRIBUTES}(?:(?:public|private|noncomputable|meta)\s+)*(?:section|mutual)\b"
)
END_RE = re.compile(r"end\b")
VARIABLE_RE = re.compile(r"variable\b")
CONTINUATION_RE = re.compile(r"(?:where|termination_by|decreasing_by)\b")
BODY_RE = re.compile(rf"(?:by\s+(?:exact|simpa\s+using)\s+)?({NAME})((?:\s+{IDENT})*)")
OPENING = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSING = frozenset(OPENING.values())


def commands(uncommented: str) -> list[str]:
    """Split a source into the blocks that start in the first column."""
    blocks: list[list[str]] = []
    for line in uncommented.splitlines():
        if line[:1].strip():
            blocks.append([line])
        elif blocks:
            blocks[-1].append(line)
    return ["\n".join(block) for block in blocks]


def matching_close(text: str, start: int) -> int | None:
    """Return the index of the bracket that closes the one at ``start``."""
    expected: list[str] = []
    for index in range(start, len(text)):
        character = text[index]
        if character in OPENING:
            expected.append(OPENING[character])
        elif character in CLOSING:
            if not expected or expected.pop() != character:
                return None
            if not expected:
                return index
    return None


def top_level_find(text: str, token: str, start: int = 0) -> int | None:
    """Return the first index at or after ``start`` of ``token`` outside all brackets."""
    index = start
    while index < len(text):
        if text[index] in OPENING:
            close = matching_close(text, index)
            if close is None:
                return None
            index = close + 1
        elif text.startswith(token, index):
            return index
        else:
            index += 1
    return None


def binder_names(group: str) -> list[str] | None:
    """Return the names bound by the inside of one binder group.

    ``None`` means the group is not a plain list of names with an optional type.
    """
    if top_level_find(group, ":=") is not None:
        return None
    colon = top_level_find(group, ":")
    names = (group if colon is None else group[:colon]).split()
    if not names or not all(re.fullmatch(IDENT, name) for name in names):
        return None
    return names


def header(block: str, start: int) -> tuple[list[str], set[str], str] | None:
    """Parse the binders after a declaration name.

    Returns the explicit binder names in order, the names of all binders, and
    the body after ``:=``; ``None`` if the declaration has another form.
    """
    explicit: list[str] = []
    bound: set[str] = set()
    index = start
    while True:
        while index < len(block) and block[index].isspace():
            index += 1
        if index >= len(block):
            return None
        character = block[index]
        if character in ("(", "{", "⦃", "["):
            close = matching_close(block, index)
            if close is None:
                return None
            group = block[index + 1 : close]
            names = binder_names(group)
            if names is None:
                if character != "[":
                    return None
                names = []
            elif character == "[" and top_level_find(group, ":") is None:
                # ``[NeZero d]`` binds no name: ``NeZero`` is a class, not a binder.
                names = []
            bound.update(names)
            if character == "(":
                explicit += names
            index = close + 1
        elif block.startswith(":=", index):
            return explicit, bound, block[index + 2 :]
        elif character == ":":
            assign = top_level_find(block, ":=", index + 1)
            if assign is None:
                return None
            return explicit, bound, block[assign + 2 :]
        else:
            return None


def variable_names(blocks: list[str]) -> set[str]:
    """Return every name bound by a ``variable`` command of a module."""
    names: set[str] = set()
    for block in blocks:
        if VARIABLE_RE.match(block) is None:
            continue
        index = 0
        while index < len(block):
            if block[index] in OPENING:
                close = matching_close(block, index)
                if close is None:
                    break
                group = block[index + 1 : close]
                if block[index] != "[" or top_level_find(group, ":") is not None:
                    names.update(binder_names(group) or [])
                index = close + 1
            else:
                index += 1
    return names


def pass_throughs_of_source(source: str) -> Iterator[str]:
    """Yield the full names of the pass-through declarations of one module."""
    uncommented, error = strip_lean_comments(source)
    if error is not None:
        return
    blocks = commands(uncommented)
    variables = variable_names(blocks)
    scopes: list[str | None] = []
    for position, block in enumerate(blocks):
        namespace = NAMESPACE_RE.match(block.strip())
        if namespace is not None:
            scopes.append(namespace.group(1))
            continue
        if SCOPE_RE.match(block) is not None:
            scopes.append(None)
            continue
        if END_RE.match(block) is not None:
            if scopes:
                scopes.pop()
            continue
        declaration = DECLARATION_RE.match(block)
        if declaration is None:
            continue
        if position + 1 < len(blocks) and CONTINUATION_RE.match(blocks[position + 1]):
            continue
        parsed = header(block, declaration.end())
        if parsed is None:
            continue
        explicit, bound, body = parsed
        application = BODY_RE.fullmatch(body.strip())
        if application is None or not explicit:
            continue
        function, arguments = application.group(1), application.group(2).split()
        *namespaces, last = function.split(".")
        name = declaration.group(1)
        if not namespaces or last != name.split(".")[-1]:
            continue
        if any(not part[0].isupper() or part in bound | variables for part in namespaces):
            continue
        if arguments != explicit:
            continue
        if name.startswith("_root_."):
            yield name[len("_root_.") :]
        else:
            yield ".".join([scope for scope in scopes if scope is not None] + [name])


def pass_throughs(sources: Mapping[str, str]) -> dict[str, str]:
    """Return each pass-through declaration with the module that states it."""
    found: dict[str, str] = {}
    for module in sorted(sources):
        for name in pass_throughs_of_source(sources[module]):
            found.setdefault(name, module)
    return found


# Existing pass-throughs only, by full declaration name.  Never add an entry:
# use the original declaration at the call site.
PASS_THROUGH: frozenset[str] = frozenset(
    {
        "MPSChainTensor.rectangularTransfer_apply",
        "MPSPreparation.permOp_conjTranspose",
        "MPSTensor.HasNNCPHGroundSpaces.hasParentHamiltonianGroundSpaceSpanning",
        "MPSTensor.blockPhysDim",
        "MPSTensor.blockPhysDim_eq_pow",
        "MPSTensor.blockTensor",
        "MPSTensor.decodeBlock",
        "MPSTensor.decodeBlockEquiv",
        "MPSTensor.decodeBlock_decodeBlockEquiv_symm",
        "MPSTensor.evalWord_blockTensor",
        "MPSTensor.evalWord_replicate",
        "MPSTensor.flattenBlockedWord",
        "MPSTensor.flattenBlockedWord_cons",
        "MPSTensor.flattenBlockedWord_nil",
        "MPSTensor.isNBlkInjective_iff_blockTensor_isInjective",
        "MPSTensor.length_flattenBlockedWord",
        "MPSTensor.length_wordOfBlock",
        "MPSTensor.singleBlockEquiv",
        "MPSTensor.wordOfBlock",
        "QuantumCircuit.IsBlockedLocalChannelConversion.mono",
        "QuantumCircuit.IsBlockedLocalChannelConversion.trans",
        "TNLean.Algebra.RestrictedFusionGauge.fusionGauge_one",
        "TNLean.Algebra.RestrictedScalarGauge.gauge_one",
        "TNLean.Algebra.ScalarThreeCochain.IsTrivialGaugeClass.comap",
        "TNLean.PEPS.EncodedFrame.PairwiseDisjointOuter.of_cons",
    }
)


def check_pass_throughs(
    sources: Mapping[str, str],
    recorded: frozenset[str] = PASS_THROUGH,
    base: frozenset[str] | None = None,
) -> list[str]:
    """Return the error messages of the check; an empty list means it passes."""
    current = pass_throughs(sources)
    return ratchet_errors(
        frozenset(current),
        recorded,
        base,
        new="Declaration only applies another declaration to its own arguments",
        stale="Declaration is no longer a pass-through but is listed in PASS_THROUGH; remove it",
        added="Entry added to PASS_THROUGH; this set may only shrink",
        describe=lambda name: f"{name} ({current[name]})" if name in current else name,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject new declarations that only rename another declaration."
    )
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--base-ref",
        help="ref whose merge base with HEAD fixes the entries that may remain",
    )
    parser.add_argument(
        "--print-record", action="store_true", help="print the current pass-throughs and exit"
    )
    args = parser.parse_args()
    root = args.root.resolve()

    sources = tracked_sources(root)
    if args.print_record:
        for name in sorted(pass_throughs(sources)):
            print(f'        "{name}",')
        return 0

    base: frozenset[str] | None = None
    if args.base_ref is not None:
        try:
            base = records_at_merge_base(root, args.base_ref, CHECKER_PATH, ("PASS_THROUGH",))[
                "PASS_THROUGH"
            ]
        except (SyntaxError, ValueError) as error:
            print(f"::error title=Pass-through check failed::{error}")
            return 1

    errors = check_pass_throughs(sources, PASS_THROUGH, base)
    for message in errors:
        print(f"::error title=Pass-through declaration policy::{message}")
    if errors:
        print(
            "A declaration must not restate another one under a second name, and "
            "PASS_THROUGH may only shrink. Use the original declaration at the call "
            "sites; see docs/many_body_circuit_architecture.md."
        )
        return 1
    print(f"No new pass-through declarations ({len(PASS_THROUGH)} recorded ones remain).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
