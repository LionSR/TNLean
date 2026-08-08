"""Freeze exact semantic sites for active RMP physical dimensions."""

from __future__ import annotations

import json
import re
import stat
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Iterable, Mapping, Sequence

from tenkzlib.dimensions import (
    DIMENSION_COMMAND_OWNERS,
    DIMENSION_INVOCATION_NAMES,
    DIMENSION_OPTION_CONTAINER_KEYS,
    DIMENSION_OPTION_OWNERS,
    DIMENSION_RE,
    DIMENSION_SCOPE_NAMES,
    DimensionOwner,
    DimensionOwnerSite,
    DimensionReport,
    DimensionScope,
    collect_dimension_report,
    scan_case_constructs,
    scan_case_dimension_sites,
    scan_case_invocations,
    scan_case_scopes,
    validate_dimension_report,
)
from tenkzlib.texcase import (
    DRAWING_CONSTRUCT_NAMES,
    PICTURE_ENVIRONMENT_NAMES,
    Construct,
    is_static_control_word_letter,
)


DIMENSION_INVENTORY_SCHEMA_VERSION = 5
DEFAULT_DIMENSION_INVENTORY = Path("tests/tenkz/rmp/dimension-ownership.json")
_SITE_FIELDS = {"site", "owner", "literals"}
_CASE_FIELDS = {"scopes", "constructs", "invocations", "sites"}
_ACTIVE_OWNERS = {
    DimensionOwner.METRIC,
    DimensionOwner.FRAME,
    DimensionOwner.ROUTE,
    DimensionOwner.LAYOUT,
}
# ``tenkzeq`` is a lexical wrapper only.  Picture environments and command
# body scopes are represented in both the scope and invocation inventories.
_INVOCATION_SCOPE_NAMES = DIMENSION_SCOPE_NAMES & DIMENSION_INVOCATION_NAMES
_SCOPE_NAME_PATTERN = "|".join(
    re.escape(name)
    for name in sorted(DIMENSION_SCOPE_NAMES, key=len, reverse=True)
)
_CONSTRUCT_NAME_PATTERN = "|".join(
    re.escape(name)
    for name in sorted(DRAWING_CONSTRUCT_NAMES, key=len, reverse=True)
)
_INVOCATION_NAME_PATTERN = "|".join(
    re.escape(name)
    for name in sorted(DIMENSION_INVOCATION_NAMES, key=len, reverse=True)
)
_PATH_NAME_PATTERN = "|".join(
    re.escape(name)
    for name in sorted(
        DIMENSION_SCOPE_NAMES | DIMENSION_INVOCATION_NAMES,
        key=len,
        reverse=True,
    )
)
_ORDINAL_PATTERN = r"@[1-9][0-9]*"
_SCOPE_SEGMENT_PATTERN = rf"(?:{_SCOPE_NAME_PATTERN}){_ORDINAL_PATTERN}"
_CONSTRUCT_SEGMENT_PATTERN = (
    rf"(?:{_CONSTRUCT_NAME_PATTERN}){_ORDINAL_PATTERN}"
)
_INVOCATION_SEGMENT_PATTERN = (
    rf"(?:{_INVOCATION_NAME_PATTERN}){_ORDINAL_PATTERN}"
)
_CONSTRUCT_ANCHOR_PATTERN = (
    rf"(?:{_SCOPE_SEGMENT_PATTERN}/)*{_CONSTRUCT_SEGMENT_PATTERN}"
)
_INVOCATION_PATH_PATTERN = (
    rf"(?:{_SCOPE_SEGMENT_PATTERN}/)*{_INVOCATION_SEGMENT_PATTERN}"
)
_INVOCATION_ANCHOR_PATTERN = (
    rf"{_CONSTRUCT_ANCHOR_PATTERN}::{_INVOCATION_PATH_PATTERN}"
)
_PATH_SEGMENT_RE = re.compile(
    r"(?P<name>" + _PATH_NAME_PATTERN + r")"
    r"@(?P<ordinal>[1-9][0-9]*)"
)
_SITE_KEY_RE = re.compile(
    rf"(?P<invocation_anchor>{_INVOCATION_ANCHOR_PATTERN})/"
    r"(?P<kind>command|option):(?P<skeleton>.+)"
)
_DUPLICATE_SUFFIX_RE = re.compile(r"^(.*)#occurrence=([1-9][0-9]*)$")
_COMMAND_SITE_RE = re.compile(
    r"\\(?P<command>" + "|".join(DIMENSION_COMMAND_OWNERS) + r")"
    r"(?P<star>\*)?(?=[\[{])"
)
_OPTION_SITE_OWNERS = {
    re.sub(r"\s+", "", key): owner
    for key, owner in DIMENSION_OPTION_OWNERS.items()
}
_OPTION_CONTAINER_KEYS = {
    container: frozenset(re.sub(r"\s+", "", key) for key in keys)
    for container, keys in DIMENSION_OPTION_CONTAINER_KEYS.items()
}
_OPTION_SITE_RE = re.compile(
    r"(?P<container>"
    + "|".join(
        re.escape(container)
        for container in sorted(_OPTION_CONTAINER_KEYS, key=len, reverse=True)
    )
    + r")/(?P<option>"
    + "|".join(sorted(_OPTION_SITE_OWNERS, key=len, reverse=True))
    + r")="
)


class DimensionInventoryError(ValueError):
    """The exact RMP dimension inventory is absent, invalid, or stale."""


@dataclass(frozen=True)
class DimensionInventorySite:
    """One normalized owner-site vector, with an ephemeral source line."""

    site: str
    owner: DimensionOwner
    literals: tuple[str, ...]
    line: int | None = field(default=None, compare=False)


@dataclass(frozen=True)
class DimensionInventoryCase:
    """Ordered dimension-bearing sites in one source case."""

    path: Path
    scopes: tuple[str, ...]
    constructs: tuple[str, ...]
    invocations: tuple[str, ...]
    sites: tuple[DimensionInventorySite, ...]


@dataclass(frozen=True)
class DimensionInventory:
    """Versioned, case-grouped exact active-dimension inventory."""

    cases: tuple[DimensionInventoryCase, ...]
    source_end_lines: tuple[tuple[Path, int], ...] = field(
        default=(), compare=False, repr=False
    )

    @property
    def case_count(self) -> int:
        return len(self.cases)

    @property
    def site_count(self) -> int:
        return sum(len(case.sites) for case in self.cases)

    @property
    def construct_count(self) -> int:
        return sum(len(case.constructs) for case in self.cases)

    @property
    def scope_count(self) -> int:
        return sum(len(case.scopes) for case in self.cases)

    @property
    def invocation_count(self) -> int:
        return sum(len(case.invocations) for case in self.cases)

    @property
    def dimension_count(self) -> int:
        return sum(len(site.literals) for case in self.cases for site in case.sites)


def normalize_dimension_literal(literal: str) -> str:
    """Normalize only lexical TeX-unit spelling, retaining the authored value."""
    return re.sub(r"\s+", "", literal).lower()


def _normalize_site_tokens(source: str) -> str:
    """Serialize TeX tokens without erasing whitespace inside arguments."""
    output: list[str] = []
    # A bracket frame carries ``False``/``True`` while parsing a structural
    # option list and ``None`` when the bracket itself belongs to a value.
    # Braces, parentheses, and value brackets are token-list contexts whose
    # whitespace must survive recursively.
    group_stack: list[tuple[str, bool | None]] = []
    top_option_value = False
    index = 0
    while index < len(source):
        character = source[index]
        if character == "\\":
            output.append(character)
            index += 1
            if index >= len(source):
                break
            if not is_static_control_word_letter(source[index]):
                output.append(source[index])
                index += 1
                continue
            while (
                index < len(source)
                and is_static_control_word_letter(source[index])
            ):
                output.append(source[index])
                index += 1
            whitespace_end = index
            while whitespace_end < len(source) and source[whitespace_end].isspace():
                whitespace_end += 1
            # Preserve a canonical separator only when dropping it would merge
            # the following letter into the control-word token.
            if (
                whitespace_end > index
                and whitespace_end < len(source)
                and is_static_control_word_letter(source[whitespace_end])
            ):
                output.append(" ")
            index = whitespace_end
            continue
        if character in "[{(":
            if character == "[":
                in_token_list = any(
                    opener in "{(" or (opener == "[" and state is None)
                    for opener, state in group_stack
                )
                in_option_value = (
                    top_option_value
                    if not group_stack
                    else group_stack[-1] == ("[", True)
                )
                state: bool | None = (
                    None if in_token_list or in_option_value else False
                )
                group_stack.append((character, state))
            else:
                group_stack.append((character, None))
            output.append(character)
            index += 1
            continue
        if character in "]})":
            opener = {"]": "[", "}": "{", ")": "("}[character]
            if group_stack and group_stack[-1][0] == opener:
                group_stack.pop()
            output.append(character)
            index += 1
            continue
        if character == "=" and (
            not group_stack
            or (group_stack[-1][0] == "[" and group_stack[-1][1] is not None)
        ):
            if group_stack:
                group_stack[-1] = ("[", True)
            else:
                top_option_value = True
            output.append(character)
            index += 1
            continue
        if character == "," and (
            not group_stack
            or (group_stack[-1][0] == "[" and group_stack[-1][1] is not None)
        ):
            if group_stack:
                group_stack[-1] = ("[", False)
            else:
                top_option_value = False
            output.append(character)
            index += 1
            continue
        if character.isspace():
            whitespace_end = index + 1
            while (
                whitespace_end < len(source)
                and source[whitespace_end].isspace()
            ):
                whitespace_end += 1
            following = source[whitespace_end : whitespace_end + 1]
            in_token_list = any(
                opener in "{(" or (opener == "[" and state is None)
                for opener, state in group_stack
            )
            in_option_value = (
                (
                    top_option_value
                    if not group_stack
                    else group_stack[-1] == ("[", True)
                )
                and output
                and output[-1] not in "[=, "
                and following not in ("", "]", ",")
            )
            # Command separators, option keys, delimiters, and surrounding
            # option whitespace are structural. One canonical space remains
            # inside token-list arguments and actual unbraced option values.
            if (in_token_list or in_option_value) and output[-1] != " ":
                output.append(" ")
            index = whitespace_end
            continue
        output.append(character)
        index += 1
    return "".join(output)


def _encode_authored_site_text(source: str) -> str:
    """Escape marker syntax before generated placeholders are inserted."""
    return (
        source.replace("%", "%25")
        .replace("#", "%23")
        .replace("<", "%3C")
        .replace(">", "%3E")
    )


def _site_skeleton(site: DimensionOwnerSite) -> str:
    """Erase values while distinguishing this site from nested owner sites."""
    owned_offsets = frozenset(
        occurrence.offset for occurrence in site.occurrences
    )
    parts: list[str] = []
    position = 0
    for match in DIMENSION_RE.finditer(site.source):
        parts.append(
            _encode_authored_site_text(site.source[position : match.start()])
        )
        source_offset = site.source_offsets[match.start()]
        parts.append(
            "<dimension>"
            if source_offset in owned_offsets
            else "<nested-dimension>"
        )
        position = match.end()
    parts.append(_encode_authored_site_text(site.source[position:]))
    return _normalize_site_tokens("".join(parts))


def _narrowest_construct_index(
    constructs: Sequence[Construct], offset: int
) -> int | None:
    """Return the innermost picture construct containing one source offset."""
    candidates = [
        (index, construct)
        for index, construct in enumerate(constructs)
        if construct.start <= offset < construct.end
    ]
    if not candidates:
        return None
    index, _construct = min(
        candidates,
        key=lambda item: (
            item[1].end - item[1].start,
            -item[1].start,
            item[0],
        ),
    )
    return index


def _scope_path_at(
    scopes: Sequence[DimensionScope],
    paths: Mapping[tuple[int, str], tuple[str, ...]],
    offset: int,
) -> tuple[str, ...]:
    """Return the path of the narrowest PICTURE scope containing an offset."""
    candidates = [
        scope
        for scope in scopes
        if scope.body_start <= offset < scope.body_end
    ]
    if not candidates:
        return ()
    scope = min(
        candidates,
        key=lambda candidate: (
            candidate.body_end - candidate.body_start,
            -candidate.body_start,
            candidate.start,
        ),
    )
    key = (scope.start, scope.name)
    try:
        return paths[key]
    except KeyError as exc:
        raise DimensionInventoryError(
            "PICTURE scope ancestry is not in source order"
        ) from exc


def _path_text(path: Sequence[str]) -> str:
    return "/".join(path)


def _case_inventory(path: Path, source: str) -> DimensionInventoryCase | None:
    owner_sites = scan_case_dimension_sites(path, source)
    if not owner_sites:
        return None
    constructs = scan_case_constructs(source)
    assigned: list[tuple[DimensionOwnerSite, int]] = []
    for owner_site in owner_sites:
        construct_index = _narrowest_construct_index(
            constructs, owner_site.offset
        )
        if construct_index is None:
            raise DimensionInventoryError(
                f"{path.as_posix()}:{owner_site.line}: dimension owner site is "
                "outside a tenkz environment"
            )
        assigned.append((owner_site, construct_index))

    scopes = scan_case_scopes(source)
    scope_paths: dict[tuple[int, str], tuple[str, ...]] = {}
    scope_counts: Counter[tuple[tuple[str, ...], str]] = Counter()
    scope_anchors: list[str] = []
    for scope in scopes:
        parent_path = _scope_path_at(scopes, scope_paths, scope.start)
        count_key = (parent_path, scope.name)
        scope_counts[count_key] += 1
        scope_path = parent_path + (
            f"{scope.name}@{scope_counts[count_key]}",
        )
        scope_paths[(scope.start, scope.name)] = scope_path
        scope_anchors.append(_path_text(scope_path))

    construct_counts: Counter[tuple[tuple[str, ...], str]] = Counter()
    anchors: list[str] = []
    for construct in constructs:
        scope_key = (construct.start, construct.name)
        if scope_key in scope_paths:
            construct_path = scope_paths[scope_key]
        else:
            parent_path = _scope_path_at(
                scopes, scope_paths, construct.start
            )
            count_key = (parent_path, construct.name)
            construct_counts[count_key] += 1
            construct_path = parent_path + (
                f"{construct.name}@{construct_counts[count_key]}",
            )
        anchors.append(_path_text(construct_path))

    construct_container_by_row = {
        (index, construct.start, construct.name): anchors[index]
        for index, construct in enumerate(constructs)
    }
    invocation_rows = set(construct_container_by_row)
    for invocation in scan_case_invocations(source):
        construct_index = _narrowest_construct_index(
            constructs, invocation.offset
        )
        if construct_index is None:
            continue
        invocation_rows.add((construct_index, invocation.offset, invocation.name))
    sorted_invocations = sorted(
        invocation_rows, key=lambda row: (row[1], row[0], row[2])
    )
    invocation_counts: Counter[
        tuple[int, tuple[str, ...], str]
    ] = Counter()
    invocation_anchors: list[str] = []
    anchor_by_invocation: dict[tuple[int, int, str], str] = {}
    for construct_index, offset, name in sorted_invocations:
        key = (construct_index, offset, name)
        construct_container = construct_container_by_row.get(key)
        if construct_container is not None:
            invocation_path = construct_container
        else:
            scope_key = (offset, name)
            if scope_key in scope_paths:
                invocation_path_segments = scope_paths[scope_key]
            else:
                parent_path = _scope_path_at(scopes, scope_paths, offset)
                count_key = (construct_index, parent_path, name)
                invocation_counts[count_key] += 1
                invocation_path_segments = parent_path + (
                    f"{name}@{invocation_counts[count_key]}",
                )
            invocation_path = _path_text(invocation_path_segments)
        anchor = f"{anchors[construct_index]}::{invocation_path}"
        anchor_by_invocation[key] = anchor
        invocation_anchors.append(anchor)

    base_rows: list[tuple[str, DimensionOwner, tuple[str, ...], int]] = []
    for owner_site, construct_index in assigned:
        invocation_key = (
            construct_index,
            owner_site.invocation_offset,
            owner_site.invocation_name,
        )
        invocation_anchor = anchor_by_invocation.get(invocation_key)
        if invocation_anchor is None:
            raise DimensionInventoryError(
                f"{path.as_posix()}:{owner_site.line}: dimension owner site "
                "lacks an executed invocation anchor"
            )
        skeleton = _site_skeleton(owner_site)
        if not skeleton:
            raise DimensionInventoryError(
                f"{path.as_posix()}:{owner_site.line}: empty dimension site skeleton"
            )
        if owner_site.kind == "option":
            if owner_site.option_container is None:
                raise DimensionInventoryError(
                    f"{path.as_posix()}:{owner_site.line}: option dimension site "
                    "lacks its owning container"
                )
            skeleton = f"{owner_site.option_container}/{skeleton}"
        elif owner_site.option_container is not None:
            raise DimensionInventoryError(
                f"{path.as_posix()}:{owner_site.line}: non-option dimension site "
                "has an option container"
            )
        base_site = f"{invocation_anchor}/{owner_site.kind}:{skeleton}"
        literals = tuple(
            normalize_dimension_literal(occurrence.literal)
            for occurrence in owner_site.occurrences
        )
        base_rows.append((base_site, owner_site.owner, literals, owner_site.line))

    totals = Counter(row[0] for row in base_rows)
    seen: Counter[str] = Counter()
    sites: list[DimensionInventorySite] = []
    for base_site, owner, literals, line in base_rows:
        seen[base_site] += 1
        site = base_site
        if totals[base_site] > 1:
            site += f"#occurrence={seen[base_site]}"
        sites.append(DimensionInventorySite(site, owner, literals, line))
    return DimensionInventoryCase(
        path,
        tuple(scope_anchors),
        tuple(anchors),
        tuple(invocation_anchors),
        tuple(sites),
    )


def build_dimension_inventory_from_sources(
    sources: Mapping[Path, str],
) -> DimensionInventory:
    """Build an inventory from repo-relative case sources."""
    canonical_sources: list[tuple[Path, str]] = []
    seen: set[Path] = set()
    for path, source in sources.items():
        canonical = _canonical_inventory_case_path(path.as_posix(), "source path")
        if canonical in seen:
            raise DimensionInventoryError(
                f"duplicate dimension source path: {canonical.as_posix()}"
            )
        if not isinstance(source, str):
            raise DimensionInventoryError(
                f"dimension source {canonical.as_posix()} must be text"
            )
        seen.add(canonical)
        canonical_sources.append((canonical, source))
    canonical_sources.sort(key=lambda item: item[0].as_posix())

    cases: list[DimensionInventoryCase] = []
    source_end_lines: list[tuple[Path, int]] = []
    for path, source in canonical_sources:
        source_end_lines.append((path, source.count("\n") + 1))
        case = _case_inventory(path, source)
        if case is not None:
            cases.append(case)
    return DimensionInventory(tuple(cases), tuple(source_end_lines))


def collect_dimension_inventory(
    repo: Path, case_paths: Iterable[Path]
) -> DimensionInventory:
    """Read each manifest case and build its exact active-dimension sites."""
    paths = tuple(case_paths)
    if len(set(paths)) != len(paths):
        raise DimensionInventoryError(
            "manifest contains duplicate dimension case paths"
        )
    sources: dict[Path, str] = {}
    for path in paths:
        canonical = _canonical_inventory_case_path(
            path.as_posix(), "manifest case path"
        )
        sources[canonical] = _read_inventory_case(repo, canonical)
    return build_dimension_inventory_from_sources(sources)


def _read_inventory_case(repo: Path, path: Path) -> str:
    """Read one exact regular case path without following component symlinks."""
    try:
        repo_root = repo.resolve(strict=True)
        current = repo_root
        for index, part in enumerate(path.parts):
            current /= part
            metadata = current.lstat()
            if stat.S_ISLNK(metadata.st_mode):
                raise DimensionInventoryError(
                    f"dimension case path contains a symlink: {path.as_posix()}"
                )
            final = index + 1 == len(path.parts)
            if final and not stat.S_ISREG(metadata.st_mode):
                raise DimensionInventoryError(
                    f"dimension case path must be a regular file: {path.as_posix()}"
                )
            if not final and not stat.S_ISDIR(metadata.st_mode):
                raise DimensionInventoryError(
                    f"dimension case parent must be a directory: {path.as_posix()}"
                )
        resolved = current.resolve(strict=True)
        required_root = (repo_root / path.parent).resolve(strict=True)
        if resolved.parent != required_root or not resolved.is_relative_to(repo_root):
            raise DimensionInventoryError(
                f"dimension case escapes its required case root: {path.as_posix()}"
            )
        return current.read_text(encoding="utf-8")
    except DimensionInventoryError:
        raise
    except (OSError, UnicodeError) as exc:
        raise DimensionInventoryError(
            f"cannot read dimension case {path.as_posix()}: {exc}"
        ) from exc


def _canonical_case_path(raw: str, field_name: str) -> Path:
    if not isinstance(raw, str) or not raw:
        raise DimensionInventoryError(f"{field_name} must be a nonempty string")
    pure = PurePosixPath(raw)
    if (
        pure.is_absolute()
        or ".." in pure.parts
        or pure.as_posix() != raw
        or pure.suffix != ".tex"
    ):
        raise DimensionInventoryError(
            f"{field_name} must be a canonical repo-relative .tex path: {raw!r}"
        )
    return Path(*pure.parts)


def _canonical_inventory_case_path(raw: str, field_name: str) -> Path:
    """Require the manifest's stable RMP case-root shape in stored rows."""
    path = _canonical_case_path(raw, field_name)
    parts = path.parts
    if (
        len(parts) != 6
        or parts[:3] != ("tests", "tenkz", "rmp")
        or parts[-2] != "cases"
    ):
        raise DimensionInventoryError(
            f"{field_name} must be under tests/tenkz/rmp/<section>/cases/: {raw!r}"
        )
    return path


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DimensionInventoryError(f"duplicate JSON field: {key!r}")
        result[key] = value
    return result


def _exact_fields(
    value: object, expected: set[str], field_name: str
) -> dict[str, object]:
    if not isinstance(value, dict):
        raise DimensionInventoryError(f"{field_name} must be an object")
    actual = set(value)
    if actual != expected:
        raise DimensionInventoryError(
            f"{field_name} fields must be exactly {', '.join(sorted(expected))}; "
            f"found {', '.join(sorted(actual)) or 'none'}"
        )
    return value


def _site_contract(
    site_name: object, where: str
) -> tuple[DimensionOwner, str, int]:
    """Return a site's owner, invocation anchor, and placeholder count."""
    if not isinstance(site_name, str) or any(
        character.isspace() and character != " " for character in site_name
    ):
        raise DimensionInventoryError(
            f"{where}.site must be a normalized semantic site key"
        )
    duplicate = _DUPLICATE_SUFFIX_RE.fullmatch(site_name)
    base = duplicate.group(1) if duplicate is not None else site_name
    match = _SITE_KEY_RE.fullmatch(base)
    if match is None:
        raise DimensionInventoryError(
            f"{where}.site must be a normalized semantic site key"
        )
    invocation_anchor = match.group("invocation_anchor")
    _construct, _scope, invocation_name, _ordinal = _invocation_anchor(
        invocation_anchor, f"{where}.site"
    )
    skeleton = match.group("skeleton")
    authored_skeleton = (
        skeleton.replace("<dimension>", "")
        .replace("<nested-dimension>", "")
    )
    if (
        "<dimension>" not in skeleton
        or "#occurrence=" in skeleton
        or DIMENSION_RE.search(skeleton) is not None
        or "<" in authored_skeleton
        or ">" in authored_skeleton
        or "#" in authored_skeleton
        or re.search(r"%(?!23|25|3C|3E)", authored_skeleton) is not None
    ):
        raise DimensionInventoryError(
            f"{where}.site must contain only normalized dimension placeholders"
        )
    if _normalize_site_tokens(skeleton) != skeleton:
        raise DimensionInventoryError(
            f"{where}.site must be a normalized semantic site key"
        )
    if match.group("kind") == "command":
        command = _COMMAND_SITE_RE.match(skeleton)
        if command is None or command.group("star") is not None:
            raise DimensionInventoryError(
                f"{where}.site command skeleton is not a dimension owner"
            )
        command_name = command.group("command") + (
            "*" if command.group("star") is not None else ""
        )
        if command_name != invocation_name:
            raise DimensionInventoryError(
                f"{where}.site command skeleton does not match its invocation"
            )
        owner = DIMENSION_COMMAND_OWNERS[command.group("command")]
    else:
        option = _OPTION_SITE_RE.match(skeleton)
        if option is None:
            raise DimensionInventoryError(
                f"{where}.site option skeleton is not a dimension owner"
            )
        if option.group("option") not in _OPTION_CONTAINER_KEYS[
            option.group("container")
        ]:
            raise DimensionInventoryError(
                f"{where}.site option skeleton is not owned by its container"
            )
        if option.group("container") != invocation_name:
            raise DimensionInventoryError(
                f"{where}.site option container does not match its invocation"
            )
        owner = _OPTION_SITE_OWNERS[option.group("option")]
    return owner, invocation_anchor, skeleton.count("<dimension>")


def _path_segments(
    anchor: object, where: str
) -> tuple[tuple[str, int], ...]:
    """Parse one slash-delimited semantic path."""
    if not isinstance(anchor, str) or not anchor:
        raise DimensionInventoryError(f"{where} must be a semantic path")
    segments: list[tuple[str, int]] = []
    for raw_segment in anchor.split("/"):
        match = _PATH_SEGMENT_RE.fullmatch(raw_segment)
        if match is None:
            raise DimensionInventoryError(f"{where} must be a semantic path")
        segments.append((match.group("name"), int(match.group("ordinal"))))
    return tuple(segments)


def _segments_text(segments: Sequence[tuple[str, int]]) -> str:
    return "/".join(f"{name}@{ordinal}" for name, ordinal in segments)


def _is_scope_at_or_below(scope: str, ancestor: str) -> bool:
    """Whether one scope path lies in the subtree rooted at another."""
    return not ancestor or scope == ancestor or scope.startswith(ancestor + "/")


def _scope_anchor(anchor: object, where: str) -> tuple[str, str, int]:
    """Parse one hierarchical PICTURE-scope anchor."""
    try:
        segments = _path_segments(anchor, where)
    except DimensionInventoryError as exc:
        raise DimensionInventoryError(f"{where} must be a scope anchor") from exc
    if any(name not in DIMENSION_SCOPE_NAMES for name, _ in segments):
        raise DimensionInventoryError(f"{where} must be a scope anchor")
    parent = _segments_text(segments[:-1])
    name, ordinal = segments[-1]
    return parent, name, ordinal


def _construct_anchor(anchor: object, where: str) -> tuple[str, str, int]:
    """Parse one scope-aware picture-construct anchor."""
    try:
        segments = _path_segments(anchor, where)
    except DimensionInventoryError as exc:
        raise DimensionInventoryError(
            f"{where} must be a construct anchor"
        ) from exc
    if (
        segments[-1][0] not in DRAWING_CONSTRUCT_NAMES
        or any(
            name not in DIMENSION_SCOPE_NAMES
            for name, _ in segments[:-1]
        )
    ):
        raise DimensionInventoryError(f"{where} must be a construct anchor")
    parent = _segments_text(segments[:-1])
    name, ordinal = segments[-1]
    return parent, name, ordinal


def _invocation_anchor(
    anchor: object, where: str
) -> tuple[str, str, str, int]:
    """Parse one construct-qualified, scope-aware invocation anchor."""
    if not isinstance(anchor, str) or anchor.count("::") != 1:
        raise DimensionInventoryError(f"{where} must be an invocation anchor")
    construct_anchor, invocation_path = anchor.split("::")
    try:
        _construct_anchor(construct_anchor, where)
        segments = _path_segments(invocation_path, where)
    except DimensionInventoryError as exc:
        raise DimensionInventoryError(
            f"{where} must be an invocation anchor"
        ) from exc
    if any(
        name not in DIMENSION_SCOPE_NAMES for name, _ in segments[:-1]
    ):
        raise DimensionInventoryError(f"{where} must be an invocation anchor")
    scope_path = _segments_text(segments[:-1])
    name, ordinal = segments[-1]
    if name not in DIMENSION_INVOCATION_NAMES:
        raise DimensionInventoryError(f"{where} must be an invocation anchor")
    return construct_anchor, scope_path, name, ordinal


def _validate_duplicate_ordinals(
    path: Path, sites: tuple[DimensionInventorySite, ...]
) -> None:
    parsed: list[tuple[str, int | None]] = []
    for site in sites:
        match = _DUPLICATE_SUFFIX_RE.fullmatch(site.site)
        parsed.append(
            (match.group(1), int(match.group(2)))
            if match is not None
            else (site.site, None)
        )
    totals = Counter(base for base, _ in parsed)
    seen: Counter[str] = Counter()
    for base, ordinal in parsed:
        seen[base] += 1
        if totals[base] == 1 and ordinal is not None:
            raise DimensionInventoryError(
                f"{path.as_posix()}: unique site has a duplicate ordinal: {base}"
            )
        if totals[base] > 1 and ordinal != seen[base]:
            raise DimensionInventoryError(
                f"{path.as_posix()}: duplicate site ordinals for {base!r} must be "
                f"1 through {totals[base]} in source order"
            )


def parse_dimension_inventory(
    text: str, *, source_name: str = "dimension inventory"
) -> DimensionInventory:
    """Parse and strictly validate one version-5 inventory document."""
    try:
        raw = json.loads(text, object_pairs_hook=_unique_object)
    except json.JSONDecodeError as exc:
        raise DimensionInventoryError(
            f"cannot parse {source_name} as JSON: {exc}"
        ) from exc
    root = _exact_fields(raw, {"schema_version", "cases"}, source_name)
    schema_version = root["schema_version"]
    if (
        not isinstance(schema_version, int)
        or isinstance(schema_version, bool)
        or schema_version != DIMENSION_INVENTORY_SCHEMA_VERSION
    ):
        raise DimensionInventoryError(
            f"{source_name} schema_version must be exactly "
            f"{DIMENSION_INVENTORY_SCHEMA_VERSION}"
        )
    raw_cases = root["cases"]
    if not isinstance(raw_cases, dict):
        raise DimensionInventoryError(f"{source_name}.cases must be an object")
    if list(raw_cases) != sorted(raw_cases):
        raise DimensionInventoryError(
            f"{source_name}.cases paths must be in canonical sorted order"
        )

    cases: list[DimensionInventoryCase] = []
    for raw_path, raw_case in raw_cases.items():
        path = _canonical_inventory_case_path(
            raw_path, f"{source_name}.cases path"
        )
        case_where = f"{source_name}.cases[{raw_path!r}]"
        case_fields = _exact_fields(raw_case, _CASE_FIELDS, case_where)
        raw_scopes = case_fields["scopes"]
        if not isinstance(raw_scopes, list):
            raise DimensionInventoryError(
                f"{case_where}.scopes must be an array"
            )
        scopes: list[str] = []
        scope_anchors: set[str] = set()
        scope_name_by_anchor: dict[str, str] = {}
        scope_counts: Counter[tuple[str, str]] = Counter()
        for index, anchor in enumerate(raw_scopes, 1):
            where = f"{case_where}.scopes[{index}]"
            parent_scope, scope_name, scope_ordinal = _scope_anchor(
                anchor, where
            )
            if parent_scope and parent_scope not in scope_anchors:
                raise DimensionInventoryError(
                    f"{where} references missing parent scope "
                    f"{parent_scope!r}"
                )
            count_key = (parent_scope, scope_name)
            scope_counts[count_key] += 1
            if scope_ordinal != scope_counts[count_key]:
                raise DimensionInventoryError(
                    f"{where} must continue contiguous {scope_name} ordinals "
                    f"under {parent_scope or 'the case root'} with "
                    f"@{scope_counts[count_key]}"
                )
            assert isinstance(anchor, str)
            if anchor in scope_anchors:
                raise DimensionInventoryError(f"{where} duplicates {anchor!r}")
            scope_anchors.add(anchor)
            scope_name_by_anchor[anchor] = scope_name
            scopes.append(anchor)
        raw_constructs = case_fields["constructs"]
        if not isinstance(raw_constructs, list) or not raw_constructs:
            raise DimensionInventoryError(
                f"{case_where}.constructs must be a nonempty array"
            )
        constructs: list[str] = []
        construct_anchors: set[str] = set()
        construct_name_by_anchor: dict[str, str] = {}
        construct_parent_by_anchor: dict[str, str] = {}
        construct_counts: Counter[tuple[str, str]] = Counter()
        for index, anchor in enumerate(raw_constructs, 1):
            where = f"{case_where}.constructs[{index}]"
            parent_scope, construct_name, construct_ordinal = (
                _construct_anchor(anchor, where)
            )
            if parent_scope and parent_scope not in scope_anchors:
                raise DimensionInventoryError(
                    f"{where} references missing parent scope "
                    f"{parent_scope!r}"
                )
            if (
                construct_name in DIMENSION_SCOPE_NAMES
                and anchor not in scope_anchors
            ):
                raise DimensionInventoryError(
                    f"{where} scope construct lacks matching scope {anchor!r}"
                )
            count_key = (parent_scope, construct_name)
            construct_counts[count_key] += 1
            if construct_ordinal != construct_counts[count_key]:
                raise DimensionInventoryError(
                    f"{where} must continue contiguous {construct_name} ordinals "
                    f"under {parent_scope or 'the case root'} with "
                    f"@{construct_counts[count_key]}"
                )
            assert isinstance(anchor, str)
            if anchor in construct_anchors:
                raise DimensionInventoryError(f"{where} duplicates {anchor!r}")
            construct_anchors.add(anchor)
            construct_name_by_anchor[anchor] = construct_name
            construct_parent_by_anchor[anchor] = parent_scope
            constructs.append(anchor)
        construct_positions = {
            anchor: index for index, anchor in enumerate(constructs)
        }
        for nested_construct in constructs:
            parent_scope = construct_parent_by_anchor[nested_construct]
            late_enclosing_construct = next(
                (
                    candidate
                    for candidate in constructs
                    if (
                        candidate != nested_construct
                        and construct_name_by_anchor[candidate]
                        in PICTURE_ENVIRONMENT_NAMES
                        and _is_scope_at_or_below(parent_scope, candidate)
                        and construct_positions[candidate]
                        > construct_positions[nested_construct]
                    )
                ),
                None,
            )
            if late_enclosing_construct is not None:
                raise DimensionInventoryError(
                    f"{case_where}.constructs enclosing construct "
                    f"{late_enclosing_construct!r} must precede nested "
                    f"construct {nested_construct!r}"
                )
        scope_construct_anchors = tuple(
            anchor
            for anchor in constructs
            if construct_name_by_anchor[anchor] in DIMENSION_SCOPE_NAMES
        )
        raw_invocations = case_fields["invocations"]
        if not isinstance(raw_invocations, list) or not raw_invocations:
            raise DimensionInventoryError(
                f"{case_where}.invocations must be a nonempty array"
            )
        invocations: list[str] = []
        invocation_anchors: set[str] = set()
        invoked_scope_paths: set[str] = set()
        seen_construct_containers: set[str] = set()
        invocation_counts: Counter[tuple[str, str, str]] = Counter()
        for index, anchor in enumerate(raw_invocations, 1):
            where = f"{case_where}.invocations[{index}]"
            (
                construct_anchor,
                parent_scope,
                invocation_name,
                invocation_ordinal,
            ) = _invocation_anchor(anchor, where)
            if construct_anchor not in construct_anchors:
                raise DimensionInventoryError(
                    f"{where} references missing construct anchor "
                    f"{construct_anchor!r}"
                )
            assert isinstance(anchor, str)
            invocation_path = anchor.split("::", 1)[1]
            if parent_scope and parent_scope not in scope_anchors:
                raise DimensionInventoryError(
                    f"{where} references missing parent scope "
                    f"{parent_scope!r}"
                )
            is_construct_container = invocation_path == construct_anchor
            construct_name = construct_name_by_anchor[construct_anchor]
            construct_parent = construct_parent_by_anchor[construct_anchor]
            if not is_construct_container:
                if construct_name in DIMENSION_SCOPE_NAMES:
                    compatible_scope_constructs = tuple(
                        candidate
                        for candidate in scope_construct_anchors
                        if _is_scope_at_or_below(parent_scope, candidate)
                    )
                    narrowest_construct = max(
                        compatible_scope_constructs,
                        key=lambda candidate: candidate.count("/"),
                        default=None,
                    )
                    if narrowest_construct != construct_anchor:
                        raise DimensionInventoryError(
                            f"{where} must use its narrowest compatible scope "
                            f"construct; found {construct_anchor!r}, expected "
                            f"{narrowest_construct!r}"
                        )
                else:
                    if not _is_scope_at_or_below(parent_scope, construct_parent):
                        raise DimensionInventoryError(
                            f"{where} invocation scope {parent_scope!r} is not "
                            f"inside construct parent {construct_parent!r}"
                        )
                    nested_scope_constructs = tuple(
                        candidate
                        for candidate in scope_construct_anchors
                        if (
                            candidate != construct_parent
                            and _is_scope_at_or_below(
                                candidate, construct_parent
                            )
                            and _is_scope_at_or_below(parent_scope, candidate)
                        )
                    )
                    if nested_scope_constructs:
                        narrowest_construct = max(
                            nested_scope_constructs,
                            key=lambda candidate: candidate.count("/"),
                        )
                        raise DimensionInventoryError(
                            f"{where} must use its narrowest compatible scope "
                            f"construct {narrowest_construct!r}"
                        )
            if invocation_name in _INVOCATION_SCOPE_NAMES:
                if invocation_path in invoked_scope_paths:
                    raise DimensionInventoryError(
                        f"{where} duplicates scope invocation "
                        f"{invocation_path!r}"
                    )
            elif not is_construct_container:
                count_key = (
                    construct_anchor,
                    parent_scope,
                    invocation_name,
                )
                invocation_counts[count_key] += 1
                if invocation_ordinal != invocation_counts[count_key]:
                    raise DimensionInventoryError(
                        f"{where} must continue contiguous {invocation_name} "
                        f"ordinals in {construct_anchor} under "
                        f"{parent_scope or 'the case root'} with "
                        f"@{invocation_counts[count_key]}"
                    )
            if (
                not is_construct_container
                and construct_anchor not in seen_construct_containers
            ):
                raise DimensionInventoryError(
                    f"{where} depends on construct {construct_anchor!r} before "
                    "its container invocation"
                )
            missing_parent_scope = next(
                (
                    scope_anchor
                    for scope_anchor in reversed(scopes)
                    if (
                        scope_name_by_anchor[scope_anchor]
                        in _INVOCATION_SCOPE_NAMES
                        and _is_scope_at_or_below(parent_scope, scope_anchor)
                        and scope_anchor not in invoked_scope_paths
                    )
                ),
                None,
            )
            if missing_parent_scope is not None:
                raise DimensionInventoryError(
                    f"{where} depends on represented parent scope "
                    f"{missing_parent_scope!r} before its invocation"
                )
            if anchor in invocation_anchors:
                raise DimensionInventoryError(f"{where} duplicates {anchor!r}")
            invocation_anchors.add(anchor)
            if is_construct_container:
                seen_construct_containers.add(construct_anchor)
            if invocation_name in _INVOCATION_SCOPE_NAMES:
                invoked_scope_paths.add(invocation_path)
            invocations.append(anchor)
        for construct_anchor, construct_name in construct_name_by_anchor.items():
            container_anchor = f"{construct_anchor}::{construct_anchor}"
            if container_anchor not in invocation_anchors:
                raise DimensionInventoryError(
                    f"{case_where}.invocations lacks construct container "
                    f"{container_anchor!r}"
                )
        expected_scope_invocations = {
            anchor
            for anchor, scope_name in scope_name_by_anchor.items()
            if scope_name in _INVOCATION_SCOPE_NAMES
        }
        missing_scope_invocations = sorted(
            expected_scope_invocations - invoked_scope_paths
        )
        extra_scope_invocations = sorted(
            invoked_scope_paths - expected_scope_invocations
        )
        if missing_scope_invocations or extra_scope_invocations:
            raise DimensionInventoryError(
                f"{case_where}.invocation-bearing scopes and scope "
                "invocations disagree: "
                f"missing invocations={missing_scope_invocations!r}, "
                f"extra invocations={extra_scope_invocations!r}"
            )
        picture_scope_anchors = {
            anchor
            for anchor, scope_name in scope_name_by_anchor.items()
            if scope_name in PICTURE_ENVIRONMENT_NAMES
        }
        picture_construct_anchors = {
            anchor
            for anchor, construct_name in construct_name_by_anchor.items()
            if construct_name in PICTURE_ENVIRONMENT_NAMES
        }
        missing_picture_constructs = sorted(
            picture_scope_anchors - picture_construct_anchors
        )
        extra_picture_constructs = sorted(
            picture_construct_anchors - picture_scope_anchors
        )
        if missing_picture_constructs or extra_picture_constructs:
            raise DimensionInventoryError(
                f"{case_where}.picture scopes and constructs disagree: "
                f"missing constructs={missing_picture_constructs!r}, "
                f"extra constructs={extra_picture_constructs!r}"
            )
        raw_sites = case_fields["sites"]
        if not isinstance(raw_sites, list) or not raw_sites:
            raise DimensionInventoryError(
                f"{case_where}.sites must be a nonempty array"
            )
        sites: list[DimensionInventorySite] = []
        site_names: set[str] = set()
        for index, raw_site in enumerate(raw_sites, 1):
            where = f"{case_where}.sites[{index}]"
            fields = _exact_fields(raw_site, _SITE_FIELDS, where)
            site_name = fields["site"]
            expected_owner, invocation_anchor, placeholder_count = (
                _site_contract(site_name, where)
            )
            assert isinstance(site_name, str)
            if invocation_anchor not in invocation_anchors:
                raise DimensionInventoryError(
                    f"{where}.site references missing invocation anchor "
                    f"{invocation_anchor!r}"
                )
            if site_name in site_names:
                raise DimensionInventoryError(f"{where}.site duplicates {site_name!r}")
            site_names.add(site_name)
            raw_owner = fields["owner"]
            try:
                owner = DimensionOwner(raw_owner)
            except (TypeError, ValueError) as exc:
                raise DimensionInventoryError(
                    f"{where}.owner is not a dimension owner: {raw_owner!r}"
                ) from exc
            if owner not in _ACTIVE_OWNERS:
                raise DimensionInventoryError(
                    f"{where}.owner must describe an active case dimension"
                )
            if owner is not expected_owner:
                raise DimensionInventoryError(
                    f"{where}.owner must match the owner implied by its site command "
                    f"or option: expected {expected_owner.value!r}, found {owner.value!r}"
                )
            raw_literals = fields["literals"]
            if not isinstance(raw_literals, list) or not raw_literals:
                raise DimensionInventoryError(
                    f"{where}.literals must be a nonempty array"
                )
            literals: list[str] = []
            for literal_index, literal in enumerate(raw_literals, 1):
                literal_where = f"{where}.literals[{literal_index}]"
                if (
                    not isinstance(literal, str)
                    or DIMENSION_RE.fullmatch(literal) is None
                    or normalize_dimension_literal(literal) != literal
                ):
                    raise DimensionInventoryError(
                        f"{literal_where} must be a normalized absolute TeX dimension"
                    )
                literals.append(literal)
            if len(literals) != placeholder_count:
                raise DimensionInventoryError(
                    f"{where}.site dimension count does not match its literal vector"
                )
            sites.append(DimensionInventorySite(site_name, owner, tuple(literals)))
        case_sites = tuple(sites)
        _validate_duplicate_ordinals(path, case_sites)
        cases.append(
            DimensionInventoryCase(
                path,
                tuple(scopes),
                tuple(constructs),
                tuple(invocations),
                case_sites,
            )
        )
    return DimensionInventory(tuple(cases))


def load_dimension_inventory(path: Path) -> DimensionInventory:
    """Read a required exact inventory, rejecting every I/O or schema failure."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise DimensionInventoryError(
            f"cannot read dimension inventory {path}: {exc}"
        ) from exc
    return parse_dimension_inventory(text, source_name=path.as_posix())


def format_dimension_inventory(inventory: DimensionInventory) -> str:
    """Serialize compact one-row-per-site canonical JSON."""
    lines = [
        "{",
        f'  "schema_version": {DIMENSION_INVENTORY_SCHEMA_VERSION},',
        '  "cases": {',
    ]
    for case_index, case in enumerate(inventory.cases):
        case_comma = "," if case_index + 1 < len(inventory.cases) else ""
        path_json = json.dumps(case.path.as_posix(), ensure_ascii=False)
        scopes_json = json.dumps(list(case.scopes), ensure_ascii=False)
        constructs_json = json.dumps(list(case.constructs), ensure_ascii=False)
        invocations_json = json.dumps(list(case.invocations), ensure_ascii=False)
        lines.append(f"    {path_json}: {{")
        lines.append(f'      "scopes": {scopes_json},')
        lines.append(f'      "constructs": {constructs_json},')
        lines.append(f'      "invocations": {invocations_json},')
        lines.append('      "sites": [')
        for site_index, site in enumerate(case.sites):
            site_comma = "," if site_index + 1 < len(case.sites) else ""
            row = {
                "site": site.site,
                "owner": site.owner.value,
                "literals": list(site.literals),
            }
            lines.append(
                "        "
                + json.dumps(row, ensure_ascii=False, separators=(", ", ": "))
                + site_comma
            )
        lines.append("      ]")
        lines.append(f"    }}{case_comma}")
    lines.extend(("  }", "}"))
    return "\n".join(lines) + "\n"


def _stored_site(site: DimensionInventorySite) -> tuple[str, str, tuple[str, ...]]:
    return site.site, site.owner.value, site.literals


def _source_location(
    inventory: DimensionInventory, path: Path, site: DimensionInventorySite | None
) -> str:
    if site is not None and site.line is not None:
        return f"{path.as_posix()}:{site.line}"
    end_lines = dict(inventory.source_end_lines)
    if path in end_lines:
        return f"{path.as_posix()}:{end_lines[path]} (end of source)"
    return path.as_posix()


def validate_dimension_inventory(
    expected: DimensionInventory, actual: DimensionInventory
) -> None:
    """Reject the first path, site, owner, or literal-vector difference."""
    expected_cases = {case.path: case for case in expected.cases}
    actual_cases = {case.path: case for case in actual.cases}
    for path in sorted(
        set(expected_cases) | set(actual_cases), key=lambda item: item.as_posix()
    ):
        expected_case = expected_cases.get(path)
        actual_case = actual_cases.get(path)
        if expected_case is None:
            first = actual_case.sites[0] if actual_case is not None else None
            raise DimensionInventoryError(
                f"dimension inventory has no case for new source site at "
                f"{_source_location(actual, path, first)}"
            )
        if actual_case is None:
            raise DimensionInventoryError(
                f"dimension inventory expects {len(expected_case.sites)} site(s) in "
                f"{_source_location(actual, path, None)}, but the source has none"
            )
        if expected_case.scopes != actual_case.scopes:
            raise DimensionInventoryError(
                f"dimension scope anchors changed at {path.as_posix()}: expected "
                f"{list(expected_case.scopes)!r}, found "
                f"{list(actual_case.scopes)!r}"
            )
        if expected_case.constructs != actual_case.constructs:
            raise DimensionInventoryError(
                f"dimension construct anchors changed at {path.as_posix()}: expected "
                f"{list(expected_case.constructs)!r}, found "
                f"{list(actual_case.constructs)!r}"
            )
        if expected_case.invocations != actual_case.invocations:
            raise DimensionInventoryError(
                f"dimension invocation anchors changed at {path.as_posix()}: "
                f"expected {list(expected_case.invocations)!r}, found "
                f"{list(actual_case.invocations)!r}"
            )
        limit = min(len(expected_case.sites), len(actual_case.sites))
        for index in range(limit):
            expected_site = expected_case.sites[index]
            actual_site = actual_case.sites[index]
            if _stored_site(expected_site) == _stored_site(actual_site):
                continue
            location = _source_location(actual, path, actual_site)
            if (
                expected_site.site == actual_site.site
                and expected_site.owner is actual_site.owner
            ):
                raise DimensionInventoryError(
                    f"dimension literal vector changed at {location} for "
                    f"{actual_site.site}: expected {list(expected_site.literals)!r}, "
                    f"found {list(actual_site.literals)!r}"
                )
            raise DimensionInventoryError(
                f"dimension owner site changed at {location} (site {index + 1}): "
                f"expected {_stored_site(expected_site)!r}, "
                f"found {_stored_site(actual_site)!r}"
            )
        if len(expected_case.sites) != len(actual_case.sites):
            actual_site = (
                actual_case.sites[limit] if limit < len(actual_case.sites) else None
            )
            raise DimensionInventoryError(
                f"dimension site count changed at "
                f"{_source_location(actual, path, actual_site)}: expected "
                f"{len(expected_case.sites)}, found {len(actual_case.sites)}"
            )


def validate_rmp_dimension_gate(
    repo: Path,
    case_paths: Iterable[Path],
    *,
    inventory_path: Path | None = None,
) -> DimensionReport:
    """Run aggregate ownership and exact-site checks as one production gate."""
    paths = tuple(case_paths)
    report = collect_dimension_report(repo, paths)
    validate_dimension_report(report)
    actual = collect_dimension_inventory(repo, paths)
    path = inventory_path or repo / DEFAULT_DIMENSION_INVENTORY
    expected = load_dimension_inventory(path)
    validate_dimension_inventory(expected, actual)
    return report


def format_dimension_inventory_counts(inventory: DimensionInventory) -> str:
    """Return stable counts for updater and review output."""
    return (
        f"cases {inventory.case_count} | scopes {inventory.scope_count} | "
        f"constructs {inventory.construct_count} | "
        f"invocations {inventory.invocation_count} | "
        f"sites {inventory.site_count} | "
        f"dimensions {inventory.dimension_count}"
    )
