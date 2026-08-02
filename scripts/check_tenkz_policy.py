#!/usr/bin/env python3
"""Pure validation for the tenkz compatibility policy and 1.0 soak log."""

from __future__ import annotations

import re
import tomllib
from dataclasses import dataclass
from datetime import date, datetime, timedelta, timezone
from typing import Callable


SOAK_MARKER = "<!-- tenkz-soak-entries: append below; do not edit preceding bytes -->"
PREREQUISITES = ["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]
FREEZE_TAG_RE = re.compile(r"tenkz-v0\.9\.(?:0|[1-9][0-9]*)")
SHA_RE = re.compile(r"[0-9a-f]{40}")
ENTRY_ID_RE = re.compile(r"S1-[0-9]{4}")
IDENTITY_RE = re.compile(r"github:[a-z0-9](?:[a-z0-9-]{0,37}[a-z0-9])?")
UTC_RE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z")
ENTRY_KINDS = {
    "freeze",
    "work",
    "friction",
    "resolution",
    "reset",
    "correction",
    "sign-off",
}
TRIAGE = {"fix-compatible", "defer-to-2.0", "breaking-required"}
SURFACES = {"tex-api", "tnlog"}

EXPECTED_POLICY = {
    "policy": {
        "schema": 1,
        "tag_namespace": "tenkz-v*",
        "repository_tag_namespace": "v*",
        "freeze_tag_pattern": "tenkz-v0.9.PATCH",
        "freeze_tag_kind": "annotated",
        "soak_days": 28,
        "event_format_implementation": "pending",
        "event_format_owners": ["#4162", "#4703"],
        "soak_blocker_chain": [
            ["#5086", "#4699", "#4162"],
            ["#4703", "#4708", "#4163"],
        ],
        "deprecation_removal": "next-major",
        "tombstone_reuse": False,
        "frozen_twin_scope": "library-or-package-entry-point",
        "frozen_twin_lifetime": "permanent",
        "frozen_twin_precedent": "quantikz/quantikz2",
        "maintainer_identity": "github:lionsr",
        "signer_identity_scheme": "github:lowercase-login",
    },
    "compatibility": {
        "patch": {
            "tex_api": "backward-compatible-fix",
            "tnlog": "byte-stable",
        },
        "minor": {
            "tex_api": "backward-compatible-addition",
            "tnlog": "additive-versioned",
        },
        "major": {
            "tex_api": "breaking-change",
            "tnlog": "breaking-versioned",
        },
    },
}

EXPECTED_SOAK = {
    "soak": {
        "schema": 1,
        "policy": "docs/tenkz/DESIGN.md",
        "append_only": True,
        "minimum_days": 28,
        "normal_work_windows": 4,
        "required_prerequisites": PREREQUISITES,
        "freeze_tag_pattern": "tenkz-v0.9.PATCH",
        "freeze_tag_kind": "annotated",
        "release_tag": "tenkz-v1.0.0",
        "maintainer_identity": "github:lionsr",
        "signer_identity_scheme": "github:lowercase-login",
    }
}

COMMON_FIELDS = {"id", "kind", "date", "author", "attempt"}
FIELDS_BY_KIND = {
    "freeze": COMMON_FIELDS
    | {
        "freeze_sha",
        "freeze_tag_object",
        "freeze_tag",
        "freeze_tagger_utc",
        "prerequisites",
        "evidence",
    },
    "work": COMMON_FIELDS
    | {"work_sha", "work_committed_utc", "summary", "evidence"},
    "friction": COMMON_FIELDS | {"surface", "triage", "summary", "evidence"},
    "resolution": COMMON_FIELDS | {"friction", "summary", "evidence"},
    "reset": COMMON_FIELDS | {"friction", "reason", "evidence"},
    "correction": COMMON_FIELDS | {"target", "summary", "evidence"},
    "sign-off": COMMON_FIELDS
    | {
        "freeze",
        "freeze_sha",
        "release_tag",
        "maintainer",
        "reviewer",
        "work_evidence",
        "decision",
    },
}


class PolicyError(ValueError):
    """A compatibility policy or soak record is invalid."""


@dataclass(frozen=True)
class TagEvidence:
    object_id: str
    object_type: str
    commit: str
    tagger_utc: datetime | None
    reachable_from_main: bool


@dataclass(frozen=True)
class CommitEvidence:
    object_type: str
    committed_utc: datetime | None
    reachable_from_main: bool
    descends_from_freeze: bool


def require(condition: bool, message: str) -> None:
    if not condition:
        raise PolicyError(message)


def fenced_blocks(text: str, label: str) -> list[str]:
    pattern = re.compile(
        rf"^```toml[ \t]+{re.escape(label)}[ \t]*\n(.*?)^```[ \t]*$",
        re.MULTILINE | re.DOTALL,
    )
    return [match.group(1) for match in pattern.finditer(text)]


def parse_toml_block(text: str, label: str) -> dict:
    blocks = fenced_blocks(text, label)
    require(len(blocks) == 1, f"expected exactly one {label} block, found {len(blocks)}")
    try:
        parsed = tomllib.loads(blocks[0])
    except tomllib.TOMLDecodeError as error:
        raise PolicyError(f"invalid TOML in {label}: {error}") from error
    require(isinstance(parsed, dict), f"{label} must decode to a table")
    return parsed


def validate_policy_text(text: str) -> dict:
    required_headings = {
        "## Compatibility ownership",
        "## Package versions",
        "## Deprecations, tombstones, and frozen twins",
        "## Release tags",
        "## The 1.0 freeze and soak",
    }
    missing = sorted(heading for heading in required_headings if heading not in text)
    require(not missing, f"DESIGN.md lacks required section(s): {', '.join(missing)}")
    policy = parse_toml_block(text, "tenkz-policy-v1")
    require(policy == EXPECTED_POLICY, "tenkz-policy-v1 differs from the signed policy")
    return policy


def parse_entry_block(block: str, index: int) -> dict:
    try:
        parsed = tomllib.loads(block)
    except tomllib.TOMLDecodeError as error:
        raise PolicyError(f"entry {index} contains invalid TOML: {error}") from error
    require(set(parsed) == {"entry"}, f"entry {index} must contain only [entry]")
    entry = parsed["entry"]
    require(isinstance(entry, dict), f"entry {index} [entry] must be a table")
    return entry


def parse_soak_text(text: str) -> tuple[dict, list[dict]]:
    soak = parse_toml_block(text, "tenkz-soak-v1")
    require(soak == EXPECTED_SOAK, "tenkz-soak-v1 differs from the signed schema")
    require(text.count(SOAK_MARKER) == 1, "SOAK-1.0.md must contain one append marker")
    prefix, tail = text.split(SOAK_MARKER, 1)
    require(
        not fenced_blocks(prefix, "tenkz-soak-entry-v1"),
        "soak entries must appear after the append marker",
    )

    pattern = re.compile(
        r"^```toml[ \t]+tenkz-soak-entry-v1[ \t]*\n(.*?)^```[ \t]*$",
        re.MULTILINE | re.DOTALL,
    )
    entries: list[dict] = []
    cursor = 0
    for index, match in enumerate(pattern.finditer(tail), start=1):
        require(
            not tail[cursor : match.start()].strip(),
            "only soak entry blocks may follow the append marker",
        )
        entries.append(parse_entry_block(match.group(1), index))
        cursor = match.end()
    require(not tail[cursor:].strip(), "only soak entry blocks may follow the append marker")
    return soak, entries


def nonempty_string(value: object, field: str, entry_id: str) -> str:
    require(
        isinstance(value, str) and bool(value.strip()),
        f"{entry_id} field {field} must be a nonempty string",
    )
    return value


def string_list(value: object, field: str, entry_id: str) -> list[str]:
    require(
        isinstance(value, list)
        and all(isinstance(item, str) and item.strip() for item in value),
        f"{entry_id} field {field} must be a list of nonempty strings",
    )
    return value


def iso_date(value: object, entry_id: str) -> date:
    text = nonempty_string(value, "date", entry_id)
    try:
        parsed = date.fromisoformat(text)
    except ValueError as error:
        raise PolicyError(f"{entry_id} date must use YYYY-MM-DD") from error
    require(parsed.isoformat() == text, f"{entry_id} date must use YYYY-MM-DD")
    return parsed


def iso_utc(value: object, field: str, entry_id: str) -> datetime:
    text = nonempty_string(value, field, entry_id)
    require(UTC_RE.fullmatch(text) is not None, f"{entry_id} {field} must use UTC seconds")
    try:
        return datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )
    except ValueError as error:
        raise PolicyError(f"{entry_id} {field} is not a real UTC timestamp") from error


def normalized_identity(value: object, field: str, entry_id: str) -> str:
    identity = nonempty_string(value, field, entry_id)
    require(
        IDENTITY_RE.fullmatch(identity) is not None,
        f"{entry_id} {field} must use github:lowercase-login",
    )
    return identity


def validate_entry_shape(entry: dict, index: int) -> tuple[str, str, date, int]:
    expected_id = f"S1-{index:04d}"
    entry_id = nonempty_string(entry.get("id"), "id", expected_id)
    require(ENTRY_ID_RE.fullmatch(entry_id) is not None, f"invalid entry id {entry_id}")
    require(entry_id == expected_id, f"expected entry id {expected_id}, found {entry_id}")
    kind = nonempty_string(entry.get("kind"), "kind", entry_id)
    require(kind in ENTRY_KINDS, f"{entry_id} has unknown kind {kind}")
    require(
        set(entry) == FIELDS_BY_KIND[kind],
        f"{entry_id} {kind} fields differ from the schema",
    )
    entry_date = iso_date(entry["date"], entry_id)
    normalized_identity(entry["author"], "author", entry_id)
    attempt = entry["attempt"]
    require(
        isinstance(attempt, int) and not isinstance(attempt, bool) and attempt > 0,
        f"{entry_id} attempt must be a positive integer",
    )
    return entry_id, kind, entry_date, attempt


def validate_entries(
    entries: list[dict],
    *,
    resolve_tag: Callable[[str], TagEvidence] | None = None,
    resolve_commit: Callable[[str, str], CommitEvidence] | None = None,
    now: datetime | None = None,
) -> str:
    current = now or datetime.now(timezone.utc)
    require(current.tzinfo is not None, "current time must be timezone-aware")
    current = current.astimezone(timezone.utc)
    seen: dict[str, tuple[dict, date]] = {}
    active: dict | None = None
    last_date: date | None = None
    last_attempt = 0
    pending_break: str | None = None
    signed = False
    prior_freeze_sha: str | None = None
    used_freeze_tags: set[str] = set()
    used_freeze_objects: set[str] = set()
    used_freeze_shas: set[str] = set()

    for index, entry in enumerate(entries, start=1):
        entry_id, kind, entry_date, attempt = validate_entry_shape(entry, index)
        require(not signed, f"{entry_id} appears after final sign-off")
        require(entry_date <= current.date(), f"{entry_id} date is in the future")
        if last_date is not None:
            require(entry_date >= last_date, f"{entry_id} date precedes the prior entry")
        last_date = entry_date

        if pending_break is not None:
            require(
                kind == "reset" and entry["friction"] == pending_break,
                f"{pending_break} breaking need must be followed immediately by its reset",
            )

        if kind == "freeze":
            require(active is None, f"{entry_id} starts a freeze while an attempt is active")
            require(attempt == last_attempt + 1, f"{entry_id} has the wrong attempt number")
            freeze_sha = nonempty_string(entry["freeze_sha"], "freeze_sha", entry_id)
            tag_object = nonempty_string(
                entry["freeze_tag_object"], "freeze_tag_object", entry_id
            )
            freeze_tag = nonempty_string(entry["freeze_tag"], "freeze_tag", entry_id)
            tagger_utc = iso_utc(
                entry["freeze_tagger_utc"], "freeze_tagger_utc", entry_id
            )
            require(SHA_RE.fullmatch(freeze_sha) is not None, f"{entry_id} has invalid freeze_sha")
            require(
                SHA_RE.fullmatch(tag_object) is not None,
                f"{entry_id} has invalid freeze_tag_object",
            )
            require(
                FREEZE_TAG_RE.fullmatch(freeze_tag) is not None,
                f"{entry_id} freeze tag must use tenkz-v0.9.PATCH",
            )
            require(
                freeze_tag not in used_freeze_tags,
                f"{entry_id} reuses a prior freeze tag",
            )
            require(
                tag_object not in used_freeze_objects,
                f"{entry_id} reuses a prior freeze tag object",
            )
            require(
                freeze_sha not in used_freeze_shas,
                f"{entry_id} reuses a prior freeze commit",
            )
            require(
                entry_date == tagger_utc.date(),
                f"{entry_id} date differs from the tagger UTC date",
            )
            require(tagger_utc <= current, f"{entry_id} tagger timestamp is in the future")
            require(
                entry["prerequisites"] == PREREQUISITES,
                f"{entry_id} lacks the full blocker chain",
            )
            nonempty_string(entry["evidence"], "evidence", entry_id)
            require(resolve_tag is not None, f"{entry_id} requires Git tag resolution")
            require(resolve_commit is not None, f"{entry_id} requires Git commit resolution")
            tag = resolve_tag(freeze_tag)
            require(tag.object_type == "tag", f"{entry_id} freeze tag is not annotated")
            require(tag.object_id == tag_object, f"{entry_id} freeze tag object was replaced")
            require(tag.commit == freeze_sha, f"{entry_id} freeze tag peels to another commit")
            require(tag.tagger_utc is not None, f"{entry_id} annotated tag lacks a tagger date")
            require(
                tag.tagger_utc.astimezone(timezone.utc) == tagger_utc,
                f"{entry_id} tagger timestamp differs from the tag object",
            )
            require(
                tag.reachable_from_main,
                f"{entry_id} freeze commit is not reachable from main",
            )
            freeze_commit = resolve_commit(
                freeze_sha,
                prior_freeze_sha if prior_freeze_sha is not None else freeze_sha,
            )
            require(
                freeze_commit.object_type == "commit",
                f"{entry_id} freeze_sha is not a commit",
            )
            require(
                freeze_commit.committed_utc is not None,
                f"{entry_id} freeze commit lacks a committer date",
            )
            require(
                freeze_commit.committed_utc.tzinfo is not None,
                f"{entry_id} freeze commit timestamp must be timezone-aware",
            )
            require(
                freeze_commit.committed_utc.astimezone(timezone.utc) <= tagger_utc,
                f"{entry_id} freeze commit postdates the annotated tag",
            )
            if prior_freeze_sha is not None:
                require(
                    freeze_commit.descends_from_freeze,
                    f"{entry_id} freeze commit does not descend from the prior freeze",
                )
            active = {
                "attempt": attempt,
                "freeze_id": entry_id,
                "freeze_utc": tagger_utc,
                "freeze_sha": freeze_sha,
                "work": {},
                "friction": {},
            }
            prior_freeze_sha = freeze_sha
            used_freeze_tags.add(freeze_tag)
            used_freeze_objects.add(tag_object)
            used_freeze_shas.add(freeze_sha)
            last_attempt = attempt
        elif kind == "correction":
            target = nonempty_string(entry["target"], "target", entry_id)
            require(target in seen, f"{entry_id} correction target is not an earlier entry")
            require(
                attempt == seen[target][0]["attempt"],
                f"{entry_id} correction attempt differs from its target",
            )
            nonempty_string(entry["summary"], "summary", entry_id)
            nonempty_string(entry["evidence"], "evidence", entry_id)
        else:
            require(active is not None, f"{entry_id} {kind} appears without an active freeze")
            require(attempt == active["attempt"], f"{entry_id} has the wrong active attempt")

            if kind == "work":
                work_sha = nonempty_string(entry["work_sha"], "work_sha", entry_id)
                work_utc = iso_utc(
                    entry["work_committed_utc"], "work_committed_utc", entry_id
                )
                require(SHA_RE.fullmatch(work_sha) is not None, f"{entry_id} has invalid work_sha")
                require(
                    entry_date == work_utc.date(),
                    f"{entry_id} date differs from the work commit UTC date",
                )
                require(work_utc <= current, f"{entry_id} work commit is in the future")
                require(
                    work_utc >= active["freeze_utc"],
                    f"{entry_id} work commit predates the freeze tag",
                )
                require(resolve_commit is not None, f"{entry_id} requires Git commit resolution")
                commit = resolve_commit(work_sha, active["freeze_sha"])
                require(commit.object_type == "commit", f"{entry_id} work_sha is not a commit")
                require(
                    commit.committed_utc is not None,
                    f"{entry_id} work commit lacks a committer date",
                )
                require(
                    commit.committed_utc.astimezone(timezone.utc) == work_utc,
                    f"{entry_id} timestamp differs from the commit object",
                )
                require(
                    commit.reachable_from_main,
                    f"{entry_id} work commit is not reachable from main",
                )
                require(
                    commit.descends_from_freeze,
                    f"{entry_id} work commit does not descend from the freeze",
                )
                require(
                    all(record["sha"] != work_sha for record in active["work"].values()),
                    f"{entry_id} repeats a work commit",
                )
                nonempty_string(entry["summary"], "summary", entry_id)
                nonempty_string(entry["evidence"], "evidence", entry_id)
                active["work"][entry_id] = {"sha": work_sha, "when": work_utc}
            elif kind == "friction":
                surface = nonempty_string(entry["surface"], "surface", entry_id)
                triage = nonempty_string(entry["triage"], "triage", entry_id)
                require(surface in SURFACES, f"{entry_id} has invalid friction surface")
                require(triage in TRIAGE, f"{entry_id} has invalid friction triage")
                nonempty_string(entry["summary"], "summary", entry_id)
                nonempty_string(entry["evidence"], "evidence", entry_id)
                active["friction"][entry_id] = {
                    "triage": triage,
                    "resolved": False,
                }
                if triage == "breaking-required":
                    pending_break = entry_id
            elif kind == "resolution":
                friction = nonempty_string(entry["friction"], "friction", entry_id)
                record = active["friction"].get(friction)
                require(record is not None, f"{entry_id} names no friction in this attempt")
                require(
                    record["triage"] == "fix-compatible",
                    f"{entry_id} may resolve only fix-compatible friction",
                )
                require(not record["resolved"], f"{entry_id} resolves friction twice")
                nonempty_string(entry["summary"], "summary", entry_id)
                nonempty_string(entry["evidence"], "evidence", entry_id)
                record["resolved"] = True
            elif kind == "reset":
                friction = nonempty_string(entry["friction"], "friction", entry_id)
                record = active["friction"].get(friction)
                require(record is not None, f"{entry_id} names no friction in this attempt")
                require(
                    record["triage"] == "breaking-required",
                    f"{entry_id} reset needs a breaking-required friction",
                )
                nonempty_string(entry["reason"], "reason", entry_id)
                nonempty_string(entry["evidence"], "evidence", entry_id)
                pending_break = None
                active = None
            elif kind == "sign-off":
                freeze = nonempty_string(entry["freeze"], "freeze", entry_id)
                freeze_sha = nonempty_string(entry["freeze_sha"], "freeze_sha", entry_id)
                release_tag = nonempty_string(entry["release_tag"], "release_tag", entry_id)
                decision = nonempty_string(entry["decision"], "decision", entry_id)
                maintainer = normalized_identity(entry["maintainer"], "maintainer", entry_id)
                reviewer = normalized_identity(entry["reviewer"], "reviewer", entry_id)
                work_evidence = string_list(entry["work_evidence"], "work_evidence", entry_id)
                require(freeze == active["freeze_id"], f"{entry_id} names the wrong freeze entry")
                require(
                    freeze_sha == active["freeze_sha"],
                    f"{entry_id} names the wrong freeze SHA",
                )
                require(release_tag == "tenkz-v1.0.0", f"{entry_id} has the wrong release tag")
                require(decision == "release", f"{entry_id} decision must be release")
                require(maintainer == "github:lionsr", f"{entry_id} has the wrong maintainer")
                require(reviewer != maintainer, f"{entry_id} reviewer must be independent")
                require(
                    len(work_evidence) == len(set(work_evidence)),
                    f"{entry_id} repeats work evidence",
                )
                eligible_at = active["freeze_utc"] + timedelta(days=28)
                require(current >= eligible_at, f"{entry_id} current UTC is before 28 full days")
                require(
                    entry_date >= eligible_at.date(),
                    f"{entry_id} sign-off date is backdated",
                )
                windows: set[int] = set()
                for work_id in work_evidence:
                    require(
                        work_id in active["work"],
                        f"{entry_id} names missing work entry {work_id}",
                    )
                    offset = active["work"][work_id]["when"] - active["freeze_utc"]
                    if timedelta(0) <= offset < timedelta(days=28):
                        windows.add(offset.days // 7)
                require(
                    windows == {0, 1, 2, 3},
                    f"{entry_id} lacks normal-work evidence in all four windows",
                )
                unresolved = sorted(
                    friction
                    for friction, record in active["friction"].items()
                    if record["triage"] == "fix-compatible" and not record["resolved"]
                )
                require(
                    not unresolved,
                    f"{entry_id} has unresolved friction: {', '.join(unresolved)}",
                )
                active = None
                signed = True

        seen[entry_id] = (entry, entry_date)

    require(pending_break is None, f"{pending_break} breaking need lacks an immediate reset")
    if signed:
        return "signed-off"
    if active is not None:
        return f"attempt-{active['attempt']}-active"
    if entries:
        return "reset"
    return "not-started"


def check_append_only(previous: str | None, current: str) -> None:
    if previous is None:
        return
    require(current.startswith(previous), "SOAK-1.0.md changed existing bytes instead of appending")
