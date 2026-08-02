#!/usr/bin/env python3
"""Perturbation tests for the tenkz compatibility and soak policy."""

from __future__ import annotations

import sys
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_tenkz_policy as policy


DESIGN_TEXT = (ROOT / "docs/tenkz/DESIGN.md").read_text(encoding="utf-8")
SOAK_TEXT = (ROOT / "docs/tenkz/SOAK-1.0.md").read_text(encoding="utf-8")
SHA = "a" * 40
TAG_OBJECT = "c" * 40
SECOND_SHA = "b" * 40
SECOND_TAG_OBJECT = "d" * 40
FREEZE_UTC = datetime(2026, 9, 1, tzinfo=timezone.utc)
SECOND_FREEZE_UTC = datetime(2026, 9, 4, tzinfo=timezone.utc)
NOW = datetime(2026, 9, 30, 12, tzinfo=timezone.utc)
PREREQUISITES = '["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]'
WORK_COMMITS = {
    "S1-0002": ("2" * 40, datetime(2026, 9, 2, 12, tzinfo=timezone.utc)),
    "S1-0003": ("3" * 40, datetime(2026, 9, 8, 12, tzinfo=timezone.utc)),
    "S1-0005": ("5" * 40, datetime(2026, 9, 15, 12, tzinfo=timezone.utc)),
    "S1-0006": ("6" * 40, datetime(2026, 9, 22, 12, tzinfo=timezone.utc)),
    "S1-0007": ("7" * 40, datetime(2026, 9, 15, 12, tzinfo=timezone.utc)),
    "S1-0008": ("8" * 40, datetime(2026, 9, 22, 12, tzinfo=timezone.utc)),
}


def block(contents: str) -> str:
    return f"\n```toml tenkz-soak-entry-v1\n[entry]\n{contents.strip()}\n```\n"


def utc_text(value: datetime) -> str:
    return value.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def freeze(
    entry_id: str = "S1-0001",
    *,
    when: str = "2026-09-01",
    attempt: int = 1,
    sha: str = SHA,
    tag_object: str = TAG_OBJECT,
    tag: str = "tenkz-v0.9.0",
    tagger_utc: str = "2026-09-01T00:00:00Z",
    prerequisites: str = PREREQUISITES,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "freeze"
date = "{when}"
author = "github:lionsr"
attempt = {attempt}
freeze_sha = "{sha}"
freeze_tag_object = "{tag_object}"
freeze_tag = "{tag}"
freeze_tagger_utc = "{tagger_utc}"
prerequisites = {prerequisites}
evidence = "https://example.test/freeze"'''
    )


def work(
    entry_id: str,
    *,
    attempt: int = 1,
    sha: str | None = None,
    committed_utc: datetime | None = None,
    when: str | None = None,
) -> str:
    default_sha, default_time = WORK_COMMITS[entry_id]
    work_sha = sha or default_sha
    work_time = committed_utc or default_time
    entry_date = when or work_time.date().isoformat()
    return block(
        f'''id = "{entry_id}"
kind = "work"
date = "{entry_date}"
author = "github:blueprint-author"
attempt = {attempt}
work_sha = "{work_sha}"
work_committed_utc = "{utc_text(work_time)}"
summary = "ordinary blueprint diagram work"
evidence = "https://example.test/{entry_id}"'''
    )


def friction(
    entry_id: str,
    when: str,
    triage: str,
    *,
    attempt: int = 1,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "friction"
date = "{when}"
author = "github:blueprint-author"
attempt = {attempt}
surface = "tex-api"
triage = "{triage}"
summary = "recorded interface friction"
evidence = "https://example.test/{entry_id}"'''
    )


def resolution(entry_id: str, when: str, target: str, *, attempt: int = 1) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "resolution"
date = "{when}"
author = "github:lionsr"
attempt = {attempt}
friction = "{target}"
summary = "compatible repair"
evidence = "https://example.test/{entry_id}"'''
    )


def reset(entry_id: str, when: str, target: str, *, attempt: int = 1) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "reset"
date = "{when}"
author = "github:lionsr"
attempt = {attempt}
friction = "{target}"
reason = "the documented surface needs a breaking change"
evidence = "https://example.test/{entry_id}"'''
    )


def correction(entry_id: str, when: str, target: str, *, attempt: int = 1) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "correction"
date = "{when}"
author = "github:lionsr"
attempt = {attempt}
target = "{target}"
summary = "additional explanatory evidence"
evidence = "https://example.test/{entry_id}"'''
    )


def sign_off(
    entry_id: str,
    when: str,
    work_ids: list[str],
    *,
    attempt: int = 1,
    freeze_id: str = "S1-0001",
    sha: str = SHA,
    maintainer: str = "github:lionsr",
    reviewer: str = "github:independent-reviewer",
) -> str:
    work_array = ", ".join(f'"{item}"' for item in work_ids)
    return block(
        f'''id = "{entry_id}"
kind = "sign-off"
date = "{when}"
author = "github:lionsr"
attempt = {attempt}
freeze = "{freeze_id}"
freeze_sha = "{sha}"
release_tag = "tenkz-v1.0.0"
maintainer = "{maintainer}"
reviewer = "{reviewer}"
work_evidence = [{work_array}]
decision = "release"'''
    )


def parsed_entries(*blocks: str) -> list[dict]:
    _schema, entries = policy.parse_soak_text(SOAK_TEXT + "".join(blocks))
    return entries


def expect_failure(action, fragment: str) -> None:
    try:
        action()
    except policy.PolicyError as error:
        assert fragment in str(error), (fragment, str(error))
    else:
        raise AssertionError(f"expected PolicyError containing {fragment!r}")


def resolve_tag(tag: str) -> policy.TagEvidence:
    return {
        "tenkz-v0.9.0": policy.TagEvidence(
            TAG_OBJECT, "tag", SHA, FREEZE_UTC, True
        ),
        "tenkz-v0.9.1": policy.TagEvidence(
            SECOND_TAG_OBJECT, "tag", SECOND_SHA, SECOND_FREEZE_UTC, True
        ),
    }[tag]


def resolve_commit(sha: str, _freeze_sha: str) -> policy.CommitEvidence:
    if sha == SHA:
        return policy.CommitEvidence("commit", FREEZE_UTC, True, True)
    if sha == SECOND_SHA:
        return policy.CommitEvidence("commit", SECOND_FREEZE_UTC, True, True)
    committed = next(time for work_sha, time in WORK_COMMITS.values() if work_sha == sha)
    return policy.CommitEvidence("commit", committed, True, True)


def validate(entries: list[dict], **overrides) -> str:
    arguments = {
        "resolve_tag": resolve_tag,
        "resolve_commit": resolve_commit,
        "now": NOW,
    }
    arguments.update(overrides)
    return policy.validate_entries(entries, **arguments)


def complete_log() -> list[str]:
    return [
        freeze(),
        work("S1-0002"),
        work("S1-0003"),
        friction("S1-0004", "2026-09-10", "fix-compatible"),
        resolution("S1-0005", "2026-09-11", "S1-0004"),
        friction("S1-0006", "2026-09-12", "defer-to-2.0"),
        work("S1-0007"),
        work("S1-0008"),
        sign_off(
            "S1-0009",
            "2026-09-29",
            ["S1-0002", "S1-0003", "S1-0007", "S1-0008"],
        ),
    ]


def main() -> int:
    assert policy.validate_policy_text(DESIGN_TEXT) == policy.EXPECTED_POLICY
    _schema, empty_entries = policy.parse_soak_text(SOAK_TEXT)
    assert policy.validate_entries(empty_entries) == "not-started"

    signed_entries = parsed_entries(*complete_log())
    assert validate(signed_entries) == "signed-off"

    reset_entries = parsed_entries(
        freeze(),
        friction("S1-0002", "2026-09-02", "breaking-required"),
        reset("S1-0003", "2026-09-02", "S1-0002"),
        correction("S1-0004", "2026-09-03", "S1-0002"),
        freeze(
            "S1-0005",
            when="2026-09-04",
            attempt=2,
            sha=SECOND_SHA,
            tag_object=SECOND_TAG_OBJECT,
            tag="tenkz-v0.9.1",
            tagger_utc="2026-09-04T00:00:00Z",
        ),
    )
    assert validate(reset_entries) == "attempt-2-active"

    reused_freeze = parsed_entries(
        freeze(),
        friction("S1-0002", "2026-09-01", "breaking-required"),
        reset("S1-0003", "2026-09-01", "S1-0002"),
        freeze("S1-0004", when="2026-09-01", attempt=2),
    )
    expect_failure(lambda: validate(reused_freeze), "reuses a prior freeze tag")

    reused_object = parsed_entries(
        freeze(),
        friction("S1-0002", "2026-09-01", "breaking-required"),
        reset("S1-0003", "2026-09-01", "S1-0002"),
        freeze(
            "S1-0004",
            when="2026-09-04",
            attempt=2,
            sha=SECOND_SHA,
            tag_object=TAG_OBJECT,
            tag="tenkz-v0.9.1",
            tagger_utc="2026-09-04T00:00:00Z",
        ),
    )
    expect_failure(lambda: validate(reused_object), "reuses a prior freeze tag object")

    reused_commit = parsed_entries(
        freeze(),
        friction("S1-0002", "2026-09-01", "breaking-required"),
        reset("S1-0003", "2026-09-01", "S1-0002"),
        freeze(
            "S1-0004",
            when="2026-09-04",
            attempt=2,
            sha=SHA,
            tag_object=SECOND_TAG_OBJECT,
            tag="tenkz-v0.9.1",
            tagger_utc="2026-09-04T00:00:00Z",
        ),
    )
    expect_failure(lambda: validate(reused_commit), "reuses a prior freeze commit")

    non_descending_freeze = lambda sha, _prior: policy.CommitEvidence(
        "commit", SECOND_FREEZE_UTC if sha == SECOND_SHA else FREEZE_UTC, True, False
    )
    expect_failure(
        lambda: validate(reset_entries, resolve_commit=non_descending_freeze),
        "does not descend from the prior freeze",
    )

    first_reset_freeze_utc = datetime(2026, 9, 1, 12, tzinfo=timezone.utc)
    for second_reset_freeze_utc in (
        datetime(2026, 9, 1, 11, tzinfo=timezone.utc),
        first_reset_freeze_utc,
    ):
        nonincreasing_reset_entries = parsed_entries(
            freeze(tagger_utc=utc_text(first_reset_freeze_utc)),
            friction("S1-0002", "2026-09-01", "breaking-required"),
            reset("S1-0003", "2026-09-01", "S1-0002"),
            freeze(
                "S1-0004",
                when="2026-09-01",
                attempt=2,
                sha=SECOND_SHA,
                tag_object=SECOND_TAG_OBJECT,
                tag="tenkz-v0.9.1",
                tagger_utc=utc_text(second_reset_freeze_utc),
            ),
        )
        reset_tags = lambda tag, second=second_reset_freeze_utc: {
            "tenkz-v0.9.0": policy.TagEvidence(
                TAG_OBJECT, "tag", SHA, first_reset_freeze_utc, True
            ),
            "tenkz-v0.9.1": policy.TagEvidence(
                SECOND_TAG_OBJECT, "tag", SECOND_SHA, second, True
            ),
        }[tag]
        reset_commits = lambda sha, _prior, second=second_reset_freeze_utc: (
            policy.CommitEvidence(
                "commit",
                first_reset_freeze_utc if sha == SHA else second,
                True,
                True,
            )
        )
        expect_failure(
            lambda: validate(
                nonincreasing_reset_entries,
                resolve_tag=reset_tags,
                resolve_commit=reset_commits,
            ),
            "must follow the prior freeze",
        )

    expect_failure(
        lambda: policy.validate_policy_text(
            DESIGN_TEXT.replace('tag_namespace = "tenkz-v*"', 'tag_namespace = "v*"')
        ),
        "signed policy",
    )
    expect_failure(
        lambda: policy.validate_policy_text(
            DESIGN_TEXT.replace(
                'frozen_twin_scope = "library-or-package-entry-point"',
                'frozen_twin_scope = "spelling-level"',
            )
        ),
        "signed policy",
    )
    expect_failure(
        lambda: policy.validate_policy_text(
            DESIGN_TEXT.replace('tnlog = "byte-stable"', 'tnlog = "best-effort"')
        ),
        "signed policy",
    )
    expect_failure(
        lambda: policy.parse_soak_text(
            SOAK_TEXT.replace("minimum_days = 28", "minimum_days = 27")
        ),
        "signed schema",
    )
    expect_failure(
        lambda: policy.parse_soak_text(SOAK_TEXT + "free-form tail\n"),
        "only soak entry blocks",
    )

    bad_prerequisites = parsed_entries(
        freeze(prerequisites='["#5086", "#4699", "#4162", "#4703", "#4708"]')
    )
    expect_failure(lambda: validate(bad_prerequisites), "full blocker chain")
    expect_failure(lambda: validate(parsed_entries(freeze(sha="abc"))), "invalid freeze_sha")
    expect_failure(
        lambda: validate(parsed_entries(freeze(tag="tenkz-v1.0.0"))),
        "tenkz-v0.9.PATCH",
    )

    lightweight = lambda _tag: policy.TagEvidence(
        SHA, "commit", SHA, None, True
    )
    expect_failure(
        lambda: validate(parsed_entries(freeze()), resolve_tag=lightweight),
        "not annotated",
    )
    replaced = lambda _tag: policy.TagEvidence(
        SECOND_TAG_OBJECT, "tag", SHA, FREEZE_UTC, True
    )
    expect_failure(
        lambda: validate(parsed_entries(freeze()), resolve_tag=replaced),
        "object was replaced",
    )
    wrong_peeled_commit = lambda _tag: policy.TagEvidence(
        TAG_OBJECT, "tag", SECOND_SHA, FREEZE_UTC, True
    )
    expect_failure(
        lambda: validate(
            parsed_entries(freeze()),
            resolve_tag=wrong_peeled_commit,
        ),
        "peels to another commit",
    )
    unreachable_freeze = lambda _tag: policy.TagEvidence(
        TAG_OBJECT, "tag", SHA, FREEZE_UTC, False
    )
    expect_failure(
        lambda: validate(
            parsed_entries(freeze()),
            resolve_tag=unreachable_freeze,
        ),
        "freeze commit is not reachable from main",
    )
    expect_failure(
        lambda: validate(parsed_entries(freeze(when="2026-08-31"))),
        "differs from the tagger UTC date",
    )
    naive_tag_time = lambda _tag: policy.TagEvidence(
        TAG_OBJECT, "tag", SHA, datetime(2026, 9, 1), True
    )
    expect_failure(
        lambda: validate(parsed_entries(freeze()), resolve_tag=naive_tag_time),
        "tagger timestamp must be timezone-aware",
    )
    missing_freeze_time = lambda _sha, _prior: policy.CommitEvidence(
        "commit", None, True, True
    )
    expect_failure(
        lambda: validate(
            parsed_entries(freeze()),
            resolve_commit=missing_freeze_time,
        ),
        "freeze commit lacks a committer date",
    )
    postdated_freeze_commit = lambda _sha, _prior: policy.CommitEvidence(
        "commit", datetime(2026, 9, 1, 0, 0, 1, tzinfo=timezone.utc), True, True
    )
    expect_failure(
        lambda: validate(
            parsed_entries(freeze()),
            resolve_commit=postdated_freeze_commit,
        ),
        "freeze commit postdates the annotated tag",
    )
    future_utc = datetime(2026, 10, 1, tzinfo=timezone.utc)
    future_tag = lambda _tag: policy.TagEvidence(
        TAG_OBJECT, "tag", SHA, future_utc, True
    )
    expect_failure(
        lambda: validate(
            parsed_entries(
                freeze(when="2026-10-01", tagger_utc="2026-10-01T00:00:00Z")
            ),
            resolve_tag=future_tag,
        ),
        "future",
    )

    fake_work_entries = parsed_entries(freeze(), work("S1-0002"))
    freeze_as_work = parsed_entries(
        freeze(),
        work("S1-0002", sha=SHA, committed_utc=FREEZE_UTC),
    )
    expect_failure(lambda: validate(freeze_as_work), "reuses the freeze commit")
    simultaneous_work = parsed_entries(
        freeze(),
        work("S1-0002", committed_utc=FREEZE_UTC),
    )
    expect_failure(lambda: validate(simultaneous_work), "must postdate the freeze tag")
    fake_work = lambda sha, freeze_sha: (
        resolve_commit(sha, freeze_sha)
        if sha == SHA
        else policy.CommitEvidence("missing", None, False, False)
    )
    expect_failure(
        lambda: validate(fake_work_entries, resolve_commit=fake_work),
        "not a commit",
    )
    non_main = lambda sha, freeze_sha: (
        resolve_commit(sha, freeze_sha)
        if sha == SHA
        else policy.CommitEvidence(
            "commit", resolve_commit(sha, freeze_sha).committed_utc, False, True
        )
    )
    expect_failure(
        lambda: validate(fake_work_entries, resolve_commit=non_main),
        "not reachable from main",
    )
    not_descendant = lambda sha, freeze_sha: (
        resolve_commit(sha, freeze_sha)
        if sha == SHA
        else policy.CommitEvidence(
            "commit", resolve_commit(sha, freeze_sha).committed_utc, True, False
        )
    )
    expect_failure(
        lambda: validate(fake_work_entries, resolve_commit=not_descendant),
        "does not descend from the freeze",
    )
    wrong_time = lambda sha, freeze_sha: (
        resolve_commit(sha, freeze_sha)
        if sha == SHA
        else policy.CommitEvidence(
            "commit", datetime(2026, 9, 3, tzinfo=timezone.utc), True, True
        )
    )
    expect_failure(
        lambda: validate(fake_work_entries, resolve_commit=wrong_time),
        "differs from the commit object",
    )
    naive_work_time = lambda sha, freeze_sha: (
        resolve_commit(sha, freeze_sha)
        if sha == SHA
        else policy.CommitEvidence(
            "commit", datetime(2026, 9, 2, 12), True, True
        )
    )
    expect_failure(
        lambda: validate(fake_work_entries, resolve_commit=naive_work_time),
        "work commit timestamp must be timezone-aware",
    )

    too_early = complete_log()
    too_early[-1] = sign_off(
        "S1-0009",
        "2026-09-28",
        ["S1-0002", "S1-0003", "S1-0007", "S1-0008"],
    )
    expect_failure(
        lambda: validate(
            parsed_entries(*too_early),
            now=datetime(2026, 9, 28, 12, tzinfo=timezone.utc),
        ),
        "current UTC is before 28 full days",
    )
    backdated_signoff = complete_log()
    backdated_signoff[-1] = sign_off(
        "S1-0009",
        "2026-09-28",
        ["S1-0002", "S1-0003", "S1-0007", "S1-0008"],
    )
    expect_failure(
        lambda: validate(parsed_entries(*backdated_signoff)),
        "sign-off date is backdated",
    )

    missing_window = complete_log()
    missing_window[-1] = sign_off(
        "S1-0009",
        "2026-09-29",
        ["S1-0002", "S1-0003", "S1-0007"],
    )
    expect_failure(lambda: validate(parsed_entries(*missing_window)), "all four windows")

    bad_maintainer = complete_log()
    bad_maintainer[-1] = sign_off(
        "S1-0009",
        "2026-09-29",
        ["S1-0002", "S1-0003", "S1-0007", "S1-0008"],
        maintainer="LionSR",
    )
    expect_failure(
        lambda: validate(parsed_entries(*bad_maintainer)),
        "github:lowercase-login",
    )
    bad_reviewer = complete_log()
    bad_reviewer[-1] = sign_off(
        "S1-0009",
        "2026-09-29",
        ["S1-0002", "S1-0003", "S1-0007", "S1-0008"],
        reviewer="github:Independent-Reviewer",
    )
    expect_failure(
        lambda: validate(parsed_entries(*bad_reviewer)),
        "github:lowercase-login",
    )
    same_signer = complete_log()
    same_signer[-1] = sign_off(
        "S1-0009",
        "2026-09-29",
        ["S1-0002", "S1-0003", "S1-0007", "S1-0008"],
        reviewer="github:lionsr",
    )
    expect_failure(lambda: validate(parsed_entries(*same_signer)), "independent")

    breaking_without_reset = parsed_entries(
        freeze(),
        friction("S1-0002", "2026-09-02", "breaking-required"),
        work("S1-0003"),
    )
    expect_failure(lambda: validate(breaking_without_reset), "followed immediately")

    unresolved = parsed_entries(
        freeze(),
        work("S1-0002"),
        work("S1-0003"),
        friction("S1-0004", "2026-09-10", "fix-compatible"),
        work("S1-0005"),
        work("S1-0006"),
        sign_off(
            "S1-0007",
            "2026-09-29",
            ["S1-0002", "S1-0003", "S1-0005", "S1-0006"],
        ),
    )
    expect_failure(lambda: validate(unresolved), "unresolved friction")

    policy.check_append_only(SOAK_TEXT, SOAK_TEXT + freeze())
    expect_failure(
        lambda: policy.check_append_only(
            SOAK_TEXT,
            SOAK_TEXT.replace("append-only evidence", "rewritten evidence") + freeze(),
        ),
        "changed existing bytes",
    )

    invented_field = freeze().replace(
        'evidence = "https://example.test/freeze"',
        'evidence = "https://example.test/freeze"\ninvented = true',
    )
    expect_failure(
        lambda: validate(parsed_entries(invented_field)),
        "fields differ",
    )

    print("PASS: tenkz policy anchors tags, work, identities, and soak resets")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
