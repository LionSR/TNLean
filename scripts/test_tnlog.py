#!/usr/bin/env python3
"""Focused contract tests for the shared tenkz event parser."""

from tenkz_audit import Event as AuditEvent
from tenkz_audit import FIELD_VALIDATORS as AUDIT_FIELD_VALIDATORS
from tenkz_audit import Picture as AuditPicture
from tenkz_audit import parse_log as audit_parse_log
from tenkzlib.tnlog import Event, FIELD_VALIDATORS, Picture, parse_log


def main() -> int:
    hard: list[tuple[str, str, str]] = []
    advisory: list[tuple[str, str, str]] = []
    parsed = parse_log(
        "\n".join(
            (
                "picture|id=1|lang=grid",
                "frame|picture=1|scope=picture|map=rotate(30)|"
                "a=0.866025|b=-0.5|c=0.5|d=0.866025",
                "atom|picture=1|cell=1-2|name=A|kind=tensor",
                "bond|picture=1|row=1|from=2|to=3|dir=none",
                "boundary|picture=1|virtual-west=1|virtual-east=2|"
                "physical-up=3|physical-down=4",
                "tree|picture=0|id=1|style=wire|leaves=2|vertices=1|"
                "topology=(1,2)|role=none|species=plain",
            )
        ),
        source_name="case.tnlog",
        known_langs={"grid"},
        hard=lambda *finding: hard.append(finding),
        advisory=lambda *finding: advisory.append(finding),
    )
    assert not hard
    assert not advisory
    assert [event.kind for event in parsed.events] == [
        "picture",
        "frame",
        "atom",
        "bond",
        "boundary",
        "tree",
    ]
    assert all(event.valid for event in parsed.events)
    assert len(parsed.pictures) == 1
    picture = parsed.pictures[0]
    assert picture is parsed.by_id[1]
    assert [event.kind for event in picture.content()] == ["atom", "bond"]
    assert picture.boundary() == (1, 2, 3, 4)
    assert picture.ncols() == 3

    malformed: list[tuple[str, str, str]] = []
    notes: list[tuple[str, str, str]] = []
    malformed_parsed = parse_log(
        "\n".join(
            (
                "picture|id=1|lang=future",
                "picture|id=1|lang=grid",
                "atom|picture=oops|cell=1-1|name=A|kind=tensor",
                "frame|picture=1|scope=atom|map=rotate(30)|"
                "a=bad|b=0|c=0|d=1",
                "check|relation=1|result=equal",
                "check|scope=9|scope=1|relation=1|result=equal",
                "check|picture=1|scope=1|relation=1|result=equal",
                "check|scope=1|relation=1|result=off",
                "check|scope=1|relation=1|result=equal",
                "check|scope=1|result=mismatch",
                "check|scope=1|result=malformed|reason=relation-count",
                "mystery|picture=2|bare",
            )
        ),
        source_name="bad.tnlog",
        known_langs={"grid"},
        hard=lambda *finding: malformed.append(finding),
        advisory=lambda *finding: notes.append(finding),
    )
    assert {finding[0] for finding in malformed} == {
        "duplicate-picture",
        "malformed-event",
        "dangling-picture-ref",
    }
    assert {finding[0] for finding in notes} == {"unknown-event", "unknown-lang"}
    assert any(
        finding[0] == "malformed-event"
        and "check event lacks required field(s): scope" in finding[2]
        for finding in malformed
    )
    assert any("duplicate field 'scope'" in finding[2] for finding in malformed)
    assert any(
        "check event forbids field(s): picture" in finding[2]
        for finding in malformed
    )
    assert all(
        not event.valid
        for event in malformed_parsed.events
        if event.kind == "check"
    )
    assert not malformed_parsed.by_id[1].events

    stale_findings: list[tuple[str, str, str]] = []
    stale_owner = parse_log(
        "picture|id=k1|lang=kernel\n"
        "atom|id=atom-1|kind=tn\n"
        "picture|id=k2|lang=kernel|scope=1|scope=2\n"
        "kernel-boundary|signature=bad\n",
        source_name="stale-owner.tnlog",
        known_langs={"kernel"},
        hard=lambda *finding: stale_findings.append(finding),
    )
    assert {finding[0] for finding in stale_findings} == {"malformed-event"}
    assert [event.kind for event in stale_owner.by_id["k1"].events] == ["atom"]
    assert not next(
        event for event in stale_owner.events
        if event.kind == "kernel-boundary"
    ).valid

    check_delimiter_findings: list[tuple[str, str, str]] = []
    check_delimiter = parse_log(
        "picture|id=k1|lang=kernel\n"
        "atom|id=atom-1|kind=tn\n"
        "check|scope=1|relation=1|result=equal|signature=open:e\n"
        "kernel-boundary|signature=open:e\n",
        source_name="check-delimiter.tnlog",
        known_langs={"kernel"},
        hard=lambda *finding: check_delimiter_findings.append(finding),
    )
    assert {finding[0] for finding in check_delimiter_findings} == {
        "malformed-event"
    }
    assert [event.kind for event in check_delimiter.by_id["k1"].events] == [
        "atom"
    ]
    assert not next(
        event for event in check_delimiter.events
        if event.kind == "kernel-boundary"
    ).valid

    assert AuditEvent is Event
    assert AuditPicture is Picture
    assert AUDIT_FIELD_VALIDATORS is FIELD_VALIDATORS
    assert audit_parse_log is parse_log
    print("tnlog: typed parsing, diagnostics, picture grouping, and shims passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
