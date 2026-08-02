#!/usr/bin/env python3
"""Perturbation tests for the pure tenkz release-evidence state machine."""

from __future__ import annotations

import sys
from dataclasses import dataclass, replace
from datetime import datetime, timedelta, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_tenkz_policy as policy


DESIGN_TEXT = (ROOT / "docs/tenkz/DESIGN.md").read_text(encoding="utf-8")
SOAK_TEXT = (ROOT / "docs/tenkz/SOAK-1.0.md").read_text(encoding="utf-8")
ACTIVATION = "#900"
SOURCE = "#901"
FREEZE_RECORD = "#902"
FORMAL_WORK = "#903"
FORMAL_RECORD = "#904"
RMP_WORK = "#905"
RMP_RECORD = "#906"
SIGNOFF_RECORD = "#907"
RELEASE_PREP = "#920"
SHA = "a" * 40
TAG_OBJECT = "b" * 40
FINAL_TAG_OBJECT = "c" * 40
FREEZE_TIME = datetime(2026, 9, 1, 12, 0, 10, tzinfo=timezone.utc)
FORMAL_MERGE = FREEZE_TIME + timedelta(seconds=1)
RMP_MERGE = FREEZE_TIME + timedelta(seconds=2)
RELEASE_MERGE = FREEZE_TIME + timedelta(seconds=2, microseconds=500_000)
SIGNOFF_REVIEW = FREEZE_TIME + timedelta(seconds=3)
SIGNOFF_MERGE = FREEZE_TIME + timedelta(seconds=11)
PREREQUISITES = '["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]'
INVENTORY_DIGEST = "d" * 64
TEST_CODE_TREE = "e" * 40
TEST_SUPPORT_TREE = "1" * 40
POLICY_DIGEST = "f" * 64

ARMED_POLICY = {
    **policy.EXPECTED_POLICY,
    "policy": {
        **policy.EXPECTED_POLICY["policy"],
        "enforcement": "armed",
        "release_test_inventory_sha256": INVENTORY_DIGEST,
        "release_test_code_tree": TEST_CODE_TREE,
        "release_test_support_tree": TEST_SUPPORT_TREE,
    },
}
ARMED_SOAK = {
    **policy.EXPECTED_SOAK,
    "soak": {
        **policy.EXPECTED_SOAK["soak"],
        "enforcement": "armed",
        "policy_sha256": POLICY_DIGEST,
        "armed_by_pr": ACTIVATION,
    },
}
ARMED_DESIGN_TEXT = (
    DESIGN_TEXT.replace('enforcement = "pending"', 'enforcement = "armed"', 1)
    .replace(
        'release_test_inventory_sha256 = "pending"',
        f'release_test_inventory_sha256 = "{INVENTORY_DIGEST}"',
        1,
    )
    .replace(
        'release_test_code_tree = "pending"',
        f'release_test_code_tree = "{TEST_CODE_TREE}"',
        1,
    )
    .replace(
        'release_test_support_tree = "pending"',
        f'release_test_support_tree = "{TEST_SUPPORT_TREE}"',
        1,
    )
)
ARMED_SOAK_TEXT = (
    SOAK_TEXT.replace('enforcement = "pending"', 'enforcement = "armed"', 1)
    .replace('policy_sha256 = "pending"', f'policy_sha256 = "{POLICY_DIGEST}"', 1)
    .replace('armed_by_pr = "pending"', f'armed_by_pr = "{ACTIVATION}"', 1)
)


def oid(number: int) -> str:
    return f"{number:040x}"


FREEZE_PAYLOAD_BLOBS = tuple(oid(10_000 + index) for index in range(6))
FINAL_PAYLOAD_BLOBS = tuple(oid(20_000 + index) for index in range(6))


def block(contents: str) -> str:
    return f"\n```toml tenkz-soak-entry-v1\n[entry]\n{contents.strip()}\n```\n"


def freeze(
    entry_id: str = "S1-0001",
    *,
    record_pr: str = FREEZE_RECORD,
    attempt: int = 1,
    source_pr: str = SOURCE,
    source_sha: str = SHA,
    tag_object: str = TAG_OBJECT,
    tag: str = "tenkz-v0.9.0",
    prerequisites: str = PREREQUISITES,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "freeze"
record_pr = "{record_pr}"
attempt = {attempt}
source_pr = "{source_pr}"
source_sha = "{source_sha}"
freeze_tag_object = "{tag_object}"
freeze_tag = "{tag}"
prerequisites = {prerequisites}
evidence = "source, tag, and issue evidence"'''
    )


def work(
    entry_id: str,
    record_pr: str,
    work_pr: str,
    work_class: str,
    *,
    attempt: int = 1,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "work"
record_pr = "{record_pr}"
attempt = {attempt}
work_pr = "{work_pr}"
class = "{work_class}"
summary = "ordinary qualifying work"
evidence = "immutable PR evidence"'''
    )


def friction(
    entry_id: str,
    record_pr: str,
    triage: str,
    *,
    attempt: int = 1,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "friction"
record_pr = "{record_pr}"
attempt = {attempt}
surface = "tex-api"
triage = "{triage}"
summary = "observed interface friction"
evidence = "reproducer and triage"'''
    )


def resolution(
    entry_id: str,
    record_pr: str,
    target: str,
    *,
    attempt: int = 1,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "resolution"
record_pr = "{record_pr}"
attempt = {attempt}
friction = "{target}"
summary = "compatible repair"
evidence = "merged repair evidence"'''
    )


def reset(
    entry_id: str,
    record_pr: str,
    cause: str,
    target: str,
    *,
    attempt: int = 1,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "reset"
record_pr = "{record_pr}"
attempt = {attempt}
cause = "{cause}"
target = "{target}"
reason = "attempt evidence requires a new freeze"
evidence = "verified reset cause"'''
    )


def correction(
    entry_id: str,
    record_pr: str,
    target: str,
    *,
    attempt: int = 1,
) -> str:
    return block(
        f'''id = "{entry_id}"
kind = "correction"
record_pr = "{record_pr}"
attempt = {attempt}
target = "{target}"
summary = "additional explanation"
evidence = "historical clarification"'''
    )


def sign_off(
    entry_id: str,
    record_pr: str,
    work_ids: list[str],
    *,
    attempt: int = 1,
    freeze_id: str = "S1-0001",
    source_sha: str = SHA,
    release_prep_pr: str = RELEASE_PREP,
    reviewer: str = "github:release-reviewer",
) -> str:
    work_array = ", ".join(f'"{item}"' for item in work_ids)
    return block(
        f'''id = "{entry_id}"
kind = "sign-off"
record_pr = "{record_pr}"
attempt = {attempt}
freeze = "{freeze_id}"
source_sha = "{source_sha}"
release_prep_pr = "{release_prep_pr}"
release_tag = "tenkz-v1.0.0"
reviewer = "{reviewer}"
work_evidence = [{work_array}]
decision = "release"'''
    )


def review(
    login: str,
    submitted_at: datetime,
    head: str,
    *,
    state: str = "APPROVED",
    dismissed: bool = False,
) -> policy.ReviewEvidence:
    return policy.ReviewEvidence(login, state, submitted_at, head, dismissed)


def merged_pr(
    number: int,
    merged_at: datetime,
    *,
    author: str = "author",
    merger: str = "lionsr",
    reviews: tuple[policy.ReviewEvidence, ...] = (),
) -> policy.PullRequestEvidence:
    return policy.PullRequestEvidence(
        in_repository=True,
        base_ref_name="main",
        author_login=author,
        head_oid=oid(number * 10),
        merged=True,
        merged_at=merged_at,
        merged_by_login=merger,
        merge_commit_oid=oid(number * 10 + 1),
        reviews=reviews,
        reviews_complete=True,
        integration_reachable_from_main=True,
        integration_tree_matches_head=True,
        integration_strict_descendant_of_anchor=True,
    )


def candidate_pr(
    number: int,
    *,
    author: str = "author",
    reviews: tuple[policy.ReviewEvidence, ...] = (),
) -> policy.PullRequestEvidence:
    return policy.PullRequestEvidence(
        in_repository=True,
        base_ref_name="main",
        author_login=author,
        head_oid=oid(number * 10),
        merged=False,
        reviews=reviews,
        reviews_complete=True,
    )


@dataclass
class Context:
    prs: dict[str, policy.PullRequestEvidence]
    activation_diff: policy.ActivationDiffEvidence
    records: dict[str, policy.RecordDiffEvidence]
    work_diffs: dict[str, policy.WorkDiffEvidence]
    release_preps: dict[str, policy.ReleasePrepEvidence]
    payloads: dict[tuple[str, str], policy.ReleasePayloadEvidence]
    tags: dict[str, policy.TagEvidence]
    issues: dict[str, policy.IssueEvidence]

    def resolve_replay_activation_diff(self, _ref: str) -> policy.ActivationDiffEvidence:
        return self.activation_diff

    def resolve_replay_pr(self, ref: str, _anchor: str | None) -> policy.PullRequestEvidence:
        return self.prs[ref]

    def resolve_replay_record_diff(
        self,
        entry_id: str,
        _record_pr: str,
        _source_sha: str | None,
    ) -> policy.RecordDiffEvidence:
        return self.records[entry_id]

    def resolve_replay_work_diff(self, ref: str) -> policy.WorkDiffEvidence:
        return self.work_diffs[ref]

    def resolve_replay_release_prep(
        self,
        ref: str,
        _paths: tuple[str, ...],
        _work_integrations: tuple[str, ...],
    ) -> policy.ReleasePrepEvidence:
        return self.release_preps[ref]

    def resolve_replay_release_payload(
        self,
        tree_oid: str,
        tag: str,
        _contract: policy.ReleaseContract,
    ) -> policy.ReleasePayloadEvidence:
        return self.payloads[(tree_oid, tag)]

    def resolve_replay_freeze_tag(self, tag: str) -> policy.TagEvidence:
        assert tag != policy.FINAL_TAG
        return self.tags[tag]

    def resolve_current_final_tag(self, tag: str) -> policy.TagEvidence:
        assert tag == policy.FINAL_TAG
        return self.tags[tag]

    def resolve_replay_issue(self, issue: str) -> policy.IssueEvidence:
        return self.issues[issue]


def payload_evidence(
    tree_oid: str,
    tag: str,
    blob_oids: tuple[str, ...],
) -> policy.ReleasePayloadEvidence:
    contract = policy.policy_rules(ARMED_POLICY)[4]
    return policy.ReleasePayloadEvidence(
        validated_tree_oid=tree_oid,
        validated_tag=tag,
        validated_contract=contract,
        complete=True,
        manifest_path=contract.manifest_path(tag),
        regular_distinct_paths=True,
        manifest_contract_valid=True,
        artifact_declarations_agree=True,
        inventory_digest_matches=True,
        inventory_contract_valid=True,
        test_code_tree_matches=True,
        test_support_tree_matches=True,
        inventory_data_paths_within_mutable_roots=True,
        executable_dependencies_within_code_tree=True,
        acceptance_dependencies_within_support_tree=True,
        subject_data_cannot_reduce_coverage=True,
        hermetic_execution_contract_valid=True,
        payload_execution_receipts_complete_and_matching=True,
        test_execution_complete=True,
        compatibility_tests_passed=True,
        payload_blob_oids=blob_oids,
    )


def context() -> Context:
    activation_head = oid(9000)
    formal_head = oid(9030)
    rmp_head = oid(9050)
    signoff_head = oid(9070)
    release_head = oid(9200)
    prs = {
        ACTIVATION: merged_pr(
            900,
            FREEZE_TIME - timedelta(seconds=70),
            author="policy-author",
            reviews=(
                review(
                    "policy-reviewer",
                    FREEZE_TIME - timedelta(seconds=80),
                    activation_head,
                ),
            ),
        ),
        SOURCE: replace(
            merged_pr(
                901,
                FREEZE_TIME - timedelta(seconds=20),
                author="source-author",
                reviews=(
                    review(
                        "source-reviewer",
                        FREEZE_TIME - timedelta(seconds=21),
                        oid(9010),
                    ),
                ),
            ),
            merge_commit_oid=SHA,
        ),
        FREEZE_RECORD: merged_pr(902, FREEZE_TIME, author="record-author"),
        FORMAL_WORK: merged_pr(
            903,
            FORMAL_MERGE,
            author="formal-author",
            reviews=(
                review(
                    "formal-reviewer",
                    FORMAL_MERGE - timedelta(microseconds=1),
                    formal_head,
                ),
            ),
        ),
        FORMAL_RECORD: merged_pr(
            904,
            FREEZE_TIME + timedelta(seconds=5),
            author="record-author",
        ),
        RMP_WORK: merged_pr(
            905,
            RMP_MERGE,
            author="rmp-author",
            reviews=(
                review(
                    "rmp-reviewer",
                    RMP_MERGE - timedelta(microseconds=1),
                    rmp_head,
                ),
            ),
        ),
        RMP_RECORD: merged_pr(
            906,
            FREEZE_TIME + timedelta(seconds=7),
            author="record-author",
        ),
        RELEASE_PREP: merged_pr(
            920,
            RELEASE_MERGE,
            author="release-prep-author",
            reviews=(
                review(
                    "release-prep-reviewer",
                    RELEASE_MERGE - timedelta(microseconds=1),
                    release_head,
                ),
            ),
        ),
        SIGNOFF_RECORD: merged_pr(
            907,
            SIGNOFF_MERGE,
            author="release-author",
            reviews=(review("release-reviewer", SIGNOFF_REVIEW, signoff_head),),
        ),
    }
    entry_records = {
        "S1-0001": FREEZE_RECORD,
        "S1-0002": FORMAL_RECORD,
        "S1-0003": RMP_RECORD,
        "S1-0004": SIGNOFF_RECORD,
    }
    activation_diff = policy.ActivationDiffEvidence(
        validated_pr_ref=ACTIVATION,
        validated_head_oid=activation_head,
        complete=True,
        candidate_main_is_ancestor_of_head=True,
        unique_merge_base=True,
        exact_seven_scalar_replacements=True,
        inventory_digest_matches=True,
        test_code_tree_matches=True,
        test_support_tree_matches=True,
        inventory_data_paths_within_mutable_roots=True,
        executable_dependencies_within_code_tree=True,
        acceptance_dependencies_within_support_tree=True,
        subject_data_cannot_reduce_coverage=True,
        hermetic_execution_contract_valid=True,
        supervisor_self_test_receipt_valid=True,
        policy_digest_matches=True,
        ledger_prefix_matches=True,
    )
    records = {
        entry_id: policy.RecordDiffEvidence(
            validated_pr_ref=record_ref,
            validated_head_oid=prs[record_ref].head_oid,
            complete=True,
            unique_merge_base=True,
            integration_parent_count=1,
            base_lacks_entry=True,
            appends_exact_entry=True,
            pinned_prefix_unchanged=True,
            other_entries_unchanged=True,
            no_other_path_changes=True,
            candidate_main_is_ancestor_of_head=True,
            integration_parent_is_ancestor_of_head=True,
            integration_second_parent_matches_head=True,
            source_to_head_is_exact_freeze_append=entry_id == "S1-0001",
            candidate_main_tip_is_source=entry_id == "S1-0001",
            integration_parent_is_source=entry_id == "S1-0001",
            candidate_main_tip_is_release_integration=entry_id == "S1-0004",
            integration_parent_is_release_integration=entry_id == "S1-0004",
            validated_release_integration=(
                prs[RELEASE_PREP].merge_commit_oid if entry_id == "S1-0004" else None
            ),
            validated_work_integrations=(
                (
                    prs[FORMAL_WORK].merge_commit_oid,
                    prs[RMP_WORK].merge_commit_oid,
                )
                if entry_id == "S1-0004"
                else None
            ),
        )
        for entry_id, record_ref in entry_records.items()
    }
    work_diffs = {
        FORMAL_WORK: policy.WorkDiffEvidence(
            complete=True,
            integration_parent_count=1,
            unique_merge_base=True,
            integration_parent_is_ancestor_of_head=True,
            integration_second_parent_matches_head=True,
            policy_paths_untouched=True,
            excluded_paths_applied=True,
            semantic_add_or_modify_classes=("formalization-or-blueprint",),
            semantic_lean_changed=True,
            semantic_blueprint_changed=False,
            semantic_rmp_changed=False,
            lean_modules_build=True,
            proof_integrity_clean=True,
            blueprint_checkdecls_passed=True,
            blueprint_build_passed=True,
            rmp_targets_resolved=True,
            rmp_stages_complete=True,
            rmp_checks_passed=True,
        ),
        RMP_WORK: policy.WorkDiffEvidence(
            complete=True,
            integration_parent_count=2,
            unique_merge_base=True,
            integration_parent_is_ancestor_of_head=True,
            integration_second_parent_matches_head=True,
            policy_paths_untouched=True,
            excluded_paths_applied=True,
            semantic_add_or_modify_classes=("rmp-benchmark",),
            semantic_lean_changed=False,
            semantic_blueprint_changed=False,
            semantic_rmp_changed=True,
            lean_modules_build=True,
            proof_integrity_clean=True,
            blueprint_checkdecls_passed=True,
            blueprint_build_passed=True,
            rmp_targets_resolved=True,
            rmp_stages_complete=True,
            rmp_checks_passed=True,
        ),
    }
    work_integrations = (
        prs[FORMAL_WORK].merge_commit_oid,
        prs[RMP_WORK].merge_commit_oid,
    )
    assert all(isinstance(item, str) for item in work_integrations)
    release_preps = {
        RELEASE_PREP: policy.ReleasePrepEvidence(
            validated_pr_ref=RELEASE_PREP,
            validated_head_oid=release_head,
            validated_manifest_path="docs/tenkz/releases/tenkz-v1.0.0.toml",
            validated_changed_paths=policy.policy_rules(ARMED_POLICY)[4].release_varying_paths(
                policy.FINAL_TAG
            ),
            validated_work_integrations=work_integrations,
            complete=True,
            integration_parent_count=1,
            unique_merge_base=True,
            integration_parent_is_ancestor_of_head=True,
            integration_second_parent_matches_head=True,
            integration_descends_from_work_integrations=True,
            exact_release_varying_path_diff=True,
        )
    }
    payloads = {
        (SHA, "tenkz-v0.9.0"): payload_evidence(
            SHA,
            "tenkz-v0.9.0",
            FREEZE_PAYLOAD_BLOBS,
        ),
        (release_head, policy.FINAL_TAG): payload_evidence(
            release_head,
            policy.FINAL_TAG,
            FINAL_PAYLOAD_BLOBS,
        ),
        (signoff_head, policy.FINAL_TAG): payload_evidence(
            signoff_head,
            policy.FINAL_TAG,
            FINAL_PAYLOAD_BLOBS,
        ),
        (oid(9071), policy.FINAL_TAG): payload_evidence(
            oid(9071),
            policy.FINAL_TAG,
            FINAL_PAYLOAD_BLOBS,
        ),
    }
    issues = {
        issue: policy.IssueEvidence(
            True,
            True,
            FREEZE_TIME - timedelta(seconds=100),
        )
        for issue in ("#5086", "#4699", "#4162", "#4703", "#4708", "#4163")
    }
    return Context(
        prs,
        activation_diff,
        records,
        work_diffs,
        release_preps,
        payloads,
        {
            "tenkz-v0.9.0": policy.TagEvidence(TAG_OBJECT, "tag", SHA, True),
            policy.FINAL_TAG: policy.TagEvidence(None, None, None, exists=False),
        },
        issues,
    )


def parsed_entries(*blocks: str) -> list[dict]:
    _schema, entries = policy.parse_soak_text(ARMED_SOAK_TEXT + "".join(blocks))
    return entries


def audit_evidence(
    boundary: str | None,
    invalid_entries: tuple[str, ...] = (),
) -> policy.AuditEvidence:
    return policy.AuditEvidence(boundary, invalid_entries, True, True)


def protected_tags() -> policy.TagProtectionEvidence:
    return policy.TagProtectionEvidence(
        repository_rulesets_complete=True,
        organization_rulesets_complete=True,
        credential_has_write_visibility=True,
        details_unredacted=True,
        namespace_fully_covered=True,
        applicable_rulesets_active=True,
        updates_forbidden=True,
        deletions_forbidden=True,
        bypass_actors=(),
        unambiguous=True,
    )


def validate(blocks: list[str], facts: Context, **overrides) -> str:
    entries = parsed_entries(*blocks)
    if "audit" not in overrides:
        boundary: str | None = None
        for entry in entries:
            record = facts.prs.get(entry["record_pr"])
            if record is None or record.merged is not True:
                break
            boundary = entry["id"]
        overrides["audit"] = audit_evidence(boundary)
    arguments = {
        "policy": ARMED_POLICY,
        "soak": ARMED_SOAK,
        "resolve_replay_pr": facts.resolve_replay_pr,
        "resolve_replay_activation_diff": facts.resolve_replay_activation_diff,
        "resolve_replay_record_diff": facts.resolve_replay_record_diff,
        "resolve_replay_work_diff": facts.resolve_replay_work_diff,
        "resolve_replay_release_prep": facts.resolve_replay_release_prep,
        "resolve_replay_release_payload": facts.resolve_replay_release_payload,
        "resolve_replay_freeze_tag": facts.resolve_replay_freeze_tag,
        "resolve_current_final_tag": facts.resolve_current_final_tag,
        "resolve_replay_issue": facts.resolve_replay_issue,
        "tag_protection": protected_tags(),
    }
    arguments.update(overrides)
    return policy.validate_entries(entries, **arguments)


def complete_log() -> list[str]:
    return [
        freeze(),
        work(
            "S1-0002",
            FORMAL_RECORD,
            FORMAL_WORK,
            "formalization-or-blueprint",
        ),
        work("S1-0003", RMP_RECORD, RMP_WORK, "rmp-benchmark"),
        sign_off(
            "S1-0004",
            SIGNOFF_RECORD,
            ["S1-0002", "S1-0003"],
        ),
    ]


def expect_failure(action, fragment: str) -> None:
    try:
        action()
    except policy.PolicyError as error:
        assert fragment in str(error), (fragment, str(error))
    else:
        raise AssertionError(f"expected PolicyError containing {fragment!r}")


def add_record(
    facts: Context,
    entry_id: str,
    record_ref: str,
    number: int,
    merged_at: datetime,
    *,
    invalid_tree: bool = False,
    freeze_entry: bool = False,
) -> None:
    facts.prs[record_ref] = replace(
        merged_pr(number, merged_at, author="record-author"),
        integration_tree_matches_head=not invalid_tree,
    )
    facts.records[entry_id] = policy.RecordDiffEvidence(
        validated_pr_ref=record_ref,
        validated_head_oid=facts.prs[record_ref].head_oid,
        complete=True,
        unique_merge_base=True,
        integration_parent_count=1,
        base_lacks_entry=True,
        appends_exact_entry=True,
        pinned_prefix_unchanged=True,
        other_entries_unchanged=True,
        no_other_path_changes=True,
        candidate_main_is_ancestor_of_head=True,
        integration_parent_is_ancestor_of_head=True,
        integration_second_parent_matches_head=True,
        source_to_head_is_exact_freeze_append=freeze_entry,
        candidate_main_tip_is_source=freeze_entry,
        integration_parent_is_source=freeze_entry,
    )


def add_freeze_facts(
    facts: Context,
    entry_id: str,
    *,
    source_ref: str,
    source_number: int,
    source_sha: str,
    record_ref: str,
    record_number: int,
    tag: str,
    tag_object: str,
    merged_at: datetime,
) -> None:
    source_time = merged_at - timedelta(seconds=1)
    facts.prs[source_ref] = replace(
        merged_pr(
            source_number,
            source_time,
            reviews=(
                review(
                    f"source-reviewer-{source_number}",
                    source_time - timedelta(microseconds=1),
                    oid(source_number * 10),
                ),
            ),
        ),
        merge_commit_oid=source_sha,
    )
    add_record(
        facts,
        entry_id,
        record_ref,
        record_number,
        merged_at,
        freeze_entry=True,
    )
    facts.tags[tag] = policy.TagEvidence(tag_object, "tag", source_sha, True)
    facts.payloads[(source_sha, tag)] = payload_evidence(
        source_sha,
        tag,
        tuple(oid(30_000 + source_number * 10 + index) for index in range(6)),
    )


def main() -> int:
    assert policy.validate_policy_text(DESIGN_TEXT) == policy.EXPECTED_POLICY
    schema, empty_entries = policy.parse_soak_text(SOAK_TEXT)
    assert schema == policy.EXPECTED_SOAK
    assert policy.validate_entries(empty_entries) == "not-started"
    assert policy.validate_policy_text(ARMED_DESIGN_TEXT) == ARMED_POLICY
    armed_schema, armed_empty_entries = policy.parse_soak_text(ARMED_SOAK_TEXT)
    assert armed_schema["soak"]["enforcement"] == "armed"
    assert armed_schema["soak"]["policy_sha256"] == POLICY_DIGEST
    assert armed_schema["soak"]["armed_by_pr"] == ACTIVATION
    assert armed_schema == ARMED_SOAK
    assert armed_empty_entries == []
    assert validate([], context()) == "not-started"
    empty_mixed_activation = context()
    empty_mixed_activation.activation_diff = replace(
        empty_mixed_activation.activation_diff,
        exact_seven_scalar_replacements=False,
    )
    expect_failure(
        lambda: validate([], empty_mixed_activation),
        "not exactly the seven permitted scalar replacements",
    )
    expect_failure(
        lambda: validate(
            [freeze()],
            context(),
            policy=policy.EXPECTED_POLICY,
            soak=policy.EXPECTED_SOAK,
        ),
        "entries require armed policy enforcement",
    )
    assert "minimum_days" not in schema["soak"]
    assert "work_classes" not in schema["soak"]
    assert "work_excluded_paths" not in schema["soak"]
    assert policy.EXPECTED_POLICY["policy"]["work_excluded_paths"] == [
        "TNLean/Archive/**"
    ]
    assert "event_format_implementation" not in policy.EXPECTED_POLICY["policy"]

    # Both qualifying merges, the sign-off review, and sign-off merge occur in
    # one minute.  Strict event ordering, not elapsed calendar time, is enough.
    assert validate(complete_log(), context()) == "signed-off-awaiting-tag"

    candidate = context()
    candidate_head = candidate.prs[SIGNOFF_RECORD].head_oid
    assert candidate_head is not None
    candidate.prs[SIGNOFF_RECORD] = candidate_pr(
        907,
        author="release-author",
        reviews=(
            review(
                "release-reviewer",
                SIGNOFF_REVIEW,
                candidate_head,
            ),
        ),
    )
    assert validate(complete_log(), candidate) == "sign-off-pending"

    released = context()
    released.tags[policy.FINAL_TAG] = policy.TagEvidence(
        FINAL_TAG_OBJECT,
        "tag",
        oid(9071),
        exists=True,
        validated_entry_id="S1-0004",
        validated_record_pr=SIGNOFF_RECORD,
        commit_is_validated_record_integration=True,
    )
    assert validate(complete_log(), released) == "released"

    # The current-validity audit runs forever while replay callbacks retain the
    # integration-time history.  Before the tag, drift enters the reset queue;
    # once a final-tag ref exists it is a hard incident and never reopens it.
    expect_failure(
        lambda: validate(
            complete_log(),
            released,
            audit=audit_evidence("S1-0004", ("S1-0004",)),
        ),
        "final tag exists while release evidence requires reset",
    )
    expect_failure(
        lambda: validate(
            complete_log(),
            released,
            tag_protection=replace(protected_tags(), updates_forbidden=False),
        ),
        "tag updates are not forbidden",
    )
    expect_failure(
        lambda: validate(
            complete_log(),
            released,
            tag_protection=replace(protected_tags(), details_unredacted=False),
        ),
        "omitted or redacted",
    )
    expect_failure(
        lambda: validate(
            complete_log(),
            released,
            tag_protection=replace(protected_tags(), bypass_actors=("admin",)),
        ),
        "has a bypass actor",
    )
    expect_failure(
        lambda: validate(
            complete_log(),
            released,
            tag_protection=replace(protected_tags(), bypass_actors=None),
        ),
        "bypass actors are unavailable",
    )
    expect_failure(
        lambda: validate(
            complete_log(),
            released,
            tag_protection=replace(protected_tags(), organization_rulesets_complete=False),
        ),
        "organization ruleset pagination is incomplete",
    )

    unclassified_released_drift = context()
    unclassified_released_drift.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    unclassified_released_drift.prs[SIGNOFF_RECORD] = replace(
        unclassified_released_drift.prs[SIGNOFF_RECORD],
        reviews_complete=False,
    )
    expect_failure(
        lambda: validate(complete_log(), unclassified_released_drift),
        "final tag exists while release evidence requires reset",
    )

    lightweight_final = context()
    lightweight_final.tags[policy.FINAL_TAG] = policy.TagEvidence(
        FINAL_TAG_OBJECT,
        "commit",
        oid(9071),
        exists=True,
    )
    expect_failure(
        lambda: validate(complete_log(), lightweight_final),
        "final release tag is not annotated",
    )
    replay_before_tag_check = context()
    replay_before_tag_check.tags[policy.FINAL_TAG] = lightweight_final.tags[policy.FINAL_TAG]
    replay_before_tag_check.activation_diff = replace(
        replay_before_tag_check.activation_diff,
        exact_seven_scalar_replacements=False,
    )
    expect_failure(
        lambda: validate(complete_log(), replay_before_tag_check),
        "not exactly the seven permitted scalar replacements",
    )

    wrong_final_target = context()
    wrong_final_target.tags[policy.FINAL_TAG] = policy.TagEvidence(
        FINAL_TAG_OBJECT,
        "tag",
        oid(9991),
        exists=True,
        validated_entry_id="S1-0004",
        validated_record_pr=SIGNOFF_RECORD,
        commit_is_validated_record_integration=False,
    )
    expect_failure(
        lambda: validate(complete_log(), wrong_final_target),
        "does not target the validated sign-off integration",
    )

    premature_final = context()
    premature_final.tags[policy.FINAL_TAG] = policy.TagEvidence(
        FINAL_TAG_OBJECT,
        "tag",
        oid(9071),
        exists=True,
        validated_entry_id="S1-0004",
        validated_record_pr=SIGNOFF_RECORD,
        commit_is_validated_record_integration=True,
    )
    expect_failure(
        lambda: validate(complete_log()[:3], premature_final),
        "without a successfully validated sign-off",
    )

    inconsistent_absent = context()
    inconsistent_absent.tags[policy.FINAL_TAG] = replace(
        inconsistent_absent.tags[policy.FINAL_TAG],
        validated_entry_id="S1-0004",
    )
    expect_failure(
        lambda: validate(complete_log(), inconsistent_absent),
        "absent final-tag evidence is inconsistent",
    )

    forged_release = context()
    forged_release.records["S1-0003"] = replace(
        forged_release.records["S1-0004"],
        validated_pr_ref=SIGNOFF_RECORD,
        validated_head_oid=forged_release.prs[SIGNOFF_RECORD].head_oid,
    )
    forged_release.tags[policy.FINAL_TAG] = replace(
        released.tags[policy.FINAL_TAG],
        validated_entry_id="S1-0003",
    )
    forged_log = [
        freeze(),
        work(
            "S1-0002",
            FORMAL_RECORD,
            FORMAL_WORK,
            "formalization-or-blueprint",
        ),
        sign_off("S1-0003", SIGNOFF_RECORD, ["S1-0002"]),
    ]
    expect_failure(
        lambda: validate(forged_log, forged_release),
        "lacks one work class",
    )

    incomplete_audit = policy.AuditEvidence("S1-0004", (), False, True)
    expect_failure(
        lambda: validate(complete_log(), context(), audit=incomplete_audit),
        "audit snapshot is incomplete",
    )
    inexact_target_audit = policy.AuditEvidence("S1-0004", (), True, False)
    expect_failure(
        lambda: validate(complete_log(), context(), audit=inexact_target_audit),
        "audit validation target is not exact",
    )

    mixed_activation = context()
    mixed_activation.activation_diff = replace(
        mixed_activation.activation_diff,
        exact_seven_scalar_replacements=False,
    )
    expect_failure(
        lambda: validate([freeze()], mixed_activation),
        "not exactly the seven permitted scalar replacements",
    )

    wrong_activation_code_tree = context()
    wrong_activation_code_tree.activation_diff = replace(
        wrong_activation_code_tree.activation_diff,
        test_code_tree_matches=False,
    )
    expect_failure(
        lambda: validate([freeze()], wrong_activation_code_tree),
        "activation test-code tree is wrong",
    )
    wrong_activation_support_tree = context()
    wrong_activation_support_tree.activation_diff = replace(
        wrong_activation_support_tree.activation_diff,
        test_support_tree_matches=False,
    )
    expect_failure(
        lambda: validate([freeze()], wrong_activation_support_tree),
        "activation test-support tree is wrong",
    )
    activation_subject_controls_coverage = context()
    activation_subject_controls_coverage.activation_diff = replace(
        activation_subject_controls_coverage.activation_diff,
        subject_data_cannot_reduce_coverage=False,
    )
    expect_failure(
        lambda: validate([freeze()], activation_subject_controls_coverage),
        "subject data can reduce release-test coverage",
    )
    activation_unhermetic = context()
    activation_unhermetic.activation_diff = replace(
        activation_unhermetic.activation_diff,
        hermetic_execution_contract_valid=False,
    )
    expect_failure(
        lambda: validate([freeze()], activation_unhermetic),
        "hermetic execution contract is invalid",
    )
    invalid_supervisor_receipt = context()
    invalid_supervisor_receipt.activation_diff = replace(
        invalid_supervisor_receipt.activation_diff,
        supervisor_self_test_receipt_valid=False,
    )
    expect_failure(
        lambda: validate([freeze()], invalid_supervisor_receipt),
        "supervisor self-test receipt is invalid",
    )

    unapproved_source = context()
    unapproved_source.prs[SOURCE] = replace(
        unapproved_source.prs[SOURCE],
        reviews=(),
    )
    assert validate([freeze()], unapproved_source) == "reset-required:S1-0001"

    source_tree_mismatch = context()
    source_tree_mismatch.prs[SOURCE] = replace(
        source_tree_mismatch.prs[SOURCE],
        integration_tree_matches_head=False,
    )
    assert validate([freeze()], source_tree_mismatch) == "reset-required:S1-0001"

    bad_freeze_payload = context()
    bad_freeze_payload.payloads[(SHA, "tenkz-v0.9.0")] = replace(
        bad_freeze_payload.payloads[(SHA, "tenkz-v0.9.0")],
        compatibility_tests_passed=False,
    )
    assert validate([freeze()], bad_freeze_payload) == "reset-required:S1-0001"

    bad_release_payload = context()
    bad_release_payload.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        bad_release_payload.payloads[(oid(9200), policy.FINAL_TAG)],
        inventory_contract_valid=False,
    )
    assert (
        validate(complete_log(), bad_release_payload)
        == "reset-required:S1-0004"
    )

    changed_test_code = context()
    changed_test_code.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        changed_test_code.payloads[(oid(9200), policy.FINAL_TAG)],
        test_code_tree_matches=False,
    )
    assert (
        validate(complete_log(), changed_test_code)
        == "reset-required:S1-0004"
    )

    changed_test_support = context()
    changed_test_support.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        changed_test_support.payloads[(oid(9200), policy.FINAL_TAG)],
        test_support_tree_matches=False,
    )
    assert (
        validate(complete_log(), changed_test_support)
        == "reset-required:S1-0004"
    )

    undeclared_subject_data = context()
    undeclared_subject_data.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        undeclared_subject_data.payloads[(oid(9200), policy.FINAL_TAG)],
        inventory_data_paths_within_mutable_roots=False,
    )
    assert (
        validate(complete_log(), undeclared_subject_data)
        == "reset-required:S1-0004"
    )

    acceptance_from_subject = context()
    acceptance_from_subject.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        acceptance_from_subject.payloads[(oid(9200), policy.FINAL_TAG)],
        acceptance_dependencies_within_support_tree=False,
    )
    assert (
        validate(complete_log(), acceptance_from_subject)
        == "reset-required:S1-0004"
    )

    executable_from_subject = context()
    executable_from_subject.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        executable_from_subject.payloads[(oid(9200), policy.FINAL_TAG)],
        executable_dependencies_within_code_tree=False,
    )
    assert (
        validate(complete_log(), executable_from_subject)
        == "reset-required:S1-0004"
    )

    subject_reduces_coverage = context()
    subject_reduces_coverage.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        subject_reduces_coverage.payloads[(oid(9200), policy.FINAL_TAG)],
        subject_data_cannot_reduce_coverage=False,
    )
    assert (
        validate(complete_log(), subject_reduces_coverage)
        == "reset-required:S1-0004"
    )

    mismatched_receipt = context()
    mismatched_receipt.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        mismatched_receipt.payloads[(oid(9200), policy.FINAL_TAG)],
        payload_execution_receipts_complete_and_matching=False,
    )
    assert (
        validate(complete_log(), mismatched_receipt)
        == "reset-required:S1-0004"
    )

    changed_signoff_payload = context()
    changed_signoff_payload.payloads[(oid(9070), policy.FINAL_TAG)] = replace(
        changed_signoff_payload.payloads[(oid(9070), policy.FINAL_TAG)],
        payload_blob_oids=tuple(oid(21_000 + index) for index in range(6)),
    )
    assert (
        validate(complete_log(), changed_signoff_payload)
        == "reset-required:S1-0004"
    )

    failing_integration_payload = context()
    failing_integration_payload.payloads[(oid(9071), policy.FINAL_TAG)] = replace(
        failing_integration_payload.payloads[(oid(9071), policy.FINAL_TAG)],
        test_execution_complete=False,
    )
    assert (
        validate(complete_log(), failing_integration_payload)
        == "reset-required:S1-0004"
    )

    unprepared = context()
    unprepared.release_preps[RELEASE_PREP] = replace(
        unprepared.release_preps[RELEASE_PREP],
        exact_release_varying_path_diff=False,
    )
    assert validate(complete_log(), unprepared) == "reset-required:S1-0004"

    unprepared_candidate = context()
    signoff = unprepared_candidate.prs[SIGNOFF_RECORD]
    assert signoff.head_oid is not None
    unprepared_candidate.prs[SIGNOFF_RECORD] = candidate_pr(
        907,
        author="release-author",
        reviews=(review("release-reviewer", SIGNOFF_REVIEW, signoff.head_oid),),
    )
    unprepared_candidate.release_preps[RELEASE_PREP] = replace(
        unprepared_candidate.release_preps[RELEASE_PREP],
        exact_release_varying_path_diff=False,
    )
    expect_failure(
        lambda: validate(complete_log(), unprepared_candidate),
        "release diff is not exactly the policy-owned payload",
    )

    non_atomic_candidate = context()
    non_atomic_candidate.records["S1-0004"] = replace(
        non_atomic_candidate.records["S1-0004"],
        candidate_main_tip_is_release_integration=False,
    )
    assert (
        validate(complete_log(), non_atomic_candidate)
        == "reset-required:S1-0004"
    )

    non_atomic_pending = context()
    pending_head = non_atomic_pending.prs[SIGNOFF_RECORD].head_oid
    assert pending_head is not None
    non_atomic_pending.prs[SIGNOFF_RECORD] = candidate_pr(
        907,
        author="release-author",
        reviews=(review("release-reviewer", SIGNOFF_REVIEW, pending_head),),
    )
    non_atomic_pending.records["S1-0004"] = replace(
        non_atomic_pending.records["S1-0004"],
        candidate_main_tip_is_release_integration=False,
    )
    expect_failure(
        lambda: validate(complete_log(), non_atomic_pending),
        "candidate main tip differs from release integration",
    )

    non_atomic_merge = context()
    non_atomic_merge.records["S1-0004"] = replace(
        non_atomic_merge.records["S1-0004"],
        integration_parent_is_release_integration=False,
    )
    assert validate(complete_log(), non_atomic_merge) == "reset-required:S1-0004"

    release_wrong_ancestry = context()
    release_wrong_ancestry.release_preps[RELEASE_PREP] = replace(
        release_wrong_ancestry.release_preps[RELEASE_PREP],
        integration_descends_from_work_integrations=False,
    )
    assert (
        validate(complete_log(), release_wrong_ancestry)
        == "reset-required:S1-0004"
    )

    release_wrong_paths = context()
    release_wrong_paths.release_preps[RELEASE_PREP] = replace(
        release_wrong_paths.release_preps[RELEASE_PREP],
        validated_changed_paths=("docs/tenkz/releases/tenkz-v1.0.0.toml",),
    )
    assert (
        validate(complete_log(), release_wrong_paths)
        == "reset-required:S1-0004"
    )

    for submitted in (RMP_MERGE, RMP_MERGE - timedelta(microseconds=1)):
        too_early = context()
        signoff_pr = too_early.prs[SIGNOFF_RECORD]
        assert signoff_pr.head_oid is not None
        too_early.prs[SIGNOFF_RECORD] = replace(
            signoff_pr,
            reviews=(review("release-reviewer", submitted, signoff_pr.head_oid),),
        )
        assert validate(complete_log(), too_early) == "reset-required:S1-0004"

        candidate_too_early = context()
        candidate_head = candidate_too_early.prs[SIGNOFF_RECORD].head_oid
        assert candidate_head is not None
        candidate_too_early.prs[SIGNOFF_RECORD] = candidate_pr(
            907,
            author="release-author",
            reviews=(review("release-reviewer", submitted, candidate_head),),
        )
        expect_failure(
            lambda facts=candidate_too_early: validate(complete_log(), facts),
            "independent exact-head approval",
        )

    at_freeze = context()
    formal = at_freeze.prs[FORMAL_WORK]
    assert formal.head_oid is not None
    at_freeze.prs[FORMAL_WORK] = replace(
        formal,
        merged_at=FREEZE_TIME,
        reviews=(
            review(
                "formal-reviewer",
                FREEZE_TIME - timedelta(microseconds=1),
                formal.head_oid,
            ),
        ),
    )
    assert validate(complete_log()[:2], at_freeze) == "reset-required:S1-0002"

    duplicated_class = complete_log()
    duplicated_class[2] = work(
        "S1-0003",
        RMP_RECORD,
        RMP_WORK,
        "formalization-or-blueprint",
    )
    duplicated_facts = context()
    duplicated_facts.work_diffs[RMP_WORK] = replace(
        duplicated_facts.work_diffs[RMP_WORK],
    )
    expect_failure(
        lambda: validate(duplicated_class, duplicated_facts),
        "repeats work class",
    )

    repeated_pr = complete_log()
    repeated_pr[2] = work("S1-0003", RMP_RECORD, FORMAL_WORK, "rmp-benchmark")
    expect_failure(
        lambda: validate(repeated_pr, context()),
        "work_pr values must be distinct",
    )

    missing_class = [
        freeze(),
        work(
            "S1-0002",
            FORMAL_RECORD,
            FORMAL_WORK,
            "formalization-or-blueprint",
        ),
        sign_off("S1-0003", SIGNOFF_RECORD, ["S1-0002"]),
    ]
    missing_facts = context()
    missing_facts.records["S1-0003"] = missing_facts.records.pop("S1-0004")
    expect_failure(
        lambda: validate(missing_class, missing_facts),
        "lacks one work class",
    )

    invalid_class = complete_log()
    invalid_class[1] = work("S1-0002", FORMAL_RECORD, FORMAL_WORK, "documentation")
    expect_failure(
        lambda: validate(invalid_class, context()),
        "invalid work class",
    )

    wrong_signoff_set = complete_log()
    wrong_signoff_set[-1] = sign_off(
        "S1-0004",
        SIGNOFF_RECORD,
        ["S1-0001", "S1-0002"],
    )
    expect_failure(
        lambda: validate(wrong_signoff_set, context()),
        "exactly the active work entries",
    )

    third_facts = context()
    third_facts.prs["#908"] = merged_pr(
        908,
        FREEZE_TIME + timedelta(seconds=4),
        reviews=(
            review(
                "third-reviewer",
                FREEZE_TIME + timedelta(seconds=3),
                oid(9080),
            ),
        ),
    )
    third_facts.prs["#909"] = merged_pr(909, FREEZE_TIME + timedelta(seconds=8))
    third_facts.work_diffs["#908"] = policy.WorkDiffEvidence(
        complete=True,
        integration_parent_count=1,
        unique_merge_base=True,
        integration_parent_is_ancestor_of_head=True,
        integration_second_parent_matches_head=True,
        policy_paths_untouched=True,
        excluded_paths_applied=True,
        semantic_add_or_modify_classes=("formalization-or-blueprint",),
        semantic_lean_changed=True,
        semantic_blueprint_changed=False,
        semantic_rmp_changed=False,
        lean_modules_build=True,
        proof_integrity_clean=True,
        blueprint_checkdecls_passed=True,
        blueprint_build_passed=True,
        rmp_targets_resolved=True,
        rmp_stages_complete=True,
        rmp_checks_passed=True,
    )
    third_log = complete_log()[:3] + [
        work("S1-0004", "#909", "#908", "formalization-or-blueprint")
    ]
    expect_failure(
        lambda: validate(third_log, third_facts),
        "third work entry",
    )

    no_exact_approval = context()
    formal = no_exact_approval.prs[FORMAL_WORK]
    no_exact_approval.prs[FORMAL_WORK] = replace(
        formal,
        reviews=(
            review(
                "formal-reviewer",
                FORMAL_MERGE - timedelta(microseconds=2),
                formal.head_oid or oid(0),
            ),
            review(
                "formal-reviewer",
                FORMAL_MERGE - timedelta(microseconds=1),
                formal.head_oid or oid(0),
                state="CHANGES_REQUESTED",
            ),
        ),
    )
    assert (
        validate(complete_log()[:2], no_exact_approval)
        == "reset-required:S1-0002"
    )

    incomplete_reviews = context()
    incomplete_reviews.prs[RMP_WORK] = replace(
        incomplete_reviews.prs[RMP_WORK],
        reviews_complete=False,
    )
    assert (
        validate(complete_log()[:3], incomplete_reviews)
        == "reset-required:S1-0003"
    )

    changed_policy = context()
    changed_policy.work_diffs[FORMAL_WORK] = replace(
        changed_policy.work_diffs[FORMAL_WORK],
        policy_paths_untouched=False,
    )
    assert validate(complete_log()[:2], changed_policy) == "reset-required:S1-0002"

    comment_only_work = context()
    comment_only_work.work_diffs[FORMAL_WORK] = replace(
        comment_only_work.work_diffs[FORMAL_WORK],
        semantic_add_or_modify_classes=(),
        semantic_lean_changed=False,
    )
    assert (
        validate(complete_log()[:2], comment_only_work)
        == "reset-required:S1-0002"
    )

    failing_lean_work = context()
    failing_lean_work.work_diffs[FORMAL_WORK] = replace(
        failing_lean_work.work_diffs[FORMAL_WORK],
        lean_modules_build=False,
    )
    assert (
        validate(complete_log()[:2], failing_lean_work)
        == "reset-required:S1-0002"
    )

    incomplete_rmp_work = context()
    incomplete_rmp_work.work_diffs[RMP_WORK] = replace(
        incomplete_rmp_work.work_diffs[RMP_WORK],
        rmp_stages_complete=False,
    )
    assert (
        validate(complete_log()[:3], incomplete_rmp_work)
        == "reset-required:S1-0003"
    )

    bad_tree = context()
    bad_tree.prs[RMP_WORK] = replace(
        bad_tree.prs[RMP_WORK],
        integration_tree_matches_head=False,
    )
    assert validate(complete_log()[:3], bad_tree) == "reset-required:S1-0003"

    bad_work_parent = context()
    bad_work_parent.work_diffs[FORMAL_WORK] = replace(
        bad_work_parent.work_diffs[FORMAL_WORK],
        integration_parent_is_ancestor_of_head=False,
    )
    assert (
        validate(complete_log()[:2], bad_work_parent)
        == "reset-required:S1-0002"
    )

    bad_work_second_parent = context()
    bad_work_second_parent.work_diffs[RMP_WORK] = replace(
        bad_work_second_parent.work_diffs[RMP_WORK],
        integration_second_parent_matches_head=False,
    )
    assert (
        validate(complete_log()[:3], bad_work_second_parent)
        == "reset-required:S1-0003"
    )

    bad_record = context()
    bad_record.records["S1-0002"] = replace(
        bad_record.records["S1-0002"],
        pinned_prefix_unchanged=False,
    )
    assert (
        validate(complete_log()[:2], bad_record)
        == "reset-required:S1-0002"
    )

    bad_record_parent = context()
    bad_record_parent.records["S1-0002"] = replace(
        bad_record_parent.records["S1-0002"],
        integration_parent_is_ancestor_of_head=False,
    )
    assert (
        validate(complete_log()[:2], bad_record_parent)
        == "reset-required:S1-0002"
    )

    bad_record_second_parent = context()
    bad_record_second_parent.records["S1-0002"] = replace(
        bad_record_second_parent.records["S1-0002"],
        integration_parent_count=2,
        integration_second_parent_matches_head=False,
    )
    assert (
        validate(complete_log()[:2], bad_record_second_parent)
        == "reset-required:S1-0002"
    )

    candidate_freeze = context()
    candidate_freeze.prs[FREEZE_RECORD] = candidate_pr(902, author="record-author")
    assert validate([freeze()], candidate_freeze) == "freeze-pending"

    bad_candidate_parent = context()
    bad_candidate_parent.prs[FREEZE_RECORD] = candidate_pr(902, author="record-author")
    bad_candidate_parent.records["S1-0001"] = replace(
        bad_candidate_parent.records["S1-0001"],
        candidate_main_is_ancestor_of_head=False,
    )
    expect_failure(
        lambda: validate([freeze()], bad_candidate_parent),
        "candidate main is not an ancestor",
    )

    reset_facts = context()
    reset_facts.prs["#908"] = merged_pr(908, FREEZE_TIME + timedelta(seconds=4))
    reset_facts.prs["#909"] = merged_pr(909, FREEZE_TIME + timedelta(seconds=5))
    reset_facts.prs["#910"] = merged_pr(910, FREEZE_TIME + timedelta(seconds=6))
    for entry_id in ("S1-0002", "S1-0003", "S1-0004"):
        reset_facts.records[entry_id] = policy.RecordDiffEvidence(
            validated_pr_ref={
                "S1-0002": "#908",
                "S1-0003": "#909",
                "S1-0004": "#910",
            }[entry_id],
            validated_head_oid=reset_facts.prs[
                {
                    "S1-0002": "#908",
                    "S1-0003": "#909",
                    "S1-0004": "#910",
                }[entry_id]
            ].head_oid,
            complete=True,
            unique_merge_base=True,
            integration_parent_count=1,
            base_lacks_entry=True,
            appends_exact_entry=True,
            pinned_prefix_unchanged=True,
            other_entries_unchanged=True,
            no_other_path_changes=True,
            candidate_main_is_ancestor_of_head=True,
            integration_parent_is_ancestor_of_head=True,
            integration_second_parent_matches_head=True,
        )
    reset_log = [
        freeze(),
        friction("S1-0002", "#908", "breaking-required"),
        correction("S1-0003", "#909", "S1-0002"),
        reset("S1-0004", "#910", "breaking-required", "S1-0002"),
    ]
    assert validate(reset_log, reset_facts) == "reset"

    missing_reset = reset_log[:2] + [
        work("S1-0003", FORMAL_RECORD, FORMAL_WORK, "formalization-or-blueprint")
    ]
    expect_failure(
        lambda: validate(missing_reset, reset_facts),
        "must be followed by its reset",
    )

    invalid_facts = context()
    invalid_facts.prs["#908"] = merged_pr(908, FREEZE_TIME + timedelta(seconds=6))
    invalid_facts.records["S1-0003"] = policy.RecordDiffEvidence(
        validated_pr_ref="#908",
        validated_head_oid=invalid_facts.prs["#908"].head_oid,
        complete=True,
        unique_merge_base=True,
        integration_parent_count=1,
        base_lacks_entry=True,
        appends_exact_entry=True,
        pinned_prefix_unchanged=True,
        other_entries_unchanged=True,
        no_other_path_changes=True,
        candidate_main_is_ancestor_of_head=True,
        integration_parent_is_ancestor_of_head=True,
        integration_second_parent_matches_head=True,
    )
    invalid_log = complete_log()[:2]
    assert (
        validate(
            invalid_log,
            invalid_facts,
            audit=audit_evidence("S1-0002", ("S1-0002",)),
        )
        == "reset-required:S1-0002"
    )
    recovered = invalid_log + [
        reset("S1-0003", "#908", "record-invalid", "S1-0002")
    ]
    assert (
        validate(
            recovered,
            invalid_facts,
            audit=audit_evidence("S1-0002", ("S1-0002",)),
        )
        == "reset"
    )
    expect_failure(
        lambda: validate(
            invalid_log,
            invalid_facts,
            audit=audit_evidence(None, ("S1-0002",)),
        ),
        "audit with an empty prefix names invalid entries",
    )
    expect_failure(
        lambda: validate(
            invalid_log,
            invalid_facts,
            audit=audit_evidence("S1-0001", ("S1-0002",)),
        ),
        "audit boundary precedes an invalid target",
    )

    # Drift is discovered against the current repository, not at the old
    # entry's integration point.  Replay every later historical entry with its
    # immutable integration facts, then require the first new non-correction
    # entry to reset the earliest drifted record.
    replayed_drift = context()
    add_record(
        replayed_drift,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
    )
    assert (
        validate(
            complete_log(),
            replayed_drift,
            audit=audit_evidence("S1-0004", ("S1-0002",)),
        )
        == "reset-required:S1-0002"
    )
    assert (
        validate(
            complete_log()
            + [reset("S1-0005", "#908", "record-invalid", "S1-0002")],
            replayed_drift,
            audit=audit_evidence("S1-0004", ("S1-0002",)),
        )
        == "reset"
    )

    replayed_freeze_drift = context()
    add_record(
        replayed_freeze_drift,
        "S1-0004",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=8),
    )
    assert (
        validate(
            complete_log()[:3]
            + [reset("S1-0004", "#908", "record-invalid", "S1-0001")],
            replayed_freeze_drift,
            audit=audit_evidence("S1-0003", ("S1-0001",)),
        )
        == "reset"
    )

    corrected_drift = context()
    add_record(
        corrected_drift,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
    )
    add_record(
        corrected_drift,
        "S1-0006",
        "#909",
        909,
        SIGNOFF_MERGE + timedelta(seconds=2),
    )
    assert (
        validate(
            complete_log()
            + [
                correction("S1-0005", "#908", "S1-0001"),
                reset("S1-0006", "#909", "record-invalid", "S1-0002"),
            ],
            corrected_drift,
            audit=audit_evidence("S1-0004", ("S1-0002",)),
        )
        == "reset"
    )

    # An already-pending breaking-required reset has priority at the drift
    # boundary; the administrative drift reset follows immediately after it.
    ordered_resets = context()
    add_record(
        ordered_resets,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=3),
    )
    add_record(
        ordered_resets,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=4),
    )
    add_record(
        ordered_resets,
        "S1-0004",
        "#910",
        910,
        FREEZE_TIME + timedelta(seconds=5),
    )
    breaking_then_drift = [
        freeze(),
        friction("S1-0002", "#908", "breaking-required"),
        reset("S1-0003", "#909", "breaking-required", "S1-0002"),
        reset("S1-0004", "#910", "record-invalid", "S1-0001"),
    ]
    assert (
        validate(
            breaking_then_drift[:3],
            ordered_resets,
            audit=audit_evidence("S1-0002", ("S1-0001",)),
        )
        == "reset-required:S1-0001"
    )
    assert (
        validate(
            breaking_then_drift,
            ordered_resets,
            audit=audit_evidence("S1-0002", ("S1-0001",)),
        )
        == "reset"
    )

    batched_drift = context()
    add_record(
        batched_drift,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
    )
    add_record(
        batched_drift,
        "S1-0006",
        "#909",
        909,
        SIGNOFF_MERGE + timedelta(seconds=2),
    )
    unsorted_audit = policy.AuditEvidence(
        "S1-0004",
        ("S1-0002", "S1-0001"),
        True,
        True,
    )
    expect_failure(
        lambda: validate(complete_log(), batched_drift, audit=unsorted_audit),
        "invalid entries are not in ledger order",
    )
    ordered_audit = policy.AuditEvidence(
        "S1-0004",
        ("S1-0001", "S1-0002"),
        True,
        True,
    )
    batched_log = complete_log() + [
        reset("S1-0005", "#908", "record-invalid", "S1-0001"),
        reset("S1-0006", "#909", "record-invalid", "S1-0002"),
    ]
    assert validate(batched_log[:-1], batched_drift, audit=ordered_audit) == (
        "reset-required:S1-0002"
    )
    assert validate(batched_log, batched_drift, audit=ordered_audit) == "reset"

    # The self-referential record rule is common to every entry kind.  A
    # copied or tree-mismatched merged record never supplies usable evidence;
    # the next non-correction entry must reset that exact record.
    common_cases: list[tuple[str, list[str], str, str, str]] = []

    freeze_common = context()
    freeze_common.prs[FREEZE_RECORD] = replace(
        freeze_common.prs[FREEZE_RECORD],
        integration_tree_matches_head=False,
    )
    add_record(
        freeze_common,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    common_cases.append(
        (
            "freeze",
            [
                freeze(),
                reset("S1-0002", "#908", "record-invalid", "S1-0001"),
            ],
            "S1-0001",
            "S1-0002",
            "#908",
        )
    )

    work_common = context()
    work_common.prs[FORMAL_RECORD] = replace(
        work_common.prs[FORMAL_RECORD],
        integration_tree_matches_head=False,
    )
    add_record(
        work_common,
        "S1-0003",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=6),
    )
    common_cases.append(
        (
            "work",
            [
                freeze(),
                work(
                    "S1-0002",
                    FORMAL_RECORD,
                    FORMAL_WORK,
                    "formalization-or-blueprint",
                ),
                reset("S1-0003", "#908", "record-invalid", "S1-0002"),
            ],
            "S1-0002",
            "S1-0003",
            "#908",
        )
    )

    friction_common = context()
    add_record(
        friction_common,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=3),
        invalid_tree=True,
    )
    add_record(
        friction_common,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=4),
    )
    common_cases.append(
        (
            "friction",
            [
                freeze(),
                friction("S1-0002", "#908", "defer-to-2.0"),
                reset("S1-0003", "#909", "record-invalid", "S1-0002"),
            ],
            "S1-0002",
            "S1-0003",
            "#909",
        )
    )

    resolution_common = context()
    add_record(
        resolution_common,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=3),
    )
    add_record(
        resolution_common,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=4),
        invalid_tree=True,
    )
    add_record(
        resolution_common,
        "S1-0004",
        "#910",
        910,
        FREEZE_TIME + timedelta(seconds=5),
    )
    common_cases.append(
        (
            "resolution",
            [
                freeze(),
                friction("S1-0002", "#908", "fix-compatible"),
                resolution("S1-0003", "#909", "S1-0002"),
                reset("S1-0004", "#910", "record-invalid", "S1-0003"),
            ],
            "S1-0003",
            "S1-0004",
            "#910",
        )
    )

    correction_common = context()
    add_record(
        correction_common,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=3),
        invalid_tree=True,
    )
    add_record(
        correction_common,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=4),
    )
    common_cases.append(
        (
            "correction",
            [
                freeze(),
                correction("S1-0002", "#908", "S1-0001"),
                reset("S1-0003", "#909", "record-invalid", "S1-0002"),
            ],
            "S1-0002",
            "S1-0003",
            "#909",
        )
    )

    reset_common = context()
    add_record(
        reset_common,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=3),
    )
    add_record(
        reset_common,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=4),
        invalid_tree=True,
    )
    add_record(
        reset_common,
        "S1-0004",
        "#910",
        910,
        FREEZE_TIME + timedelta(seconds=5),
    )
    common_cases.append(
        (
            "reset",
            [
                freeze(),
                friction("S1-0002", "#908", "breaking-required"),
                reset("S1-0003", "#909", "breaking-required", "S1-0002"),
                reset("S1-0004", "#910", "record-invalid", "S1-0003"),
            ],
            "S1-0003",
            "S1-0004",
            "#910",
        )
    )

    signoff_common = context()
    signoff_common.prs[SIGNOFF_RECORD] = replace(
        signoff_common.prs[SIGNOFF_RECORD],
        integration_tree_matches_head=False,
    )
    add_record(
        signoff_common,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
    )
    common_cases.append(
        (
            "sign-off",
            complete_log()
            + [reset("S1-0005", "#908", "record-invalid", "S1-0004")],
            "S1-0004",
            "S1-0005",
            "#908",
        )
    )

    case_facts = {
        "freeze": freeze_common,
        "work": work_common,
        "friction": friction_common,
        "resolution": resolution_common,
        "correction": correction_common,
        "reset": reset_common,
        "sign-off": signoff_common,
    }
    for name, log, invalid_id, reset_id, _reset_pr in common_cases:
        facts = case_facts[name]
        assert validate(log[:-1], facts) == f"reset-required:{invalid_id}"
        assert log[-1].find(f'id = "{reset_id}"') >= 0
        assert validate(log, facts) == "reset"

    copied_candidate = context()
    copied_candidate.prs[FREEZE_RECORD] = candidate_pr(902, author="record-author")
    copied_candidate.records["S1-0001"] = replace(
        copied_candidate.records["S1-0001"],
        validated_pr_ref="#999",
    )
    expect_failure(
        lambda: validate([freeze()], copied_candidate),
        "validated on another PR",
    )

    copied_merged = context()
    copied_merged.records["S1-0001"] = replace(
        copied_merged.records["S1-0001"],
        validated_pr_ref="#999",
    )
    add_record(
        copied_merged,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    copied_log = [
        freeze(),
        reset("S1-0002", "#908", "record-invalid", "S1-0001"),
    ]
    assert validate(copied_log[:-1], copied_merged) == "reset-required:S1-0001"
    assert validate(copied_log, copied_merged) == "reset"

    moved_tag = context()
    moved_tag.tags["tenkz-v0.9.0"] = policy.TagEvidence("9" * 40, "tag", SHA, True)
    add_record(
        moved_tag,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    moved_tag_log = [
        freeze(),
        reset("S1-0002", "#908", "record-invalid", "S1-0001"),
    ]
    assert validate(moved_tag_log[:-1], moved_tag) == "reset-required:S1-0001"
    assert validate(moved_tag_log, moved_tag) == "reset"

    moved_tag_candidate = context()
    moved_tag_candidate.prs[FREEZE_RECORD] = candidate_pr(902, author="record-author")
    moved_tag_candidate.tags["tenkz-v0.9.0"] = policy.TagEvidence(
        "9" * 40,
        "tag",
        SHA,
        True,
    )
    expect_failure(
        lambda: validate([freeze()], moved_tag_candidate),
        "tag object was replaced",
    )

    advanced_candidate = context()
    advanced_candidate.prs[FREEZE_RECORD] = candidate_pr(902, author="record-author")
    advanced_candidate.records["S1-0001"] = replace(
        advanced_candidate.records["S1-0001"],
        candidate_main_tip_is_source=False,
    )
    expect_failure(
        lambda: validate([freeze()], advanced_candidate),
        "candidate main tip differs from source_sha",
    )

    wrong_parent = context()
    wrong_parent.records["S1-0001"] = replace(
        wrong_parent.records["S1-0001"],
        integration_parent_is_source=False,
    )
    add_record(
        wrong_parent,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    wrong_parent_log = [
        freeze(),
        reset("S1-0002", "#908", "record-invalid", "S1-0001"),
    ]
    assert validate(wrong_parent_log[:-1], wrong_parent) == "reset-required:S1-0001"
    assert validate(wrong_parent_log, wrong_parent) == "reset"

    stale_patch = context()
    stale_patch.prs[FREEZE_RECORD] = candidate_pr(902, author="record-author")
    stale_patch.tags["tenkz-v0.9.0"] = replace(
        stale_patch.tags["tenkz-v0.9.0"],
        patch_is_fresh_for_attempt=False,
    )
    expect_failure(
        lambda: validate([freeze()], stale_patch),
        "PATCH does not exceed abandoned tags",
    )

    mixed_record = context()
    mixed_record.records["S1-0002"] = replace(
        mixed_record.records["S1-0002"],
        no_other_path_changes=False,
    )
    assert (
        validate(complete_log()[:2], mixed_record)
        == "reset-required:S1-0002"
    )

    archived_work = context()
    archived_work.work_diffs[FORMAL_WORK] = replace(
        archived_work.work_diffs[FORMAL_WORK],
        excluded_paths_applied=False,
    )
    assert (
        validate(complete_log()[:2], archived_work)
        == "reset-required:S1-0002"
    )
    archive_only = context()
    archive_only.work_diffs[FORMAL_WORK] = replace(
        archive_only.work_diffs[FORMAL_WORK],
        semantic_add_or_modify_classes=(),
        semantic_lean_changed=False,
    )
    assert (
        validate(complete_log()[:2], archive_only)
        == "reset-required:S1-0002"
    )

    # A historical correction retains its target attempt, but an invalid
    # record is repaired administratively.  With no active attempt, that
    # reset uses the most recently opened number and leaves the state inactive.
    historical = context()
    add_record(
        historical,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    add_record(
        historical,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=2),
    )
    add_record(
        historical,
        "S1-0004",
        "#910",
        910,
        FREEZE_TIME + timedelta(seconds=3),
        invalid_tree=True,
    )
    add_record(
        historical,
        "S1-0005",
        "#911",
        911,
        FREEZE_TIME + timedelta(seconds=4),
    )
    second_sha = "c" * 40
    second_tag_object = "d" * 40
    add_freeze_facts(
        historical,
        "S1-0006",
        source_ref="#912",
        source_number=912,
        source_sha=second_sha,
        record_ref="#913",
        record_number=913,
        tag="tenkz-v0.9.1",
        tag_object=second_tag_object,
        merged_at=FREEZE_TIME + timedelta(seconds=6),
    )
    add_record(
        historical,
        "S1-0007",
        "#914",
        914,
        FREEZE_TIME + timedelta(seconds=7),
        invalid_tree=True,
    )
    add_record(
        historical,
        "S1-0008",
        "#915",
        915,
        FREEZE_TIME + timedelta(seconds=8),
    )
    third_sha = "e" * 40
    third_tag_object = "f" * 40
    add_freeze_facts(
        historical,
        "S1-0009",
        source_ref="#916",
        source_number=916,
        source_sha=third_sha,
        record_ref="#917",
        record_number=917,
        tag="tenkz-v0.9.2",
        tag_object=third_tag_object,
        merged_at=FREEZE_TIME + timedelta(seconds=10),
    )
    historical_log = [
        freeze(),
        friction("S1-0002", "#908", "breaking-required"),
        reset("S1-0003", "#909", "breaking-required", "S1-0002"),
        correction("S1-0004", "#910", "S1-0001", attempt=1),
        reset("S1-0005", "#911", "record-invalid", "S1-0004", attempt=1),
        freeze(
            "S1-0006",
            record_pr="#913",
            attempt=2,
            source_pr="#912",
            source_sha=second_sha,
            tag_object=second_tag_object,
            tag="tenkz-v0.9.1",
        ),
        correction("S1-0007", "#914", "S1-0001", attempt=1),
        reset("S1-0008", "#915", "record-invalid", "S1-0007", attempt=2),
        freeze(
            "S1-0009",
            record_pr="#917",
            attempt=3,
            source_pr="#916",
            source_sha=third_sha,
            tag_object=third_tag_object,
            tag="tenkz-v0.9.2",
        ),
    ]
    assert (
        validate(historical_log[:4], historical)
        == "reset-required:S1-0004"
    )
    assert validate(historical_log[:5], historical) == "reset"
    assert validate(historical_log[:6], historical) == "attempt-2-active"
    assert (
        validate(historical_log[:7], historical)
        == "reset-required:S1-0007"
    )
    assert validate(historical_log[:8], historical) == "reset"
    assert validate(historical_log, historical) == "attempt-3-active"

    expect_failure(
        lambda: policy.validate_policy_text(
            DESIGN_TEXT.replace(
                "required_distinct_work_prs = 2",
                "required_distinct_work_prs = 3",
            )
        ),
        "signed policy",
    )
    expect_failure(
        lambda: policy.validate_policy_text(
            DESIGN_TEXT.replace(
                'work_classes = ["formalization-or-blueprint", "rmp-benchmark"]',
                'work_classes = ["rmp-benchmark", "formalization-or-blueprint"]',
            )
        ),
        "signed policy",
    )
    expect_failure(
        lambda: policy.parse_soak_text(
            SOAK_TEXT.replace(
                "append_only = true",
                'minimum_elapsed = "forbidden"\nappend_only = true',
            )
        ),
        "signed schema",
    )
    expect_failure(
        lambda: policy.parse_soak_text(SOAK_TEXT + "free-form tail\n"),
        "only evidence entry blocks",
    )

    invented = freeze().replace(
        'evidence = "source, tag, and issue evidence"',
        'evidence = "source, tag, and issue evidence"\ninvented = true',
    )
    expect_failure(
        lambda: validate([invented], context()),
        "fields differ from schema",
    )

    policy.check_append_only(SOAK_TEXT, SOAK_TEXT + freeze())
    expect_failure(
        lambda: policy.check_append_only(
            SOAK_TEXT,
            SOAK_TEXT.replace("release-evidence log", "rewritten log") + freeze(),
        ),
        "changed existing bytes",
    )

    print("PASS: tenkz evidence gate enforces two exact classes without calendar delay")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
