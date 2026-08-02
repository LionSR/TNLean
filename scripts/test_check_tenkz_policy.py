#!/usr/bin/env python3
"""Perturbation tests for the pure tenkz release-evidence state machine."""

from __future__ import annotations

import sys
from dataclasses import dataclass, field, replace
from datetime import datetime, timedelta, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_tenkz_policy as policy  # noqa: E402


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
    fix_pr: str | None = None,
) -> str:
    entry_number = int(entry_id.removeprefix("S1-"))
    fix_ref = fix_pr or f"#{18_000 + entry_number}"
    return block(
        f'''id = "{entry_id}"
kind = "resolution"
record_pr = "{record_pr}"
attempt = {attempt}
friction = "{target}"
fix_pr = "{fix_ref}"
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
    replay_receipt_pr: str | None = None,
    replay_receipt_sha256: str | None = None,
) -> str:
    replay_fields = ""
    if cause == "record-invalid":
        entry_number = int(entry_id.removeprefix("S1-"))
        receipt_ref = replay_receipt_pr or f"#{19_000 + entry_number}"
        receipt_digest = replay_receipt_sha256 or f"{entry_number:064x}"
        replay_fields = (
            f'\nreplay_receipt_pr = "{receipt_ref}"'
            f'\nreplay_receipt_sha256 = "{receipt_digest}"'
        )
    return block(
        f'''id = "{entry_id}"
kind = "reset"
record_pr = "{record_pr}"
attempt = {attempt}
cause = "{cause}"
target = "{target}"
reason = "attempt evidence requires a new freeze"
evidence = "verified reset cause"{replay_fields}'''
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
    permission: str | None = "write",
) -> policy.ReviewEvidence:
    return policy.ReviewEvidence(login, state, submitted_at, head, dismissed, permission)


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
    resolution_diffs: dict[str, policy.ResolutionDiffEvidence]
    release_preps: dict[str, policy.ReleasePrepEvidence]
    payloads: dict[tuple[str, str], policy.ReleasePayloadEvidence]
    tags: dict[str, policy.TagEvidence]
    issues: dict[str, policy.IssueEvidence]
    reset_replays: dict[str, policy.RecordInvalidResetReplayEvidence] = field(
        default_factory=dict
    )
    workflow_override: policy.WorkflowEvidence | None = None

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

    def resolve_replay_resolution_diff(self, ref: str) -> policy.ResolutionDiffEvidence:
        return self.resolution_diffs[ref]

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

    def resolve_replay_record_invalid_reset(
        self,
        entry_id: str,
        target: str,
        receipt_ref: str,
        receipt_digest: str,
        current_tree_oid: str,
    ) -> policy.RecordInvalidResetReplayEvidence:
        override = self.reset_replays.get(entry_id)
        if override is not None:
            return override
        receipt = self.prs[receipt_ref]
        index = int(entry_id.removeprefix("S1-"))
        return policy.RecordInvalidResetReplayEvidence(
            validated_entry_id=entry_id,
            validated_target_entry_id=target,
            validated_receipt_pr=receipt_ref,
            validated_receipt_head_oid=receipt.head_oid,
            validated_receipt_integration_oid=receipt.merge_commit_oid,
            complete=True,
            receipt_candidate_main_tip_exact=True,
            changes_exactly_one_new_regular_blob=True,
            receipt_path=f"docs/tenkz/soak-replay/{receipt_ref[1:]}.json",
            raw_blob_sha256=receipt_digest,
            validated_current_tree_oid=current_tree_oid,
            raw_blob_read_from_current_validation_tree=True,
            current_tree_blob_has_exact_path_mode_bytes_and_digest=True,
            schema_path=policy.policy_rules(ARMED_POLICY)[4].reset_replay_schema,
            schema_support_tree_oid=TEST_SUPPORT_TREE,
            schema_from_pinned_support_tree=True,
            schema_closed_and_valid=True,
            boundary_entry_id=f"S1-{index - 1:04d}",
            validation_target_oid=receipt.head_oid,
            raw_invalid_entries=(target,),
            pending_breaking_target=None,
            normalized_resolver_inputs_complete_and_matching=True,
            workflow_dependency_closure_pinned=True,
            supervisor_receipts_complete_and_matching=True,
            current_candidate_snapshot_reproduces_receipt=True,
        )

    def resolve_current_workflow(
        self,
        activation_integration: str,
        target_oid: str,
        paths: tuple[str, ...],
    ) -> policy.WorkflowEvidence:
        if self.workflow_override is not None:
            return self.workflow_override
        return policy.WorkflowEvidence(
            validated_activation_integration=activation_integration,
            validated_target_oid=target_oid,
            validated_paths=paths,
            complete=True,
            activation_paths_are_regular_blobs=True,
            target_blobs_and_modes_match_activation=True,
            local_dependencies_pinned_and_matching=True,
            external_dependencies_use_full_commit_shas=True,
            containers_use_content_digests=True,
            dependency_graph_complete_and_acyclic=True,
            package_managers_absent=True,
            downloaders_absent=True,
            unhashed_runtime_dependencies_absent=True,
            runtime_fetched_executables_absent=True,
            network_disabled_before_repository_code=True,
            candidate_diff_untouched=True,
            github_checks_bind_exact_head_and_workflows=True,
            supervisor_receipt_complete_and_matching=True,
        )


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
        enforcement_workflows_pinned=True,
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
            validated_pr_ref=FORMAL_WORK,
            validated_head_oid=prs[FORMAL_WORK].head_oid,
            validated_integration_oid=prs[FORMAL_WORK].merge_commit_oid,
            validated_freeze_integration=prs[FREEZE_RECORD].merge_commit_oid,
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
            validated_pr_ref=RMP_WORK,
            validated_head_oid=prs[RMP_WORK].head_oid,
            validated_integration_oid=prs[RMP_WORK].merge_commit_oid,
            validated_freeze_integration=prs[FREEZE_RECORD].merge_commit_oid,
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
        {},
        release_preps,
        payloads,
        {
            "tenkz-v0.9.0": policy.TagEvidence(
                TAG_OBJECT,
                "tag",
                SHA,
                True,
                True,
                True,
            ),
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
    target_oid: str = oid(99_999),
) -> policy.AuditEvidence:
    return policy.AuditEvidence(boundary, invalid_entries, True, True, target_oid)


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


def prepare_reset_receipts(entries: list[dict], facts: Context) -> None:
    """Populate the default durable receipt facts used by unrelated scenarios."""

    for entry in entries:
        if entry["kind"] != "reset" or entry["cause"] != "record-invalid":
            continue
        entry_id = entry["id"]
        record = facts.prs[entry["record_pr"]]
        receipt_ref = entry["replay_receipt_pr"]
        receipt_number = int(receipt_ref[1:])
        if receipt_ref not in facts.prs:
            record_time = record.merged_at
            receipt_time = (
                record_time - timedelta(microseconds=1)
                if record_time is not None
                else SIGNOFF_MERGE + timedelta(seconds=100 + receipt_number)
            )
            receipt_head = oid(receipt_number * 10)
            facts.prs[receipt_ref] = merged_pr(
                receipt_number,
                receipt_time,
                author=f"receipt-author-{receipt_number}",
                reviews=(
                    review(
                        f"receipt-reviewer-{receipt_number}",
                        receipt_time - timedelta(microseconds=1),
                        receipt_head,
                    ),
                ),
            )
        receipt_integration = facts.prs[receipt_ref].merge_commit_oid
        record_diff = facts.records[entry_id]
        facts.records[entry_id] = replace(
            record_diff,
            candidate_main_tip_is_receipt_integration=(
                True
                if record_diff.candidate_main_tip_is_receipt_integration is None
                else record_diff.candidate_main_tip_is_receipt_integration
            ),
            integration_parent_is_receipt_integration=(
                True
                if record_diff.integration_parent_is_receipt_integration is None
                else record_diff.integration_parent_is_receipt_integration
            ),
            validated_receipt_integration=(
                receipt_integration
                if record_diff.validated_receipt_integration is None
                else record_diff.validated_receipt_integration
            ),
            receipt_blob_preserved_from_candidate_base_to_head=(
                True
                if record_diff.receipt_blob_preserved_from_candidate_base_to_head is None
                else record_diff.receipt_blob_preserved_from_candidate_base_to_head
            ),
            receipt_blob_preserved_in_integration=(
                True
                if record_diff.receipt_blob_preserved_in_integration is None
                else record_diff.receipt_blob_preserved_in_integration
            ),
        )


def prepare_receipt_retention(entries: list[dict], facts: Context) -> None:
    """Bind every later record tree to all earlier durable receipt blobs."""

    prior_receipts: list[tuple[str, str]] = []
    for entry in entries:
        if prior_receipts:
            record_diff = facts.records[entry["id"]]
            facts.records[entry["id"]] = replace(
                record_diff,
                validated_prior_receipts=(
                    tuple(prior_receipts)
                    if record_diff.validated_prior_receipts is None
                    else record_diff.validated_prior_receipts
                ),
                candidate_target_preserves_prior_receipts=(
                    True
                    if record_diff.candidate_target_preserves_prior_receipts is None
                    else record_diff.candidate_target_preserves_prior_receipts
                ),
                head_preserves_prior_receipts=(
                    True
                    if record_diff.head_preserves_prior_receipts is None
                    else record_diff.head_preserves_prior_receipts
                ),
                integration_preserves_prior_receipts=(
                    True
                    if record_diff.integration_preserves_prior_receipts is None
                    else record_diff.integration_preserves_prior_receipts
                ),
                entry_diff_untouched_prior_receipts=(
                    True
                    if record_diff.entry_diff_untouched_prior_receipts is None
                    else record_diff.entry_diff_untouched_prior_receipts
                ),
            )
        if entry["kind"] == "reset" and entry["cause"] == "record-invalid":
            receipt_ref = entry["replay_receipt_pr"]
            prior_receipts.append(
                (
                    f"docs/tenkz/soak-replay/{receipt_ref[1:]}.json",
                    entry["replay_receipt_sha256"],
                )
            )


def prepare_resolution_facts(entries: list[dict], facts: Context) -> None:
    """Populate exact fix-PR evidence for scenarios not testing resolutions."""

    by_id = {entry["id"]: entry for entry in entries}
    for entry in entries:
        if entry["kind"] != "resolution":
            continue
        entry_id = entry["id"]
        friction_entry = by_id[entry["friction"]]
        friction_pr = facts.prs[friction_entry["record_pr"]]
        friction_time = friction_pr.merged_at
        friction_integration = friction_pr.merge_commit_oid
        assert friction_time is not None and friction_integration is not None
        freeze_entry = next(
            candidate
            for candidate in reversed(entries[: entries.index(entry)])
            if candidate["kind"] == "freeze" and candidate["attempt"] == entry["attempt"]
        )
        freeze_integration = facts.prs[freeze_entry["record_pr"]].merge_commit_oid
        assert freeze_integration is not None
        resolution_record = facts.prs[entry["record_pr"]]
        fix_ref = entry["fix_pr"]
        fix_number = int(fix_ref[1:])
        if fix_ref not in facts.prs:
            resolution_time = resolution_record.merged_at
            fix_time = (
                friction_time + (resolution_time - friction_time) / 2
                if resolution_time is not None
                else friction_time + timedelta(seconds=1)
            )
            fix_head = oid(fix_number * 10)
            facts.prs[fix_ref] = merged_pr(
                fix_number,
                fix_time,
                author=f"fix-author-{fix_number}",
                reviews=(
                    review(
                        f"fix-reviewer-{fix_number}",
                        fix_time - timedelta(microseconds=1),
                        fix_head,
                    ),
                ),
            )
        fix_pr = facts.prs[fix_ref]
        fix_integration = fix_pr.merge_commit_oid
        assert fix_integration is not None
        if fix_ref not in facts.resolution_diffs:
            facts.resolution_diffs[fix_ref] = policy.ResolutionDiffEvidence(
                validated_pr_ref=fix_ref,
                validated_head_oid=fix_pr.head_oid,
                validated_integration_oid=fix_integration,
                validated_freeze_integration=freeze_integration,
                validated_friction_integration=friction_integration,
                complete=True,
                integration_parent_count=1,
                unique_merge_base=True,
                integration_parent_is_ancestor_of_head=True,
                integration_second_parent_matches_head=True,
                integration_strict_descendant_of_freeze=True,
                integration_strict_descendant_of_friction=True,
                policy_paths_untouched=True,
                has_added_or_modified_regular_nonledger_blob=True,
                normalized_token_stream_changed=True,
                semantic_witness_is_same_regular_nonledger_blob=True,
                validated_contract=policy.policy_rules(ARMED_POLICY)[4],
                inventory_commands_complete=True,
                inventory_commands_passed=True,
                execution_receipts_exact_and_matching=True,
            )
        record_diff = facts.records[entry_id]
        facts.records[entry_id] = replace(
            record_diff,
            candidate_main_tip_descends_from_fix_integration=(
                True
                if record_diff.candidate_main_tip_descends_from_fix_integration is None
                else record_diff.candidate_main_tip_descends_from_fix_integration
            ),
            integration_parent_descends_from_fix_integration=(
                True
                if record_diff.integration_parent_descends_from_fix_integration is None
                else record_diff.integration_parent_descends_from_fix_integration
            ),
            validated_fix_integration=(
                fix_integration
                if record_diff.validated_fix_integration is None
                else record_diff.validated_fix_integration
            ),
        )


def set_review_permission(facts: Context, ref: str, permission: str | None) -> None:
    pull_request = facts.prs[ref]
    assert pull_request.reviews is not None
    facts.prs[ref] = replace(
        pull_request,
        reviews=tuple(
            replace(item, repository_top_level_permission=permission)
            for item in pull_request.reviews
        ),
    )


def validate(blocks: list[str], facts: Context, **overrides) -> str:
    entries = parsed_entries(*blocks)
    prepare_reset_receipts(entries, facts)
    prepare_resolution_facts(entries, facts)
    prepare_receipt_retention(entries, facts)
    if "audit" not in overrides:
        boundary: str | None = None
        target_oid = facts.prs[ACTIVATION].merge_commit_oid
        for entry in entries:
            record = facts.prs.get(entry["record_pr"])
            if record is None:
                break
            target_oid = record.head_oid
            if record.merged is not True:
                break
            boundary = entry["id"]
            target_oid = record.merge_commit_oid
        assert isinstance(target_oid, str)
        overrides["audit"] = audit_evidence(boundary, target_oid=target_oid)
    arguments = {
        "policy": ARMED_POLICY,
        "soak": ARMED_SOAK,
        "resolve_replay_pr": facts.resolve_replay_pr,
        "resolve_replay_activation_diff": facts.resolve_replay_activation_diff,
        "resolve_replay_record_diff": facts.resolve_replay_record_diff,
        "resolve_replay_work_diff": facts.resolve_replay_work_diff,
        "resolve_replay_resolution_diff": facts.resolve_replay_resolution_diff,
        "resolve_replay_release_prep": facts.resolve_replay_release_prep,
        "resolve_replay_release_payload": facts.resolve_replay_release_payload,
        "resolve_replay_freeze_tag": facts.resolve_replay_freeze_tag,
        "resolve_current_final_tag": facts.resolve_current_final_tag,
        "resolve_replay_issue": facts.resolve_replay_issue,
        "resolve_replay_record_invalid_reset": facts.resolve_replay_record_invalid_reset,
        "resolve_current_workflow": facts.resolve_current_workflow,
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
    facts.tags[tag] = policy.TagEvidence(
        tag_object,
        "tag",
        source_sha,
        True,
        True,
        True,
    )
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

    # Every approval path uses the policy's closed collaborator-permission set.
    for denied_permission in (None, "none", "read", "maintain", "push", "triage"):
        denied_activation = context()
        set_review_permission(denied_activation, ACTIVATION, denied_permission)
        expect_failure(
            lambda facts=denied_activation: validate([], facts),
            "repository-authorized independent exact-head approval",
        )
    admin_reviewer = context()
    set_review_permission(admin_reviewer, ACTIVATION, "admin")
    assert validate([], admin_reviewer) == "not-started"

    denied_source = context()
    set_review_permission(denied_source, SOURCE, "read")
    denied_source.prs[FREEZE_RECORD] = candidate_pr(902, author="record-author")
    expect_failure(
        lambda: validate([freeze()], denied_source),
        "repository-authorized independent exact-head approval",
    )

    denied_work = context()
    set_review_permission(denied_work, FORMAL_WORK, "read")
    denied_work.prs[FORMAL_RECORD] = candidate_pr(904, author="record-author")
    expect_failure(
        lambda: validate(complete_log()[:2], denied_work),
        "repository-authorized independent exact-head approval",
    )

    denied_release = context()
    set_review_permission(denied_release, RELEASE_PREP, "read")
    signoff_head = denied_release.prs[SIGNOFF_RECORD].head_oid
    assert signoff_head is not None
    denied_release.prs[SIGNOFF_RECORD] = candidate_pr(
        907,
        author="release-author",
        reviews=(review("release-reviewer", SIGNOFF_REVIEW, signoff_head),),
    )
    expect_failure(
        lambda: validate(complete_log(), denied_release),
        "repository-authorized independent exact-head approval",
    )

    denied_signoff = context()
    signoff_head = denied_signoff.prs[SIGNOFF_RECORD].head_oid
    assert signoff_head is not None
    denied_signoff.prs[SIGNOFF_RECORD] = candidate_pr(
        907,
        author="release-author",
        reviews=(
            review(
                "release-reviewer",
                SIGNOFF_REVIEW,
                signoff_head,
                permission="read",
            ),
        ),
    )
    expect_failure(
        lambda: validate(complete_log(), denied_signoff),
        "repository-authorized independent exact-head approval",
    )

    receipt_log = [
        freeze(),
        reset("S1-0002", "#908", "record-invalid", "S1-0001"),
    ]
    denied_receipt = context()
    add_record(
        denied_receipt,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    denied_receipt.prs["#908"] = candidate_pr(908, author="record-author")
    receipt_entries = parsed_entries(*receipt_log)
    prepare_reset_receipts(receipt_entries, denied_receipt)
    receipt_ref = receipt_entries[-1]["replay_receipt_pr"]
    set_review_permission(denied_receipt, receipt_ref, "read")
    expect_failure(
        lambda: validate(
            receipt_log,
            denied_receipt,
            audit=audit_evidence(
                "S1-0001",
                ("S1-0001",),
                target_oid=denied_receipt.prs["#908"].head_oid,
            ),
        ),
        "repository-authorized independent exact-head approval",
    )

    expect_failure(
        lambda: validate([freeze(tag="tenkz-v0.9.00")], context()),
        "invalid freeze tag",
    )

    missing_receipt_field = reset(
        "S1-0002", "#908", "record-invalid", "S1-0001"
    ).replace('\nreplay_receipt_pr = "#19002"', "")
    expect_failure(
        lambda: policy.validate_entry_shape(
            parsed_entries(freeze(), missing_receipt_field)[1],
            2,
        ),
        "fields differ from schema",
    )
    breaking_with_receipt = reset(
        "S1-0002", "#908", "breaking-required", "S1-0001"
    ).replace(
        'evidence = "verified reset cause"',
        'evidence = "verified reset cause"\nreplay_receipt_pr = "#19002"\n'
        f'replay_receipt_sha256 = "{"2" * 64}"',
    )
    expect_failure(
        lambda: policy.validate_entry_shape(
            parsed_entries(freeze(), breaking_with_receipt)[1],
            2,
        ),
        "fields differ from schema",
    )

    def reset_candidate_case() -> tuple[
        list[str],
        Context,
        policy.AuditEvidence,
        policy.RecordInvalidResetReplayEvidence,
    ]:
        blocks = [
            freeze(),
            reset("S1-0002", "#908", "record-invalid", "S1-0001"),
        ]
        facts = context()
        add_record(
            facts,
            "S1-0002",
            "#908",
            908,
            FREEZE_TIME + timedelta(seconds=1),
        )
        facts.prs["#908"] = candidate_pr(908, author="record-author")
        entries = parsed_entries(*blocks)
        prepare_reset_receipts(entries, facts)
        receipt_ref = entries[-1]["replay_receipt_pr"]
        receipt_digest = entries[-1]["replay_receipt_sha256"]
        candidate_head = facts.prs["#908"].head_oid
        assert candidate_head is not None
        replay = facts.resolve_replay_record_invalid_reset(
            "S1-0002",
            "S1-0001",
            receipt_ref,
            receipt_digest,
            candidate_head,
        )
        audit = audit_evidence(
            "S1-0001",
            ("S1-0001",),
            target_oid=candidate_head,
        )
        return blocks, facts, audit, replay

    receipt_perturbations = (
        ("validated_target_entry_id", "S1-9999", "used another target"),
        ("validated_receipt_pr", "#9999", "used another PR"),
        ("validated_receipt_head_oid", oid(99_991), "used another exact head"),
        (
            "validated_receipt_integration_oid",
            oid(99_992),
            "used another integration",
        ),
        ("complete", False, "reset receipt is incomplete"),
        ("receipt_candidate_main_tip_exact", False, "exact current main tip"),
        ("changes_exactly_one_new_regular_blob", False, "new regular blob"),
        ("receipt_path", "docs/tenkz/soak-replay/wrong.json", "wrong path"),
        (
            "raw_blob_read_from_current_validation_tree",
            False,
            "current validation tree",
        ),
        (
            "current_tree_blob_has_exact_path_mode_bytes_and_digest",
            False,
            "does not retain the exact receipt blob",
        ),
        ("schema_path", "schema.json", "used another schema"),
        ("schema_support_tree_oid", oid(99_993), "used another support tree"),
        ("schema_from_pinned_support_tree", False, "pinned support tree"),
        ("schema_closed_and_valid", False, "closed schema"),
        ("boundary_entry_id", "S1-9999", "another pre-reset prefix"),
        ("validation_target_oid", oid(99_994), "inexact validation target"),
        ("raw_invalid_entries", (), "does not match its current reset receipt"),
        (
            "pending_breaking_target",
            "S1-0001",
            "wrong pending breaking target",
        ),
        (
            "normalized_resolver_inputs_complete_and_matching",
            False,
            "resolver inputs are incomplete",
        ),
        ("workflow_dependency_closure_pinned", False, "workflow closure is not pinned"),
        (
            "supervisor_receipts_complete_and_matching",
            False,
            "supervisor results are incomplete",
        ),
        (
            "current_candidate_snapshot_reproduces_receipt",
            False,
            "no longer reproduces its receipt",
        ),
    )
    for field_name, bad_value, error_fragment in receipt_perturbations:
        receipt_blocks, receipt_facts, receipt_audit, replay = reset_candidate_case()
        receipt_facts.reset_replays["S1-0002"] = replace(
            replay,
            **{field_name: bad_value},
        )
        expect_failure(
            lambda blocks=receipt_blocks, facts=receipt_facts, audit=receipt_audit: validate(
                blocks,
                facts,
                audit=audit,
            ),
            error_fragment,
        )

    wrong_receipt_digest_blocks, wrong_receipt_digest, digest_audit, replay = (
        reset_candidate_case()
    )
    wrong_receipt_digest.reset_replays["S1-0002"] = replace(
        replay,
        raw_blob_sha256="f" * 64,
    )
    expect_failure(
        lambda: validate(
            wrong_receipt_digest_blocks,
            wrong_receipt_digest,
            audit=digest_audit,
        ),
        "blob digest differs from the entry",
    )

    wrong_receipt_base_blocks, wrong_receipt_base, base_audit, _replay = (
        reset_candidate_case()
    )
    wrong_receipt_base.records["S1-0002"] = replace(
        wrong_receipt_base.records["S1-0002"],
        candidate_main_tip_is_receipt_integration=False,
    )
    expect_failure(
        lambda: validate(
            wrong_receipt_base_blocks,
            wrong_receipt_base,
            audit=base_audit,
        ),
        "candidate base differs from receipt integration",
    )

    missing_receipt_in_head_blocks, missing_receipt_in_head, head_audit, _replay = (
        reset_candidate_case()
    )
    missing_receipt_in_head.records["S1-0002"] = replace(
        missing_receipt_in_head.records["S1-0002"],
        receipt_blob_preserved_from_candidate_base_to_head=False,
    )
    expect_failure(
        lambda: validate(
            missing_receipt_in_head_blocks,
            missing_receipt_in_head,
            audit=head_audit,
        ),
        "reset head does not preserve its receipt blob",
    )

    invalid_acknowledgement = context()
    add_record(
        invalid_acknowledgement,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    invalid_acknowledgement.records["S1-0002"] = replace(
        invalid_acknowledgement.records["S1-0002"],
        integration_parent_is_receipt_integration=False,
    )
    invalid_ack_log = [
        freeze(),
        reset("S1-0002", "#908", "record-invalid", "S1-0001"),
    ]
    assert validate(
        invalid_ack_log,
        invalid_acknowledgement,
        audit=audit_evidence(
            "S1-0002",
            ("S1-0001", "S1-0002"),
            target_oid=invalid_acknowledgement.prs["#908"].merge_commit_oid,
        ),
    ) == "reset-required:S1-0001"

    def retained_receipt_case(candidate_record: bool) -> tuple[list[str], Context, str]:
        blocks = [
            freeze(),
            reset("S1-0002", "#908", "record-invalid", "S1-0001"),
            correction("S1-0003", "#909", "S1-0001"),
        ]
        facts = context()
        add_record(
            facts,
            "S1-0002",
            "#908",
            908,
            FREEZE_TIME + timedelta(seconds=1),
        )
        add_record(
            facts,
            "S1-0003",
            "#909",
            909,
            FREEZE_TIME + timedelta(seconds=2),
        )
        if candidate_record:
            facts.prs["#909"] = candidate_pr(909, author="record-author")
        entries = parsed_entries(*blocks)
        prepare_reset_receipts(entries, facts)
        prepare_receipt_retention(entries, facts)
        return blocks, facts, entries[1]["replay_receipt_pr"]

    retained_candidate, retained_candidate_facts, receipt_ref = retained_receipt_case(True)
    retained_candidate_facts.prs[receipt_ref] = replace(
        retained_candidate_facts.prs[receipt_ref],
        integration_reachable_from_main=False,
    )
    assert validate(retained_candidate, retained_candidate_facts) == "correction-pending"

    missing_current_blob, missing_current_blob_facts, receipt_ref = retained_receipt_case(
        False
    )
    missing_current_blob = missing_current_blob[:2]
    current_tree_oid = missing_current_blob_facts.prs["#908"].merge_commit_oid
    assert current_tree_oid is not None
    receipt_entry = parsed_entries(*missing_current_blob)[1]
    replay = missing_current_blob_facts.resolve_replay_record_invalid_reset(
        "S1-0002",
        "S1-0001",
        receipt_ref,
        receipt_entry["replay_receipt_sha256"],
        current_tree_oid,
    )
    missing_current_blob_facts.reset_replays["S1-0002"] = replace(
        replay,
        current_tree_blob_has_exact_path_mode_bytes_and_digest=False,
    )
    assert validate(
        missing_current_blob,
        missing_current_blob_facts,
        audit=audit_evidence(
            "S1-0002",
            (),
            target_oid=current_tree_oid,
        ),
    ) == "reset-required:S1-0001"

    unreachable_creation_blocks, unreachable_creation, creation_audit, _replay = (
        reset_candidate_case()
    )
    receipt_ref = parsed_entries(*unreachable_creation_blocks)[1]["replay_receipt_pr"]
    unreachable_creation.prs[receipt_ref] = replace(
        unreachable_creation.prs[receipt_ref],
        integration_reachable_from_main=False,
    )
    expect_failure(
        lambda: validate(
            unreachable_creation_blocks,
            unreachable_creation,
            audit=creation_audit,
        ),
        "integration is not reachable from main",
    )

    retention_candidate_failures = (
        (
            "candidate_target_preserves_prior_receipts",
            False,
            "candidate target does not retain every prior receipt",
        ),
        (
            "head_preserves_prior_receipts",
            False,
            "exact head does not retain every prior receipt",
        ),
        (
            "entry_diff_untouched_prior_receipts",
            False,
            "diff changes a prior receipt path",
        ),
        (
            "validated_prior_receipts",
            (("docs/tenkz/soak-replay/wrong.json", "0" * 64),),
            "another prior-receipt set",
        ),
    )
    for field_name, bad_value, error_fragment in retention_candidate_failures:
        blocks, facts, _receipt_ref = retained_receipt_case(True)
        facts.records["S1-0003"] = replace(
            facts.records["S1-0003"],
            **{field_name: bad_value},
        )
        expect_failure(
            lambda blocks=blocks, facts=facts: validate(blocks, facts),
            error_fragment,
        )

    retained_postmerge, retained_postmerge_facts, _receipt_ref = retained_receipt_case(False)
    retained_postmerge_facts.records["S1-0003"] = replace(
        retained_postmerge_facts.records["S1-0003"],
        integration_preserves_prior_receipts=False,
    )
    assert validate(retained_postmerge, retained_postmerge_facts) == (
        "reset-required:S1-0003"
    )

    missing_reset_integration = context()
    add_record(
        missing_reset_integration,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    missing_reset_integration.records["S1-0002"] = replace(
        missing_reset_integration.records["S1-0002"],
        receipt_blob_preserved_in_integration=False,
    )
    assert validate(
        [
            freeze(),
            reset("S1-0002", "#908", "record-invalid", "S1-0001"),
        ],
        missing_reset_integration,
        audit=audit_evidence(
            "S1-0002",
            ("S1-0001", "S1-0002"),
            target_oid=missing_reset_integration.prs["#908"].merge_commit_oid,
        ),
    ) == "reset-required:S1-0001"

    receipt_collision_blocks, receipt_collision, collision_audit, _replay = (
        reset_candidate_case()
    )
    receipt_collision_blocks[-1] = reset(
        "S1-0002",
        "#908",
        "record-invalid",
        "S1-0001",
        replay_receipt_pr=ACTIVATION,
    )
    expect_failure(
        lambda: validate(
            receipt_collision_blocks,
            receipt_collision,
            audit=collision_audit,
        ),
        "replay receipt PR #900 is the activation PR",
    )

    mutable_workflow = context()
    activation_integration = mutable_workflow.prs[ACTIVATION].merge_commit_oid
    target_oid = mutable_workflow.prs[SIGNOFF_RECORD].merge_commit_oid
    assert activation_integration is not None and target_oid is not None
    workflow = mutable_workflow.resolve_current_workflow(
        activation_integration,
        target_oid,
        (".github/workflows/tenkz-release-policy.yml",),
    )
    mutable_workflow.workflow_override = replace(
        workflow,
        external_dependencies_use_full_commit_shas=False,
    )
    expect_failure(
        lambda: validate(complete_log(), mutable_workflow),
        "external workflow dependency uses a mutable ref",
    )
    workflow_failures = (
        ("package_managers_absent", False, "invokes a package manager"),
        ("downloaders_absent", False, "invokes a downloader"),
        (
            "unhashed_runtime_dependencies_absent",
            False,
            "unhashed runtime dependency",
        ),
        (
            "runtime_fetched_executables_absent",
            False,
            "fetches executable content at runtime",
        ),
        (
            "network_disabled_before_repository_code",
            False,
            "does not disable network before repository code",
        ),
    )
    for field_name, bad_value, error_fragment in workflow_failures:
        workflow_facts = context()
        activation_integration = workflow_facts.prs[ACTIVATION].merge_commit_oid
        target_oid = workflow_facts.prs[SIGNOFF_RECORD].merge_commit_oid
        assert activation_integration is not None and target_oid is not None
        workflow = workflow_facts.resolve_current_workflow(
            activation_integration,
            target_oid,
            (".github/workflows/tenkz-release-policy.yml",),
        )
        workflow_facts.workflow_override = replace(
            workflow,
            **{field_name: bad_value},
        )
        expect_failure(
            lambda facts=workflow_facts: validate(complete_log(), facts),
            error_fragment,
        )

    boolean_record_parent = context()
    boolean_record_parent.records["S1-0001"] = replace(
        boolean_record_parent.records["S1-0001"],
        integration_parent_count=True,
    )
    assert validate([freeze()], boolean_record_parent) == "reset-required:S1-0001"

    boolean_work_parent = context()
    boolean_work_parent.work_diffs[FORMAL_WORK] = replace(
        boolean_work_parent.work_diffs[FORMAL_WORK],
        integration_parent_count=True,
    )
    assert validate(complete_log()[:2], boolean_work_parent) == (
        "reset-required:S1-0002"
    )

    work_after_record = context()
    work_after_record.prs[FORMAL_RECORD] = replace(
        work_after_record.prs[FORMAL_RECORD],
        merged_at=FORMAL_MERGE - timedelta(microseconds=1),
    )
    assert validate(complete_log()[:2], work_after_record) == (
        "reset-required:S1-0002"
    )

    cross_bound_work = context()
    cross_bound_work.work_diffs[FORMAL_WORK] = replace(
        cross_bound_work.work_diffs[FORMAL_WORK],
        validated_head_oid=oid(99_995),
    )
    assert validate(complete_log()[:2], cross_bound_work) == (
        "reset-required:S1-0002"
    )

    missing_fix_pr = resolution("S1-0003", RMP_RECORD, "S1-0002").replace(
        '\nfix_pr = "#18003"',
        "",
    )
    expect_failure(
        lambda: policy.validate_entry_shape(
            parsed_entries(
                freeze(),
                friction("S1-0002", FORMAL_RECORD, "fix-compatible"),
                missing_fix_pr,
            )[2],
            3,
        ),
        "fields differ from schema",
    )

    def resolution_case(candidate_record: bool) -> tuple[list[str], Context, str]:
        blocks = [
            freeze(),
            friction("S1-0002", FORMAL_RECORD, "fix-compatible"),
            resolution("S1-0003", RMP_RECORD, "S1-0002"),
        ]
        facts = context()
        if candidate_record:
            facts.prs[RMP_RECORD] = candidate_pr(906, author="record-author")
        entries = parsed_entries(*blocks)
        prepare_resolution_facts(entries, facts)
        return blocks, facts, entries[-1]["fix_pr"]

    valid_resolution, valid_resolution_facts, _fix_ref = resolution_case(False)
    assert validate(valid_resolution, valid_resolution_facts) == "attempt-1-active"
    pending_resolution, pending_resolution_facts, _fix_ref = resolution_case(True)
    assert validate(pending_resolution, pending_resolution_facts) == "resolution-pending"

    resolution_diff_failures = (
        (
            "has_added_or_modified_regular_nonledger_blob",
            False,
            "no added or modified regular non-ledger blob",
        ),
        (
            "normalized_token_stream_changed",
            False,
            "no semantic normalized-token change",
        ),
        (
            "semantic_witness_is_same_regular_nonledger_blob",
            False,
            "not one qualifying blob",
        ),
        ("validated_head_oid", oid(99_980), "not validated at its exact head"),
        (
            "integration_strict_descendant_of_friction",
            False,
            "does not descend from its friction record",
        ),
        ("policy_paths_untouched", False, "changes policy or the soak ledger"),
        ("inventory_commands_complete", False, "every pinned inventory command"),
        ("inventory_commands_passed", False, "failed a pinned inventory command"),
        (
            "execution_receipts_exact_and_matching",
            False,
            "execution receipts are incomplete",
        ),
    )
    for field_name, bad_value, error_fragment in resolution_diff_failures:
        blocks, facts, fix_ref = resolution_case(True)
        facts.resolution_diffs[fix_ref] = replace(
            facts.resolution_diffs[fix_ref],
            **{field_name: bad_value},
        )
        expect_failure(
            lambda blocks=blocks, facts=facts: validate(blocks, facts),
            error_fragment,
        )

    unreviewed_resolution, unreviewed_facts, fix_ref = resolution_case(True)
    unreviewed_facts.prs[fix_ref] = replace(unreviewed_facts.prs[fix_ref], reviews=())
    expect_failure(
        lambda: validate(unreviewed_resolution, unreviewed_facts),
        "repository-authorized independent exact-head approval",
    )

    unauthorized_resolution, unauthorized_facts, fix_ref = resolution_case(True)
    set_review_permission(unauthorized_facts, fix_ref, "read")
    expect_failure(
        lambda: validate(unauthorized_resolution, unauthorized_facts),
        "repository-authorized independent exact-head approval",
    )

    stale_resolution_base, stale_resolution_facts, _fix_ref = resolution_case(True)
    stale_resolution_facts.records["S1-0003"] = replace(
        stale_resolution_facts.records["S1-0003"],
        candidate_main_tip_descends_from_fix_integration=False,
    )
    expect_failure(
        lambda: validate(stale_resolution_base, stale_resolution_facts),
        "resolution candidate does not descend from its fix",
    )

    wrong_postmerge_ancestry, wrong_postmerge_facts, _fix_ref = resolution_case(False)
    wrong_postmerge_facts.records["S1-0003"] = replace(
        wrong_postmerge_facts.records["S1-0003"],
        integration_parent_descends_from_fix_integration=False,
    )
    assert validate(wrong_postmerge_ancestry, wrong_postmerge_facts) == (
        "reset-required:S1-0003"
    )

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

    incomplete_audit = policy.AuditEvidence("S1-0004", (), False, True, oid(99_999))
    expect_failure(
        lambda: validate(complete_log(), context(), audit=incomplete_audit),
        "audit snapshot is incomplete",
    )
    inexact_target_audit = policy.AuditEvidence("S1-0004", (), True, False, oid(99_999))
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
        validated_pr_ref="#908",
        validated_head_oid=third_facts.prs["#908"].head_oid,
        validated_integration_oid=third_facts.prs["#908"].merge_commit_oid,
        validated_freeze_integration=third_facts.prs[FREEZE_RECORD].merge_commit_oid,
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
    assert validate(recovered, invalid_facts) == "reset"
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
    assert validate(
        complete_log() + [reset("S1-0005", "#908", "record-invalid", "S1-0002")],
        replayed_drift,
    ) == "reset"

    replayed_freeze_drift = context()
    add_record(
        replayed_freeze_drift,
        "S1-0004",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=8),
    )
    assert validate(
        complete_log()[:3]
        + [reset("S1-0004", "#908", "record-invalid", "S1-0001")],
        replayed_freeze_drift,
    ) == "reset"

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
    assert validate(
        complete_log()
        + [
            correction("S1-0005", "#908", "S1-0001"),
            reset("S1-0006", "#909", "record-invalid", "S1-0002"),
        ],
        corrected_drift,
    ) == "reset"

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
            audit=audit_evidence(
                "S1-0003",
                ("S1-0001",),
                target_oid=ordered_resets.prs["#909"].merge_commit_oid,
            ),
        )
        == "reset-required:S1-0001"
    )
    assert validate(breaking_then_drift, ordered_resets) == "reset"

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
        oid(99_999),
    )
    expect_failure(
        lambda: validate(complete_log(), batched_drift, audit=unsorted_audit),
        "invalid entries are not in ledger order",
    )
    batched_log = complete_log() + [
        reset("S1-0005", "#908", "record-invalid", "S1-0001"),
        reset("S1-0006", "#909", "record-invalid", "S1-0002"),
    ]
    first_reset_audit = audit_evidence(
        "S1-0005",
        ("S1-0002",),
        target_oid=batched_drift.prs["#908"].merge_commit_oid,
    )
    assert validate(batched_log[:-1], batched_drift, audit=first_reset_audit) == (
        "reset-required:S1-0002"
    )
    assert validate(batched_log, batched_drift) == "reset"

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
    add_record(
        reset_common,
        "S1-0005",
        "#911",
        911,
        FREEZE_TIME + timedelta(seconds=6),
    )
    common_cases.append(
        (
            "reset",
            [
                freeze(),
                friction("S1-0002", "#908", "breaking-required"),
                reset("S1-0003", "#909", "breaking-required", "S1-0002"),
                reset("S1-0004", "#910", "breaking-required", "S1-0002"),
                reset("S1-0005", "#911", "record-invalid", "S1-0003"),
            ],
            "S1-0003",
            "S1-0005",
            "#911",
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
        actual = validate(log[:-1], facts)
        assert actual == f"reset-required:{invalid_id}", (name, actual)
        assert log[-1].find(f'id = "{reset_id}"') >= 0
        final_actual = validate(log, facts)
        assert final_actual == "reset", (name, final_actual)

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
    moved_tag.tags["tenkz-v0.9.0"] = policy.TagEvidence(
        "9" * 40,
        "tag",
        SHA,
        True,
        True,
        True,
    )
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
        True,
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
        patch_exceeds_other_namespace_tags=False,
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
            DESIGN_TEXT.replace("schema = 1", "schema = true", 1)
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
        lambda: policy.parse_soak_text(
            SOAK_TEXT.replace("append_only = true", "append_only = 1", 1)
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
