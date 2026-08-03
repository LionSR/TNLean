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
SIGNOFF_TAGGER_EPOCH = int(SIGNOFF_MERGE.timestamp())
PREREQUISITES = '["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]'
INVENTORY_DIGEST = "d" * 64
TEST_CODE_TREE = "e" * 40
TEST_SUPPORT_TREE = "1" * 40
POLICY_DIGEST = "f" * 64
PREFIX_DIGEST = "3" * 64
FINAL_TAG_SCHEMA_BLOB = "4" * 40
FINAL_TAG_PUBLIC_KEY_BLOB = "5" * 40
REGRESSION_TEST = "tex-api-regression"
FAILURE_FINGERPRINT = "2" * 64

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
    tag_snapshot: tuple[str, ...] | None = None,
    prerequisites: str = PREREQUISITES,
) -> str:
    if tag_snapshot is None:
        patch = int(tag.rsplit(".", 1)[1])
        tag_snapshot = tuple(f"tenkz-v0.9.{index}" for index in range(patch + 1))
    rendered_snapshot = ", ".join(f'"{item}"' for item in tag_snapshot)
    return block(
        f'''id = "{entry_id}"
kind = "freeze"
record_pr = "{record_pr}"
attempt = {attempt}
source_pr = "{source_pr}"
source_sha = "{source_sha}"
freeze_tag_object = "{tag_object}"
freeze_tag = "{tag}"
freeze_tag_snapshot = [{rendered_snapshot}]
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
    surface: str = "tex-api",
    regression_tests: tuple[str, ...] | None = None,
) -> str:
    selected_tests = regression_tests
    if selected_tests is None and triage == "fix-compatible":
        selected_tests = (REGRESSION_TEST,)
    regression_line = ""
    if selected_tests is not None:
        rendered_tests = ", ".join(f'"{item}"' for item in selected_tests)
        regression_line = f"\nregression_tests = [{rendered_tests}]"
    return block(
        f'''id = "{entry_id}"
kind = "friction"
record_pr = "{record_pr}"
attempt = {attempt}
surface = "{surface}"
triage = "{triage}"
summary = "observed interface friction"
evidence = "reproducer and triage"{regression_line}'''
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


def publisher_evidence(
    integration_oid: str,
    *,
    status: str = "not-run",
    tagger_epoch_seconds: int = SIGNOFF_TAGGER_EPOCH,
    prefix_boundary: str = "S1-0004",
    prior_released: bool = False,
    prior_released_prefix_boundary: str | None = None,
    prior_released_target_oid: str | None = None,
) -> policy.FinalTagPublisherEvidence:
    ran = status in {"incomplete", "failure", "success"}
    succeeded = status == "success"
    if prior_released:
        prior_released_prefix_boundary = (
            prior_released_prefix_boundary or prefix_boundary
        )
        prior_released_target_oid = prior_released_target_oid or integration_oid
    return policy.FinalTagPublisherEvidence(
        validated_integration_oid=integration_oid,
        validated_tagger_epoch_seconds=tagger_epoch_seconds,
        validated_policy_sha256=POLICY_DIGEST,
        validated_prefix_sha256=PREFIX_DIGEST,
        validated_prefix_boundary=prefix_boundary,
        validated_support_tree_oid=TEST_SUPPORT_TREE,
        validated_schema_blob_oid=FINAL_TAG_SCHEMA_BLOB,
        validated_public_key_blob_oid=FINAL_TAG_PUBLIC_KEY_BLOB,
        complete=True,
        workflow_runs_complete_and_paginated=True,
        workflow_jobs_complete_and_paginated=True,
        release_validation_runs_complete_and_paginated=True,
        prior_released_validation_exact_and_successful=prior_released,
        prior_released_validation_prefix_boundary=prior_released_prefix_boundary,
        prior_released_validation_target_oid=prior_released_target_oid,
        prior_released_validation_target_contains_exact_prefix=(
            True if prior_released else None
        ),
        pinned_workflow_runs_exact=True,
        postmerge_validation_succeeded=True,
        postmerge_validation_network_disabled=True,
        publisher_status=status,
        publisher_needs_exact_postmerge_validation=True,
        publisher_started_after_validation_success=True if ran else None,
        validation_jobs_lack_contents_write=True,
        publisher_has_only_contents_write=True,
        publisher_has_no_checkout_or_repository_execution=True,
        publisher_has_no_uses_or_inherited_secrets=True,
        publisher_uses_only_version_fingerprinted_hosted_gh_git_ssh_keygen=True,
        publisher_command_and_inputs_closed=True,
        publisher_uses_only_github_control_plane=True,
        other_networked_steps_absent=True,
        closed_needs_tuple_complete_and_matching=True,
        closed_needs_has_no_caller_substitute=True,
        github_metadata_matches_closed_needs=True,
        caller_controlled_inputs_absent=True,
        exact_git_objects_fetched_by_oid_and_verified=True,
        publisher_environment_and_secret_exact=True,
        publisher_is_only_private_key_consumer=True,
        deterministic_signed_tag_object_contract=True,
        signature_algorithm_and_namespace_exact=True,
        tagger_epoch_exact_canonical_and_in_range=True,
        publisher_reads_ref_before_private_key_access=True,
        private_key_available_only_to_absent_ref_path=True,
        existing_ref_path_cannot_access_private_key=True,
        absent_ref_candidate_authenticated_before_write=True,
        existing_ref_object_authenticated_without_mutation=True,
        publisher_success_requires_authenticated_final_readback=True,
        publisher_emits_no_durable_output_receipt=True,
        successful_job_head_matches_integration=True if succeeded else None,
        successful_job_historical_workflow_tree_matches_activation=(
            True if succeeded else None
        ),
        successful_job_follows_successful_postmerge_validation=(
            True if succeeded else None
        ),
        successful_job_conclusion_api_visible=True if succeeded else None,
    )


def authenticated_final_tag(
    integration_oid: str,
    *,
    object_oid: str = FINAL_TAG_OBJECT,
    tagger_epoch_seconds: int = SIGNOFF_TAGGER_EPOCH,
    prefix_boundary: str = "S1-0004",
) -> policy.TagEvidence:
    return policy.TagEvidence(
        object_oid,
        "tag",
        integration_oid,
        exists=True,
        final_lookup_before_fetch_object_id=object_oid,
        final_fetched_object_id=object_oid,
        final_lookup_after_fetch_object_id=object_oid,
        final_network_disabled_before_object_read=True,
        final_raw_object_bytes_complete=True,
        final_object_schema_valid=True,
        final_recomputed_object_id=object_oid,
        final_signature_algorithm="ssh-ed25519",
        final_signature_namespace="git",
        final_raw_signature_valid=True,
        final_public_key_blob_oid=FINAL_TAG_PUBLIC_KEY_BLOB,
        final_public_key_from_pinned_support_tree=True,
        final_schema_blob_oid=FINAL_TAG_SCHEMA_BLOB,
        final_schema_from_pinned_support_tree=True,
        final_tagger_identity_matches_schema=True,
        final_tagger_epoch_seconds=tagger_epoch_seconds,
        final_tagger_timezone="+0000",
        final_message_tag=policy.FINAL_TAG,
        final_message_integration_oid=integration_oid,
        final_message_policy_sha256=POLICY_DIGEST,
        final_message_prefix_sha256=PREFIX_DIGEST,
        final_message_prefix_boundary=prefix_boundary,
        final_commit_reachable_from_main=True,
    )


def publisher_secret_evidence(
    *,
    retired: bool = False,
    locations: tuple[str, ...] | None = None,
) -> policy.PublisherSecretEvidence:
    if locations is None:
        locations = () if retired else ("environment:tenkz-release-publisher",)
    return policy.PublisherSecretEvidence(
        validated_environment="tenkz-release-publisher",
        validated_secret_name="TENKZ_FINAL_TAG_SIGNING_KEY",
        validated_secret_scope="environment-only-no-shadow",
        validated_key_retirement="required-before-released",
        complete=True,
        repository_environments_complete_and_paginated=True,
        all_environment_secret_names_complete_and_paginated=True,
        repository_secret_names_complete_and_paginated=True,
        organization_secret_names_and_access_complete_and_paginated=True,
        configured_secret_locations=locations,
        dedicated_environment_configuration_complete=True,
        dedicated_environment_restricts_protected_release_branch=True,
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
    publishers: dict[str, policy.FinalTagPublisherEvidence] = field(default_factory=dict)
    observations: dict[
        tuple[str, str, str], policy.ReleaseTestObservationEvidence
    ] = field(default_factory=dict)
    reset_replays: dict[str, policy.RecordInvalidResetReplayEvidence] = field(
        default_factory=dict
    )
    workflow_override: policy.WorkflowEvidence | None = None
    publisher_secret_override: policy.PublisherSecretEvidence | None = None

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
        _integration_oid: str,
        _paths: tuple[str, ...],
        _work_integrations: tuple[str, ...],
        _resolution_integrations: tuple[str, ...],
    ) -> policy.ReleasePrepEvidence:
        return self.release_preps[ref]

    def resolve_replay_release_payload(
        self,
        tree_oid: str,
        tag: str,
        _contract: policy.ReleaseContract,
    ) -> policy.ReleasePayloadEvidence:
        return self.payloads[(tree_oid, tag)]

    def resolve_replay_release_test_observation(
        self,
        tree_oid: str,
        tag: str,
        test_ref: str,
        _contract: policy.ReleaseContract,
    ) -> policy.ReleaseTestObservationEvidence:
        return self.observations[(tree_oid, tag, test_ref)]

    def resolve_replay_freeze_tag(self, tag: str) -> policy.TagEvidence:
        assert tag != policy.FINAL_TAG
        return self.tags[tag]

    def resolve_current_final_tag(self, tag: str) -> policy.TagEvidence:
        assert tag == policy.FINAL_TAG
        return self.tags[tag]

    def resolve_final_tag_publisher(
        self,
        integration_oid: str,
    ) -> policy.FinalTagPublisherEvidence:
        override = self.publishers.get(integration_oid)
        if override is not None:
            return override
        for entry_id, record_diff in self.records.items():
            record_ref = record_diff.validated_pr_ref
            if record_ref is None:
                continue
            record = self.prs.get(record_ref)
            if record is not None and record.merge_commit_oid == integration_oid:
                assert record.merged_at is not None
                return publisher_evidence(
                    integration_oid,
                    tagger_epoch_seconds=policy.canonical_tagger_epoch_seconds(
                        record.merged_at,
                        f"{record_ref} mergedAt",
                    ),
                    prefix_boundary=entry_id,
                )
        raise AssertionError(f"no sign-off record resolves to {integration_oid}")

    def resolve_current_publisher_secret(
        self,
        _environment: str,
        _secret_name: str,
        _secret_scope: str,
        _key_retirement: str,
    ) -> policy.PublisherSecretEvidence:
        return self.publisher_secret_override or publisher_secret_evidence()

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
            pending_restart_target=None,
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
        publisher_workflow_root: str,
    ) -> policy.WorkflowEvidence:
        if self.workflow_override is not None:
            return self.workflow_override
        return policy.WorkflowEvidence(
            validated_activation_integration=activation_integration,
            validated_target_oid=target_oid,
            validated_paths=paths,
            validated_publisher_workflow_root=publisher_workflow_root,
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
            activation_publisher_workflow_tree_complete=True,
            target_publisher_workflow_tree_matches_activation=True,
            workflow_jobs_complete_and_paginated=True,
            publisher_is_sole_environment_consumer=True,
            publisher_is_sole_secret_consumer=True,
            workflow_secret_inheritance_absent=True,
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
        inventory_exact_schema_valid=True,
        inventory_ids_and_failure_fingerprints_unique=True,
        inventory_test_surface_valid=True,
        inventory_atomic_assertions_one_per_test=True,
        test_code_tree_matches=True,
        test_support_tree_matches=True,
        inventory_subject_paths_within_subject_roots=True,
        inventory_program_paths_regular_and_surface_owned=True,
        inventory_fixture_paths_regular_or_trees=True,
        inventory_subject_roles_disjoint=True,
        inventory_fixtures_nonexecutable=True,
        executable_dependencies_within_harness_tree=True,
        acceptance_dependencies_within_support_tree=True,
        subjects_cannot_supply_evidence_logic=True,
        hermetic_execution_contract_valid=True,
        payload_execution_receipts_complete_and_matching=True,
        test_execution_complete=True,
        compatibility_tests_passed=True,
        payload_blob_oids=blob_oids,
    )


def observation_evidence(
    tree_oid: str,
    tag: str,
    test_ref: str,
    *,
    surface: str = "tex-api",
    result: str = "assertion-failed",
    failure_fingerprint: str = FAILURE_FINGERPRINT,
    program_paths: tuple[str, ...] = ("tex/tenkz/tenkz.sty",),
    fixture_paths: tuple[str, ...] = ("tests/tenkz/rmp/fixtures/baseline.tex",),
) -> policy.ReleaseTestObservationEvidence:
    contract = policy.policy_rules(ARMED_POLICY)[4]
    assertion_failed = result == "assertion-failed"
    return policy.ReleaseTestObservationEvidence(
        validated_tree_oid=tree_oid,
        validated_tag=tag,
        validated_test_ref=test_ref,
        validated_contract=contract,
        complete=True,
        manifest_path=contract.manifest_path(tag),
        regular_distinct_paths=True,
        manifest_contract_valid=True,
        artifact_declarations_agree=True,
        inventory_digest_matches=True,
        inventory_exact_schema_valid=True,
        inventory_ids_and_failure_fingerprints_unique=True,
        inventory_test_surface_valid=True,
        inventory_atomic_assertions_one_per_test=True,
        inventory_test_exists=True,
        inventory_command_exact_and_matching=True,
        test_code_tree_matches=True,
        test_support_tree_matches=True,
        inventory_subject_paths_within_subject_roots=True,
        executable_dependencies_within_harness_tree=True,
        acceptance_dependencies_within_support_tree=True,
        subjects_cannot_supply_evidence_logic=True,
        hermetic_execution_contract_valid=True,
        tool_fingerprints_match=True,
        inventory_test_surface=surface,
        inventory_test_failure_fingerprint=failure_fingerprint,
        inventory_test_program_paths=program_paths,
        inventory_test_fixture_paths=fixture_paths,
        inventory_test_program_paths_regular_blobs=True,
        inventory_test_fixture_paths_regular_blobs_or_trees=True,
        inventory_test_fixture_trees_exclude_program_paths=True,
        inventory_test_fixtures_nonexecutable=True,
        atomic_assertion_count=1,
        exactly_one_inventory_test_run=True,
        setup_complete_and_matching=True,
        isolation_valid=True,
        execution_receipt_exact_and_matching=True,
        execution_complete=True,
        timed_out=False,
        terminated_by_signal=False,
        result=result,
        exit_code=10 if assertion_failed else 0,
        assertion_failure_receipt_path=(
            "/tenkz-output/assertion-failure-v1.json" if assertion_failed else None
        ),
        observed_failure_fingerprint=(
            failure_fingerprint if assertion_failed else None
        ),
        assertion_failure_receipt_exact_and_matching=(
            True if assertion_failed else None
        ),
        assertion_failure_receipt_atomically_written=(
            True if assertion_failed else None
        ),
        single_failure_cause=True if assertion_failed else None,
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
        inventory_exact_schema_valid=True,
        inventory_ids_and_failure_fingerprints_unique=True,
        inventory_test_surface_valid=True,
        inventory_atomic_assertions_one_per_test=True,
        test_code_tree_matches=True,
        test_support_tree_matches=True,
        inventory_subject_paths_within_subject_roots=True,
        inventory_program_paths_regular_and_surface_owned=True,
        inventory_fixture_paths_regular_or_trees=True,
        inventory_subject_roles_disjoint=True,
        inventory_fixtures_nonexecutable=True,
        executable_dependencies_within_harness_tree=True,
        acceptance_dependencies_within_support_tree=True,
        subjects_cannot_supply_evidence_logic=True,
        hermetic_execution_contract_valid=True,
        supervisor_self_test_receipt_valid=True,
        enforcement_workflows_pinned=True,
        publisher_workflow_tree_pinned=True,
        publisher_workflow_jobs_complete_and_paginated=True,
        publisher_is_sole_environment_consumer=True,
        publisher_is_sole_secret_consumer=True,
        workflow_secret_inheritance_absent=True,
        publisher_environment_configuration_complete=True,
        publisher_environment_restricts_protected_release_branch=True,
        repository_environments_complete_and_paginated=True,
        all_environment_secret_names_complete_and_paginated=True,
        repository_secret_names_complete_and_paginated=True,
        organization_secret_names_and_access_complete_and_paginated=True,
        configured_secret_only_in_dedicated_environment=True,
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
            validated_integration_oid=prs[RELEASE_PREP].merge_commit_oid,
            validated_manifest_path="docs/tenkz/releases/tenkz-v1.0.0.toml",
            validated_changed_paths=policy.policy_rules(ARMED_POLICY)[4].release_varying_paths(
                policy.FINAL_TAG
            ),
            validated_work_integrations=work_integrations,
            validated_resolution_integrations=(),
            complete=True,
            integration_parent_count=1,
            unique_merge_base=True,
            integration_parent_is_ancestor_of_head=True,
            integration_second_parent_matches_head=True,
            integration_descends_from_work_integrations=True,
            integration_descends_from_resolution_integrations=True,
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
                historical_candidate_check_exact_and_successful=True,
                historical_current_namespace_complete=True,
                historical_current_matching_tag_names=("tenkz-v0.9.0",),
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


def prepare_friction_observations(entries: list[dict], facts: Context) -> None:
    """Populate exact head/integration failure receipts for named regressions."""

    freeze_tags = {
        entry["attempt"]: entry["freeze_tag"]
        for entry in entries
        if entry["kind"] == "freeze"
    }
    for entry in entries:
        if entry["kind"] != "friction" or entry["triage"] != "fix-compatible":
            continue
        tag = freeze_tags[entry["attempt"]]
        record = facts.prs[entry["record_pr"]]
        trees = [record.head_oid]
        if record.merged is True:
            trees.append(record.merge_commit_oid)
        program_path = (
            "scripts/tenkzlib/tnlog.py"
            if entry["surface"] == "tnlog"
            else "tex/tenkz/tenkz.sty"
        )
        for tree_oid in trees:
            assert isinstance(tree_oid, str)
            for test_ref in entry["regression_tests"]:
                facts.observations.setdefault(
                    (tree_oid, tag, test_ref),
                    observation_evidence(
                        tree_oid,
                        tag,
                        test_ref,
                        surface=entry["surface"],
                        result="assertion-failed",
                        program_paths=(program_path,),
                    ),
                )


def prepare_resolution_facts(entries: list[dict], facts: Context) -> None:
    """Populate exact fix-PR evidence for scenarios not testing resolutions."""

    by_id = {entry["id"]: entry for entry in entries}
    for entry in entries:
        if entry["kind"] != "resolution":
            continue
        entry_id = entry["id"]
        friction_entry = by_id[entry["friction"]]
        if friction_entry["triage"] != "fix-compatible":
            continue
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
        fix_head = fix_pr.head_oid
        assert fix_head is not None
        fix_base = oid(fix_number * 10 - 1)
        surface = friction_entry["surface"]
        program_path = (
            "scripts/tenkzlib/tnlog.py"
            if surface == "tnlog"
            else "tex/tenkz/tenkz.sty"
        )
        stream_kind = (
            "python-location-free-ast"
            if surface == "tnlog"
            else "tex-comment-stripped-tokens"
        )
        regression_fixes = tuple(
            policy.RegressionFixEvidence(
                test_ref=test_ref,
                validated_surface=surface,
                declared_program_paths=(program_path,),
                changed_program_path=program_path,
                program_blob_modified=True,
                semantic_stream_kind=stream_kind,
                semantic_stream_changed=True,
                python_reader_parses=True if surface == "tnlog" else None,
                baseline_failure_fingerprint=FAILURE_FINGERPRINT,
            )
            for test_ref in friction_entry["regression_tests"]
        )
        if fix_ref not in facts.resolution_diffs:
            facts.resolution_diffs[fix_ref] = policy.ResolutionDiffEvidence(
                validated_pr_ref=fix_ref,
                validated_head_oid=fix_head,
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
                validated_base_oid=fix_base,
                validated_regression_tests=tuple(friction_entry["regression_tests"]),
                regression_fixes=regression_fixes,
                validated_identity_trees=(
                    friction_pr.head_oid,
                    friction_integration,
                    fix_base,
                    fix_head,
                    fix_integration,
                ),
                fixture_blobs_modes_and_trees_identical=True,
                freeze_manifest_blob_identical=True,
            )
        fix_diff = facts.resolution_diffs[fix_ref]
        observation_base = fix_diff.validated_base_oid
        if isinstance(observation_base, str):
            for test_ref in friction_entry["regression_tests"]:
                facts.observations.setdefault(
                    (observation_base, freeze_entry["freeze_tag"], test_ref),
                    observation_evidence(
                        observation_base,
                        freeze_entry["freeze_tag"],
                        test_ref,
                        surface=surface,
                        result="assertion-failed",
                        program_paths=(program_path,),
                    ),
                )
                facts.observations.setdefault(
                    (fix_head, freeze_entry["freeze_tag"], test_ref),
                    observation_evidence(
                        fix_head,
                        freeze_entry["freeze_tag"],
                        test_ref,
                        surface=surface,
                        result="passed",
                        program_paths=(program_path,),
                    ),
                )
                facts.observations.setdefault(
                    (fix_integration, freeze_entry["freeze_tag"], test_ref),
                    observation_evidence(
                        fix_integration,
                        freeze_entry["freeze_tag"],
                        test_ref,
                        surface=surface,
                        result="passed",
                        program_paths=(program_path,),
                    ),
                )
        facts.payloads.setdefault(
            (fix_head, freeze_entry["freeze_tag"]),
            payload_evidence(
                fix_head,
                freeze_entry["freeze_tag"],
                FREEZE_PAYLOAD_BLOBS,
            ),
        )
        facts.payloads.setdefault(
            (fix_integration, freeze_entry["freeze_tag"]),
            payload_evidence(
                fix_integration,
                freeze_entry["freeze_tag"],
                FREEZE_PAYLOAD_BLOBS,
            ),
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

    resolution_integrations = tuple(
        facts.prs[entry["record_pr"]].merge_commit_oid
        for entry in entries
        if entry["kind"] == "resolution"
        and entry["fix_pr"] in facts.resolution_diffs
        and isinstance(facts.prs[entry["record_pr"]].merge_commit_oid, str)
    )
    assert all(isinstance(item, str) for item in resolution_integrations)
    if resolution_integrations:
        for ref, evidence in tuple(facts.release_preps.items()):
            if evidence.validated_resolution_integrations == ():
                facts.release_preps[ref] = replace(
                    evidence,
                    validated_resolution_integrations=resolution_integrations,
                    integration_descends_from_resolution_integrations=True,
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
    for entry in entries:
        if entry["kind"] != "freeze":
            continue
        record = facts.prs.get(entry["record_pr"])
        if record is None or record.merged is not False:
            continue
        tag = facts.tags[entry["freeze_tag"]]
        facts.tags[entry["freeze_tag"]] = replace(
            tag,
            candidate_namespace_complete=(
                True
                if tag.candidate_namespace_complete is None
                else tag.candidate_namespace_complete
            ),
            candidate_matching_tag_names=(
                tuple(entry["freeze_tag_snapshot"])
                if tag.candidate_matching_tag_names is None
                else tag.candidate_matching_tag_names
            ),
        )
    prepare_reset_receipts(entries, facts)
    prepare_friction_observations(entries, facts)
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
        "resolve_replay_release_test_observation": (
            facts.resolve_replay_release_test_observation
        ),
        "resolve_replay_freeze_tag": facts.resolve_replay_freeze_tag,
        "resolve_current_final_tag": facts.resolve_current_final_tag,
        "resolve_final_tag_publisher": facts.resolve_final_tag_publisher,
        "resolve_current_publisher_secret": facts.resolve_current_publisher_secret,
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
        historical_candidate_check_exact_and_successful=True,
        historical_current_namespace_complete=True,
    )
    current_names = tuple(
        sorted(
            (name for name in facts.tags if policy.FREEZE_TAG_RE.fullmatch(name)),
            key=lambda name: int(name.rsplit(".", 1)[1]),
        )
    )
    for name in current_names:
        facts.tags[name] = replace(
            facts.tags[name],
            historical_current_namespace_complete=True,
            historical_current_matching_tag_names=current_names,
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
    invalid_activation_surfaces = context()
    invalid_activation_surfaces.activation_diff = replace(
        invalid_activation_surfaces.activation_diff,
        inventory_test_surface_valid=False,
    )
    expect_failure(
        lambda: validate([], invalid_activation_surfaces),
        "activation inventory test surface is invalid",
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
    contract = policy.policy_rules(ARMED_POLICY)[4]
    assert contract.fix_paths("tex-api") == (
        "tex/tenkz/*.tex",
        "tex/tenkz/*.sty",
    )
    assert contract.fix_paths("tnlog") == (
        *contract.fix_paths("tex-api"),
        "scripts/tenkzlib/tnlog.py",
    )
    assert policy.policy_glob_matches(
        "tex/tenkz/tenkz.sty",
        contract.fix_paths("tex-api")[1],
    )
    assert not policy.policy_glob_matches(
        "tex/tenkz/internal/parser.tex",
        contract.fix_paths("tex-api")[0],
    )
    assert not policy.policy_glob_matches(
        "TNLean/Fix.lean",
        contract.fix_paths("tex-api")[0],
    )
    assert contract.tag_signature == "ssh-ed25519"
    assert contract.tag_public_key.endswith("final-tag-signing-key.pub")
    assert contract.tag_object_schema.endswith("final-tag-object-v1.schema.json")
    assert contract.publisher_environment == "tenkz-release-publisher"
    assert contract.publisher_secret == "TENKZ_FINAL_TAG_SIGNING_KEY"
    assert contract.publisher_secret_scope == "environment-only-no-shadow"
    assert contract.publisher_key_retirement == "required-before-released"
    assert contract.publisher_workflow_root == ".github/workflows"
    assert {
        "validated_signoff_merged_at",
        "successful_publisher_object_oids",
        "publisher_operation",
        "reported_tag_object_oid",
        "ref_created_without_force",
        "readback_complete_and_matching",
    }.isdisjoint(policy.FinalTagPublisherEvidence.__dataclass_fields__)
    assert "final_tagger_merged_at" not in policy.TagEvidence.__dataclass_fields__
    assert (
        policy.canonical_tagger_epoch_seconds(SIGNOFF_MERGE, "sign-off mergedAt")
        == SIGNOFF_TAGGER_EPOCH
    )
    expect_failure(
        lambda: policy.canonical_tagger_epoch_seconds(
            SIGNOFF_MERGE + timedelta(microseconds=1),
            "sign-off mergedAt",
        ),
        "not an unambiguous integral UTC instant",
    )
    expect_failure(
        lambda: policy.canonical_tagger_epoch_seconds(
            SIGNOFF_MERGE.astimezone(timezone(timedelta(hours=1))),
            "sign-off mergedAt",
        ),
        "not an unambiguous integral UTC instant",
    )
    wrong_fix_paths = {
        **ARMED_POLICY,
        "policy": {
            **ARMED_POLICY["policy"],
            "tex_api_fix_paths": ["TNLean/**/*.lean"],
        },
    }
    expect_failure(
        lambda: policy.policy_rules(wrong_fix_paths),
        "differs from the signed policy",
    )
    legacy_identity_root = {
        key: value
        for key, value in ARMED_POLICY["policy"].items()
        if key != "github_identity_scheme"
    }
    legacy_identity_root["signer_identity_scheme"] = "github:lowercase-login"
    legacy_identity_policy = {
        **ARMED_POLICY,
        "policy": legacy_identity_root,
    }
    expect_failure(
        lambda: policy.policy_rules(legacy_identity_policy),
        "differs from the signed policy",
    )
    assert "signer_identity_scheme" not in policy.EXPECTED_POLICY["policy"]
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

    missing_snapshot = freeze().replace(
        '\nfreeze_tag_snapshot = ["tenkz-v0.9.0"]',
        "",
    )
    expect_failure(
        lambda: policy.validate_entry_shape(parsed_entries(missing_snapshot)[0], 1),
        "fields differ from schema",
    )
    expect_failure(
        lambda: validate([freeze(tag_snapshot=())], context()),
        "freeze_tag_snapshot is missing",
    )
    expect_failure(
        lambda: validate(
            [
                freeze(
                    tag="tenkz-v0.9.2",
                    tag_snapshot=(
                        "tenkz-v0.9.1",
                        "tenkz-v0.9.0",
                        "tenkz-v0.9.2",
                    ),
                )
            ],
            context(),
        ),
        "not in ascending numeric PATCH order",
    )
    expect_failure(
        lambda: validate(
            [
                freeze(
                    tag="tenkz-v0.9.1",
                    tag_snapshot=("tenkz-v0.9.1", "tenkz-v0.9.2"),
                )
            ],
            context(),
        ),
        "freeze PATCH is not maximal in its retained snapshot",
    )

    later_reservation = context()
    later_reservation.tags["tenkz-v0.9.0"] = replace(
        later_reservation.tags["tenkz-v0.9.0"],
        historical_current_matching_tag_names=(
            "tenkz-v0.9.0",
            "tenkz-v0.9.1",
        ),
    )
    assert validate([freeze()], later_reservation) == "attempt-1-active"

    lost_retained_name = context()
    lost_retained_name.tags["tenkz-v0.9.0"] = replace(
        lost_retained_name.tags["tenkz-v0.9.0"],
        historical_current_matching_tag_names=("tenkz-v0.9.1",),
    )
    assert validate([freeze()], lost_retained_name) == "reset-required:S1-0001"

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
    restart_with_receipt = reset(
        "S1-0002", "#908", "restart-required", "S1-0001"
    ).replace(
        'evidence = "verified reset cause"',
        'evidence = "verified reset cause"\nreplay_receipt_pr = "#19002"\n'
        f'replay_receipt_sha256 = "{"2" * 64}"',
    )
    expect_failure(
        lambda: policy.validate_entry_shape(
            parsed_entries(freeze(), restart_with_receipt)[1],
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
            "pending_restart_target",
            "S1-0001",
            "wrong pending restart target",
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
        ".github/workflows",
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
        (
            "validated_publisher_workflow_root",
            ".github/other-workflows",
            "another publisher workflow root",
        ),
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
        (
            "activation_publisher_workflow_tree_complete",
            False,
            "activation publisher workflow tree is incomplete",
        ),
        (
            "target_publisher_workflow_tree_matches_activation",
            False,
            "publisher workflow tree differs from activation",
        ),
        (
            "workflow_jobs_complete_and_paginated",
            False,
            "workflow job enumeration is incomplete",
        ),
        (
            "publisher_is_sole_environment_consumer",
            False,
            "another workflow job names the publisher environment",
        ),
        (
            "publisher_is_sole_secret_consumer",
            False,
            "another workflow job names the publisher secret",
        ),
        (
            "workflow_secret_inheritance_absent",
            False,
            "permits inherited secrets",
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
            ".github/workflows",
        )
        workflow_facts.workflow_override = replace(
            workflow,
            **{field_name: bad_value},
        )
        expect_failure(
            lambda facts=workflow_facts: validate(complete_log(), facts),
            error_fragment,
        )

    publisher_secret_failures = (
        ("validated_environment", "another-environment", "another environment"),
        ("validated_secret_name", "ANOTHER_KEY", "another secret name"),
        ("validated_secret_scope", "repository", "another scope contract"),
        ("validated_key_retirement", "optional", "another retirement contract"),
        ("complete", False, "publisher secret evidence is incomplete"),
        (
            "repository_environments_complete_and_paginated",
            False,
            "repository environment pagination is incomplete",
        ),
        (
            "all_environment_secret_names_complete_and_paginated",
            False,
            "environment secret-name pagination is incomplete",
        ),
        (
            "repository_secret_names_complete_and_paginated",
            False,
            "repository secret-name pagination is incomplete",
        ),
        (
            "organization_secret_names_and_access_complete_and_paginated",
            False,
            "organization secret-name or access pagination is incomplete",
        ),
        (
            "dedicated_environment_configuration_complete",
            False,
            "publisher environment configuration is incomplete",
        ),
        (
            "dedicated_environment_restricts_protected_release_branch",
            False,
            "does not restrict the protected release branch",
        ),
    )
    for field_name, bad_value, error_fragment in publisher_secret_failures:
        secret_facts = context()
        secret_facts.publisher_secret_override = replace(
            publisher_secret_evidence(),
            **{field_name: bad_value},
        )
        expect_failure(
            lambda facts=secret_facts: validate([], facts),
            error_fragment,
        )

    for locations in (
        (),
        ("environment:another-environment",),
        ("repository:TENKZ_FINAL_TAG_SIGNING_KEY",),
        ("organization:TNLean-org:access-none",),
        ("organization:TNLean-org:access-selected",),
        (
            "environment:tenkz-release-publisher",
            "repository:TENKZ_FINAL_TAG_SIGNING_KEY",
        ),
    ):
        shadowed_secret = context()
        shadowed_secret.publisher_secret_override = publisher_secret_evidence(
            locations=locations,
        )
        expect_failure(
            lambda facts=shadowed_secret: validate([], facts),
            "publisher signing-key name is missing, shadowed, or outside its environment",
        )

    malformed_secret_locations = context()
    malformed_secret_locations.publisher_secret_override = publisher_secret_evidence(
        locations=(
            "environment:tenkz-release-publisher",
            "environment:tenkz-release-publisher",
        ),
    )
    expect_failure(
        lambda: validate([], malformed_secret_locations),
        "publisher secret locations are incomplete or malformed",
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

    missing_freeze_merge_time = context()
    missing_freeze_merge_time.prs[FREEZE_RECORD] = replace(
        missing_freeze_merge_time.prs[FREEZE_RECORD],
        merged_at=None,
    )
    assert validate(complete_log(), missing_freeze_merge_time) == (
        "reset-required:S1-0001"
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

    missing_regression_tests = friction(
        "S1-0002",
        FORMAL_RECORD,
        "fix-compatible",
    ).replace(f'\nregression_tests = ["{REGRESSION_TEST}"]', "")
    expect_failure(
        lambda: policy.validate_entry_shape(
            parsed_entries(freeze(), missing_regression_tests)[1],
            2,
        ),
        "fields differ from schema",
    )

    forbidden_regression_tests = friction(
        "S1-0002",
        FORMAL_RECORD,
        "defer-to-2.0",
        regression_tests=(REGRESSION_TEST,),
    )
    expect_failure(
        lambda: policy.validate_entry_shape(
            parsed_entries(freeze(), forbidden_regression_tests)[1],
            2,
        ),
        "fields differ from schema",
    )

    deferred_friction_facts = context()
    formal_record_diff = deferred_friction_facts.records["S1-0002"]
    rmp_record_diff = deferred_friction_facts.records["S1-0003"]
    signoff_record_diff = deferred_friction_facts.records["S1-0004"]
    add_record(
        deferred_friction_facts,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(microseconds=500_000),
    )
    deferred_friction_facts.records["S1-0003"] = formal_record_diff
    deferred_friction_facts.records["S1-0004"] = rmp_record_diff
    deferred_friction_facts.records["S1-0005"] = signoff_record_diff
    deferred_friction_log = [
        freeze(),
        friction("S1-0002", "#908", "defer-to-2.0"),
        work(
            "S1-0003",
            FORMAL_RECORD,
            FORMAL_WORK,
            "formalization-or-blueprint",
        ),
        work("S1-0004", RMP_RECORD, RMP_WORK, "rmp-benchmark"),
        sign_off(
            "S1-0005",
            SIGNOFF_RECORD,
            ["S1-0003", "S1-0004"],
        ),
    ]
    assert validate(deferred_friction_log, deferred_friction_facts) == (
        "signed-off-awaiting-tag"
    )

    deferred_resolution_facts = context()
    add_record(
        deferred_resolution_facts,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    add_record(
        deferred_resolution_facts,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=2),
    )
    expect_failure(
        lambda: validate(
            [
                freeze(),
                friction("S1-0002", "#908", "defer-to-2.0"),
                resolution("S1-0003", "#909", "S1-0002"),
            ],
            deferred_resolution_facts,
        ),
        "resolves incompatible triage",
    )

    for bad_tests, error_fragment in (
        (("Bad_Test",), "invalid regression test"),
        ((REGRESSION_TEST, REGRESSION_TEST), "has duplicates"),
    ):
        expect_failure(
            lambda tests=bad_tests: validate(
                [
                    freeze(),
                    friction(
                        "S1-0002",
                        FORMAL_RECORD,
                        "fix-compatible",
                        regression_tests=tests,
                    ),
                ],
                context(),
            ),
            error_fragment,
        )

    def friction_case(candidate_record: bool) -> tuple[list[str], Context, tuple[str, str, str]]:
        blocks = [
            freeze(),
            friction("S1-0002", FORMAL_RECORD, "fix-compatible"),
        ]
        facts = context()
        if candidate_record:
            facts.prs[FORMAL_RECORD] = candidate_pr(904, author="record-author")
        entries = parsed_entries(*blocks)
        prepare_friction_observations(entries, facts)
        record = facts.prs[FORMAL_RECORD]
        tree_oid = record.head_oid if candidate_record else record.merge_commit_oid
        assert isinstance(tree_oid, str)
        return blocks, facts, (tree_oid, "tenkz-v0.9.0", REGRESSION_TEST)

    friction_observation_failures = (
        ("inventory_test_surface", "tnlog", "test covers another surface"),
        ("inventory_test_surface", None, "test surface is missing or invalid"),
        ("inventory_test_exists", False, "test is absent from inventory"),
        ("inventory_command_exact_and_matching", False, "command differs from the pinned"),
        (
            "inventory_test_fixture_trees_exclude_program_paths",
            False,
            "fixture tree contains a program path",
        ),
        ("inventory_test_fixtures_nonexecutable", False, "fixture is executable"),
        ("atomic_assertion_count", 2, "does not contain exactly one atomic assertion"),
        ("timed_out", True, "timed out"),
        ("terminated_by_signal", True, "ended by signal"),
        ("setup_complete_and_matching", False, "setup is incomplete"),
        ("isolation_valid", False, "isolation failed"),
        ("execution_complete", False, "execution is incomplete"),
        ("result", "setup-failed", "returned another result"),
        ("exit_code", 9, "assertion failure did not exit exactly 10"),
        ("exit_code", True, "invalid process exit code"),
        (
            "observed_failure_fingerprint",
            "3" * 64,
            "observed another failure fingerprint",
        ),
        ("single_failure_cause", False, "coarse or multiple-cause failure"),
        ("validated_tag", "tenkz-v0.9.1", "used another freeze tag"),
    )
    for field_name, bad_value, error_fragment in friction_observation_failures:
        blocks, facts, observation_key = friction_case(True)
        facts.observations[observation_key] = replace(
            facts.observations[observation_key],
            **{field_name: bad_value},
        )
        expect_failure(
            lambda blocks=blocks, facts=facts: validate(blocks, facts),
            error_fragment,
        )

    fixture_gaming, fixture_gaming_facts, observation_key = friction_case(True)
    observation = fixture_gaming_facts.observations[observation_key]
    fixture_gaming_facts.observations[observation_key] = replace(
        observation,
        inventory_test_fixture_paths=observation.inventory_test_program_paths,
    )
    expect_failure(
        lambda: validate(fixture_gaming, fixture_gaming_facts),
        "program and fixture roles overlap",
    )

    postmerge_friction, postmerge_friction_facts, integration_key = friction_case(False)
    postmerge_friction_facts.observations[integration_key] = replace(
        postmerge_friction_facts.observations[integration_key],
        exit_code=0,
    )
    assert validate(postmerge_friction, postmerge_friction_facts) == (
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

    empty_regression_resolution = [
        freeze(),
        friction(
            "S1-0002",
            FORMAL_RECORD,
            "fix-compatible",
            regression_tests=(),
        ),
        resolution("S1-0003", RMP_RECORD, "S1-0002"),
    ]
    expect_failure(
        lambda: validate(empty_regression_resolution, context()),
        "regression_tests must be nonempty",
    )

    empty_gap_signoff = [
        freeze(),
        friction(
            "S1-0002",
            FORMAL_RECORD,
            "fix-compatible",
            regression_tests=(),
        ),
        work(
            "S1-0003",
            RMP_RECORD,
            FORMAL_WORK,
            "formalization-or-blueprint",
        ),
        work("S1-0004", "#930", RMP_WORK, "rmp-benchmark"),
        sign_off("S1-0005", "#931", ["S1-0003", "S1-0004"]),
    ]
    empty_gap_facts = context()
    add_record(
        empty_gap_facts,
        "S1-0004",
        "#930",
        930,
        FREEZE_TIME + timedelta(seconds=8),
    )
    add_record(
        empty_gap_facts,
        "S1-0005",
        "#931",
        931,
        SIGNOFF_MERGE,
    )
    empty_gap_head = empty_gap_facts.prs["#931"].head_oid
    assert isinstance(empty_gap_head, str)
    empty_gap_facts.prs["#931"] = replace(
        empty_gap_facts.prs["#931"],
        author_login="release-author",
        reviews=(review("release-reviewer", SIGNOFF_REVIEW, empty_gap_head),),
    )
    empty_gap_facts.records["S1-0005"] = replace(
        empty_gap_facts.records["S1-0005"],
        candidate_main_tip_is_release_integration=True,
        integration_parent_is_release_integration=True,
        validated_release_integration=empty_gap_facts.prs[RELEASE_PREP].merge_commit_oid,
        validated_work_integrations=(
            empty_gap_facts.prs[FORMAL_WORK].merge_commit_oid,
            empty_gap_facts.prs[RMP_WORK].merge_commit_oid,
        ),
    )
    empty_gap_facts.payloads[(empty_gap_head, policy.FINAL_TAG)] = payload_evidence(
        empty_gap_head,
        policy.FINAL_TAG,
        FINAL_PAYLOAD_BLOBS,
    )
    expect_failure(
        lambda: validate(empty_gap_signoff, empty_gap_facts),
        "regression_tests must be nonempty",
    )

    def resolution_case(
        candidate_record: bool,
        *,
        surface: str = "tex-api",
        test_ref: str = REGRESSION_TEST,
    ) -> tuple[list[str], Context, str]:
        blocks = [
            freeze(),
            friction(
                "S1-0002",
                FORMAL_RECORD,
                "fix-compatible",
                surface=surface,
                regression_tests=(test_ref,),
            ),
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

    reader_resolution, reader_resolution_facts, reader_fix_ref = resolution_case(
        True,
        surface="tnlog",
        test_ref="tnlog-reader-regression",
    )
    assert validate(reader_resolution, reader_resolution_facts) == "resolution-pending"
    reader_diff = reader_resolution_facts.resolution_diffs[reader_fix_ref]
    assert reader_diff.regression_fixes is not None
    reader_resolution_facts.resolution_diffs[reader_fix_ref] = replace(
        reader_diff,
        regression_fixes=(
            replace(reader_diff.regression_fixes[0], python_reader_parses=False),
        ),
    )
    expect_failure(
        lambda: validate(reader_resolution, reader_resolution_facts),
        "reader semantic stream is invalid",
    )

    resolution_diff_failures = (
        ("validated_base_oid", "bad", "merge base is missing or malformed"),
        ("validated_regression_tests", (), "used another regression-test set"),
        ("regression_fixes", (), "lacks one semantic witness per regression test"),
        (
            "validated_identity_trees",
            (SHA, SHA, SHA, SHA, SHA),
            "identity check used another five-tree boundary",
        ),
        (
            "fixture_blobs_modes_and_trees_identical",
            False,
            "changes a regression fixture identity",
        ),
        (
            "freeze_manifest_blob_identical",
            False,
            "changes the active-freeze manifest identity",
        ),
        ("validated_head_oid", oid(99_980), "not validated at its exact head"),
        (
            "integration_strict_descendant_of_friction",
            False,
            "does not descend from its friction record",
        ),
        ("policy_paths_untouched", False, "changes policy or the soak ledger"),
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

    regression_fix_failures = (
        ("validated_surface", "tnlog", "used another compatibility surface"),
        (
            "declared_program_paths",
            ("tex/tenkz/other.sty",),
            "used another declared program set",
        ),
        ("program_blob_modified", False, "program blob was not modified"),
        ("semantic_stream_changed", False, "changed only nonsemantic text"),
        ("semantic_stream_kind", "raw-bytes", "TeX semantic stream is invalid"),
        ("python_reader_parses", True, "TeX semantic stream is invalid"),
        (
            "baseline_failure_fingerprint",
            "3" * 64,
            "used another baseline fingerprint",
        ),
    )
    for field_name, bad_value, error_fragment in regression_fix_failures:
        blocks, facts, fix_ref = resolution_case(True)
        fix_diff = facts.resolution_diffs[fix_ref]
        assert fix_diff.regression_fixes is not None
        facts.resolution_diffs[fix_ref] = replace(
            fix_diff,
            regression_fixes=(
                replace(fix_diff.regression_fixes[0], **{field_name: bad_value}),
            ),
        )
        expect_failure(
            lambda blocks=blocks, facts=facts: validate(blocks, facts),
            error_fragment,
        )

    # Neither a Lean-only change, a harness-only change, nor a fixture change
    # can stand in for the declared compatibility program.
    for rejected_path in (
        "TNLean/Fix.lean",
        "tests/tenkz/release-harness/test_fix.py",
        "tests/tenkz/rmp/fixtures/baseline.tex",
    ):
        blocks, facts, fix_ref = resolution_case(True)
        fix_diff = facts.resolution_diffs[fix_ref]
        assert fix_diff.regression_fixes is not None
        facts.resolution_diffs[fix_ref] = replace(
            fix_diff,
            regression_fixes=(
                replace(
                    fix_diff.regression_fixes[0],
                    changed_program_path=rejected_path,
                ),
            ),
        )
        expect_failure(
            lambda blocks=blocks, facts=facts: validate(blocks, facts),
            "changed no eligible declared program",
        )

    def fix_observation_keys(
        facts: Context,
        fix_ref: str,
    ) -> tuple[
        tuple[str, str, str],
        tuple[str, str, str],
        tuple[str, str, str],
    ]:
        fix_base = facts.resolution_diffs[fix_ref].validated_base_oid
        fix_head = facts.prs[fix_ref].head_oid
        fix_integration = facts.prs[fix_ref].merge_commit_oid
        assert (
            isinstance(fix_base, str)
            and isinstance(fix_head, str)
            and isinstance(fix_integration, str)
        )
        tag = "tenkz-v0.9.0"
        return (
            (fix_base, tag, REGRESSION_TEST),
            (fix_head, tag, REGRESSION_TEST),
            (fix_integration, tag, REGRESSION_TEST),
        )

    base_passes, base_passes_facts, fix_ref = resolution_case(True)
    base_key, _head_key, _integration_key = fix_observation_keys(
        base_passes_facts,
        fix_ref,
    )
    base_passes_facts.observations[base_key] = replace(
        base_passes_facts.observations[base_key],
        exit_code=0,
    )
    expect_failure(
        lambda: validate(base_passes, base_passes_facts),
        "fix-base test tex-api-regression assertion failure did not exit exactly 10",
    )

    head_fails, head_fails_facts, fix_ref = resolution_case(True)
    _base_key, head_key, _integration_key = fix_observation_keys(
        head_fails_facts,
        fix_ref,
    )
    head_fails_facts.observations[head_key] = replace(
        head_fails_facts.observations[head_key],
        exit_code=9,
    )
    expect_failure(
        lambda: validate(head_fails, head_fails_facts),
        "fix-head test tex-api-regression passed result did not exit zero",
    )

    wrong_fix_tag, wrong_fix_tag_facts, fix_ref = resolution_case(True)
    _base_key, head_key, _integration_key = fix_observation_keys(
        wrong_fix_tag_facts,
        fix_ref,
    )
    wrong_fix_tag_facts.observations[head_key] = replace(
        wrong_fix_tag_facts.observations[head_key],
        validated_tag="tenkz-v0.9.1",
    )
    expect_failure(
        lambda: validate(wrong_fix_tag, wrong_fix_tag_facts),
        "fix-head test tex-api-regression used another freeze tag",
    )

    integration_fails, integration_fails_facts, fix_ref = resolution_case(True)
    _base_key, _head_key, integration_key = fix_observation_keys(
        integration_fails_facts,
        fix_ref,
    )
    integration_fails_facts.observations[integration_key] = replace(
        integration_fails_facts.observations[integration_key],
        exit_code=9,
    )
    expect_failure(
        lambda: validate(integration_fails, integration_fails_facts),
        "fix-integration test tex-api-regression passed result did not exit zero",
    )

    incomplete_fix_payload, incomplete_fix_payload_facts, fix_ref = resolution_case(True)
    fix_head = incomplete_fix_payload_facts.prs[fix_ref].head_oid
    assert isinstance(fix_head, str)
    payload_key = (fix_head, "tenkz-v0.9.0")
    incomplete_fix_payload_facts.payloads[payload_key] = replace(
        incomplete_fix_payload_facts.payloads[payload_key],
        compatibility_tests_passed=False,
    )
    expect_failure(
        lambda: validate(incomplete_fix_payload, incomplete_fix_payload_facts),
        "fix head release compatibility tests did not pass",
    )

    incomplete_integration_payload, integration_payload_facts, fix_ref = resolution_case(True)
    fix_integration = integration_payload_facts.prs[fix_ref].merge_commit_oid
    assert isinstance(fix_integration, str)
    integration_payload_key = (fix_integration, "tenkz-v0.9.0")
    integration_payload_facts.payloads[integration_payload_key] = replace(
        integration_payload_facts.payloads[integration_payload_key],
        compatibility_tests_passed=False,
    )
    expect_failure(
        lambda: validate(incomplete_integration_payload, integration_payload_facts),
        "fix integration release compatibility tests did not pass",
    )

    invalid_inventory_surfaces, invalid_inventory_facts, fix_ref = resolution_case(True)
    fix_head = invalid_inventory_facts.prs[fix_ref].head_oid
    assert isinstance(fix_head, str)
    payload_key = (fix_head, "tenkz-v0.9.0")
    invalid_inventory_facts.payloads[payload_key] = replace(
        invalid_inventory_facts.payloads[payload_key],
        inventory_test_surface_valid=False,
    )
    expect_failure(
        lambda: validate(invalid_inventory_surfaces, invalid_inventory_facts),
        "fix head test inventory has an invalid surface declaration",
    )

    postmerge_recheck, postmerge_recheck_facts, fix_ref = resolution_case(False)
    _base_key, head_key, _integration_key = fix_observation_keys(
        postmerge_recheck_facts,
        fix_ref,
    )
    postmerge_recheck_facts.observations[head_key] = replace(
        postmerge_recheck_facts.observations[head_key],
        exit_code=2,
    )
    assert validate(postmerge_recheck, postmerge_recheck_facts) == (
        "reset-required:S1-0003"
    )

    integration_postmerge_recheck, integration_postmerge_facts, fix_ref = (
        resolution_case(False)
    )
    _base_key, _head_key, integration_key = fix_observation_keys(
        integration_postmerge_facts,
        fix_ref,
    )
    integration_postmerge_facts.observations[integration_key] = replace(
        integration_postmerge_facts.observations[integration_key],
        exit_code=2,
    )
    assert validate(integration_postmerge_recheck, integration_postmerge_facts) == (
        "reset-required:S1-0003"
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

    old_attempt_facts = context()
    add_record(
        old_attempt_facts,
        "S1-0002",
        "#908",
        908,
        FREEZE_TIME + timedelta(seconds=1),
    )
    add_record(
        old_attempt_facts,
        "S1-0003",
        "#909",
        909,
        FREEZE_TIME + timedelta(seconds=2),
    )
    second_source_sha = "4" * 40
    add_freeze_facts(
        old_attempt_facts,
        "S1-0004",
        source_ref="#910",
        source_number=910,
        source_sha=second_source_sha,
        record_ref="#911",
        record_number=911,
        tag="tenkz-v0.9.1",
        tag_object="5" * 40,
        merged_at=FREEZE_TIME + timedelta(seconds=4),
    )
    add_record(
        old_attempt_facts,
        "S1-0005",
        "#912",
        912,
        FREEZE_TIME + timedelta(seconds=6),
    )
    old_attempt_resolution = [
        freeze(),
        friction("S1-0002", "#908", "restart-required"),
        reset("S1-0003", "#909", "restart-required", "S1-0002"),
        freeze(
            "S1-0004",
            record_pr="#911",
            attempt=2,
            source_pr="#910",
            source_sha=second_source_sha,
            tag_object="5" * 40,
            tag="tenkz-v0.9.1",
        ),
        resolution(
            "S1-0005",
            "#912",
            "S1-0002",
            attempt=2,
        ),
    ]
    expect_failure(
        lambda: validate(old_attempt_resolution, old_attempt_facts),
        "names no friction in this attempt",
    )

    def resolution_signoff_case(
        *,
        release_merge: datetime,
        candidate_signoff: bool,
    ) -> tuple[list[str], Context]:
        facts = context()
        record_specs = (
            ("S1-0002", "#908", 908, 3),
            ("S1-0003", "#909", 909, 5),
            ("S1-0004", "#910", 910, 6),
            ("S1-0005", "#911", 911, 7),
            ("S1-0006", "#912", 912, 11),
        )
        for entry_id, ref, number, seconds in record_specs:
            add_record(
                facts,
                entry_id,
                ref,
                number,
                FREEZE_TIME + timedelta(seconds=seconds),
            )
        release_head = facts.prs[RELEASE_PREP].head_oid
        assert isinstance(release_head, str)
        facts.prs[RELEASE_PREP] = replace(
            facts.prs[RELEASE_PREP],
            merged_at=release_merge,
            reviews=(
                review(
                    "release-prep-reviewer",
                    release_merge - timedelta(microseconds=1),
                    release_head,
                ),
            ),
        )
        signoff_head = facts.prs["#912"].head_oid
        assert isinstance(signoff_head, str)
        if candidate_signoff:
            facts.prs["#912"] = candidate_pr(
                912,
                author="release-author",
                reviews=(
                    review(
                        "release-reviewer",
                        FREEZE_TIME + timedelta(seconds=10),
                        signoff_head,
                    ),
                ),
            )
        else:
            facts.prs["#912"] = replace(
                facts.prs["#912"],
                author_login="release-author",
                reviews=(
                    review(
                        "release-reviewer",
                        FREEZE_TIME + timedelta(seconds=10),
                        signoff_head,
                    ),
                ),
            )
        work_integrations = (
            facts.prs[FORMAL_WORK].merge_commit_oid,
            facts.prs[RMP_WORK].merge_commit_oid,
        )
        facts.records["S1-0006"] = replace(
            facts.records["S1-0006"],
            candidate_main_tip_is_release_integration=True,
            integration_parent_is_release_integration=True,
            validated_release_integration=facts.prs[RELEASE_PREP].merge_commit_oid,
            validated_work_integrations=work_integrations,
        )
        facts.payloads[(signoff_head, policy.FINAL_TAG)] = payload_evidence(
            signoff_head,
            policy.FINAL_TAG,
            FINAL_PAYLOAD_BLOBS,
        )
        signoff_integration = facts.prs["#912"].merge_commit_oid
        if isinstance(signoff_integration, str):
            facts.payloads[(signoff_integration, policy.FINAL_TAG)] = payload_evidence(
                signoff_integration,
                policy.FINAL_TAG,
                FINAL_PAYLOAD_BLOBS,
            )
        blocks = [
            freeze(),
            friction("S1-0002", "#908", "fix-compatible"),
            resolution("S1-0003", "#909", "S1-0002"),
            work(
                "S1-0004",
                "#910",
                FORMAL_WORK,
                "formalization-or-blueprint",
            ),
            work("S1-0005", "#911", RMP_WORK, "rmp-benchmark"),
            sign_off(
                "S1-0006",
                "#912",
                ["S1-0004", "S1-0005"],
            ),
        ]
        prepared_entries = parsed_entries(*blocks)
        prepare_friction_observations(prepared_entries, facts)
        prepare_resolution_facts(prepared_entries, facts)
        return blocks, facts

    resolution_signoff, resolution_signoff_facts = resolution_signoff_case(
        release_merge=FREEZE_TIME + timedelta(seconds=8),
        candidate_signoff=True,
    )
    resolution_signoff_status = validate(resolution_signoff, resolution_signoff_facts)
    assert resolution_signoff_status == "sign-off-pending", resolution_signoff_status
    prep_before_resolution, prep_before_resolution_facts = resolution_signoff_case(
        release_merge=FREEZE_TIME + timedelta(seconds=3, microseconds=500_000),
        candidate_signoff=True,
    )
    expect_failure(
        lambda: validate(prep_before_resolution, prep_before_resolution_facts),
        "release preparation merged before work or resolution evidence",
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
    released.tags[policy.FINAL_TAG] = authenticated_final_tag(oid(9071))
    released.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
        prior_released=True,
    )
    released.publisher_secret_override = publisher_secret_evidence(retired=True)
    assert validate(complete_log(), released) == "released"

    prior_release_binding_failures = (
        (
            "prior_released_validation_prefix_boundary",
            "S1-9999",
            "prior released validation used another ledger prefix",
        ),
        (
            "prior_released_validation_target_oid",
            None,
            "prior released validation target is missing or malformed",
        ),
        (
            "prior_released_validation_target_contains_exact_prefix",
            False,
            "did not contain the exact ledger prefix",
        ),
    )
    for field_name, bad_value, error_fragment in prior_release_binding_failures:
        bad_prior_release = context()
        bad_prior_release.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
        bad_prior_release.publishers[oid(9071)] = replace(
            publisher_evidence(
                oid(9071),
                status="success",
                prior_released=True,
            ),
            **{field_name: bad_value},
        )
        bad_prior_release.publisher_secret_override = publisher_secret_evidence(
            retired=True
        )
        expect_failure(
            lambda facts=bad_prior_release: validate(complete_log(), facts),
            error_fragment,
        )

    first_release_declaration = context()
    first_release_declaration.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    first_release_declaration.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    first_release_declaration.publisher_secret_override = publisher_secret_evidence(
        retired=True,
    )
    assert validate(complete_log(), first_release_declaration) == "released"

    first_release_with_workflow_drift = context()
    first_release_with_workflow_drift.tags[policy.FINAL_TAG] = released.tags[
        policy.FINAL_TAG
    ]
    first_release_with_workflow_drift.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    first_release_with_workflow_drift.publisher_secret_override = (
        publisher_secret_evidence(retired=True)
    )
    activation_integration = first_release_with_workflow_drift.prs[
        ACTIVATION
    ].merge_commit_oid
    target_oid = first_release_with_workflow_drift.prs[
        SIGNOFF_RECORD
    ].merge_commit_oid
    assert isinstance(activation_integration, str) and isinstance(target_oid, str)
    transition_workflow = first_release_with_workflow_drift.resolve_current_workflow(
        activation_integration,
        target_oid,
        (".github/workflows/tenkz-release-policy.yml",),
        ".github/workflows",
    )
    first_release_with_workflow_drift.workflow_override = replace(
        transition_workflow,
        target_publisher_workflow_tree_matches_activation=False,
    )
    expect_failure(
        lambda: validate(complete_log(), first_release_with_workflow_drift),
        "publisher workflow tree differs from activation",
    )

    first_release_with_environment_drift = context()
    first_release_with_environment_drift.tags[policy.FINAL_TAG] = released.tags[
        policy.FINAL_TAG
    ]
    first_release_with_environment_drift.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    first_release_with_environment_drift.publisher_secret_override = replace(
        publisher_secret_evidence(retired=True),
        dedicated_environment_configuration_complete=False,
    )
    expect_failure(
        lambda: validate(complete_log(), first_release_with_environment_drift),
        "publisher environment configuration is incomplete",
    )

    released_with_current_workflow_drift = context()
    released_with_current_workflow_drift.tags[policy.FINAL_TAG] = released.tags[
        policy.FINAL_TAG
    ]
    released_with_current_workflow_drift.publishers.update(released.publishers)
    released_with_current_workflow_drift.publisher_secret_override = (
        replace(
            publisher_secret_evidence(retired=True),
            dedicated_environment_configuration_complete=False,
            dedicated_environment_restricts_protected_release_branch=False,
        )
    )
    activation_integration = released_with_current_workflow_drift.prs[
        ACTIVATION
    ].merge_commit_oid
    target_oid = released_with_current_workflow_drift.prs[
        SIGNOFF_RECORD
    ].merge_commit_oid
    assert isinstance(activation_integration, str) and isinstance(target_oid, str)
    released_workflow = released_with_current_workflow_drift.resolve_current_workflow(
        activation_integration,
        target_oid,
        (".github/workflows/tenkz-release-policy.yml",),
        ".github/workflows",
    )
    released_with_current_workflow_drift.workflow_override = replace(
        released_workflow,
        target_publisher_workflow_tree_matches_activation=False,
    )
    assert validate(complete_log(), released_with_current_workflow_drift) == "released"

    reintroduced_after_release = context()
    reintroduced_after_release.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    reintroduced_after_release.publishers.update(released.publishers)
    reintroduced_after_release.publisher_secret_override = publisher_secret_evidence()
    reintroduced_after_release.workflow_override = replace(
        released_workflow,
        target_publisher_workflow_tree_matches_activation=False,
    )
    expect_failure(
        lambda: validate(complete_log(), reintroduced_after_release),
        "publisher signing-key name was reintroduced after retirement",
    )

    manual_final = context()
    manual_final.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    assert validate(complete_log(), manual_final) == (
        "signed-off-awaiting-publisher-success"
    )

    failed_publisher = context()
    failed_publisher.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="failure",
    )
    assert validate(complete_log(), failed_publisher) == "signed-off-awaiting-tag"

    failed_after_write = context()
    failed_after_write.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    failed_after_write.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="failure",
    )
    assert validate(complete_log(), failed_after_write) == (
        "signed-off-awaiting-publisher-success"
    )

    incomplete_after_write = context()
    incomplete_after_write.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    incomplete_after_write.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="incomplete",
    )
    assert validate(complete_log(), incomplete_after_write) == (
        "signed-off-awaiting-publisher-success"
    )

    key_retirement_pending = context()
    key_retirement_pending.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    key_retirement_pending.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    assert validate(complete_log(), key_retirement_pending) == (
        "signed-off-awaiting-key-retirement"
    )

    lost_published_ref = context()
    lost_published_ref.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    expect_failure(
        lambda: validate(complete_log(), lost_published_ref),
        "publisher succeeded but the final ref is absent",
    )

    # A later record-invalid reset supersedes the live sign-off state, but it
    # cannot erase the publisher's authenticated success history.  Delayed
    # success with no final ref remains a hard release incident after reset.
    post_signoff_reset = context()
    add_record(
        post_signoff_reset,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
        invalid_tree=True,
    )
    add_record(
        post_signoff_reset,
        "S1-0006",
        "#909",
        909,
        SIGNOFF_MERGE + timedelta(seconds=3),
    )
    post_signoff_reset_log = complete_log() + [
        correction("S1-0005", "#908", "S1-0002"),
        reset("S1-0006", "#909", "record-invalid", "S1-0005"),
    ]
    assert validate(post_signoff_reset_log, post_signoff_reset) == "reset"
    post_signoff_reset.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="failure",
    )
    assert validate(post_signoff_reset_log, post_signoff_reset) == "reset"
    post_signoff_reset.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    expect_failure(
        lambda: validate(post_signoff_reset_log, post_signoff_reset),
        "publisher succeeded but the final ref is absent",
    )

    published_then_drifted = context()
    published_then_drifted.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    expect_failure(
        lambda: validate(
            complete_log(),
            published_then_drifted,
            audit=audit_evidence("S1-0004", ("S1-0002",)),
        ),
        "publisher succeeded while release evidence requires reset",
    )

    independently_authenticated_object = context()
    independently_authenticated_object.tags[policy.FINAL_TAG] = authenticated_final_tag(
        oid(9071),
        object_oid="d" * 40,
    )
    independently_authenticated_object.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    independently_authenticated_object.publisher_secret_override = (
        publisher_secret_evidence(retired=True)
    )
    assert validate(complete_log(), independently_authenticated_object) == "released"

    publisher_contract_failures = (
        (
            "workflow_runs_complete_and_paginated",
            False,
            "run pagination is incomplete",
        ),
        (
            "workflow_jobs_complete_and_paginated",
            False,
            "job pagination is incomplete",
        ),
        (
            "release_validation_runs_complete_and_paginated",
            False,
            "release-validation run pagination is incomplete",
        ),
        (
            "prior_released_validation_exact_and_successful",
            None,
            "prior released-validation history is unavailable",
        ),
        (
            "pinned_workflow_runs_exact",
            False,
            "not bound to the pinned exact workflow",
        ),
        (
            "postmerge_validation_succeeded",
            False,
            "lacks successful exact post-merge validation",
        ),
        (
            "postmerge_validation_network_disabled",
            False,
            "validation was not network-disabled",
        ),
        (
            "publisher_needs_exact_postmerge_validation",
            False,
            "does not depend on the exact validation job",
        ),
        (
            "validation_jobs_lack_contents_write",
            False,
            "validation job has contents write permission",
        ),
        (
            "publisher_has_only_contents_write",
            False,
            "missing or excess permissions",
        ),
        (
            "publisher_has_no_checkout_or_repository_execution",
            False,
            "checks out or executes repository content",
        ),
        (
            "publisher_has_no_uses_or_inherited_secrets",
            False,
            "uses an action, called workflow, or inherited secret",
        ),
        (
            "publisher_uses_only_version_fingerprinted_hosted_gh_git_ssh_keygen",
            False,
            "unpinned or unapproved executable",
        ),
        (
            "publisher_command_and_inputs_closed",
            False,
            "command or inputs are not closed",
        ),
        (
            "publisher_uses_only_github_control_plane",
            False,
            "uses a non-GitHub network service",
        ),
        ("other_networked_steps_absent", False, "another networked step"),
        (
            "closed_needs_tuple_complete_and_matching",
            False,
            "closed needs tuple is incomplete or mismatched",
        ),
        (
            "closed_needs_has_no_caller_substitute",
            False,
            "accepts a caller substitute",
        ),
        (
            "github_metadata_matches_closed_needs",
            False,
            "GitHub metadata differs",
        ),
        (
            "caller_controlled_inputs_absent",
            False,
            "caller-controlled input",
        ),
        (
            "exact_git_objects_fetched_by_oid_and_verified",
            False,
            "exact Git objects by OID",
        ),
        (
            "publisher_environment_and_secret_exact",
            False,
            "another environment or secret",
        ),
        (
            "publisher_is_only_private_key_consumer",
            False,
            "another job can consume",
        ),
        (
            "deterministic_signed_tag_object_contract",
            False,
            "deterministic signed object",
        ),
        (
            "signature_algorithm_and_namespace_exact",
            False,
            "another signature algorithm or namespace",
        ),
        (
            "tagger_epoch_exact_canonical_and_in_range",
            False,
            "tagger epoch is not canonical or in range",
        ),
        (
            "publisher_reads_ref_before_private_key_access",
            False,
            "accesses the private key before reading the ref",
        ),
        (
            "private_key_available_only_to_absent_ref_path",
            False,
            "private key is available outside absent-ref construction",
        ),
        (
            "existing_ref_path_cannot_access_private_key",
            False,
            "existing-ref retry can access the private key",
        ),
        (
            "absent_ref_candidate_authenticated_before_write",
            False,
            "does not authenticate the candidate object before its first write",
        ),
        (
            "existing_ref_object_authenticated_without_mutation",
            False,
            "does not authenticate an existing exact object without mutation",
        ),
        (
            "publisher_success_requires_authenticated_final_readback",
            False,
            "can succeed without an authenticated final readback",
        ),
        (
            "publisher_emits_no_durable_output_receipt",
            False,
            "relies on a durable job-output receipt",
        ),
        (
            "publisher_started_after_validation_success",
            False,
            "did not start after validation success",
        ),
        (
            "successful_job_head_matches_integration",
            False,
            "used another head",
        ),
        (
            "successful_job_historical_workflow_tree_matches_activation",
            False,
            "used another historical workflow tree",
        ),
        (
            "successful_job_follows_successful_postmerge_validation",
            False,
            "did not follow its successful validation job",
        ),
        (
            "successful_job_conclusion_api_visible",
            False,
            "conclusion is not API-visible",
        ),
    )
    for field_name, bad_value, error_fragment in publisher_contract_failures:
        bad_publisher = context()
        bad_publisher.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
        bad_publisher.publishers[oid(9071)] = replace(
            publisher_evidence(oid(9071), status="success"),
            **{field_name: bad_value},
        )
        expect_failure(
            lambda facts=bad_publisher: validate(complete_log(), facts),
            error_fragment,
        )

    wrong_publisher_integration = context()
    wrong_publisher_integration.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    wrong_publisher_integration.publishers[oid(9071)] = replace(
        publisher_evidence(oid(9071), status="success"),
        validated_integration_oid=oid(9991),
    )
    expect_failure(
        lambda: validate(complete_log(), wrong_publisher_integration),
        "used another sign-off integration",
    )

    publisher_binding_failures = (
        (
            "validated_tagger_epoch_seconds",
            SIGNOFF_TAGGER_EPOCH + 1,
            "another tagger epoch",
        ),
        ("validated_policy_sha256", "0" * 64, "another policy hash"),
        ("validated_prefix_sha256", "invalid", "invalid ledger-prefix hash"),
        ("validated_prefix_boundary", "S1-9999", "another ledger-prefix boundary"),
        ("validated_support_tree_oid", oid(9992), "another support tree"),
        ("validated_schema_blob_oid", None, "invalid object-schema blob OID"),
        ("validated_public_key_blob_oid", None, "invalid public-key blob OID"),
    )
    for field_name, bad_value, error_fragment in publisher_binding_failures:
        bad_publisher = context()
        bad_publisher.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
        bad_publisher.publishers[oid(9071)] = replace(
            publisher_evidence(oid(9071), status="success"),
            **{field_name: bad_value},
        )
        expect_failure(
            lambda facts=bad_publisher: validate(complete_log(), facts),
            error_fragment,
        )

    premature_successful_job_evidence = context()
    premature_successful_job_evidence.publishers[oid(9071)] = replace(
        publisher_evidence(oid(9071)),
        successful_job_conclusion_api_visible=True,
    )
    expect_failure(
        lambda: validate(complete_log(), premature_successful_job_evidence),
        "publisher that did not run carries successful-job evidence",
    )

    failed_with_successful_job_evidence = context()
    failed_with_successful_job_evidence.publishers[oid(9071)] = replace(
        publisher_evidence(oid(9071), status="failure"),
        successful_job_head_matches_integration=True,
    )
    expect_failure(
        lambda: validate(complete_log(), failed_with_successful_job_evidence),
        "unsuccessful publisher history carries successful-job evidence",
    )

    failed_with_prior_release = context()
    failed_with_prior_release.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="failure",
        prior_released=True,
    )
    expect_failure(
        lambda: validate(complete_log(), failed_with_prior_release),
        "prior released validation lacks a successful publisher job",
    )

    nonreleased_with_prior_binding = context()
    nonreleased_with_prior_binding.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        prior_released_target_oid=oid(9071),
    )
    expect_failure(
        lambda: validate(complete_log(), nonreleased_with_prior_binding),
        "non-released history carries a released-validation binding",
    )

    trailing_correction = context()
    add_record(
        trailing_correction,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
    )
    trailing_correction.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    trailing_correction.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    trailing_correction.publisher_secret_override = publisher_secret_evidence(retired=True)
    trailing_correction_log = complete_log() + [
        correction("S1-0005", "#908", "S1-0002")
    ]
    assert validate(trailing_correction_log, trailing_correction) == "released"

    trailing_correction_replay = context()
    add_record(
        trailing_correction_replay,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
    )
    trailing_correction_replay.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    trailing_correction_replay.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
        prior_released=True,
        prior_released_prefix_boundary="S1-0005",
        prior_released_target_oid=oid(9081),
    )
    trailing_correction_replay.publisher_secret_override = publisher_secret_evidence(
        retired=True
    )
    assert validate(trailing_correction_log, trailing_correction_replay) == "released"

    appended_after_release = context()
    add_record(
        appended_after_release,
        "S1-0005",
        "#908",
        908,
        SIGNOFF_MERGE + timedelta(seconds=1),
    )
    appended_after_release.tags[policy.FINAL_TAG] = released.tags[policy.FINAL_TAG]
    appended_after_release.publishers.update(released.publishers)
    appended_after_release.publisher_secret_override = publisher_secret_evidence(
        retired=True
    )
    expect_failure(
        lambda: validate(trailing_correction_log, appended_after_release),
        "prior released validation used another ledger prefix",
    )

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
    lightweight_final.tags[policy.FINAL_TAG] = replace(
        authenticated_final_tag(oid(9071)),
        object_type="commit",
    )
    lightweight_final.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
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
    wrong_final_target.tags[policy.FINAL_TAG] = replace(
        authenticated_final_tag(oid(9071)),
        commit=oid(9991),
    )
    wrong_final_target.publishers[oid(9071)] = publisher_evidence(
        oid(9071),
        status="success",
    )
    expect_failure(
        lambda: validate(complete_log(), wrong_final_target),
        "does not peel to the validated sign-off integration",
    )

    final_tag_authentication_failures = (
        (
            "final_lookup_after_fetch_object_id",
            "d" * 40,
            "changed across exact-object fetch and double resolution",
        ),
        (
            "final_network_disabled_before_object_read",
            False,
            "read before network removal",
        ),
        ("final_raw_object_bytes_complete", False, "raw object bytes are incomplete"),
        ("final_object_schema_valid", False, "pinned byte schema"),
        ("final_recomputed_object_id", "d" * 40, "raw object hash"),
        ("final_signature_algorithm", "rsa", "another signature algorithm"),
        ("final_signature_namespace", "file", "another namespace"),
        ("final_raw_signature_valid", False, "raw signature is invalid"),
        ("final_public_key_blob_oid", "d" * 40, "another public key"),
        (
            "final_public_key_from_pinned_support_tree",
            False,
            "another public key",
        ),
        ("final_schema_blob_oid", "d" * 40, "another object schema"),
        (
            "final_schema_from_pinned_support_tree",
            False,
            "another object schema",
        ),
        (
            "final_tagger_identity_matches_schema",
            False,
            "tagger identity differs",
        ),
        (
            "final_tagger_epoch_seconds",
            SIGNOFF_TAGGER_EPOCH + 1,
            "tagger epoch differs",
        ),
        ("final_tagger_timezone", "+0100", "timezone is not +0000"),
        ("final_message_tag", "tenkz-v1.0.1", "payload names another tag"),
        (
            "final_message_integration_oid",
            oid(9991),
            "payload names another sign-off integration",
        ),
        (
            "final_message_policy_sha256",
            "0" * 64,
            "payload names another policy hash",
        ),
        (
            "final_message_prefix_sha256",
            "0" * 64,
            "payload names another ledger-prefix hash",
        ),
        (
            "final_message_prefix_boundary",
            "S1-0003",
            "payload names another ledger-prefix boundary",
        ),
        (
            "final_commit_reachable_from_main",
            False,
            "not reachable from current main",
        ),
    )
    for field_name, bad_value, error_fragment in final_tag_authentication_failures:
        bad_tag = context()
        bad_tag.tags[policy.FINAL_TAG] = replace(
            authenticated_final_tag(oid(9071)),
            **{field_name: bad_value},
        )
        bad_tag.publishers[oid(9071)] = publisher_evidence(
            oid(9071),
            status="success",
        )
        expect_failure(
            lambda facts=bad_tag: validate(complete_log(), facts),
            error_fragment,
        )

    premature_final = context()
    premature_final.tags[policy.FINAL_TAG] = authenticated_final_tag(oid(9071))
    expect_failure(
        lambda: validate(complete_log()[:3], premature_final),
        "without a successfully validated sign-off",
    )

    inconsistent_absent = context()
    inconsistent_absent.tags[policy.FINAL_TAG] = replace(
        inconsistent_absent.tags[policy.FINAL_TAG],
        object_id=FINAL_TAG_OBJECT,
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
        subjects_cannot_supply_evidence_logic=False,
    )
    expect_failure(
        lambda: validate([freeze()], activation_subject_controls_coverage),
        "activation subjects can supply evidence or coverage logic",
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
    activation_publisher_failures = (
        (
            "publisher_workflow_tree_pinned",
            "activation publisher workflow tree is not pinned",
        ),
        (
            "publisher_workflow_jobs_complete_and_paginated",
            "activation publisher workflow job enumeration is incomplete",
        ),
        (
            "publisher_is_sole_environment_consumer",
            "another activation workflow job names the publisher environment",
        ),
        (
            "publisher_is_sole_secret_consumer",
            "another activation workflow job names the publisher secret",
        ),
        (
            "workflow_secret_inheritance_absent",
            "activation publisher workflow permits inherited secrets",
        ),
        (
            "publisher_environment_configuration_complete",
            "activation publisher environment configuration is incomplete",
        ),
        (
            "publisher_environment_restricts_protected_release_branch",
            "does not restrict the protected release branch",
        ),
        (
            "repository_environments_complete_and_paginated",
            "activation repository environment pagination is incomplete",
        ),
        (
            "all_environment_secret_names_complete_and_paginated",
            "activation environment secret-name pagination is incomplete",
        ),
        (
            "repository_secret_names_complete_and_paginated",
            "activation repository secret-name pagination is incomplete",
        ),
        (
            "organization_secret_names_and_access_complete_and_paginated",
            "activation organization secret-name or access pagination is incomplete",
        ),
        (
            "configured_secret_only_in_dedicated_environment",
            "activation publisher secret is missing, shadowed, or outside its environment",
        ),
    )
    for field_name, error_fragment in activation_publisher_failures:
        bad_activation = context()
        bad_activation.activation_diff = replace(
            bad_activation.activation_diff,
            **{field_name: False},
        )
        expect_failure(
            lambda facts=bad_activation: validate([freeze()], facts),
            error_fragment,
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
        inventory_exact_schema_valid=False,
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
        inventory_subject_paths_within_subject_roots=False,
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
        executable_dependencies_within_harness_tree=False,
    )
    assert (
        validate(complete_log(), executable_from_subject)
        == "reset-required:S1-0004"
    )

    subject_reduces_coverage = context()
    subject_reduces_coverage.payloads[(oid(9200), policy.FINAL_TAG)] = replace(
        subject_reduces_coverage.payloads[(oid(9200), policy.FINAL_TAG)],
        subjects_cannot_supply_evidence_logic=False,
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

    release_binding_call = context()
    observed_release_integrations: list[str] = []

    def resolve_bound_release_prep(
        ref: str,
        integration_oid: str,
        _paths: tuple[str, ...],
        _work_integrations: tuple[str, ...],
        _resolution_integrations: tuple[str, ...],
    ) -> policy.ReleasePrepEvidence:
        observed_release_integrations.append(integration_oid)
        return release_binding_call.release_preps[ref]

    assert validate(
        complete_log(),
        release_binding_call,
        resolve_replay_release_prep=resolve_bound_release_prep,
    ) == "signed-off-awaiting-tag"
    assert observed_release_integrations == [oid(9201)]

    for invalid_integration in (None, oid(9991)):
        release_other_integration = context()
        release_other_integration.release_preps[RELEASE_PREP] = replace(
            release_other_integration.release_preps[RELEASE_PREP],
            validated_integration_oid=invalid_integration,
        )
        assert validate(complete_log(), release_other_integration) == (
            "reset-required:S1-0004"
        )

    release_other_integration_candidate = context()
    signoff = release_other_integration_candidate.prs[SIGNOFF_RECORD]
    assert signoff.head_oid is not None
    release_other_integration_candidate.prs[SIGNOFF_RECORD] = candidate_pr(
        907,
        author="release-author",
        reviews=(review("release-reviewer", SIGNOFF_REVIEW, signoff.head_oid),),
    )
    release_other_integration_candidate.release_preps[RELEASE_PREP] = replace(
        release_other_integration_candidate.release_preps[RELEASE_PREP],
        validated_integration_oid=oid(9991),
    )
    expect_failure(
        lambda: validate(complete_log(), release_other_integration_candidate),
        "release preparation used another integration",
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

    for noncanonical_merge_time in (
        SIGNOFF_MERGE + timedelta(microseconds=1),
        SIGNOFF_MERGE.astimezone(timezone(timedelta(hours=1))),
    ):
        noncanonical_tagger_epoch = context()
        noncanonical_tagger_epoch.prs[SIGNOFF_RECORD] = replace(
            noncanonical_tagger_epoch.prs[SIGNOFF_RECORD],
            merged_at=noncanonical_merge_time,
        )
        assert validate(complete_log(), noncanonical_tagger_epoch) == (
            "reset-required:S1-0004"
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
        friction("S1-0002", "#908", "restart-required"),
        correction("S1-0003", "#909", "S1-0002"),
        reset("S1-0004", "#910", "restart-required", "S1-0002"),
    ]
    assert validate(reset_log, reset_facts) == "reset"

    invalid_correction_behind_restart = context()
    for entry_id, record_ref, number, merged_at, invalid_tree in (
        ("S1-0002", "#908", 908, FREEZE_TIME + timedelta(seconds=3), False),
        ("S1-0003", "#909", 909, FREEZE_TIME + timedelta(seconds=4), True),
        ("S1-0004", "#910", 910, FREEZE_TIME + timedelta(seconds=5), False),
        ("S1-0005", "#911", 911, FREEZE_TIME + timedelta(seconds=6), False),
    ):
        add_record(
            invalid_correction_behind_restart,
            entry_id,
            record_ref,
            number,
            merged_at,
            invalid_tree=invalid_tree,
        )
    restart_then_invalid_correction = [
        freeze(),
        friction("S1-0002", "#908", "restart-required"),
        correction("S1-0003", "#909", "S1-0002"),
        reset("S1-0004", "#910", "restart-required", "S1-0002"),
        reset("S1-0005", "#911", "record-invalid", "S1-0003"),
    ]
    assert validate(
        restart_then_invalid_correction[:3],
        invalid_correction_behind_restart,
    ) == "reset-required:S1-0002"
    assert validate(
        restart_then_invalid_correction[:4],
        invalid_correction_behind_restart,
    ) == "reset-required:S1-0003"
    assert validate(
        restart_then_invalid_correction,
        invalid_correction_behind_restart,
    ) == "reset"

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

    # An already-pending restart-required reset has priority at the drift
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
    restart_then_drift = [
        freeze(),
        friction("S1-0002", "#908", "restart-required"),
        reset("S1-0003", "#909", "restart-required", "S1-0002"),
        reset("S1-0004", "#910", "record-invalid", "S1-0001"),
    ]
    assert (
        validate(
            restart_then_drift[:3],
            ordered_resets,
            audit=audit_evidence(
                "S1-0003",
                ("S1-0001",),
                target_oid=ordered_resets.prs["#909"].merge_commit_oid,
            ),
        )
        == "reset-required:S1-0001"
    )
    assert validate(restart_then_drift, ordered_resets) == "reset"

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
                friction("S1-0002", "#908", "restart-required"),
                reset("S1-0003", "#909", "restart-required", "S1-0002"),
                reset("S1-0004", "#910", "restart-required", "S1-0002"),
                reset("S1-0005", "#911", "record-invalid", "S1-0003"),
            ],
            "S1-0003",
            "S1-0005",
            "#911",
        )
    )

    signoff_common = context()
    signoff_common.payloads[(oid(9071), policy.FINAL_TAG)] = replace(
        signoff_common.payloads[(oid(9071), policy.FINAL_TAG)],
        test_execution_complete=False,
    )
    signoff_common.publishers[oid(9071)] = replace(
        publisher_evidence(oid(9071)),
        postmerge_validation_succeeded=False,
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
        historical_candidate_check_exact_and_successful=True,
        historical_current_namespace_complete=True,
        historical_current_matching_tag_names=("tenkz-v0.9.0",),
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
        candidate_namespace_complete=True,
        candidate_matching_tag_names=("tenkz-v0.9.0",),
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
        candidate_matching_tag_names=("tenkz-v0.9.0", "tenkz-v0.9.1"),
    )
    expect_failure(
        lambda: validate([freeze()], stale_patch),
        "retained snapshot differs from the candidate namespace",
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
        friction("S1-0002", "#908", "restart-required"),
        reset("S1-0003", "#909", "restart-required", "S1-0002"),
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
