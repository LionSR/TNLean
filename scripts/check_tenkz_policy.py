#!/usr/bin/env python3
"""Pure validation for the tenkz compatibility policy and 1.0 evidence log.

Repository and GitHub access are deliberately injected.  This module owns the
closed grammar, immutable-evidence contracts, and attempt state machine; a
stacked integration layer resolves the external facts.
"""

from __future__ import annotations

import re
import tomllib
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Callable, Collection


SOAK_MARKER = "<!-- tenkz-soak-entries: append below only while enforcement=armed -->"
FREEZE_TAG_RE = re.compile(r"tenkz-v0\.9\.(?:0|[1-9][0-9]*)")
FINAL_TAG = "tenkz-v1.0.0"
SHA_RE = re.compile(r"[0-9a-f]{40}")
ENTRY_ID_RE = re.compile(r"S1-[0-9]{4}")
PR_REF_RE = re.compile(r"#[1-9][0-9]*")
ISSUE_REF_RE = PR_REF_RE
IDENTITY_RE = re.compile(r"github:[a-z0-9](?:[a-z0-9-]{0,37}[a-z0-9])?")
LOGIN_RE = re.compile(r"[a-z0-9](?:[a-z0-9-]{0,37}[a-z0-9])?")

ENTRY_KINDS = {
    "freeze",
    "work",
    "friction",
    "resolution",
    "reset",
    "correction",
    "sign-off",
}
WORK_CLASSES = ("formalization-or-blueprint", "rmp-benchmark")
TRIAGE = {"fix-compatible", "defer-to-2.0", "breaking-required"}
SURFACES = {"tex-api", "tnlog"}
RESET_CAUSES = {"breaking-required", "record-invalid"}

EXPECTED_POLICY = {
    "policy": {
        "schema": 1,
        "enforcement": "pending",
        "enforcement_transition": "pending-to-armed",
        "tag_namespace": "tenkz-v*",
        "repository_tag_namespace": "v*",
        "freeze_tag_pattern": "tenkz-v0.9.PATCH",
        "freeze_tag_kind": "annotated",
        "required_distinct_work_prs": 2,
        "work_classes": list(WORK_CLASSES),
        "one_class_per_work_pr": True,
        "work_excluded_paths": ["TNLean/Archive/**"],
        "event_format_owners": ["#4162", "#4703"],
        "soak_blocker_chain": [
            ["#5086", "#4699", "#4162"],
            ["#4703", "#4708", "#4163"],
        ],
        "deprecation_removal": "not-before-next-major",
        "tombstone_reuse": False,
        "frozen_twin_scope": "library-entry-point-in-same-package",
        "frozen_twin_lifetime": "permanent",
        "frozen_twin_precedent": "quantikz/quantikz2",
        "maintainer_identity": "github:lionsr",
        "signer_identity_scheme": "github:lowercase-login",
        "tag_immutability": "github-ruleset-no-update-delete-or-bypass",
        "release_manifest_pattern": "docs/tenkz/releases/TAG.toml",
        "release_package_metadata": "tex/tenkz/tenkz.sty",
        "release_manual": "docs/tenkz/manual2.tex",
        "release_change_record": "docs/tenkz/CHANGES.md",
        "release_event_format": "docs/tenkz/TNLOG.md",
        "release_test_inventory": "tests/tenkz/release-tests.toml",
        "release_test_inventory_sha256": "pending",
        "release_test_code_root": "scripts",
        "release_test_code_tree": "pending",
        "release_test_support_root": "tests/tenkz/release-support",
        "release_test_support_tree": "pending",
        "release_test_data_roots": ["tex/tenkz", "docs/tenkz", "tests/tenkz/rmp"],
        "release_test_dependency_contract": "pinned-code-support-declared-subject-data",
        "release_test_protocol": "hermetic-repository-view-no-shell-or-network",
    },
    "event_format": {
        "reader_accepts": "same-major-any-minor",
        "unknown_optional_fields": "ignore",
        "unknown_event_kinds": "explicitly-ignorable-only",
        "non_ignorable_change": "major",
    },
    "compatibility": {
        "patch": {"tex_api": "backward-compatible-fix", "tnlog": "byte-stable"},
        "minor": {
            "tex_api": "backward-compatible-addition",
            "tnlog": "additive-versioned",
        },
        "major": {"tex_api": "breaking-change", "tnlog": "breaking-versioned"},
    },
}

EXPECTED_SOAK = {
    "soak": {
        "schema": 1,
        "policy": "docs/tenkz/DESIGN.md",
        "enforcement": "pending",
        "enforcement_transition": "pending-to-armed",
        "policy_sha256": "pending",
        "armed_by_pr": "pending",
        "append_only": True,
        "append_only_from": "armed",
        "ordering_anchor": "freeze-record-pr-merged-at",
        "ancestry_anchor": "freeze-record-pr-merge-commit",
        "work_anchor": "work-pr-merged-at",
        "freeze_tag_pattern": "tenkz-v0.9.PATCH",
        "freeze_tag_kind": "annotated",
        "release_tag": "tenkz-v1.0.0",
    }
}

COMMON_FIELDS = {"id", "kind", "record_pr", "attempt"}
FIELDS_BY_KIND = {
    "freeze": COMMON_FIELDS
    | {
        "source_pr",
        "source_sha",
        "freeze_tag_object",
        "freeze_tag",
        "prerequisites",
        "evidence",
    },
    "work": COMMON_FIELDS | {"work_pr", "class", "summary", "evidence"},
    "friction": COMMON_FIELDS | {"surface", "triage", "summary", "evidence"},
    "resolution": COMMON_FIELDS | {"friction", "summary", "evidence"},
    "reset": COMMON_FIELDS | {"cause", "target", "reason", "evidence"},
    "correction": COMMON_FIELDS | {"target", "summary", "evidence"},
    "sign-off": COMMON_FIELDS
    | {
        "freeze",
        "source_sha",
        "release_prep_pr",
        "release_tag",
        "reviewer",
        "work_evidence",
        "decision",
    },
}


class PolicyError(ValueError):
    """A compatibility policy or evidence record is invalid."""


@dataclass(frozen=True)
class ReviewEvidence:
    """One review from complete changed-review history."""

    login: str | None
    state: str | None
    submitted_at: datetime | None
    commit_oid: str | None
    dismissed: bool | None = False


@dataclass(frozen=True)
class PullRequestEvidence:
    """GitHub facts plus Git checks for one PR relative to the requested anchor."""

    in_repository: bool | None
    base_ref_name: str | None
    author_login: str | None
    head_oid: str | None
    merged: bool | None
    merged_at: datetime | None = None
    merged_by_login: str | None = None
    merge_commit_oid: str | None = None
    reviews: tuple[ReviewEvidence, ...] | None = None
    reviews_complete: bool | None = None
    integration_reachable_from_main: bool | None = None
    integration_tree_matches_head: bool | None = None
    integration_strict_descendant_of_anchor: bool | None = None


@dataclass(frozen=True)
class RecordDiffEvidence:
    """Immutable ledger and release-payload facts for an entry record PR."""

    validated_pr_ref: str | None
    validated_head_oid: str | None
    complete: bool | None
    unique_merge_base: bool | None
    integration_parent_count: int | None
    base_lacks_entry: bool | None
    appends_exact_entry: bool | None
    pinned_prefix_unchanged: bool | None
    other_entries_unchanged: bool | None
    no_other_path_changes: bool | None
    candidate_main_is_ancestor_of_head: bool | None
    integration_parent_is_ancestor_of_head: bool | None
    integration_second_parent_matches_head: bool | None
    source_to_head_is_exact_freeze_append: bool | None = None
    candidate_main_tip_is_source: bool | None = None
    integration_parent_is_source: bool | None = None
    candidate_main_tip_is_release_integration: bool | None = None
    integration_parent_is_release_integration: bool | None = None
    validated_release_integration: str | None = None
    validated_work_integrations: tuple[str, ...] | None = None


@dataclass(frozen=True)
class WorkDiffEvidence:
    """Facts derived from the complete immutable merge-base-to-head work diff."""

    complete: bool | None
    integration_parent_count: int | None
    unique_merge_base: bool | None
    integration_parent_is_ancestor_of_head: bool | None
    integration_second_parent_matches_head: bool | None
    policy_paths_untouched: bool | None
    excluded_paths_applied: bool | None
    semantic_add_or_modify_classes: tuple[str, ...] | None
    semantic_lean_changed: bool | None
    semantic_blueprint_changed: bool | None
    semantic_rmp_changed: bool | None
    lean_modules_build: bool | None
    proof_integrity_clean: bool | None
    blueprint_checkdecls_passed: bool | None
    blueprint_build_passed: bool | None
    rmp_targets_resolved: bool | None
    rmp_stages_complete: bool | None
    rmp_checks_passed: bool | None


@dataclass(frozen=True)
class ReleaseContract:
    """Policy-owned paths, inventory digest, and execution protocol."""

    manifest_pattern: str
    package_metadata: str
    manual: str
    change_record: str
    event_format: str
    test_inventory: str
    test_inventory_sha256: str
    test_code_root: str
    test_code_tree: str
    test_support_root: str
    test_support_tree: str
    test_data_roots: tuple[str, ...]
    test_dependency_contract: str
    test_protocol: str

    def manifest_path(self, tag: str) -> str:
        return self.manifest_pattern.replace("TAG", tag)

    def release_varying_paths(self, tag: str) -> tuple[str, ...]:
        return (
            self.manifest_path(tag),
            self.package_metadata,
            self.manual,
            self.change_record,
            self.event_format,
        )


@dataclass(frozen=True)
class ReleasePayloadEvidence:
    """Complete policy-owned payload and deterministic test facts for one tree."""

    validated_tree_oid: str | None
    validated_tag: str | None
    validated_contract: ReleaseContract | None
    complete: bool | None
    manifest_path: str | None
    regular_distinct_paths: bool | None
    manifest_contract_valid: bool | None
    artifact_declarations_agree: bool | None
    inventory_digest_matches: bool | None
    inventory_contract_valid: bool | None
    test_code_tree_matches: bool | None
    test_support_tree_matches: bool | None
    inventory_data_paths_within_mutable_roots: bool | None
    executable_dependencies_within_code_tree: bool | None
    acceptance_dependencies_within_support_tree: bool | None
    subject_data_cannot_reduce_coverage: bool | None
    hermetic_execution_contract_valid: bool | None
    payload_execution_receipts_complete_and_matching: bool | None
    test_execution_complete: bool | None
    compatibility_tests_passed: bool | None
    payload_blob_oids: tuple[str, ...] | None


@dataclass(frozen=True)
class ReleasePrepEvidence:
    """Exact-head, complete-diff, manifest, and payload facts for release prep."""

    validated_pr_ref: str | None
    validated_head_oid: str | None
    validated_manifest_path: str | None
    validated_changed_paths: tuple[str, ...] | None
    validated_work_integrations: tuple[str, ...] | None
    complete: bool | None
    integration_parent_count: int | None
    unique_merge_base: bool | None
    integration_parent_is_ancestor_of_head: bool | None
    integration_second_parent_matches_head: bool | None
    integration_descends_from_work_integrations: bool | None
    exact_release_varying_path_diff: bool | None


@dataclass(frozen=True)
class TagEvidence:
    object_id: str | None
    object_type: str | None
    commit: str | None
    patch_is_fresh_for_attempt: bool | None = None
    exists: bool | None = True
    validated_entry_id: str | None = None
    validated_record_pr: str | None = None
    commit_is_validated_record_integration: bool | None = None


@dataclass(frozen=True)
class AuditEvidence:
    """Complete current-validity result and its immutable-ledger boundary.

    Replay callbacks reconstruct integration-time history (or the exact final
    unmerged candidate).  This separate channel records every entry that fails
    the current snapshot, so later drift is queued only after the fixed audit
    boundary and cannot block intervening history.
    """

    boundary_entry_id: str | None
    invalid_entries: tuple[str, ...] | None
    snapshot_complete: bool | None
    validation_target_exact: bool | None


@dataclass(frozen=True)
class ActivationDiffEvidence:
    """Exact candidate diff and pinned-value checks for the arming PR."""

    validated_pr_ref: str | None
    validated_head_oid: str | None
    complete: bool | None
    candidate_main_is_ancestor_of_head: bool | None
    unique_merge_base: bool | None
    exact_seven_scalar_replacements: bool | None
    inventory_digest_matches: bool | None
    test_code_tree_matches: bool | None
    test_support_tree_matches: bool | None
    inventory_data_paths_within_mutable_roots: bool | None
    executable_dependencies_within_code_tree: bool | None
    acceptance_dependencies_within_support_tree: bool | None
    subject_data_cannot_reduce_coverage: bool | None
    hermetic_execution_contract_valid: bool | None
    supervisor_self_test_receipt_valid: bool | None
    policy_digest_matches: bool | None
    ledger_prefix_matches: bool | None


@dataclass(frozen=True)
class TagProtectionEvidence:
    """Complete current repository and organization tag-ruleset state.

    Ruleset administrators and the GitHub control plane are the policy's
    trusted boundary; these fields describe only the observable current
    snapshot and make no historical-protection claim.
    """

    repository_rulesets_complete: bool | None
    organization_rulesets_complete: bool | None
    credential_has_write_visibility: bool | None
    details_unredacted: bool | None
    namespace_fully_covered: bool | None
    applicable_rulesets_active: bool | None
    updates_forbidden: bool | None
    deletions_forbidden: bool | None
    bypass_actors: tuple[str, ...] | None
    unambiguous: bool | None


@dataclass(frozen=True)
class IssueEvidence:
    in_repository: bool | None
    closed: bool | None
    closed_at: datetime | None


@dataclass(frozen=True)
class RecordInspection:
    """Common record state after candidate or post-merge provenance checks."""

    author: str
    pending: bool
    merged_at: datetime | None
    integration: str | None
    invalid_reasons: tuple[str, ...]


ResolveReplayPullRequest = Callable[[str, str | None], PullRequestEvidence]
ResolveReplayActivationDiff = Callable[[str], ActivationDiffEvidence]
ResolveReplayRecordDiff = Callable[[str, str, str | None], RecordDiffEvidence]
ResolveReplayWorkDiff = Callable[[str], WorkDiffEvidence]
ResolveReplayReleasePrep = Callable[
    [str, tuple[str, ...], tuple[str, ...]], ReleasePrepEvidence
]
ResolveReplayReleasePayload = Callable[[str, str, ReleaseContract], ReleasePayloadEvidence]
ResolveReplayFreezeTag = Callable[[str], TagEvidence]
ResolveCurrentFinalTag = Callable[[str], TagEvidence]
ResolveReplayIssue = Callable[[str], IssueEvidence]


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


def validate_policy_mapping(policy: dict) -> dict:
    """Validate the closed pending policy or its four-field armed form."""

    root = policy.get("policy")
    require(isinstance(root, dict), "tenkz-policy-v1 lacks [policy]")
    enforcement = root.get("enforcement")
    require(enforcement in {"pending", "armed"}, "policy enforcement state is invalid")
    normalized = {**policy, "policy": {**root}}
    if enforcement == "armed":
        inventory_digest = root.get("release_test_inventory_sha256")
        test_code_tree = root.get("release_test_code_tree")
        test_support_tree = root.get("release_test_support_tree")
        require(
            isinstance(inventory_digest, str)
            and re.fullmatch(r"[0-9a-f]{64}", inventory_digest) is not None,
            "armed policy inventory digest is invalid",
        )
        require(
            isinstance(test_code_tree, str) and SHA_RE.fullmatch(test_code_tree) is not None,
            "armed policy test-code tree is invalid",
        )
        require(
            isinstance(test_support_tree, str)
            and SHA_RE.fullmatch(test_support_tree) is not None,
            "armed policy test-support tree is invalid",
        )
        normalized["policy"]["enforcement"] = "pending"
        normalized["policy"]["release_test_inventory_sha256"] = "pending"
        normalized["policy"]["release_test_code_tree"] = "pending"
        normalized["policy"]["release_test_support_tree"] = "pending"
    require(normalized == EXPECTED_POLICY, "tenkz-policy-v1 differs from the signed policy")
    return policy


def validate_policy_text(text: str) -> dict:
    required_headings = {
        "## Compatibility ownership",
        "## Package versions",
        "## Deprecations, tombstones, and frozen twins",
        "## Release tags",
        "## The 1.0 freeze and evidence gate",
    }
    missing = sorted(heading for heading in required_headings if heading not in text)
    require(not missing, f"DESIGN.md lacks required section(s): {', '.join(missing)}")
    policy = parse_toml_block(text, "tenkz-policy-v1")
    return validate_policy_mapping(policy)


def parse_entry_block(block: str, index: int) -> dict:
    try:
        parsed = tomllib.loads(block)
    except tomllib.TOMLDecodeError as error:
        raise PolicyError(f"entry {index} contains invalid TOML: {error}") from error
    require(set(parsed) == {"entry"}, f"entry {index} must contain only [entry]")
    entry = parsed["entry"]
    require(isinstance(entry, dict), f"entry {index} [entry] must be a table")
    return entry


def validate_soak_mapping(soak: dict) -> dict:
    """Validate the closed pending schema or its three-field armed form."""

    root = soak.get("soak")
    require(isinstance(root, dict), "tenkz-soak-v1 lacks [soak]")
    enforcement = root.get("enforcement")
    require(enforcement in {"pending", "armed"}, "soak enforcement state is invalid")
    normalized = {**soak, "soak": {**root}}
    if enforcement == "armed":
        policy_digest = root.get("policy_sha256")
        armed_by_pr = root.get("armed_by_pr")
        require(
            isinstance(policy_digest, str)
            and re.fullmatch(r"[0-9a-f]{64}", policy_digest) is not None,
            "armed soak policy digest is invalid",
        )
        require(
            isinstance(armed_by_pr, str) and PR_REF_RE.fullmatch(armed_by_pr) is not None,
            "armed soak activation PR is invalid",
        )
        normalized["soak"]["enforcement"] = "pending"
        normalized["soak"]["policy_sha256"] = "pending"
        normalized["soak"]["armed_by_pr"] = "pending"
    require(normalized == EXPECTED_SOAK, "tenkz-soak-v1 differs from the signed schema")
    return soak


def parse_soak_text(text: str) -> tuple[dict, list[dict]]:
    soak = validate_soak_mapping(parse_toml_block(text, "tenkz-soak-v1"))
    require(text.count(SOAK_MARKER) == 1, "SOAK-1.0.md must contain one append marker")
    prefix, tail = text.split(SOAK_MARKER, 1)
    require(
        not fenced_blocks(prefix, "tenkz-soak-entry-v1"),
        "evidence entries must appear after the append marker",
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
            "only evidence entry blocks may follow the append marker",
        )
        entries.append(parse_entry_block(match.group(1), index))
        cursor = match.end()
    require(
        not tail[cursor:].strip(),
        "only evidence entry blocks may follow the append marker",
    )
    return soak, entries


def nonempty_string(value: object, field: str, entry_id: str) -> str:
    require(
        isinstance(value, str) and bool(value.strip()),
        f"{entry_id} field {field} must be a nonempty string",
    )
    return value


def closed_string_list(value: object, field: str, entry_id: str) -> list[str]:
    require(
        isinstance(value, list)
        and all(isinstance(item, str) and item.strip() for item in value),
        f"{entry_id} field {field} must be a list of nonempty strings",
    )
    require(len(value) == len(set(value)), f"{entry_id} field {field} has duplicates")
    return value


def sha(value: object, field: str, entry_id: str) -> str:
    result = nonempty_string(value, field, entry_id)
    require(SHA_RE.fullmatch(result) is not None, f"{entry_id} has invalid {field}")
    return result


def pr_ref(value: object, field: str, entry_id: str) -> str:
    result = nonempty_string(value, field, entry_id)
    require(PR_REF_RE.fullmatch(result) is not None, f"{entry_id} has invalid {field}")
    return result


def issue_ref(value: object, field: str, entry_id: str) -> str:
    result = nonempty_string(value, field, entry_id)
    require(ISSUE_REF_RE.fullmatch(result) is not None, f"{entry_id} has invalid {field}")
    return result


def identity(value: object, field: str, entry_id: str) -> str:
    result = nonempty_string(value, field, entry_id)
    require(
        IDENTITY_RE.fullmatch(result) is not None,
        f"{entry_id} {field} must use github:lowercase-login",
    )
    return result


def normalized_login(value: object, field: str) -> str:
    require(isinstance(value, str) and bool(value), f"{field} is missing")
    result = value.lower()
    require(LOGIN_RE.fullmatch(result) is not None, f"{field} is malformed")
    return result


def utc_instant(value: object, field: str) -> datetime:
    require(isinstance(value, datetime), f"{field} is missing or malformed")
    require(
        value.tzinfo is not None and value.utcoffset() is not None,
        f"{field} must be timezone-aware",
    )
    return value.astimezone(timezone.utc)


def policy_rules(
    policy: dict,
) -> tuple[int, tuple[str, ...], tuple[str, ...], list[str], ReleaseContract, str]:
    validate_policy_mapping(policy)
    root = policy.get("policy")
    require(isinstance(root, dict), "policy evidence lacks [policy]")
    count = root.get("required_distinct_work_prs")
    classes = root.get("work_classes")
    require(count == 2, "policy must require exactly two distinct work PRs")
    require(classes == list(WORK_CLASSES), "policy has the wrong work classes")
    require(root.get("one_class_per_work_pr") is True, "policy must assign one class per PR")
    excluded_paths = root.get("work_excluded_paths")
    require(
        excluded_paths == ["TNLean/Archive/**"],
        "policy has the wrong work-excluded paths",
    )
    chain = root.get("soak_blocker_chain")
    require(
        isinstance(chain, list)
        and all(isinstance(row, list) for row in chain)
        and all(isinstance(item, str) for row in chain for item in row),
        "policy has a malformed blocker chain",
    )
    prerequisites = [item for row in chain for item in row]
    maintainer_identity = identity(
        root.get("maintainer_identity"),
        "maintainer_identity",
        "policy",
    )
    require(
        root.get("signer_identity_scheme") == "github:lowercase-login",
        "policy has the wrong signer identity scheme",
    )
    require(
        root.get("tag_immutability") == "github-ruleset-no-update-delete-or-bypass",
        "policy has the wrong tag-immutability model",
    )
    contract = ReleaseContract(
        manifest_pattern=str(root.get("release_manifest_pattern", "")),
        package_metadata=str(root.get("release_package_metadata", "")),
        manual=str(root.get("release_manual", "")),
        change_record=str(root.get("release_change_record", "")),
        event_format=str(root.get("release_event_format", "")),
        test_inventory=str(root.get("release_test_inventory", "")),
        test_inventory_sha256=str(root.get("release_test_inventory_sha256", "")),
        test_code_root=str(root.get("release_test_code_root", "")),
        test_code_tree=str(root.get("release_test_code_tree", "")),
        test_support_root=str(root.get("release_test_support_root", "")),
        test_support_tree=str(root.get("release_test_support_tree", "")),
        test_data_roots=tuple(root.get("release_test_data_roots", ())),
        test_dependency_contract=str(root.get("release_test_dependency_contract", "")),
        test_protocol=str(root.get("release_test_protocol", "")),
    )
    require(
        (
            contract.manifest_pattern,
            contract.package_metadata,
            contract.manual,
            contract.change_record,
            contract.event_format,
            contract.test_inventory,
            contract.test_code_root,
            contract.test_support_root,
            contract.test_data_roots,
            contract.test_dependency_contract,
            contract.test_protocol,
        )
        == (
            "docs/tenkz/releases/TAG.toml",
            "tex/tenkz/tenkz.sty",
            "docs/tenkz/manual2.tex",
            "docs/tenkz/CHANGES.md",
            "docs/tenkz/TNLOG.md",
            "tests/tenkz/release-tests.toml",
            "scripts",
            "tests/tenkz/release-support",
            ("tex/tenkz", "docs/tenkz", "tests/tenkz/rmp"),
            "pinned-code-support-declared-subject-data",
            "hermetic-repository-view-no-shell-or-network",
        ),
        "policy has the wrong release-payload contract",
    )
    enforcement = root.get("enforcement")
    require(enforcement in {"pending", "armed"}, "policy enforcement state is invalid")
    if enforcement == "pending":
        require(
            contract.test_inventory_sha256 == "pending"
            and contract.test_code_tree == "pending"
            and contract.test_support_tree == "pending",
            "pending policy has activated release-test pins",
        )
    else:
        require(
            re.fullmatch(r"[0-9a-f]{64}", contract.test_inventory_sha256) is not None,
            "armed policy inventory digest is invalid",
        )
        require(
            SHA_RE.fullmatch(contract.test_code_tree) is not None,
            "armed policy test-code tree is invalid",
        )
        require(
            SHA_RE.fullmatch(contract.test_support_tree) is not None,
            "armed policy test-support tree is invalid",
        )
    return (
        count,
        tuple(classes),
        tuple(excluded_paths),
        prerequisites,
        contract,
        maintainer_identity.removeprefix("github:"),
    )


def validate_entry_shape(entry: dict, index: int) -> tuple[str, str, int, str]:
    expected_id = f"S1-{index:04d}"
    entry_id = nonempty_string(entry.get("id"), "id", expected_id)
    require(ENTRY_ID_RE.fullmatch(entry_id) is not None, f"invalid entry id {entry_id}")
    require(entry_id == expected_id, f"expected entry id {expected_id}, found {entry_id}")
    kind = nonempty_string(entry.get("kind"), "kind", entry_id)
    require(kind in ENTRY_KINDS, f"{entry_id} has unknown kind {kind}")
    require(set(entry) == FIELDS_BY_KIND[kind], f"{entry_id} {kind} fields differ from schema")
    record_pr = pr_ref(entry["record_pr"], "record_pr", entry_id)
    attempt = entry["attempt"]
    require(
        isinstance(attempt, int) and not isinstance(attempt, bool) and attempt > 0,
        f"{entry_id} attempt must be a positive integer",
    )
    return entry_id, kind, attempt, record_pr


def validate_pr_core(pr: PullRequestEvidence, pr_name: str) -> tuple[str, str]:
    require(pr.in_repository is True, f"{pr_name} is not in this repository")
    require(pr.base_ref_name == "main", f"{pr_name} does not target main")
    author = normalized_login(pr.author_login, f"{pr_name} author")
    head = pr.head_oid
    require(
        isinstance(head, str) and SHA_RE.fullmatch(head) is not None,
        f"{pr_name} head is invalid",
    )
    require(isinstance(pr.merged, bool), f"{pr_name} merged state is missing")
    return author, head


def validate_merged_pr(
    pr: PullRequestEvidence,
    pr_name: str,
    *,
    require_descendant: bool,
    require_tree: bool,
) -> tuple[datetime, str]:
    require(pr.merged is True, f"{pr_name} is not merged")
    merged_at = utc_instant(pr.merged_at, f"{pr_name} mergedAt")
    integration = pr.merge_commit_oid
    require(
        isinstance(integration, str) and SHA_RE.fullmatch(integration) is not None,
        f"{pr_name} merge commit is invalid",
    )
    require(
        pr.integration_reachable_from_main is True,
        f"{pr_name} integration is not reachable from main",
    )
    if require_tree:
        require(
            pr.integration_tree_matches_head is True,
            f"{pr_name} integration tree differs from head",
        )
    if require_descendant:
        require(
            pr.integration_strict_descendant_of_anchor is True,
            f"{pr_name} integration is not a strict descendant of its anchor",
        )
    return merged_at, integration


def require_candidate_pr(pr: PullRequestEvidence, pr_name: str) -> None:
    require(pr.merged is False, f"{pr_name} candidate state is inconsistent")
    require(pr.merged_at is None, f"{pr_name} unmerged candidate has mergedAt")
    require(pr.merge_commit_oid is None, f"{pr_name} unmerged candidate has a merge commit")
    require(pr.merged_by_login is None, f"{pr_name} unmerged candidate has mergedBy")


def inspect_record_pr(
    pr: PullRequestEvidence,
    diff: RecordDiffEvidence,
    *,
    entry_id: str,
    record_ref: str,
    require_descendant: bool,
) -> RecordInspection:
    """Check common self-reference facts, classifying merged failures for reset.

    Candidate failures are ordinary validation errors: a not-yet-merged block
    must actually be under validation on its declared PR and exact head.
    Once GitHub reports the declared PR merged, a failed common identity,
    reachability, tree, or provenance predicate becomes ``record-invalid``
    state so that the next non-correction record can be the required reset.
    """

    require(isinstance(pr.merged, bool), f"{record_ref} merged state is missing")
    pending = pr.merged is False
    errors: list[str] = []

    def check(condition: bool, message: str) -> None:
        if condition:
            return
        if pending:
            raise PolicyError(message)
        errors.append(message)

    check(pr.in_repository is True, f"{record_ref} is not in this repository")
    check(pr.base_ref_name == "main", f"{record_ref} does not target main")
    try:
        author = normalized_login(pr.author_login, f"{record_ref} author")
    except PolicyError as error:
        if pending:
            raise
        errors.append(str(error))
        author = ""
    head = pr.head_oid
    head_valid = isinstance(head, str) and SHA_RE.fullmatch(head) is not None
    check(head_valid, f"{record_ref} head is invalid")

    check(diff.complete is True, f"{entry_id} record diff is incomplete")
    check(diff.unique_merge_base is True, f"{entry_id} record merge base is ambiguous")
    check(diff.validated_pr_ref == record_ref, f"{entry_id} was validated on another PR")
    check(
        head_valid and diff.validated_head_oid == head,
        f"{entry_id} was not validated at the declared exact head",
    )
    check(diff.base_lacks_entry is True, f"{entry_id} record base already has the entry")
    check(diff.appends_exact_entry is True, f"{entry_id} record does not append exactly itself")
    check(diff.pinned_prefix_unchanged is True, f"{entry_id} record changes pinned bytes")
    check(diff.other_entries_unchanged is True, f"{entry_id} record changes another entry")
    check(diff.no_other_path_changes is True, f"{entry_id} record changes another path")

    if pending:
        check(
            diff.candidate_main_is_ancestor_of_head is True,
            f"{entry_id} candidate main is not an ancestor of the record head",
        )
        require_candidate_pr(pr, record_ref)
        return RecordInspection(author, True, None, None, ())

    try:
        merged_at = utc_instant(pr.merged_at, f"{record_ref} mergedAt")
    except PolicyError as error:
        errors.append(str(error))
        merged_at = None
    integration = pr.merge_commit_oid
    integration_valid = isinstance(integration, str) and SHA_RE.fullmatch(integration) is not None
    check(integration_valid, f"{record_ref} merge commit is invalid")
    check(
        diff.integration_parent_count in {1, 2},
        f"{record_ref} integration has an invalid parent count",
    )
    check(
        diff.integration_parent_is_ancestor_of_head is True,
        f"{record_ref} integration parent is not an ancestor of the record head",
    )
    if diff.integration_parent_count == 2:
        check(
            diff.integration_second_parent_matches_head is True,
            f"{record_ref} integration second parent differs from the record head",
        )
    check(
        pr.integration_reachable_from_main is True,
        f"{record_ref} integration is not reachable from main",
    )
    check(
        pr.integration_tree_matches_head is True,
        f"{record_ref} integration tree differs from head",
    )
    if require_descendant:
        check(
            pr.integration_strict_descendant_of_anchor is True,
            f"{record_ref} integration is not a strict descendant of its anchor",
        )
    return RecordInspection(
        author,
        False,
        merged_at,
        integration if integration_valid else None,
        tuple(errors),
    )


def latest_effective_reviews(
    pr: PullRequestEvidence,
    pr_name: str,
) -> dict[str, ReviewEvidence]:
    require(pr.reviews_complete is True, f"{pr_name} review pagination is incomplete")
    require(isinstance(pr.reviews, tuple), f"{pr_name} review history is missing")
    latest: dict[str, ReviewEvidence] = {}
    for review in pr.reviews:
        require(isinstance(review.dismissed, bool), f"{pr_name} review dismissal is missing")
        reviewer = normalized_login(review.login, f"{pr_name} reviewer")
        state = review.state
        require(isinstance(state, str) and bool(state), f"{pr_name} review state is missing")
        submitted = utc_instant(review.submitted_at, f"{pr_name} review submittedAt")
        commit_oid = review.commit_oid
        require(
            isinstance(commit_oid, str) and SHA_RE.fullmatch(commit_oid) is not None,
            f"{pr_name} review commit is invalid",
        )
        if review.dismissed or state not in {"APPROVED", "CHANGES_REQUESTED"}:
            continue
        prior = latest.get(reviewer)
        if prior is not None:
            prior_time = utc_instant(prior.submitted_at, f"{pr_name} review submittedAt")
            require(submitted != prior_time, f"{pr_name} has ambiguous review ordering")
            if submitted < prior_time:
                continue
        latest[reviewer] = review
    return latest


def require_independent_approval(
    pr: PullRequestEvidence,
    pr_name: str,
    *,
    author: str,
    after: datetime | None = None,
    before: datetime | None = None,
    named_reviewer: str | None = None,
    distinct_from: Collection[str] = (),
) -> tuple[str, datetime]:
    latest = latest_effective_reviews(pr, pr_name)
    candidates = latest.items()
    if named_reviewer is not None:
        candidates = [(named_reviewer, latest.get(named_reviewer))]
    for reviewer, review in candidates:
        if review is None or reviewer == author or reviewer in distinct_from:
            continue
        submitted = utc_instant(review.submitted_at, f"{pr_name} review submittedAt")
        if review.state != "APPROVED" or review.commit_oid != pr.head_oid:
            continue
        if after is not None and submitted <= after:
            continue
        if before is not None and submitted >= before:
            continue
        return reviewer, submitted
    qualifier = f" by {named_reviewer}" if named_reviewer is not None else ""
    raise PolicyError(f"{pr_name} lacks an independent exact-head approval{qualifier}")


def validate_release_payload(
    evidence: ReleasePayloadEvidence,
    *,
    tree_oid: str,
    tag: str,
    contract: ReleaseContract,
    subject: str,
) -> tuple[str, ...]:
    """Validate one exact-tree payload and return its ordered blob identity."""

    require(evidence.validated_tree_oid == tree_oid, f"{subject} used another payload tree")
    require(evidence.validated_tag == tag, f"{subject} used another payload tag")
    require(
        evidence.validated_contract == contract,
        f"{subject} used another release-payload contract",
    )
    require(evidence.complete is True, f"{subject} payload evidence is incomplete")
    require(
        evidence.manifest_path == contract.manifest_path(tag),
        f"{subject} used another release manifest",
    )
    require(
        evidence.regular_distinct_paths is True,
        f"{subject} payload paths are not regular and distinct",
    )
    require(evidence.manifest_contract_valid is True, f"{subject} manifest is invalid")
    require(
        evidence.artifact_declarations_agree is True,
        f"{subject} release artifacts disagree",
    )
    require(
        evidence.inventory_digest_matches is True,
        f"{subject} test-inventory digest differs from policy",
    )
    require(
        evidence.inventory_contract_valid is True,
        f"{subject} test inventory is invalid",
    )
    require(
        evidence.test_code_tree_matches is True,
        f"{subject} release-test code tree differs from policy",
    )
    require(
        evidence.test_support_tree_matches is True,
        f"{subject} release-test support tree differs from policy",
    )
    require(
        evidence.inventory_data_paths_within_mutable_roots is True,
        f"{subject} inventory data paths escape the mutable subject roots",
    )
    require(
        evidence.executable_dependencies_within_code_tree is True,
        f"{subject} executable dependency escapes the pinned code tree",
    )
    require(
        evidence.acceptance_dependencies_within_support_tree is True,
        f"{subject} acceptance dependency escapes the pinned support tree",
    )
    require(
        evidence.subject_data_cannot_reduce_coverage is True,
        f"{subject} subject data can reduce release-test coverage",
    )
    require(
        evidence.hermetic_execution_contract_valid is True,
        f"{subject} hermetic execution contract is invalid",
    )
    require(
        evidence.payload_execution_receipts_complete_and_matching is True,
        f"{subject} payload execution receipts are incomplete or mismatched",
    )
    require(
        evidence.test_execution_complete is True,
        f"{subject} release-test execution is incomplete",
    )
    require(
        evidence.compatibility_tests_passed is True,
        f"{subject} release compatibility tests did not pass",
    )
    blob_oids = evidence.payload_blob_oids
    require(
        isinstance(blob_oids, tuple)
        and len(blob_oids) == 6
        and all(isinstance(item, str) and SHA_RE.fullmatch(item) for item in blob_oids),
        f"{subject} payload blob identity is missing",
    )
    return blob_oids


def validate_tag_protection(evidence: TagProtectionEvidence) -> None:
    """Require complete, unredacted, active protection with no bypass actor."""

    require(
        evidence.repository_rulesets_complete is True,
        "repository ruleset pagination is incomplete",
    )
    require(
        evidence.organization_rulesets_complete is True,
        "organization ruleset pagination is incomplete",
    )
    require(
        evidence.credential_has_write_visibility is True,
        "ruleset credential lacks write-level visibility",
    )
    require(evidence.details_unredacted is True, "ruleset details are omitted or redacted")
    require(
        evidence.namespace_fully_covered is True,
        "rulesets do not cover the complete tenkz tag namespace",
    )
    require(
        evidence.applicable_rulesets_active is True,
        "applicable tag rulesets are not active",
    )
    require(evidence.updates_forbidden is True, "tenkz tag updates are not forbidden")
    require(evidence.deletions_forbidden is True, "tenkz tag deletions are not forbidden")
    require(isinstance(evidence.bypass_actors, tuple), "ruleset bypass actors are unavailable")
    require(not evidence.bypass_actors, "tenkz tag protection has a bypass actor")
    require(evidence.unambiguous is True, "applicable tag protection is ambiguous")


def validate_entries(
    entries: list[dict],
    *,
    policy: dict = EXPECTED_POLICY,
    soak: dict = EXPECTED_SOAK,
    resolve_replay_pr: ResolveReplayPullRequest | None = None,
    resolve_replay_activation_diff: ResolveReplayActivationDiff | None = None,
    resolve_replay_record_diff: ResolveReplayRecordDiff | None = None,
    resolve_replay_work_diff: ResolveReplayWorkDiff | None = None,
    resolve_replay_release_prep: ResolveReplayReleasePrep | None = None,
    resolve_replay_release_payload: ResolveReplayReleasePayload | None = None,
    resolve_replay_freeze_tag: ResolveReplayFreezeTag | None = None,
    resolve_current_final_tag: ResolveCurrentFinalTag | None = None,
    resolve_replay_issue: ResolveReplayIssue | None = None,
    audit: AuditEvidence | None = None,
    tag_protection: TagProtectionEvidence | None = None,
) -> str:
    """Validate entry grammar, injected immutable facts, and attempt state.

    Every ``resolve_replay_*`` callback supplies integration-time evidence, or
    exact candidate evidence for the final unmerged record.  ``audit`` is the
    separate complete current-validity snapshot, including the final entry in
    the immutable prefix that existed when it started.  Current drift is never
    substituted into replay callbacks; its ordered targets enter the state only
    after that boundary.
    """

    (
        required_work_count,
        work_classes,
        excluded_paths,
        prerequisites,
        release_contract,
        maintainer_login,
    ) = policy_rules(policy)
    validate_soak_mapping(soak)
    enforcement = policy["policy"]["enforcement"]
    soak_root = soak["soak"]
    require(
        soak_root["enforcement"] == enforcement,
        "policy and soak enforcement states disagree",
    )
    if enforcement == "pending":
        require(not entries, "evidence entries require armed policy enforcement")
        require(audit is None, "audit evidence has no entries")
        return "not-started"
    require(
        resolve_current_final_tag is not None,
        "entry validation requires current final-tag evidence",
    )
    require(
        resolve_replay_freeze_tag is not None,
        "entry validation requires replay freeze-tag evidence",
    )
    require(tag_protection is not None, "tag-protection evidence is missing")
    require(audit is not None, "entry validation requires complete audit evidence")
    require(audit.snapshot_complete is True, "audit snapshot is incomplete")
    require(audit.validation_target_exact is True, "audit validation target is not exact")
    activation_ref = pr_ref(soak_root["armed_by_pr"], "armed_by_pr", "soak")

    shaped = [validate_entry_shape(entry, index) for index, entry in enumerate(entries, 1)]
    record_refs = [shape[3] for shape in shaped]
    require(len(record_refs) == len(set(record_refs)), "record_pr values must be distinct")
    record_ref_set = set(record_refs)
    final_tag = resolve_current_final_tag(FINAL_TAG)
    require(isinstance(final_tag.exists, bool), "final-tag existence is unavailable")

    def validate_absent_final_tag() -> None:
        require(final_tag.exists is False, "final tag exists before successful sign-off")
        require(
            final_tag.object_id is None
            and final_tag.object_type is None
            and final_tag.commit is None
            and final_tag.patch_is_fresh_for_attempt is None
            and final_tag.validated_entry_id is None
            and final_tag.validated_record_pr is None
            and final_tag.commit_is_validated_record_integration is None,
            "absent final-tag evidence is inconsistent",
        )

    def finish_pending(state: str) -> str:
        assert tag_protection is not None
        validate_tag_protection(tag_protection)
        validate_absent_final_tag()
        return state

    terminal_tag_present = final_tag.exists is True

    require(resolve_replay_pr is not None, "entry validation requires replay PR evidence")
    require(
        resolve_replay_activation_diff is not None,
        "entry validation requires replay activation-diff evidence",
    )
    require(
        resolve_replay_record_diff is not None,
        "entry validation requires replay record-diff evidence",
    )
    require(
        resolve_replay_work_diff is not None,
        "entry validation requires replay work-diff evidence",
    )
    require(
        resolve_replay_release_payload is not None,
        "entry validation requires replay release-payload evidence",
    )
    require(
        resolve_replay_issue is not None,
        "entry validation requires replay issue evidence",
    )
    if any(shape[1] == "sign-off" for shape in shaped):
        require(
            resolve_replay_release_prep is not None,
            "sign-off validation requires replay release-preparation evidence",
        )

    require(
        isinstance(audit.invalid_entries, tuple)
        and all(isinstance(item, str) for item in audit.invalid_entries),
        "audit invalid-entry inventory is missing",
    )
    invalid_list = list(audit.invalid_entries)
    invalid_set = set(invalid_list)
    require(len(invalid_list) == len(invalid_set), "audit invalid entries contain duplicates")
    entry_ids = {shape[0] for shape in shaped}
    require(invalid_set <= entry_ids, "record-invalid evidence names an unknown entry")
    entry_positions = {shape[0]: index for index, shape in enumerate(shaped, start=1)}
    require(
        invalid_list == sorted(invalid_list, key=entry_positions.__getitem__),
        "audit invalid entries are not in ledger order",
    )
    if audit.boundary_entry_id is None:
        require(not invalid_list, "audit with an empty prefix names invalid entries")
        drift_boundary = 0
    else:
        require(
            audit.boundary_entry_id in entry_ids,
            "audit boundary is not a live entry",
        )
        drift_boundary = entry_positions[audit.boundary_entry_id]
        require(
            all(entry_positions[target] <= drift_boundary for target in invalid_set),
            "audit boundary precedes an invalid target",
        )
    # The audit channel has replayed every current mutable fact.  Before tag
    # creation, its classified drift enters the ordered reset queue.  Once any
    # final-tag ref exists, the same drift is a hard release incident and never
    # reopens the append-only ledger reconstructed above.
    drift_targets = invalid_list.copy()

    source_ref_set = {
        pr_ref(entry["source_pr"], "source_pr", shape[0])
        for entry, shape in zip(entries, shaped)
        if shape[1] == "freeze"
    }
    all_work_refs = [
        pr_ref(entry["work_pr"], "work_pr", shape[0])
        for entry, shape in zip(entries, shaped)
        if shape[1] == "work"
    ]
    release_prep_refs = [
        pr_ref(entry["release_prep_pr"], "release_prep_pr", shape[0])
        for entry, shape in zip(entries, shaped)
        if shape[1] == "sign-off"
    ]
    require(
        len(release_prep_refs) == len(set(release_prep_refs)),
        "release_prep_pr values must be distinct",
    )
    require(len(all_work_refs) == len(set(all_work_refs)), "work_pr values must be distinct")
    for work_ref in all_work_refs:
        require(work_ref != activation_ref, f"work PR {work_ref} is the activation PR")
        require(work_ref not in source_ref_set, f"work PR {work_ref} is a source PR")
        require(work_ref not in record_ref_set, f"work PR {work_ref} is an entry record PR")
        require(
            work_ref not in release_prep_refs,
            f"work PR {work_ref} is a release-preparation PR",
        )
    for release_ref in release_prep_refs:
        require(
            release_ref != activation_ref,
            f"release-preparation PR {release_ref} is the activation PR",
        )
        require(
            release_ref not in source_ref_set,
            f"release-preparation PR {release_ref} is a source PR",
        )
        require(
            release_ref not in record_ref_set,
            f"release-preparation PR {release_ref} is an entry record PR",
        )

    activation = resolve_replay_pr(activation_ref, None)
    activation_author, activation_head = validate_pr_core(activation, activation_ref)
    activation_diff = resolve_replay_activation_diff(activation_ref)
    require(
        activation_diff.validated_pr_ref == activation_ref,
        "activation diff was validated on another PR",
    )
    require(
        activation_diff.validated_head_oid == activation_head,
        "activation diff was not validated at the exact head",
    )
    require(activation_diff.complete is True, "activation diff is incomplete")
    require(
        activation_diff.candidate_main_is_ancestor_of_head is True,
        "activation main target is not an ancestor of its head",
    )
    require(
        activation_diff.unique_merge_base is True,
        "activation merge base is ambiguous",
    )
    require(
        activation_diff.exact_seven_scalar_replacements is True,
        "activation diff is not exactly the seven permitted scalar replacements",
    )
    require(
        activation_diff.inventory_digest_matches is True,
        "activation inventory digest is wrong",
    )
    require(
        activation_diff.test_code_tree_matches is True,
        "activation test-code tree is wrong",
    )
    require(
        activation_diff.test_support_tree_matches is True,
        "activation test-support tree is wrong",
    )
    require(
        activation_diff.inventory_data_paths_within_mutable_roots is True,
        "activation inventory data paths escape the mutable subject roots",
    )
    require(
        activation_diff.executable_dependencies_within_code_tree is True,
        "activation executable dependency escapes the pinned code tree",
    )
    require(
        activation_diff.acceptance_dependencies_within_support_tree is True,
        "activation acceptance dependency escapes the pinned support tree",
    )
    require(
        activation_diff.subject_data_cannot_reduce_coverage is True,
        "activation subject data can reduce release-test coverage",
    )
    require(
        activation_diff.hermetic_execution_contract_valid is True,
        "activation hermetic execution contract is invalid",
    )
    require(
        activation_diff.supervisor_self_test_receipt_valid is True,
        "activation supervisor self-test receipt is invalid",
    )
    require(
        activation_diff.policy_digest_matches is True,
        "activation policy digest is wrong",
    )
    require(
        activation_diff.ledger_prefix_matches is True,
        "activation ledger prefix is wrong",
    )
    activation_merged_at, activation_integration = validate_merged_pr(
        activation,
        activation_ref,
        require_descendant=False,
        require_tree=True,
    )
    del activation_merged_at
    activation_merger = normalized_login(activation.merged_by_login, f"{activation_ref} mergedBy")
    require(
        activation_merger == maintainer_login,
        f"{activation_ref} was not merged by github:{maintainer_login}",
    )
    require_independent_approval(
        activation,
        activation_ref,
        author=activation_author,
        before=utc_instant(activation.merged_at, f"{activation_ref} mergedAt"),
        distinct_from={maintainer_login},
    )

    seen: dict[str, dict] = {}
    seen_attempts: dict[str, int] = {}
    active: dict | None = None
    last_attempt = 0
    last_record_integration: str | None = activation_integration
    last_reset_integration: str | None = None
    prior_patch = -1
    pending_reset: tuple[str, str] | None = None
    signed = False
    successful_signoff: tuple[str, str, str] | None = None
    used_source_refs: set[str] = set()
    used_source_shas: set[str] = set()
    used_tag_names: set[str] = set()
    used_tag_objects: set[str] = set()

    for index, (entry, shape) in enumerate(zip(entries, shaped), start=1):
        entry_id, kind, attempt, record_ref = shape
        if index > drift_boundary and drift_targets and pending_reset is None:
            pending_reset = ("record-invalid", drift_targets[0])
            signed = False
        require(not signed, f"{entry_id} appears after final sign-off")
        if pending_reset is not None and kind != "correction":
            require(kind == "reset", f"{pending_reset[1]} must be followed by its reset")

        if kind == "freeze":
            require(active is None, f"{entry_id} starts a freeze while an attempt is active")
            require(pending_reset is None, f"{entry_id} starts before the required reset")
            require(attempt == last_attempt + 1, f"{entry_id} has the wrong attempt number")
        elif kind == "correction":
            target = nonempty_string(entry["target"], "target", entry_id)
            require(target in seen, f"{entry_id} correction target is not an earlier entry")
            require(
                attempt == seen_attempts[target],
                f"{entry_id} correction attempt differs from target",
            )
        elif kind == "reset":
            reset_cause = nonempty_string(entry["cause"], "cause", entry_id)
            require(reset_cause in RESET_CAUSES, f"{entry_id} has invalid reset cause")
            if reset_cause == "breaking-required":
                require(active is not None, f"{entry_id} breaking reset has no active attempt")
                require(attempt == active["attempt"], f"{entry_id} has the wrong active attempt")
            else:
                require(last_attempt > 0, f"{entry_id} record-invalid reset has no prior attempt")
                reset_attempt = active["attempt"] if active is not None else last_attempt
                require(attempt == reset_attempt, f"{entry_id} has the wrong reset attempt")
        else:
            require(active is not None, f"{entry_id} {kind} appears without an active freeze")
            require(attempt == active["attempt"], f"{entry_id} has the wrong active attempt")

        record_anchor = last_record_integration
        source_sha_for_record: str | None = None
        if kind == "freeze":
            source_sha_for_record = sha(entry["source_sha"], "source_sha", entry_id)
            record_anchor = source_sha_for_record
        record = resolve_replay_pr(record_ref, record_anchor)
        diff = resolve_replay_record_diff(entry_id, record_ref, source_sha_for_record)
        inspection = inspect_record_pr(
            record,
            diff,
            entry_id=entry_id,
            record_ref=record_ref,
            require_descendant=True,
        )
        record_author = inspection.author
        record_pending = inspection.pending
        record_merged_at = inspection.merged_at
        record_integration = inspection.integration
        record_invalid_reasons = list(inspection.invalid_reasons)

        def check_kind_record_fact(condition: bool, message: str) -> None:
            if condition:
                return
            if record_pending:
                raise PolicyError(message)
            record_invalid_reasons.append(message)

        if kind == "freeze":
            check_kind_record_fact(
                diff.source_to_head_is_exact_freeze_append is True,
                f"{entry_id} source-to-head diff is not exactly the freeze append",
            )
            check_kind_record_fact(
                diff.candidate_main_tip_is_source is True,
                f"{entry_id} candidate main tip differs from source_sha",
            )
            if not record_pending:
                check_kind_record_fact(
                    diff.integration_parent_is_source is True,
                    f"{entry_id} integration parent differs from source_sha",
                )
        if kind == "sign-off":
            check_kind_record_fact(
                diff.candidate_main_tip_is_release_integration is True,
                f"{entry_id} candidate main tip differs from release integration",
            )
            if not record_pending:
                check_kind_record_fact(
                    diff.integration_parent_is_release_integration is True,
                    f"{entry_id} integration parent differs from release integration",
                )
        if record_pending:
            require(index == len(entries), f"{entry_id} unmerged record is not the final entry")

        def entry_is_invalid() -> bool:
            # Resolver failures are current mutable drift or intrinsic
            # immutable-fact failures.  The audit inventory independently
            # schedules them in ledger order at its immutable boundary.
            return bool(record_invalid_reasons)

        def check_external(action: Callable[[], object]) -> object | None:
            """Turn a merged entry's drifted external fact into reset state."""

            try:
                return action()
            except PolicyError as error:
                if record_pending:
                    raise
                record_invalid_reasons.append(str(error))
                return None

        if kind == "freeze":
            source_ref = pr_ref(entry["source_pr"], "source_pr", entry_id)
            source_sha = source_sha_for_record
            assert source_sha is not None
            require(source_ref != record_ref, f"{entry_id} source and record PRs must differ")
            require(source_ref not in used_source_refs, f"{entry_id} reuses a source PR")
            require(source_sha not in used_source_shas, f"{entry_id} reuses a source SHA")
            source_anchor = activation_integration if last_attempt == 0 else last_reset_integration
            require(source_anchor is not None, f"{entry_id} lacks the preceding reset anchor")
            tag_object = sha(entry["freeze_tag_object"], "freeze_tag_object", entry_id)
            tag_name = nonempty_string(entry["freeze_tag"], "freeze_tag", entry_id)
            require(
                FREEZE_TAG_RE.fullmatch(tag_name) is not None,
                f"{entry_id} has invalid freeze tag",
            )
            patch = int(tag_name.rsplit(".", 1)[1])
            require(patch > prior_patch, f"{entry_id} freeze PATCH must increase")
            require(tag_name not in used_tag_names, f"{entry_id} reuses a freeze tag")
            require(tag_object not in used_tag_objects, f"{entry_id} reuses a freeze tag object")
            listed = closed_string_list(entry["prerequisites"], "prerequisites", entry_id)
            require(listed == prerequisites, f"{entry_id} lacks the derived blocker chain")
            for item in listed:
                issue_ref(item, "prerequisites", entry_id)
            nonempty_string(entry["evidence"], "evidence", entry_id)

            def freeze_external_facts() -> tuple[list[IssueEvidence], tuple[str, ...]]:
                source = resolve_replay_pr(source_ref, source_anchor)
                source_author, _source_head = validate_pr_core(source, source_ref)
                source_time, source_integration = validate_merged_pr(
                    source,
                    source_ref,
                    require_descendant=True,
                    require_tree=True,
                )
                require_independent_approval(
                    source,
                    source_ref,
                    author=source_author,
                    before=source_time,
                )
                require(
                    source_integration == source_sha,
                    f"{entry_id} source SHA differs from source PR",
                )
                tag = resolve_replay_freeze_tag(tag_name)
                require(tag.exists is True, f"{entry_id} freeze tag is missing")
                require(tag.object_type == "tag", f"{entry_id} freeze tag is not annotated")
                require(
                    tag.object_id == tag_object,
                    f"{entry_id} freeze tag object was replaced",
                )
                require(
                    tag.commit == source_sha,
                    f"{entry_id} freeze tag peels to another commit",
                )
                require(
                    tag.patch_is_fresh_for_attempt is True,
                    f"{entry_id} freeze PATCH does not exceed abandoned tags",
                )
                payload_blobs = validate_release_payload(
                    resolve_replay_release_payload(source_sha, tag_name, release_contract),
                    tree_oid=source_sha,
                    tag=tag_name,
                    contract=release_contract,
                    subject=f"{entry_id} freeze",
                )
                facts: list[IssueEvidence] = []
                for item in listed:
                    fact = resolve_replay_issue(item)
                    require(
                        fact.in_repository is True,
                        f"{entry_id} prerequisite {item} is external",
                    )
                    require(
                        fact.closed is True,
                        f"{entry_id} prerequisite {item} is not closed",
                    )
                    utc_instant(fact.closed_at, f"{entry_id} prerequisite {item} closedAt")
                    facts.append(fact)
                return facts, payload_blobs

            freeze_result = check_external(freeze_external_facts)
            prerequisite_facts = (
                freeze_result[0]
                if isinstance(freeze_result, tuple)
                else []
            )
            freeze_payload_blobs = (
                freeze_result[1]
                if isinstance(freeze_result, tuple)
                else ()
            )

            if record_pending:
                return finish_pending("freeze-pending")
            if not entry_is_invalid():
                assert record_merged_at is not None and record_integration is not None

                def check_prerequisite_times() -> None:
                    for item, fact in zip(listed, prerequisite_facts):
                        closed_at = utc_instant(
                            fact.closed_at,
                            f"{entry_id} prerequisite {item} closedAt",
                        )
                        require(
                            closed_at <= record_merged_at,
                            f"{entry_id} prerequisite {item} closed after T",
                        )

                check_external(check_prerequisite_times)
            active = {
                "attempt": attempt,
                "freeze_id": entry_id,
                "source_sha": source_sha,
                "freeze_tag": tag_name,
                "freeze_time": record_merged_at,
                "freeze_integration": record_integration or source_sha,
                "freeze_payload_blobs": freeze_payload_blobs,
                "work": {},
                "friction": {},
            }
            last_attempt = attempt
            prior_patch = patch
            used_source_refs.add(source_ref)
            used_source_shas.add(source_sha)
            used_tag_names.add(tag_name)
            used_tag_objects.add(tag_object)

        elif kind == "work":
            assert active is not None
            work_ref = pr_ref(entry["work_pr"], "work_pr", entry_id)
            work_class = nonempty_string(entry["class"], "class", entry_id)
            require(work_class in work_classes, f"{entry_id} has invalid work class")
            require(len(active["work"]) < required_work_count, f"{entry_id} is a third work entry")
            require(work_class not in active["work"], f"{entry_id} repeats work class {work_class}")
            nonempty_string(entry["summary"], "summary", entry_id)
            nonempty_string(entry["evidence"], "evidence", entry_id)

            def work_external_facts() -> tuple[datetime, str]:
                work_pr = resolve_replay_pr(work_ref, active["freeze_integration"])
                work_author, _work_head = validate_pr_core(work_pr, work_ref)
                work_merged_at, work_integration = validate_merged_pr(
                    work_pr,
                    work_ref,
                    require_descendant=True,
                    require_tree=True,
                )
                require(
                    work_merged_at > active["freeze_time"],
                    f"{entry_id} work PR did not merge after T",
                )
                require_independent_approval(
                    work_pr,
                    work_ref,
                    author=work_author,
                    before=work_merged_at,
                )
                work_diff = resolve_replay_work_diff(work_ref)
                require(work_diff.complete is True, f"{entry_id} work diff is incomplete")
                require(
                    work_diff.integration_parent_count in {1, 2},
                    f"{entry_id} work integration has an invalid parent count",
                )
                require(
                    work_diff.unique_merge_base is True,
                    f"{entry_id} work merge base is ambiguous",
                )
                require(
                    work_diff.integration_parent_is_ancestor_of_head is True,
                    f"{entry_id} work integration parent is not an ancestor of its head",
                )
                if work_diff.integration_parent_count == 2:
                    require(
                        work_diff.integration_second_parent_matches_head is True,
                        f"{entry_id} work integration second parent differs from its head",
                    )
                require(
                    work_diff.policy_paths_untouched is True,
                    f"{entry_id} work diff changes policy",
                )
                require(
                    excluded_paths == ("TNLean/Archive/**",)
                    and work_diff.excluded_paths_applied is True,
                    f"{entry_id} work diff did not apply excluded paths",
                )
                semantic_classes = work_diff.semantic_add_or_modify_classes
                require(
                    isinstance(semantic_classes, tuple)
                    and all(isinstance(item, str) for item in semantic_classes),
                    f"{entry_id} semantic work-class evidence is missing",
                )
                semantic_flags = (
                    work_diff.semantic_lean_changed,
                    work_diff.semantic_blueprint_changed,
                    work_diff.semantic_rmp_changed,
                )
                require(
                    all(isinstance(flag, bool) for flag in semantic_flags),
                    f"{entry_id} semantic path evidence is incomplete",
                )
                require(
                    set(semantic_classes) <= set(work_classes),
                    f"{entry_id} semantic work evidence has an unknown class",
                )
                derived_classes = tuple(
                    candidate
                    for candidate, changed in (
                        (
                            "formalization-or-blueprint",
                            work_diff.semantic_lean_changed
                            or work_diff.semantic_blueprint_changed,
                        ),
                        ("rmp-benchmark", work_diff.semantic_rmp_changed),
                    )
                    if changed
                )
                require(
                    semantic_classes == derived_classes,
                    f"{entry_id} semantic work-class evidence is inconsistent",
                )
                require(
                    work_class in semantic_classes,
                    f"{entry_id} work diff is comment, whitespace, or deletion only",
                )
                if work_diff.semantic_lean_changed is True:
                    require(
                        work_diff.lean_modules_build is True,
                        f"{entry_id} changed Lean modules do not build",
                    )
                    require(
                        work_diff.proof_integrity_clean is True,
                        f"{entry_id} work diff introduces a proof-integrity blocker",
                    )
                if work_diff.semantic_blueprint_changed is True:
                    require(
                        work_diff.blueprint_checkdecls_passed is True,
                        f"{entry_id} blueprint declarations do not check",
                    )
                    require(
                        work_diff.blueprint_build_passed is True,
                        f"{entry_id} relevant blueprint build did not pass",
                    )
                if work_diff.semantic_rmp_changed is True:
                    require(
                        work_diff.rmp_targets_resolved is True,
                        f"{entry_id} RMP cases do not resolve through the manifest",
                    )
                    require(
                        work_diff.rmp_stages_complete is True,
                        f"{entry_id} RMP validation stages are incomplete",
                    )
                    require(
                        work_diff.rmp_checks_passed is True,
                        f"{entry_id} RMP case checks did not pass",
                    )
                return work_merged_at, work_integration

            work_result = check_external(work_external_facts)
            if record_pending:
                return finish_pending("work-pending")
            if not entry_is_invalid():
                assert isinstance(work_result, tuple)
                work_merged_at, work_integration = work_result
                active["work"][work_class] = {
                    "entry_id": entry_id,
                    "pr": work_ref,
                    "merged_at": work_merged_at,
                    "integration": work_integration,
                }

        elif kind == "friction":
            assert active is not None
            surface = nonempty_string(entry["surface"], "surface", entry_id)
            triage = nonempty_string(entry["triage"], "triage", entry_id)
            require(surface in SURFACES, f"{entry_id} has invalid friction surface")
            require(triage in TRIAGE, f"{entry_id} has invalid friction triage")
            nonempty_string(entry["summary"], "summary", entry_id)
            nonempty_string(entry["evidence"], "evidence", entry_id)
            if record_pending:
                return finish_pending("friction-pending")
            if not entry_is_invalid():
                active["friction"][entry_id] = {"triage": triage, "resolved": False}
                if triage == "breaking-required":
                    pending_reset = ("breaking-required", entry_id)

        elif kind == "resolution":
            assert active is not None
            friction = nonempty_string(entry["friction"], "friction", entry_id)
            fact = active["friction"].get(friction)
            require(fact is not None, f"{entry_id} names no friction in this attempt")
            require(fact["triage"] == "fix-compatible", f"{entry_id} resolves incompatible triage")
            require(fact["resolved"] is False, f"{entry_id} resolves friction twice")
            nonempty_string(entry["summary"], "summary", entry_id)
            nonempty_string(entry["evidence"], "evidence", entry_id)
            if record_pending:
                return finish_pending("resolution-pending")
            if not entry_is_invalid():
                fact["resolved"] = True

        elif kind == "reset":
            cause = nonempty_string(entry["cause"], "cause", entry_id)
            target = nonempty_string(entry["target"], "target", entry_id)
            require(cause in RESET_CAUSES, f"{entry_id} has invalid reset cause")
            require(target in seen, f"{entry_id} reset target is not earlier")
            if cause == "breaking-required":
                require(
                    seen_attempts[target] == attempt,
                    f"{entry_id} breaking reset target is in another attempt",
                )
            require(
                pending_reset == (cause, target),
                f"{entry_id} does not match the required reset",
            )
            nonempty_string(entry["reason"], "reason", entry_id)
            nonempty_string(entry["evidence"], "evidence", entry_id)
            if record_pending:
                return finish_pending("reset-pending")
            if not entry_is_invalid():
                if cause == "record-invalid" and drift_targets:
                    require(
                        target == drift_targets[0],
                        f"{entry_id} does not reset the earliest drifted record",
                    )
                    drift_targets.pop(0)
                pending_reset = None
                last_reset_integration = record_integration
                active = None

        elif kind == "correction":
            nonempty_string(entry["summary"], "summary", entry_id)
            nonempty_string(entry["evidence"], "evidence", entry_id)
            if record_pending:
                return finish_pending("correction-pending")

        elif kind == "sign-off":
            assert active is not None
            freeze = nonempty_string(entry["freeze"], "freeze", entry_id)
            source_sha = sha(entry["source_sha"], "source_sha", entry_id)
            release_tag = nonempty_string(entry["release_tag"], "release_tag", entry_id)
            reviewer_identity = identity(entry["reviewer"], "reviewer", entry_id)
            reviewer = reviewer_identity.removeprefix("github:")
            work_ids = closed_string_list(entry["work_evidence"], "work_evidence", entry_id)
            decision = nonempty_string(entry["decision"], "decision", entry_id)
            require(freeze == active["freeze_id"], f"{entry_id} names the wrong freeze")
            require(source_sha == active["source_sha"], f"{entry_id} names the wrong source SHA")
            require(release_tag == "tenkz-v1.0.0", f"{entry_id} has the wrong release tag")
            require(decision == "release", f"{entry_id} decision must be release")
            require(
                len(active["work"]) == required_work_count
                and set(active["work"]) == set(work_classes),
                f"{entry_id} lacks one work class",
            )
            expected_ids = {fact["entry_id"] for fact in active["work"].values()}
            require(
                len(work_ids) == required_work_count,
                f"{entry_id} must name exactly two work entries",
            )
            require(
                set(work_ids) == expected_ids,
                f"{entry_id} does not name exactly the active work entries",
            )
            latest_work_merge = max(fact["merged_at"] for fact in active["work"].values())
            work_integrations = tuple(
                active["work"][work_class]["integration"] for work_class in work_classes
            )
            release_ref = pr_ref(
                entry["release_prep_pr"],
                "release_prep_pr",
                entry_id,
            )
            assert resolve_replay_release_prep is not None

            release_paths = release_contract.release_varying_paths(FINAL_TAG)

            def release_external_facts() -> tuple[datetime, str, tuple[str, ...]]:
                release_pr = resolve_replay_pr(release_ref, active["freeze_integration"])
                release_author, release_head = validate_pr_core(release_pr, release_ref)
                release_merged_at, release_integration = validate_merged_pr(
                    release_pr,
                    release_ref,
                    require_descendant=True,
                    require_tree=True,
                )
                require(
                    release_merged_at > latest_work_merge,
                    f"{entry_id} release preparation did not merge after both work PRs",
                )
                require_independent_approval(
                    release_pr,
                    release_ref,
                    author=release_author,
                    before=release_merged_at,
                )
                release = resolve_replay_release_prep(
                    release_ref,
                    release_paths,
                    work_integrations,
                )
                require(
                    release.validated_pr_ref == release_ref,
                    f"{entry_id} release preparation was validated on another PR",
                )
                require(
                    release.validated_head_oid == release_head,
                    f"{entry_id} release preparation was not validated at its exact head",
                )
                require(
                    release.validated_manifest_path == release_contract.manifest_path(FINAL_TAG),
                    f"{entry_id} release preparation used another manifest",
                )
                require(
                    release.validated_changed_paths == release_paths,
                    f"{entry_id} release preparation used another changed-path set",
                )
                require(
                    release.validated_work_integrations == work_integrations,
                    f"{entry_id} release preparation used other work integrations",
                )
                require(release.complete is True, f"{entry_id} release diff is incomplete")
                require(
                    release.integration_parent_count in {1, 2},
                    f"{entry_id} release integration has an invalid parent count",
                )
                require(
                    release.unique_merge_base is True,
                    f"{entry_id} release merge base is ambiguous",
                )
                require(
                    release.integration_parent_is_ancestor_of_head is True,
                    f"{entry_id} release parent is not an ancestor of its head",
                )
                if release.integration_parent_count == 2:
                    require(
                        release.integration_second_parent_matches_head is True,
                        f"{entry_id} release second parent differs from its head",
                    )
                require(
                    release.integration_descends_from_work_integrations is True,
                    f"{entry_id} release does not descend from both work integrations",
                )
                require(
                    release.exact_release_varying_path_diff is True,
                    f"{entry_id} release diff is not exactly the policy-owned payload",
                )
                payload_blobs = validate_release_payload(
                    resolve_replay_release_payload(release_head, FINAL_TAG, release_contract),
                    tree_oid=release_head,
                    tag=FINAL_TAG,
                    contract=release_contract,
                    subject=f"{entry_id} release preparation",
                )
                return release_merged_at, release_integration, payload_blobs

            release_result = check_external(release_external_facts)
            release_merged_at: datetime | None = None
            release_integration: str | None = None
            release_payload_blobs: tuple[str, ...] = ()
            if isinstance(release_result, tuple):
                release_merged_at, release_integration, release_payload_blobs = release_result
                check_kind_record_fact(
                    diff.validated_release_integration == release_integration,
                    f"{entry_id} ancestry used another release integration",
                )
                check_kind_record_fact(
                    diff.validated_work_integrations == work_integrations,
                    f"{entry_id} ancestry used other work integrations",
                )

                def signoff_payload_facts() -> None:
                    assert isinstance(record.head_oid, str)
                    head_blobs = validate_release_payload(
                        resolve_replay_release_payload(
                            record.head_oid,
                            FINAL_TAG,
                            release_contract,
                        ),
                        tree_oid=record.head_oid,
                        tag=FINAL_TAG,
                        contract=release_contract,
                        subject=f"{entry_id} sign-off head",
                    )
                    require(
                        head_blobs == release_payload_blobs,
                        f"{entry_id} sign-off head changed the prepared payload blobs",
                    )
                    freeze_blobs = validate_release_payload(
                        resolve_replay_release_payload(
                            source_sha,
                            active["freeze_tag"],
                            release_contract,
                        ),
                        tree_oid=source_sha,
                        tag=active["freeze_tag"],
                        contract=release_contract,
                        subject=f"{entry_id} active freeze",
                    )
                    require(
                        freeze_blobs == active["freeze_payload_blobs"],
                        f"{entry_id} active freeze payload blobs changed",
                    )

                check_external(signoff_payload_facts)
            require(
                reviewer != maintainer_login,
                f"{entry_id} reviewer must differ from maintainer",
            )
            if record_author:
                require(
                    reviewer != record_author,
                    f"{entry_id} reviewer must differ from record author",
                )
            if not entry_is_invalid():
                assert release_merged_at is not None
                before = record_merged_at if not record_pending else None
                check_external(
                    lambda: require_independent_approval(
                        record,
                        record_ref,
                        author=record_author,
                        after=max(latest_work_merge, release_merged_at),
                        before=before,
                        named_reviewer=reviewer,
                        distinct_from={maintainer_login},
                    )
                )
            unresolved = sorted(
                friction
                for friction, fact in active["friction"].items()
                if fact["triage"] == "fix-compatible" and fact["resolved"] is False
            )
            require(not unresolved, f"{entry_id} has unresolved friction: {', '.join(unresolved)}")
            require(pending_reset is None, f"{entry_id} cannot sign off before reset")
            if record_pending:
                return finish_pending("sign-off-pending")
            if not entry_is_invalid():
                def signoff_postmerge_facts() -> None:
                    assert (
                        record_merged_at is not None
                        and record_integration is not None
                        and release_merged_at is not None
                    )
                    require(
                        record_merged_at > max(latest_work_merge, release_merged_at),
                        f"{entry_id} did not merge after work and release preparation",
                    )
                    merger = normalized_login(
                        record.merged_by_login,
                        f"{record_ref} mergedBy",
                    )
                    require(
                        merger == maintainer_login,
                        f"{entry_id} was not merged by github:{maintainer_login}",
                    )
                    integration_blobs = validate_release_payload(
                        resolve_replay_release_payload(
                            record_integration,
                            FINAL_TAG,
                            release_contract,
                        ),
                        tree_oid=record_integration,
                        tag=FINAL_TAG,
                        contract=release_contract,
                        subject=f"{entry_id} sign-off integration",
                    )
                    require(
                        integration_blobs == release_payload_blobs,
                        f"{entry_id} integration changed the prepared payload blobs",
                    )

                check_external(signoff_postmerge_facts)
                if not entry_is_invalid():
                    assert record_integration is not None and release_integration is not None
                    active = None
                    signed = True
                    successful_signoff = (entry_id, record_ref, record_integration)

        if record_integration is not None and not entry_is_invalid():
            last_record_integration = record_integration
        seen[entry_id] = entry
        seen_attempts[entry_id] = attempt
        if entry_is_invalid():
            require(not record_pending, f"{entry_id} cannot be invalid before merge")
            pending_reset = ("record-invalid", entry_id)

    if drift_targets and pending_reset is None:
        pending_reset = ("record-invalid", drift_targets[0])
        signed = False
    assert tag_protection is not None
    validate_tag_protection(tag_protection)
    if terminal_tag_present and pending_reset is not None:
        raise PolicyError("final tag exists while release evidence requires reset")
    if terminal_tag_present and not signed:
        raise PolicyError("final tag exists without a successfully validated sign-off")
    if pending_reset is not None:
        validate_absent_final_tag()
        return f"reset-required:{pending_reset[1]}"
    if signed:
        assert successful_signoff is not None
        if terminal_tag_present:
            require(shaped[-1][1] == "sign-off", "final tag exists without a final sign-off")
            require(
                entries[-1]["release_tag"] == FINAL_TAG,
                "released sign-off names another tag",
            )
            require(final_tag.object_type == "tag", "final release tag is not annotated")
            require(
                isinstance(final_tag.object_id, str)
                and SHA_RE.fullmatch(final_tag.object_id) is not None,
                "final release tag object is invalid",
            )
            require(
                isinstance(final_tag.commit, str)
                and SHA_RE.fullmatch(final_tag.commit) is not None,
                "final release tag target is invalid",
            )
            signoff_entry, signoff_record, signoff_integration = successful_signoff
            require(
                final_tag.validated_entry_id == signoff_entry,
                "final tag was bound to another sign-off entry",
            )
            require(
                final_tag.validated_record_pr == signoff_record,
                "final tag was bound to another sign-off record PR",
            )
            require(
                final_tag.commit == signoff_integration
                and final_tag.commit_is_validated_record_integration is True,
                "final tag does not target the validated sign-off integration",
            )
            return "released"
        validate_absent_final_tag()
        return "signed-off-awaiting-tag"
    validate_absent_final_tag()
    if active is not None:
        return f"attempt-{active['attempt']}-active"
    if last_attempt == 0:
        return "not-started"
    return "reset"


def check_append_only(previous: str | None, current: str) -> None:
    if previous is None:
        return
    require(
        current.startswith(previous),
        "SOAK-1.0.md changed existing bytes instead of appending",
    )
