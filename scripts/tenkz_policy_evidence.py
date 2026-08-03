#!/usr/bin/env python3
"""Typed inputs and raw REST transport for tenkz policy evidence.

The policy checker consumes one :class:`PolicyEvidenceBundle`.  One resolver
reconstructs immutable history; a second resolver is bound to the exact current
snapshot.  Either resolver may report that a fact is unavailable, but neither
may replace that fact with a default.

This module also fixes the raw GitHub transport contract used by later live
resolvers: REST responses only, 100 records per page, and complete ``Link``
pagination.  It deliberately does not interpret release or supervisor facts.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import (
    TYPE_CHECKING,
    Callable,
    Literal,
    Mapping,
    Protocol,
    runtime_checkable,
)
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit


if TYPE_CHECKING:
    from check_tenkz_policy import (
        ActivationDiffEvidence,
        AuditEvidence,
        FinalTagPublisherEvidence,
        IssueEvidence,
        PublisherSecretEvidence,
        PullRequestEvidence,
        RecordDiffEvidence,
        RecordInvalidResetReplayEvidence,
        ReleaseContract,
        ReleasePayloadEvidence,
        ReleasePrepEvidence,
        ReleaseTestObservationEvidence,
        ResolutionDiffEvidence,
        TagEvidence,
        TagProtectionEvidence,
        WorkflowEvidence,
        WorkDiffEvidence,
    )


EVIDENCE_API_VERSION = 1
GITHUB_REST_API_VERSION = "2022-11-28"
GITHUB_JSON_MEDIA_TYPE = "application/vnd.github+json"
REST_PAGE_SIZE = 100


class EvidenceContractError(ValueError):
    """The raw response or in-memory evidence contract is malformed."""


class EvidenceUnavailable(ValueError):
    """A required fact was not collected by this resolver."""


@dataclass(frozen=True)
class RestResponse:
    """One raw REST response before policy-specific interpretation."""

    status: int
    headers: Mapping[str, str]
    body: bytes


RestRequest = Callable[[str, Mapping[str, str]], RestResponse]


def _with_page_size(url: str) -> str:
    """Set the closed REST page size without changing the other query fields."""

    split = urlsplit(url)
    query = [
        (key, value)
        for key, value in parse_qsl(split.query, keep_blank_values=True)
        if key != "per_page"
    ]
    query.append(("per_page", str(REST_PAGE_SIZE)))
    return urlunsplit(
        (split.scheme, split.netloc, split.path, urlencode(query), split.fragment)
    )


def _next_link(headers: Mapping[str, str]) -> str | None:
    """Read the unique ``rel=next`` target from a GitHub ``Link`` header."""

    raw = next((value for key, value in headers.items() if key.lower() == "link"), None)
    if raw is None:
        return None
    targets: list[str] = []
    for item in raw.split(","):
        parts = [part.strip() for part in item.split(";")]
        if not parts or not (parts[0].startswith("<") and parts[0].endswith(">")):
            raise EvidenceContractError(
                "GitHub Link header contains a malformed target"
            )
        relations = {
            relation
            for part in parts[1:]
            if part.startswith('rel="') and part.endswith('"')
            for relation in part.removeprefix("rel=").strip('"').split()
        }
        if "next" in relations:
            targets.append(parts[0][1:-1])
    if len(targets) > 1:
        raise EvidenceContractError("GitHub Link header contains multiple next targets")
    return targets[0] if targets else None


class GitHubRestApiV1:
    """Strict raw GitHub REST reader with complete fixed-size pagination."""

    def __init__(self, request: RestRequest) -> None:
        self._request = request

    @staticmethod
    def headers() -> Mapping[str, str]:
        return {
            "Accept": GITHUB_JSON_MEDIA_TYPE,
            "X-GitHub-Api-Version": GITHUB_REST_API_VERSION,
        }

    def object(self, url: str) -> Mapping[str, object]:
        """Return one JSON object, rejecting partial or differently shaped replies."""

        response = self._request(url, self.headers())
        value = self._decode_success(response)
        if not isinstance(value, dict) or not all(
            isinstance(key, str) for key in value
        ):
            raise EvidenceContractError("GitHub REST object response is not an object")
        return value

    def pages(self, url: str) -> tuple[Mapping[str, object], ...]:
        """Read every page of a list endpoint in server order."""

        current = _with_page_size(url)
        seen: set[str] = set()
        records: list[Mapping[str, object]] = []
        while current is not None:
            if current in seen:
                raise EvidenceContractError("GitHub REST pagination contains a cycle")
            seen.add(current)
            response = self._request(current, self.headers())
            value = self._decode_success(response)
            if not isinstance(value, list):
                raise EvidenceContractError(
                    "GitHub REST paginated response is not a list"
                )
            for item in value:
                if not isinstance(item, dict) or not all(
                    isinstance(key, str) for key in item
                ):
                    raise EvidenceContractError(
                        "GitHub REST paginated response contains a non-object"
                    )
                records.append(item)
            next_url = _next_link(response.headers)
            current = _with_page_size(next_url) if next_url is not None else None
        return tuple(records)

    @staticmethod
    def _decode_success(response: RestResponse) -> object:
        if (
            not isinstance(response.status, int)
            or isinstance(response.status, bool)
            or response.status != 200
        ):
            raise EvidenceUnavailable(
                f"GitHub REST evidence is unavailable (HTTP {response.status!r})"
            )
        try:
            return json.loads(response.body)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise EvidenceContractError(
                "GitHub REST response is not valid JSON"
            ) from error


@runtime_checkable
class PolicyEvidenceResolver(Protocol):
    """Every evidence query used by the policy replay, with no optional methods."""

    def resolve_replay_pr(
        self,
        ref: str,
        anchor: str | None,
    ) -> PullRequestEvidence:
        ...

    def resolve_replay_activation_diff(self, ref: str) -> ActivationDiffEvidence:
        ...

    def resolve_replay_record_diff(
        self,
        entry_id: str,
        record_pr: str,
        source_sha: str | None,
    ) -> RecordDiffEvidence:
        ...

    def resolve_replay_work_diff(self, ref: str) -> WorkDiffEvidence:
        ...

    def resolve_replay_resolution_diff(self, ref: str) -> ResolutionDiffEvidence:
        ...

    def resolve_replay_release_prep(
        self,
        ref: str,
        integration_oid: str,
        paths: tuple[str, ...],
        work_integrations: tuple[str, ...],
        resolution_integrations: tuple[str, ...],
    ) -> ReleasePrepEvidence:
        ...

    def resolve_replay_release_payload(
        self,
        tree_oid: str,
        tag: str,
        contract: ReleaseContract,
    ) -> ReleasePayloadEvidence:
        ...

    def resolve_replay_release_test_observation(
        self,
        tree_oid: str,
        tag: str,
        test_ref: str,
        contract: ReleaseContract,
    ) -> ReleaseTestObservationEvidence:
        ...

    def resolve_replay_freeze_tag(self, tag: str) -> TagEvidence:
        ...

    def resolve_current_final_tag(self, tag: str) -> TagEvidence:
        ...

    def resolve_final_tag_publisher(
        self,
        integration_oid: str,
    ) -> FinalTagPublisherEvidence:
        ...

    def resolve_current_publisher_secret(
        self,
        environment: str,
        secret_name: str,
        secret_scope: str,
        key_retirement: str,
    ) -> PublisherSecretEvidence:
        ...

    def resolve_replay_issue(self, ref: str) -> IssueEvidence:
        ...

    def resolve_replay_record_invalid_reset(
        self,
        entry_id: str,
        target: str,
        receipt_ref: str,
        receipt_digest: str,
        current_tree_oid: str,
    ) -> RecordInvalidResetReplayEvidence:
        ...

    def resolve_current_workflow(
        self,
        activation_integration: str,
        target_oid: str,
        paths: tuple[str, ...],
        publisher_workflow_root: str,
    ) -> WorkflowEvidence:
        ...


def _require_complete_resolver(resolver: object, subject: str) -> None:
    if not isinstance(resolver, PolicyEvidenceResolver):
        raise EvidenceContractError(f"{subject} policy evidence resolver is incomplete")


@dataclass(frozen=True)
class ImmutableReplayEvidence:
    """Evidence fixed at each historical integration or candidate head."""

    resolver: PolicyEvidenceResolver

    def __post_init__(self) -> None:
        _require_complete_resolver(self.resolver, "immutable replay")


@dataclass(frozen=True)
class CurrentEvidenceSnapshot:
    """Current facts bound to one exact repository validation target."""

    resolver: PolicyEvidenceResolver
    audit: AuditEvidence
    tag_protection: TagProtectionEvidence

    def __post_init__(self) -> None:
        _require_complete_resolver(self.resolver, "current snapshot")


@dataclass(frozen=True)
class PolicyEvidenceBundle:
    """Separate immutable replay from current drift in one checker input."""

    replay: ImmutableReplayEvidence
    current: CurrentEvidenceSnapshot
    api_version: Literal[1] = EVIDENCE_API_VERSION

    def __post_init__(self) -> None:
        if (
            not isinstance(self.api_version, int)
            or isinstance(self.api_version, bool)
            or self.api_version != EVIDENCE_API_VERSION
        ):
            raise EvidenceContractError(
                f"unsupported tenkz policy evidence API version {self.api_version!r}"
            )
        if not isinstance(self.replay, ImmutableReplayEvidence):
            raise EvidenceContractError("immutable replay evidence is malformed")
        if not isinstance(self.current, CurrentEvidenceSnapshot):
            raise EvidenceContractError("current policy evidence snapshot is malformed")
        if self.replay.resolver is self.current.resolver:
            raise EvidenceContractError(
                "immutable replay and current snapshot resolvers must be distinct"
            )
