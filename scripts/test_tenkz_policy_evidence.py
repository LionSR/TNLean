#!/usr/bin/env python3
"""Focused checks for the raw tenkz policy-evidence contract."""

from __future__ import annotations

import sys
from collections.abc import Callable, Mapping
from pathlib import Path
from unittest.mock import Mock


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import tenkz_policy_evidence as evidence  # noqa: E402


FIXTURES = ROOT / "tests/tenkz/policy-evidence/api-v1"


def fixture(name: str) -> bytes:
    return (FIXTURES / name).read_bytes()


class FrozenRequest:
    def __init__(self, responses: dict[str, evidence.RestResponse]) -> None:
        self.responses = responses
        self.calls: list[tuple[str, dict[str, str]]] = []

    def __call__(
        self,
        url: str,
        headers: Mapping[str, str],
    ) -> evidence.RestResponse:
        self.calls.append((url, dict(headers)))
        return self.responses[url]


def expect_failure(action: Callable[[], object], fragment: str) -> None:
    try:
        action()
    except (evidence.EvidenceContractError, evidence.EvidenceUnavailable) as error:
        assert fragment in str(error), (fragment, str(error))
        return
    raise AssertionError(f"expected evidence failure containing {fragment!r}")


def main() -> int:
    pull_url = "https://api.github.test/repos/LionSR/TNLean/pulls/42"
    reviews_url = pull_url + "/reviews?direction=asc"
    first_page = reviews_url + "&per_page=100"
    second_page = pull_url + "/reviews?page=2&per_page=100"
    request = FrozenRequest(
        {
            pull_url: evidence.RestResponse(200, {}, fixture("pull-request.json")),
            first_page: evidence.RestResponse(
                200,
                {
                    "Link": (
                        f'<{pull_url}/reviews?page=2&per_page=1>; rel="next", '
                        f'<{pull_url}/reviews?page=2&per_page=1>; rel="last"'
                    )
                },
                fixture("reviews-page-1.json"),
            ),
            second_page: evidence.RestResponse(
                200,
                {},
                fixture("reviews-page-2.json"),
            ),
        }
    )
    api = evidence.GitHubRestApiV1(request)
    assert api.object(pull_url)["number"] == 42
    assert [item["id"] for item in api.pages(reviews_url)] == [1001, 1002]
    expected_headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    assert request.calls == [
        (pull_url, expected_headers),
        (first_page, expected_headers),
        (second_page, expected_headers),
    ]

    issue_url = "https://api.github.test/repos/LionSR/TNLean/issues/5352"
    issue_request = FrozenRequest(
        {issue_url: evidence.RestResponse(200, {}, fixture("issue.json"))}
    )
    assert evidence.GitHubRestApiV1(issue_request).object(issue_url)["number"] == 5352

    denied = FrozenRequest(
        {pull_url: evidence.RestResponse(403, {}, b'{"message":"forbidden"}')}
    )
    expect_failure(
        lambda: evidence.GitHubRestApiV1(denied).object(pull_url),
        "HTTP 403",
    )
    partial = FrozenRequest(
        {pull_url: evidence.RestResponse(206, {}, fixture("pull-request.json"))}
    )
    expect_failure(
        lambda: evidence.GitHubRestApiV1(partial).object(pull_url),
        "HTTP 206",
    )
    malformed = FrozenRequest(
        {first_page: evidence.RestResponse(200, {}, b'{"not":"a page"}')}
    )
    expect_failure(
        lambda: evidence.GitHubRestApiV1(malformed).pages(reviews_url),
        "not a list",
    )
    cyclic = FrozenRequest(
        {
            first_page: evidence.RestResponse(
                200,
                {"link": f'<{first_page}>; rel="next"'},
                b"[]",
            )
        }
    )
    expect_failure(
        lambda: evidence.GitHubRestApiV1(cyclic).pages(reviews_url),
        "pagination contains a cycle",
    )

    expect_failure(
        lambda: evidence.ImmutableReplayEvidence(resolver=object()),
        "immutable replay policy evidence resolver is incomplete",
    )
    expect_failure(
        lambda: evidence.CurrentEvidenceSnapshot(
            resolver=object(),
            audit=object(),
            tag_protection=object(),
        ),
        "current snapshot policy evidence resolver is incomplete",
    )
    expect_failure(
        lambda: evidence.PolicyEvidenceBundle(
            replay=object(),
            current=object(),
            api_version=2,
        ),
        "unsupported tenkz policy evidence API version",
    )
    shared_resolver = Mock(spec=evidence.PolicyEvidenceResolver)
    expect_failure(
        lambda: evidence.PolicyEvidenceBundle(
            replay=evidence.ImmutableReplayEvidence(shared_resolver),
            current=evidence.CurrentEvidenceSnapshot(
                shared_resolver,
                audit=object(),
                tag_protection=object(),
            ),
        ),
        "resolvers must be distinct",
    )
    print("PASS: tenkz policy evidence uses one strict API-v1 REST contract")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
