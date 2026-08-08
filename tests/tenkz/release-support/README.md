# Release-test support tree

Immutable acceptance data for the 1.0 release campaign. `docs/tenkz/SOAK-1.0.md`
§Release payload evidence separates the two pinned trees: runner code and every
imported or sourced helper live in `tests/tenkz/release-harness/`, while
expected outputs, baselines, allowlists, thresholds, and schemas live here.
Neither tree may be supplied by a subject under test, and nothing here is
executable.

The activation change pins this tree by its exact Git tree OID. Every byte in
it must therefore be final before that change opens; afterwards a correction
means a new campaign attempt.

| File | Role |
|---|---|
| `final-tag-object-v1.schema.json` | the closed description of the one annotated `tenkz-v1.0.0` object the publisher may construct |
| `reset-replay-v1.schema.json` | the closed shape of a `record-invalid` reset's replay receipt under `docs/tenkz/soak-replay/` |
| `selftest-expectations.toml` | the supervisor self-test suite: one row per isolation probe and the outcome the supervisor must report |
| `tool-profile.toml` | the child tools an inventory command may reach, and the version fingerprint each must report |

## The final-tag signing key is not here

`DESIGN.md` names `tests/tenkz/release-support/final-tag-signing-key.pub` as the
public half of the SSH-Ed25519 key that signs the release tag. It is absent,
and deliberately so: a public key whose private half nobody holds is worse than
no key, because every check downstream of it would pass while signing nothing.

Before activation the maintainer generates the pair, keeps the private half
only in the `tenkz-release-publisher` environment secret named by
`release_publisher_secret`, and lands the public half here in an ordinary
reviewed change:

```bash
ssh-keygen -t ed25519 -C tenkz-v1.0.0 -f tenkz-final-tag
# tenkz-final-tag.pub -> tests/tenkz/release-support/final-tag-signing-key.pub
# tenkz-final-tag     -> the TENKZ_FINAL_TAG_SIGNING_KEY environment secret
```

The same change fixes the two byte constants the tag-object schema currently
leaves open, `tagger_name` and `tagger_email`, and adds the publisher job to
`.github/workflows/tenkz-release-policy.yml`. Until it lands,
`supervisor.py check-readiness` reports the key as absent, and it refuses any
policy that claims `armed` without it.
