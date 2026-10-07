# Local dependency for the exact small-size corollary

This local-only dependency commit materializes one unchanged file from TNLean
PR #8788. It is not authored as part of the exact-tree contribution and is not
intended to be published or cherry-picked with its downstream corollary.

- Dependency owner: TNLean PR #8788 / issue #8738.
- Verified public head: `158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2`.
- Reused file: `TNLean/PEPS/Approximation/Basic.lean`.
- Verified Git blob: `df2002c0ec0defb72188220cc03c4fa3ad1a7797`.
- Source: <https://github.com/LionSR/TNLean/blob/158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2/TNLean/PEPS/Approximation/Basic.lean>.
- Public dependency state when prepared, 2026-10-07: open, draft, unmerged.

The exact-tree base is `ec0672f82f4bc499c1aea862a53319aeb0770fb7`.
The next authored commit contains only the downstream consumer, its tests,
blueprint entry, and review notes. Those changes must be integrated after the
owned model interface lands, or checked locally against this pinned dependency.
The source-only worker did not compile, mutate caches, or change the owned file.
