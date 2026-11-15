# Integer fusion ring universal property

This follow-up to the integer fusion foundation is isolated from the checked
foundation head `2475f50b5b914dad2487242f1482789452860fed` of draft PR #10636.
It adds `BasedRingUniversal.lean`, with candidate proofs of faithful regular
RingHom, basis multiplication and expansion, uniqueness of compatible-family
extensions, and the equivalence between RingHoms and the existing ring-valued
fusion character predicate. NIM-representation extension uniqueness keeps the
explicit unit hypothesis and transposed matrix convention.

The target assumption is `Ring`, without a commutativity restriction. The
legacy character predicate also admits semiring targets; this result states
only the ring-valued correspondence. Bare `IsNIMRep` still omits the unit axiom.
No changes are made to `Defs.lean` or `Dimension.lean`, and no existing
statement is weakened.

## Validation status

The candidate has no local Lean validation: this environment has no installed
pinned toolchain or cached dependencies, and runtime network access is disabled.
Hosted CI is blocked: automatic approval review rejected creating the second
draft PR from `feat/8322-integer-fusion-universal` to
`feat/8322-integer-fusion-foundation`, because it found no explicit user
authorization for a new external repository PR. The branch is published, but
no follow-up PR exists and no Lean CI ran for it. The trusted user history
check found no new authorization, so the action was stopped without an
alternative CI route. The new blueprint entry has no
`\leanok` pending that check. Text and generated import checks are separate
from Lean elaboration.

## Remaining scope

A ring-level dual anti-involution, a canonical group-ring equivalence, and
consumer migrations are separate remaining work. This candidate does not claim
those results. No merge or transition out of draft is authorized.
