# Original frustration-free ground-vector entropy at every cut

The new public theorem
`TNLean.MPS.AreaLaw.exists_aklv_frustrationFree_physical_entropy_bound`
chooses a universal constant before all chain lengths, local dimensions,
interactions, states and cuts. For local dimension q≥2 and an explicit
projector gap lower bound 0<g≤1, the original unit vector Ω satisfying HΩ=0
obeys the rate `C/g * (1 + log q + log(1/g))^3` at every physical cut.

No attained first excitation is assumed. No filter, fitted window, regional
minimum, product overlap, spectral tail, cut decomposition or entropy premise
is supplied. The existing general changing-target entropy theorem is not
used to infer the new bound.

## Exact construction and source scope

The scalar theorem from draft #10434 gives one A uniformly, before q and g.
Set g0=g/8192, u=1+log q+log(1/g), u0=u+log8192, s=ceil(A*u0²/g0),
ell=s² and t=1024/g. Its width coefficient W and rank-log coefficient R are
positive universal constants. The final constant is C=4R+W.

If a window centered at a cut fits, draft #10435 constructs an actual
Chebyshev polynomial of the actual exterior-clipped Hamiltonian. It fixes
the same original Ω by the frustration-free preservation in #10430. Its
32-width rank estimate becomes precisely the scalar rank D, and its squared
Chebyshev error becomes precisely the scalar delta by the existing
`Real.exp_nat_mul` identity. The scalar tradeoff D*delta≤1/100000 implies
D*delta≤1/2. Accepted QICLean's
`Entropy.regionEntropy_le_four_log_of_cutOperatorSchmidtRank` then gives
the original vector's regional entropy at most 4logD. The existing theorem
already derives its product-overlap bootstrap, tails and cut transport.

When the window does not fit, the existing centered-window lemma gives
min(k,L-k)≤s-s/2≤s. The smaller-side dimension entropy bound then gives
S≤s*logq≤W*u³/g. Endpoint cuts, empty chains, and chains shorter than the
chosen window are included in this alternative.

This is an auxiliary retained-logarithm rate for AKLV, arXiv:1301.1162v1,
the proof of `t:ent`, lines 810–846, and `col:half`, lines 350–361. It does
not claim the printed sharper rate with inverse-gap logarithms eliminated.
The source scope is recorded in the existing
`docs/paper-gaps/aklv13_two_block_robustness.tex` note. A single module-level
scope marker covers this rate restriction.

## Visibility-only reuse

The existing private `aklv_regionEntropy_le_short_side` in
`AKLV/PhysicalEntropy.lean` now has a genuine second module consumer. Only
its `private` keyword is removed. Its mathematical signature and complete
proof remain byte-for-byte unchanged. It is cited at a new blueprint anchor
whose statement and proof remain `notready`. No copy of its proof or new
entropy bootstrap is introduced.

## Verification and dependency gates

The child inherits the exact final published filter head
`ac41990d8e1dd5f77f0e3c95f9f05aac6fb5a30a` of draft #10435, which incorporates
draft #10434. Its three QICLean pin records retain the coherent candidate
`fc38c6bda842f5d6b5379a821de04243422aeb68`; the child does not repin it.
Those parent and upstream drafts require acceptance and integration. The
generic regional entropy theorem itself already exists at accepted QICLean
pin `acda92aa70e69b37507e422bceb5414036859fe6`.

No Lean, Lake, elaboration, build or compiled-declaration checker is run.
The new global theorem and the newly exposed helper each have one blueprint
owner; statements and proofs remain `notready` pending fresh hosted checking.
Native checks and independent mathematical/API reviews are recorded in the
pull request once complete.

Root and two independent peer reviews passed the complete 140-line source,
including the exact scalar/filter interfaces, exponential-square conversion,
original-vector regional entropy, smaller-side fallback and uniform constants.
The visibility-only helper comparison is exact at parent head `ac41990d8`.
Native generated imports, full blueprint/source synchronization with unique
anchors and reverse coverage, chapter roles, complete bibliography generation,
ChkTeX, source size/width/integrity, manifest/private-source coherence, tactic
pattern scanning, and whitespace checks pass. No hosted proof acceptance is
claimed for this new source; fresh hosted verification remains required.
