# Actual joint parent support in full boundary frames

Source: GLM23v3, `Papers/2203.12563/REsubmission.tex`, lines 1695–1777.
Source-only base: public PR #8724 at
`3e1cdad36f82c24a1de80f561cf4a2c269de7b0c`. The current #8724
repair head `7b6bbfab322bb2dbd2571606d4f4f11db060ceac` is integrated
without changing the new mathematical statements.

## Mathematical result

`JointMixedEndpointFrameSupport.lean` starts with the actual two-site map

```
Γ′₂(X)[i,j] = Σₓ tr(Cₓⁱ Vₓ Vₓ† Cₓʲ Xₓ).
```

The explicit coefficient vector is

```
g(X) = Σₓ,ₐ,ₑ,ᵦ (Xₓ)ₑₐ |x,a,b⟩ ⊗ |x,b,e⟩,
Γ′₂(X) = (L ⊗ R) g(X).
```

Both physical sites retain the full shared alphabet. The ambient boundary
coordinate space includes all ordered pairs of block labels. The same label
appears in the two factors of each summand because the actual virtual trace
has that label, not because different physical blocks are orthogonal.

Polar reconstruction gives `L ⊗ R = (U_L ⊗ U_R)(P_L ⊗ P_R)`. Hence the
actual support `S` is contained in the full product frame range `F`. These
inclusions need no injectivity or positive-dimension hypothesis. They cover
empty labels, zero first or second fibers, and rectangular physical alphabets.
Simultaneous one-site spanning is used only when proving that the product
polar frame is an isometry.

`SupportedParentProjection.lean` supplies finite-dimensional projection
identities from a proved inclusion `S ≤ F`. The concrete application in
`JointMixedEndpointFrameReduction.lean` derives, for the actual parent
interaction `h = I − P_S` and frame projection `Q = P_F`,

```
Q P_S = P_S,       Q h = h Q,
I − Q ≤ h,        h v = v  for v ∈ F⊥,
‖(I − Q)v‖² ≤ Re⟨h v,v⟩.
```

Thus the full physical frame complement carries a local penalty with
coefficient one. Under simultaneous one-site spanning, put
`U = U_L ⊗ U_R`. The same actual interaction satisfies

```
Q = U U†,
U† h U = I − P_(U†S),
ker(U† h U) = U†S.
```

The reducing property and compressed kernel are conclusions, not added
hypotheses. The interaction is kept as the literal complementary projection
of the actual inserted support, avoiding duplication of the named interaction
in the separate periodic source branch.

## Scope and next obligations

These are full two-site identities at parameter zero. At length two, both
boundary frames belong to the same single term. No doubled first/last sum
is introduced.

The first/last maps in PR #8724 crop the adjacent site to the entire shared
first alphabet. Identifying their normalized support projectors with
compressions of actual chain terms still requires the periodic branch's
proved phase reduction and a controlled integration of its source stack.
That stack was deliberately not copied or imported here.

The individual first-site and last-site frame reductions, their placement
throughout a chain, the joint inactive-sector chain penalty, and the
identification with the common ordered-pair core family remain separate
obligations. This package asserts no endpoint uniform gap, does not change
an interior tensor, and adds no physical block orthogonality assumption.

## Verification

The exact complete frame-support module passes a strict, one-thread,
read-only Lean elaboration check in seven seconds with an empty log.
The complete production source bodies, all regression mathematical
assertions, and all four standard dependency guards have also been accepted
in a strict 40-second combined probe. Its sole diagnostic was one unused
simplifier argument in a regression proof. That argument was removed; the
final rerun reached the external 60-second wall cap with an empty log. This
last result is inconclusive, so a fully successful final regression run and
native module checks are still pending. All source bodies are retained in
the validation bundles; no proof stubs, replacement assumptions, generated Lean artifacts,
Lake builds, cache writes, or resource-limit changes are used. Final probe
results and source hashes are recorded in the companion validation JSON.

The focused regression includes overlapping scalar blocks in a three-letter
alphabet, vanishing second fibers, empty labels, zero first fibers, a proper
rectangular isometry, and a zero-dimensional frame. Four strict dependency guards
cover the full actual factorization, actual reducing commutator, actual
complementary penalty, and actual compressed kernel.

An independent numerical check uses complex noncommuting tensors with
`D₀=(2,1)`, `D₁=(1,2)`, and two rectangular `22 × 9` frames. A cross-label
Gram entry has absolute value about `4.97`. The actual trace factorization,
polar factorization, support absorption, reducing commutator, complement
identity, and compressed actual projector agree to within `1.2 × 10⁻¹⁴`.
The minimum eigenvalue of the penalty difference is `−1.8 × 10⁻¹⁵`, within
roundoff of positivity. This is a numerical consistency check, not proof
validation.

The new blueprint leaf contains the exact contraction equations and a
Tenkz diagram with both physical legs and the correct virtual dimensions.
Its focused PDF has seven pages; the two pages containing the new leaf
were visually inspected. No overflow, undefined-reference, or
missing-character warning occurs. The HTML contains every new label,
with no broken local anchor, duplicate identifier, or rendering sentinel.
The leaf carries no checked markers pending native package validation.

Global source/blueprint synchronization and changed-declaration reverse
coverage pass. Whitespace, forbidden proof-token, file-size, and pinned
latexindent checks pass. The tactic scan found no new repeated proof
pattern requiring a further local abstraction. Shared import routers,
chapter includes, generated declaration lists, and CI workflows are left
for the coordinated integration.
