# Issue #612 blocker report — algebra-structure coefficients

Date: 2026-04-20
Branch: `feat/612-algebra-structure-coeffs`
Target issue: #612

## Outcome

I did **not** change `TNLean/MPS/MPDO/AlgebraStructure.lean`.
The current algebra-structure side is still a scaffold on `main`, and replacing it
by a paper-faithful definition would require new support-algebra infrastructure that
is not yet present in the repository.

## Current state on `main`

The file `TNLean/MPS/MPDO/AlgebraStructure.lean` still exposes a vacuous
compatibility predicate:

- `MPOTensor.AlgebraStructureData.CompatibleWith _ _ : Prop := True`
- `MPOTensor.IsRFP_MPDO_via_algebra_scaffold M := ∃ data, data.CompatibleWith M`

So the current algebra-structure predicate is satisfied by every MPO tensor and
cannot yet serve as a mathematical formulation of Theorem IV.13(ii) from
arXiv:1606.00608 §4.5.

The blueprint already states this honestly: the §4.5 algebra-structure entry in
`blueprint/src/chapter/ch02b_mpdo.tex` marks the predicate as provisional and notes
that the compatibility relation is trivial.

## The merged #611 API that one would naturally transfer from

PR #665 (#611) added the transfer-map-level fusion formulation in
`TNLean/MPS/MPDO/FusionIsometries.lean`. For each blocked size `n`, it provides
`MPOTensor.FusionIsometryData M n` consisting of:

- a support subspace
  `supportAlgebra : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)`;
- a forward map
  `T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] supportAlgebra`;
- a backward map
  `S : supportAlgebra →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ`;
- the retract identity
  `T ∘ₗ S = LinearMap.id`;
- the characteristic identity
  `S ∘ₗ T = blockedTransferMap M n`.

This is strong enough to prove
`MPOTensor.isRFP_MPDO_via_fusion_iff_isRFP`, because an idempotent blocked
transfer map factors through its range and conversely any such retract makes the
blocked transfer map idempotent.

## Why this is still not enough for the algebra-structure side

The paper's algebra-structure formulation is not just a retract through a subspace.
It needs a genuine algebra object at each blocked size, together with multiplication
coefficients `c_{αβγ}^{(L)}` and compatibility across blocking levels.

The natural route from the merged fusion API would be to define a projected product
on the range of `blockedTransferMap M n` by

`a ⋆ b := T (S a * S b)`.

However, the current `supportAlgebra` in `FusionIsometryData` is only a
`Submodule`, not a `Subalgebra` / `StarSubalgebra`, and the existing API does not
prove that this projected product is associative or unital.

There is already an abstract conditional-expectation interface in
`TNLean/Channel/FixedPoint/ConditionalExpectation.lean`, but it assumes a
pre-existing `StarSubalgebra`. What is missing here is precisely the theorem that
upgrades the range of the blocked transfer map to such an algebraic object.

## Concrete missing pieces

To replace `CompatibleWith := True` by a paper-faithful condition, the repository
still needs the following infrastructure.

### 1. Choi–Effros identity for the blocked transfer-map idempotent

If we write `E_n := blockedTransferMap M n`, then the projected multiplication on
`range(E_n)` should be controlled by the Choi–Effros identities

- `E_n (E_n x * y) = E_n (x * y)`;
- `E_n (x * E_n y) = E_n (x * y)`.

Equivalently, one wants the standard form

`E_n (E_n x * E_n y) = E_n (x * y)`.

Without these identities there is no sound route to an associative multiplication
on the support object extracted from the fusion datum.

### 2. Packaging the range as an algebra / support-algebra object

Once the projected product is available, the range of `E_n` must be packaged as an
actual algebraic object, ideally something like a `StarSubalgebra` or a dedicated
support-algebra structure carrying:

- carrier subspace;
- multiplication;
- unit;
- closure proofs;
- associativity and unit laws;
- the relation to `E_n` as the corresponding projection / conditional expectation.

At present, `FusionIsometryData.supportAlgebra` is only a `Submodule`, so the
necessary algebraic laws cannot even be stated in the right form.

### 3. Basis-coordinate extraction for the coefficients

Theorem IV.13(ii) is phrased in terms of structure coefficients
`c_{αβγ}^{(L)}` and the idempotence relation

`m_γ = Σ_{α,β} c_{αβγ}^{(1)} m_α m_β`.

After the support algebras are available, one still needs a finite-basis / block
API extracting the coordinates of the multiplication map in that basis and proving
that they match the coefficient formulas coming from the blocked MPO operators.
Only then can `AlgebraStructureData.CompatibleWith` be replaced by something that
actually reflects the paper.

## Conclusion

Issue #612 is blocked not by a local proof gap in `AlgebraStructure.lean`, but by a
missing layer between the current fusion retracts and the paper's support-algebra
formulation. The correct next step is to build that missing layer first, and only
then return to the algebra-structure coefficients themselves.

## Recommended follow-up issue

Suggested title:

> **Choi–Effros/support-algebra API for `blockedTransferMap` idempotents**

Suggested scope:

1. For an idempotent blocked transfer map `E_n`, prove the Choi–Effros product
   identities needed on `range(E_n)`.
2. Package `range(E_n)` as a `StarSubalgebra`-like support algebra with projected
   multiplication.
3. Expose the bridge from `FusionIsometryData` to that support algebra.
4. Only after this, return to issue #612 and define the algebra-structure
   coefficients and compatibility predicate in a non-vacuous way.
