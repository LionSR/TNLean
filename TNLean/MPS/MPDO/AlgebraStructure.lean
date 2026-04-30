/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TNLean.Algebra.MatrixFrobenius
import TNLean.Channel.FixedPoint.Algebra
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint
import TNLean.MPS.MPDO.FusionIsometries

/-!
# Algebra-structure witnesses for MPDO renormalization fixed points

This file replaces the earlier construction for the algebra-structure side of
arXiv:1606.00608, §4.5.

The paper's full statement uses coefficient systems
$c_{\alpha,\beta,\gamma}^{(L)} =
  \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^L)$
and BNT data. That full coefficient layer is not yet formalized here. What we do
formalize is the stationary C$^*$-algebra structure naturally attached to an MPO
whose blocked transfer maps are idempotent, together with a first explicit
coordinate layer obtained by choosing bases of the blocked support algebras.

More precisely, `AlgebraStructureData` now contains a genuine tower of support
`StarSubalgebra`s together with multiplication and inclusion maps realized by the
ambient matrix product and the ambient inclusion. Compatibility with an MPO
tensor `M` means that, for every positive blocked size `n`, the carrier `A n`
coincides with the fixed-point algebra of the adjoint blocked transfer map
`(blockedTransferMap M n).adjoint`.

Under a trace-preserving normalization and a positive-definite fixed point of the
MPO transfer map, an RFP tensor yields a **stationary** algebra tower. Combined
with the transfer-map fusion criterion from `FusionIsometries.lean`, this gives a
one-way implication

* `isRFP_MPDO_via_algebra_of_isRFP_of_isTP_of_posDef_fixed`
* `isRFP_MPDO_via_algebra_of_isRFP_MPDO_via_fusion_of_isTP_of_posDef_fixed`

from the current fusion formulation to the algebra formulation, under the same
side hypotheses. The `IsRFP` assumption is essential here: without idempotence,
the adjoint fixed-point algebras of the blocked transfer maps need not stabilize
with the blocking length.

## Diagonal $\chi$-matrices and the trace-power formula

On top of the blocked-coefficient layer, this file now formalizes the target
shape of Theorem IV.13(ii): the special diagonal matrices
$\chi_{\alpha,\beta,\gamma}$ are represented as a `DiagonalChiFamily`, and the
identity $c_{\alpha,\beta,\gamma}^{(L)} = \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^L)$
is encoded as the `HasChiTracePowerForm` predicate. The basic trace-power
identity `tr(χ_{α,β,γ}^L) = \sum_k \chi_{\alpha,\beta,\gamma,k}^L` is proved
directly from `Matrix.diagonal_pow` and `Matrix.trace_diagonal`.

## Remaining gap to the paper

The present `CompatibleWith` relation identifies the support algebras with the
adjoint fixed-point algebras of the blocked transfer maps. It does **not** yet
construct the specific `DiagonalChiFamily` attached to an RFP MPDO tensor, nor
prove the converse algebra-to-fusion implication. Those steps still require the
BNT / coefficient-comparison layer from Appendix C.3--C.4.

### Why the converse algebra-to-fusion implication is blocked

The lemma `adjoint_transferMap_apply_of_isRFP_MPDO_via_algebra` below extracts
the strongest direct consequence of `IsRFP_MPDO_via_algebra M`: the inclusion
maps `iota n` force every adjoint fixed point of the blocked transfer map at
positive blocking size `n` to be an adjoint fixed point of the unblocked
transfer map, i.e. `Fix((blockedTransferMap M n).adjoint)` is contained in
`Fix((transferMap M).adjoint)` for every `n ≥ 1`. The reverse inclusion, proved
as `adjoint_blockedTransferMap_apply_of_adjoint_transferMap_apply`, is a simple
induction using `blockedTransferMap_eq_pow` and `LinearMap.adjoint_comp`; it
does not need the algebra-structure data. Together the two lemmas establish
the fixed-point equality
`Fix((blockedTransferMap M n).adjoint) = Fix((transferMap M).adjoint)` at every
positive blocking size `n`.

This equality already excludes *finite-order* (root-of-unity) peripheral
eigenvalues of `(transferMap M).adjoint`, because any such eigenvalue would
produce a blocked adjoint fixed point at some positive `n` that is not fixed
by the unblocked adjoint. It does *not* exclude unit-modulus eigenvalues of
irrational phase, and a fortiori it is not enough to force `transferMap M`
itself to be idempotent. Ergodic channels with a strict spectral gap on the
`1`-complement therefore satisfy `IsRFP_MPDO_via_algebra M` without being
MPDO RFPs: on `M_D(ℂ)`, with `0 < ε < 1`, consider
`E(X) = ε · X + (1 - ε) · Π_diag(X)`, where `Π_diag` is the projection that
zeroes the off-diagonal entries of `X`. Then `Π_diag ∘ Π_diag = Π_diag`,
`E` has peripheral spectrum `{1}` and diagonal fixed-point algebra at every
blocking size, yet `E ∘ E ≠ E`.

Closing the converse algebra-to-fusion implication therefore requires
strengthening the predicate to the paper's full coefficient formulation -- the
positive diagonal matrices `χ_{α,β,γ}` from Appendix C.3 and the coefficient
identity `c^{(L)}_{α,β,γ} = tr(χ_{α,β,γ}^L)` from Appendix C.4. The scalar
Newton--Girard power-sum identity needed for the latter step is already
available in this formalization.

## References

* [CPGSV17] arXiv:1606.00608, §4.5 and Appendix C.3--C.4
* [Wolf12] Wolf, *Quantum Channels & Operations*, Theorem 6.12
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

local instance instMatrixNormedAddCommGroup (D : ℕ) :
    NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.frobenius_posDef_one (D := D))

local instance instMatrixInnerProductSpace (D : ℕ) :
    InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1
    (Matrix.frobenius_posDef_one (D := D)).posSemidef

namespace MPOTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

local instance instFiniteDimensionalStarSubalgebra (S : StarSubalgebra ℂ Mat) :
    FiniteDimensional ℂ S :=
  FiniteDimensional.of_subalgebra_toSubmodule (S := S.toSubalgebra) inferInstance

/-- Algebra-structure data for the stationary support-algebra picture of an MPO.

At blocked size `n`, the support object is a `StarSubalgebra` of bond-space
matrices. The map `m n` is the blocking multiplication, landing in the
size-`2n` support algebra, while `iota n` is the inclusion into the size-`n+1`
support algebra. The fields `m_apply` and `iota_apply` require that these maps
are realized by the ambient matrix product and ambient inclusion.

This structure contains only this realization data. It does **not** yet include
the full §4.5 coherence / coefficient / BNT layer from the paper. -/
structure AlgebraStructureData (d D : ℕ) where
  /-- Support algebra at blocked size `n`. -/
  A : ℕ → StarSubalgebra ℂ (Matrix (Fin D) (Fin D) ℂ)
  /-- Blocking multiplication at size `n`. -/
  m : ∀ n : ℕ, A n →ₗ[ℂ] A n →ₗ[ℂ] A (2 * n)
  /-- Inclusion map adding one physical site. -/
  iota : ∀ n : ℕ, A n →ₗ[ℂ] A (n + 1)
  /-- `m n` is realized by ambient matrix multiplication. -/
  m_apply : ∀ n : ℕ, ∀ x y : A n,
    ((m n x y : A (2 * n)) : Matrix (Fin D) (Fin D) ℂ) =
      (x : Matrix (Fin D) (Fin D) ℂ) * y
  /-- `iota n` is realized by the ambient inclusion. -/
  iota_apply : ∀ n : ℕ, ∀ x : A n,
    ((iota n x : A (n + 1)) : Matrix (Fin D) (Fin D) ℂ) =
      (x : Matrix (Fin D) (Fin D) ℂ)

namespace AlgebraStructureData

variable {d D : ℕ}

/-- Compatibility between algebra-structure data and an MPO tensor `M`.

The current compatibility condition says that, for every positive blocked size
`n`, the support algebra `A n` is exactly the fixed-point algebra of the
adjoint blocked transfer map. This is a non-vacuous algebra-side condition, but
it is still weaker than the full coefficient statement of Theorem IV.13(ii). -/
def CompatibleWith (data : AlgebraStructureData d D) (M : MPOTensor d D) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
    X ∈ data.A n ↔ (blockedTransferMap M n).adjoint X = X

end AlgebraStructureData

/-- The fixed-point support algebra attached to a trace-preserving MPO tensor and
one of its positive-definite fixed points.

Concretely, this is the fixed-point `StarSubalgebra` of the adjoint transfer map
`(transferMap M).adjoint`, constructed using Wolf Theorem 6.12 for the doubled
MPS tensor `M.toMPSTensor`. -/
def faithfulFixedPointSupportAlgebra
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ) :
    StarSubalgebra ℂ Mat :=
  Kraus.fixedPoints_starSubalgebra (K := M.toMPSTensor) h_tp hρ
    (by simpa [transferMap_eq_toMPSTensor] using hρ_fix)

/-- Membership in `faithfulFixedPointSupportAlgebra` is fixed-point membership
for the adjoint MPO transfer map. -/
theorem mem_faithfulFixedPointSupportAlgebra_iff
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ)
    (X : Mat) :
    X ∈ faithfulFixedPointSupportAlgebra M h_tp hρ hρ_fix ↔
      (transferMap M).adjoint X = X := by
  unfold faithfulFixedPointSupportAlgebra
  rw [Kraus.mem_fixedPoints_starSubalgebra, Kraus.mem_adjointFixedPoints]
  have hAdj : Kraus.adjointMap M.toMPSTensor X = (transferMap M).adjoint X := by
    rw [transferMap_eq_toMPSTensor]
    exact (MPSTensor.transferMap_adjoint_apply_eq_adjointMap (A := M.toMPSTensor) X).symm
  rw [hAdj]

namespace AlgebraStructureData

/-- The stationary algebra tower attached to a faithful fixed point of the MPO
transfer map.

All support algebras are the same `StarSubalgebra`, multiplication is ordinary
matrix multiplication, and the inclusion maps are identities. -/
def stationaryOfFaithfulFixedPoint
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ) :
    AlgebraStructureData d D :=
  let S : StarSubalgebra ℂ Mat := faithfulFixedPointSupportAlgebra M h_tp hρ hρ_fix
  { A := fun _ => S
    m := fun _ => LinearMap.mul ℂ ↥S
    iota := fun _ => LinearMap.id
    m_apply := fun _ _ _ => rfl
    iota_apply := fun _ _ => rfl }

/-- The stationary tower from a faithful fixed point is compatible with any RFP
MPO tensor, because all positive blocked transfer maps agree with `transferMap M`. -/
theorem stationaryOfFaithfulFixedPoint_compatible
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ)
    (hRFP : IsRFP M) :
    (stationaryOfFaithfulFixedPoint M h_tp hρ hρ_fix).CompatibleWith M := by
  intro n hn X
  change X ∈ faithfulFixedPointSupportAlgebra M h_tp hρ hρ_fix ↔
    (blockedTransferMap M n).adjoint X = X
  rw [mem_faithfulFixedPointSupportAlgebra_iff (M := M) h_tp hρ hρ_fix X]
  have hAdj : LinearMap.adjoint ((MPSTensor.transferMap M.toMPSTensor) ^ n) =
      LinearMap.adjoint (MPSTensor.transferMap M.toMPSTensor) := by
    simpa [blockedTransferMap_eq_pow, transferMap_eq_toMPSTensor] using
      congrArg LinearMap.adjoint
        (blockedTransferMap_eq_transferMap_of_isRFP (M := M) hRFP hn)
  simp [blockedTransferMap_eq_pow, transferMap_eq_toMPSTensor, hAdj]

/-- The same stationary tower is compatible whenever the adjoint fixed points of
all positive blocked transfer maps agree with the adjoint fixed points of the
original transfer map. This criterion does not assume `IsRFP M`; it isolates
exactly the stabilization property needed by the current compatibility
predicate. -/
theorem stationaryOfFaithfulFixedPoint_compatible_of_adjointFixedPoints_eq
    (M : MPOTensor d D) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ)
    (hEq : ∀ n : ℕ, 0 < n → ∀ X : Mat,
      (transferMap M).adjoint X = X ↔ (blockedTransferMap M n).adjoint X = X) :
    (stationaryOfFaithfulFixedPoint M h_tp hρ hρ_fix).CompatibleWith M := by
  intro n hn X
  change X ∈ faithfulFixedPointSupportAlgebra M h_tp hρ hρ_fix ↔
    (blockedTransferMap M n).adjoint X = X
  rw [mem_faithfulFixedPointSupportAlgebra_iff (M := M) h_tp hρ hρ_fix X]
  exact hEq n hn X

end AlgebraStructureData

/-- The algebra-structure formulation of MPDO RFP used in this file.

An MPO tensor satisfies `IsRFP_MPDO_via_algebra` when it admits algebra-structure
support data compatible with its blocked adjoint transfer maps. -/
def IsRFP_MPDO_via_algebra (M : MPOTensor d D) : Prop :=
  ∃ data : AlgebraStructureData d D, data.CompatibleWith M

/-- A trace-preserving MPO with a positive-definite fixed point admits a
stationary algebra tower as soon as it is an RFP. -/
theorem isRFP_MPDO_via_algebra_of_isRFP_of_isTP_of_posDef_fixed
    {M : MPOTensor d D} (hRFP : IsRFP M) (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ) :
    IsRFP_MPDO_via_algebra M := by
  refine ⟨AlgebraStructureData.stationaryOfFaithfulFixedPoint M h_tp hρ hρ_fix, ?_⟩
  exact AlgebraStructureData.stationaryOfFaithfulFixedPoint_compatible
    (M := M) (h_tp := h_tp) hρ hρ_fix hRFP

/-- Under the same side hypotheses, the transfer-map fusion formulation implies
this algebra formulation. -/
theorem isRFP_MPDO_via_algebra_of_isRFP_MPDO_via_fusion_of_isTP_of_posDef_fixed
    {M : MPOTensor d D} (hFusion : IsRFP_MPDO_via_fusion M)
    (h_tp : Kraus.IsTP M.toMPSTensor) {ρ : Mat} (hρ : ρ.PosDef)
    (hρ_fix : transferMap M ρ = ρ) :
    IsRFP_MPDO_via_algebra M :=
  isRFP_MPDO_via_algebra_of_isRFP_of_isTP_of_posDef_fixed
    (M := M) (isRFP_of_isRFP_MPDO_via_fusion hFusion) h_tp hρ hρ_fix

/-- The current algebra-side predicate also holds whenever the blocked adjoint
fixed-point spaces stabilize across all positive powers. This extracts exactly
what the present compatibility relation can see, without asserting the fusion /
idempotence conclusion. -/
theorem isRFP_MPDO_via_algebra_of_adjointFixedPoints_eq_of_isTP_of_posDef_fixed
    {M : MPOTensor d D} (h_tp : Kraus.IsTP M.toMPSTensor)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : transferMap M ρ = ρ)
    (hEq : ∀ n : ℕ, 0 < n → ∀ X : Mat,
      (transferMap M).adjoint X = X ↔ (blockedTransferMap M n).adjoint X = X) :
    IsRFP_MPDO_via_algebra M := by
  refine ⟨AlgebraStructureData.stationaryOfFaithfulFixedPoint M h_tp hρ hρ_fix, ?_⟩
  exact
    AlgebraStructureData.stationaryOfFaithfulFixedPoint_compatible_of_adjointFixedPoints_eq
      (M := M) (h_tp := h_tp) hρ hρ_fix hEq

namespace AlgebraStructureData

/-- A chosen finite index set for coordinates on the blocked support algebra `A n`. -/
abbrev BlockedIndex (data : AlgebraStructureData d D) (n : ℕ) :=
  Module.Basis.ofVectorSpaceIndex ℂ (data.A n)

/-- The coordinate space attached to the blocked support algebra `A n`. -/
abbrev BlockedCoefficients (data : AlgebraStructureData d D) (n : ℕ) :=
  BlockedIndex data n → ℂ

/-- A chosen basis for the blocked support algebra `A n`. -/
noncomputable def blockedBasis (data : AlgebraStructureData d D) (n : ℕ) :
    Module.Basis (BlockedIndex data n) ℂ (data.A n) :=
  Module.Basis.ofVectorSpace ℂ (data.A n)

/-- Coordinates of a blocked algebra element in the chosen basis of `A n`. -/
noncomputable def toBlockedCoefficients (data : AlgebraStructureData d D) (n : ℕ) :
    data.A n ≃ₗ[ℂ] BlockedCoefficients data n :=
  (data.blockedBasis n).equivFun

/-- Reconstruct a blocked algebra element from its coefficient family. -/
noncomputable def reconstructFromBlockedCoefficients
    (data : AlgebraStructureData d D) (n : ℕ) :
    BlockedCoefficients data n →ₗ[ℂ] data.A n :=
  (data.toBlockedCoefficients n).symm.toLinearMap

@[simp] theorem toBlockedCoefficients_reconstructFromBlockedCoefficients
    (data : AlgebraStructureData d D) (n : ℕ) (a : BlockedCoefficients data n) :
    data.toBlockedCoefficients n (data.reconstructFromBlockedCoefficients n a) = a :=
  (data.toBlockedCoefficients n).apply_symm_apply a

@[simp] theorem reconstructFromBlockedCoefficients_toBlockedCoefficients
    (data : AlgebraStructureData d D) (n : ℕ) (x : data.A n) :
    data.reconstructFromBlockedCoefficients n (data.toBlockedCoefficients n x) = x :=
  (data.toBlockedCoefficients n).symm_apply_apply x

/-- The chosen basis reconstructs every blocked coefficient family by a finite sum. -/
theorem reconstructFromBlockedCoefficients_apply
    (data : AlgebraStructureData d D) (n : ℕ) (a : BlockedCoefficients data n) :
    data.reconstructFromBlockedCoefficients n a =
      ∑ i, a i • data.blockedBasis n i := by
  rw [reconstructFromBlockedCoefficients, toBlockedCoefficients]
  exact (data.blockedBasis n).equivFun_symm_apply a

/-- Ambient-matrix version of `reconstructFromBlockedCoefficients_apply`. -/
theorem coe_reconstructFromBlockedCoefficients_apply
    (data : AlgebraStructureData d D) (n : ℕ) (a : BlockedCoefficients data n) :
    ((data.reconstructFromBlockedCoefficients n a : data.A n) : Mat) =
      ∑ i, a i • ((data.blockedBasis n i : data.A n) : Mat) := by
  rw [reconstructFromBlockedCoefficients_apply (data := data) (n := n) (a := a)]
  simp

/-- Coordinates of an ambient matrix already known to lie in `A n`. -/
noncomputable def toBlockedCoefficientsOfMem
    (data : AlgebraStructureData d D) (n : ℕ) (X : Mat) (hX : X ∈ data.A n) :
    BlockedCoefficients data n :=
  data.toBlockedCoefficients n ⟨X, hX⟩

/-- Reconstructing the coefficients of a matrix in `A n` recovers that matrix. -/
@[simp] theorem reconstructFromBlockedCoefficients_of_mem
    (data : AlgebraStructureData d D) (n : ℕ) (X : Mat) (hX : X ∈ data.A n) :
    ((data.reconstructFromBlockedCoefficients n
      (data.toBlockedCoefficientsOfMem n X hX) : data.A n) : Mat) = X :=
  congrArg (fun x : data.A n => (x : Mat))
    (reconstructFromBlockedCoefficients_toBlockedCoefficients
      (data := data) (n := n) (x := ⟨X, hX⟩))

/-- Coordinates of an adjoint blocked fixed point, extracted through a compatible
algebra tower. -/
noncomputable def toBlockedCoefficientsOfFixedPoint
    (data : AlgebraStructureData d D) {M : MPOTensor d D}
    (hCompat : data.CompatibleWith M) {n : ℕ} (hn : 0 < n) (X : Mat)
    (hX : (blockedTransferMap M n).adjoint X = X) :
    BlockedCoefficients data n :=
  data.toBlockedCoefficientsOfMem n X ((hCompat n hn X).2 hX)

/-- Reconstructing the extracted coefficients of an adjoint blocked fixed point
recovers the original matrix. -/
@[simp] theorem reconstructFromBlockedCoefficients_of_fixedPoint
    (data : AlgebraStructureData d D) {M : MPOTensor d D}
    (hCompat : data.CompatibleWith M) {n : ℕ} (hn : 0 < n) (X : Mat)
    (hX : (blockedTransferMap M n).adjoint X = X) :
    ((data.reconstructFromBlockedCoefficients n
      (data.toBlockedCoefficientsOfFixedPoint hCompat hn X hX) : data.A n) : Mat) = X := by
  rw [toBlockedCoefficientsOfFixedPoint]
  exact reconstructFromBlockedCoefficients_of_mem
    (data := data) (n := n) (X := X) ((hCompat n hn X).2 hX)

/-- Any coefficient family reconstructed inside a compatible algebra tower is fixed by the
adjoint blocked transfer map. -/
theorem adjoint_blockedTransferMap_reconstructFromBlockedCoefficients_eq
    (data : AlgebraStructureData d D) {M : MPOTensor d D}
    (hCompat : data.CompatibleWith M) {n : ℕ} (hn : 0 < n)
    (a : BlockedCoefficients data n) :
    (blockedTransferMap M n).adjoint
        (((data.reconstructFromBlockedCoefficients n a : data.A n) : Mat)) =
      (((data.reconstructFromBlockedCoefficients n a : data.A n) : Mat)) :=
  (hCompat n hn _).1 (data.reconstructFromBlockedCoefficients n a).property

/-- The coefficient family of the blocked product of two chosen basis elements. -/
noncomputable def blockedStructureCoefficients
    (data : AlgebraStructureData d D) (n : ℕ)
    (i j : BlockedIndex data n) :
    BlockedCoefficients data (2 * n) :=
  data.toBlockedCoefficients (2 * n) (data.m n (data.blockedBasis n i) (data.blockedBasis n j))

/-- The multiplication coefficients reconstruct the product of two basis elements
in `A (2 * n)`. -/
@[simp] theorem reconstructFromBlockedStructureCoefficients
    (data : AlgebraStructureData d D) (n : ℕ)
    (i j : BlockedIndex data n) :
    data.reconstructFromBlockedCoefficients (2 * n)
        (data.blockedStructureCoefficients n i j) =
      data.m n (data.blockedBasis n i) (data.blockedBasis n j) := by
  simp [blockedStructureCoefficients]

/-- Ambient-matrix form of the blocked multiplication reconstruction formula. -/
theorem coe_mul_eq_sum_blockedStructureCoefficients
    (data : AlgebraStructureData d D) (n : ℕ)
    (i j : BlockedIndex data n) :
    ((data.m n (data.blockedBasis n i) (data.blockedBasis n j) : data.A (2 * n)) : Mat) =
      ∑ k, data.blockedStructureCoefficients n i j k •
        ((data.blockedBasis (2 * n) k : data.A (2 * n)) : Mat) := by
  simpa [reconstructFromBlockedStructureCoefficients] using
    coe_reconstructFromBlockedCoefficients_apply
      (data := data) (n := 2 * n) (a := data.blockedStructureCoefficients n i j)

/-- The coefficient family of the inclusion image of a chosen basis element. -/
noncomputable def blockedInclusionCoefficients
    (data : AlgebraStructureData d D) (n : ℕ) (i : BlockedIndex data n) :
    BlockedCoefficients data (n + 1) :=
  data.toBlockedCoefficients (n + 1) (data.iota n (data.blockedBasis n i))

/-- The inclusion coefficients reconstruct the ambient inclusion of a basis element. -/
@[simp] theorem reconstructFromBlockedInclusionCoefficients
    (data : AlgebraStructureData d D) (n : ℕ) (i : BlockedIndex data n) :
    data.reconstructFromBlockedCoefficients (n + 1)
        (data.blockedInclusionCoefficients n i) =
      data.iota n (data.blockedBasis n i) := by
  simp [blockedInclusionCoefficients]

/-- Ambient-matrix form of the blocked inclusion reconstruction formula. -/
theorem coe_iota_eq_sum_blockedInclusionCoefficients
    (data : AlgebraStructureData d D) (n : ℕ) (i : BlockedIndex data n) :
    ((data.iota n (data.blockedBasis n i) : data.A (n + 1)) : Mat) =
      ∑ k, data.blockedInclusionCoefficients n i k •
        ((data.blockedBasis (n + 1) k : data.A (n + 1)) : Mat) := by
  simpa [reconstructFromBlockedInclusionCoefficients] using
    coe_reconstructFromBlockedCoefficients_apply
      (data := data) (n := n + 1) (a := data.blockedInclusionCoefficients n i)

end AlgebraStructureData

/-- The algebra-structure RFP predicate forces every adjoint fixed point of the
blocked transfer map to be an adjoint fixed point of the unblocked transfer
map.

Concretely, compatibility at size `n` places `X` in `data.A n`; the inclusion
`data.iota n` lifts `X` into `data.A (n + 1)`, whence compatibility at size
`n + 1` yields `(blockedTransferMap M (n + 1)).adjoint X = X`. Rewriting
`blockedTransferMap M (n + 1) = blockedTransferMap M n ∘ₗ transferMap M`
through `pow_succ` and applying `LinearMap.adjoint_comp` then extracts
`(transferMap M).adjoint X = X`.

This is the strongest consequence available from the current
`IsRFP_MPDO_via_algebra` predicate: it excludes *finite-order*
(root-of-unity) peripheral eigenvalues of `(transferMap M).adjoint`, since
any such eigenvalue would produce a blocked adjoint fixed point that is not
fixed by the unblocked adjoint. It does not exclude unit-modulus eigenvalues
of irrational phase, and is therefore not enough to force `transferMap M`
to be idempotent. See the module docstring for the blocker on the converse
algebra-to-fusion implication. -/
theorem adjoint_transferMap_apply_of_isRFP_MPDO_via_algebra
    {M : MPOTensor d D} (hAlg : IsRFP_MPDO_via_algebra M)
    {n : ℕ} (hn : 0 < n) {X : Mat}
    (hX : (blockedTransferMap M n).adjoint X = X) :
    (transferMap M).adjoint X = X := by
  obtain ⟨data, hCompat⟩ := hAlg
  have hXn : X ∈ data.A n := (hCompat n hn X).2 hX
  have hXsuc : X ∈ data.A (n + 1) := by
    have hι : ((data.iota n ⟨X, hXn⟩ : data.A (n + 1)) : Mat) = X := by
      simpa using data.iota_apply n ⟨X, hXn⟩
    rw [← hι]
    exact (data.iota n ⟨X, hXn⟩).property
  have hXsucFix : (blockedTransferMap M (n + 1)).adjoint X = X :=
    (hCompat (n + 1) (Nat.succ_pos n) X).1 hXsuc
  have hPow : blockedTransferMap M (n + 1) =
      blockedTransferMap M n ∘ₗ transferMap M := by
    simp only [blockedTransferMap_eq_pow, pow_succ, Module.End.mul_eq_comp]
  have hAdj : (blockedTransferMap M (n + 1)).adjoint X =
      (transferMap M).adjoint X := by
    rw [hPow, LinearMap.adjoint_comp, LinearMap.comp_apply, hX]
  rw [hAdj] at hXsucFix
  exact hXsucFix

/-- Reverse inclusion for the adjoint fixed-point comparison: any adjoint fixed
point of `transferMap M` is an adjoint fixed point of every blocked transfer
map `blockedTransferMap M n`.

Combined with `adjoint_transferMap_apply_of_isRFP_MPDO_via_algebra`, this
establishes the fixed-point equality
`Fix((blockedTransferMap M n).adjoint) = Fix((transferMap M).adjoint)` at every
positive blocking size `n` under `IsRFP_MPDO_via_algebra`. The proof is a
simple induction using `blockedTransferMap_eq_pow` and `LinearMap.adjoint_comp`,
and does not require the algebra-structure data. -/
theorem adjoint_blockedTransferMap_apply_of_adjoint_transferMap_apply
    {M : MPOTensor d D} (n : ℕ) {X : Mat}
    (hX : (transferMap M).adjoint X = X) :
    (blockedTransferMap M n).adjoint X = X := by
  induction n with
  | zero =>
      simp [blockedTransferMap_eq_pow, Module.End.one_eq_id]
  | succ k ih =>
      have hPow : blockedTransferMap M (k + 1) =
          blockedTransferMap M k ∘ₗ transferMap M := by
        simp only [blockedTransferMap_eq_pow, pow_succ, Module.End.mul_eq_comp]
      rw [hPow, LinearMap.adjoint_comp, LinearMap.comp_apply, ih, hX]

/-! ### Diagonal $\chi$-matrices and the trace-power formula

The paper arXiv:1606.00608 (CPGSV17), Theorem IV.13(ii) asserts that the
structure coefficients $c_{\alpha,\beta,\gamma}^{(L)}$ of the blocked MPDO
support algebra have the form
$c_{\alpha,\beta,\gamma}^{(L)} = \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^{L})$
for a family of diagonal matrices $\chi_{\alpha,\beta,\gamma}$ with positive
entries. This subsection represents those diagonal matrices explicitly
and states the trace-power identity. -/

/-- A family of diagonal matrices `χ_{α,β,γ}` indexed by ordered triples drawn
from a common index type `I`. The diagonal size `dim α β γ` is allowed to
depend on the triple, and `entry α β γ` gives the diagonal entries as complex
numbers.

In the RFP characterization of [CPGSV17, Thm IV.13(ii)] the index type `I`
collects the BNT labels `α, β, γ`, and every `χ_{α,β,γ}` is a diagonal matrix
with positive real entries. Positivity is *not* part of this structure: it is
supplied separately through `PosEntries` so that the bare data can be used in
intermediate constructions. -/
structure DiagonalChiFamily (I : Type*) where
  /-- Size of the diagonal matrix `χ_{α,β,γ}` — the cardinality of its index
  set `Fin _`, not the linear-algebraic rank. -/
  dim : I → I → I → ℕ
  /-- Diagonal entries of `χ_{α,β,γ}`, in order. -/
  entry : ∀ α β γ : I, Fin (dim α β γ) → ℂ

namespace DiagonalChiFamily

variable {I : Type*} (χ : DiagonalChiFamily I)

/-- The underlying diagonal matrix `χ_{α,β,γ}` on the index set `Fin (dim α β γ)`. -/
noncomputable def matrix (α β γ : I) :
    Matrix (Fin (χ.dim α β γ)) (Fin (χ.dim α β γ)) ℂ :=
  Matrix.diagonal (χ.entry α β γ)

/-- The trace-power coefficient `∑_k (χ_{α,β,γ,k})^L`. -/
noncomputable def tracePowerCoeff (α β γ : I) (L : ℕ) : ℂ :=
  ∑ k, (χ.entry α β γ k) ^ L

/-- The $L$-th power of `χ_{α,β,γ}` is again diagonal, with entries
`(χ_{α,β,γ,k})^L`. -/
theorem matrix_pow (α β γ : I) (L : ℕ) :
    χ.matrix α β γ ^ L = Matrix.diagonal fun k => (χ.entry α β γ k) ^ L := by
  simp [matrix, Matrix.diagonal_pow]

/-- Trace-power identity: `tr(χ_{α,β,γ}^L) = ∑_k (χ_{α,β,γ,k})^L`, i.e. the
trace of the $L$-th matrix power matches `tracePowerCoeff`. -/
theorem trace_matrix_pow (α β γ : I) (L : ℕ) :
    (χ.matrix α β γ ^ L).trace = χ.tracePowerCoeff α β γ L := by
  simp [matrix_pow, Matrix.trace_diagonal, tracePowerCoeff]

/-- Predicate asserting that every entry of `χ_{α,β,γ}` is a positive real
number, matching the positivity hypothesis of [CPGSV17, Thm IV.13(ii)].
Under the scoped `ComplexOrder` instance (opened at the top of the file), a
strict inequality `0 < z` on `ℂ` is equivalent to `0 < z.re ∧ z.im = 0`. -/
def PosEntries : Prop :=
  ∀ α β γ : I, ∀ k : Fin (χ.dim α β γ), 0 < χ.entry α β γ k

end DiagonalChiFamily

/-- *Trace-power compatibility* between an abstract structure-coefficient family
`c L α β γ` and a diagonal `χ` family: for every blocking size `L` and every
triple `(α, β, γ)`, the structure coefficient `c L α β γ` equals the trace-power
coefficient `χ.tracePowerCoeff α β γ L = ∑_k (χ_{α,β,γ,k})^L` of `χ`.

The trace-power coefficient is equal to the trace of the `L`-th matrix power
`tr(χ_{α,β,γ}^L)` via `DiagonalChiFamily.trace_matrix_pow`, but that identity is
not definitional; the predicate is stated in terms of `tracePowerCoeff` to keep
the right-hand side a plain finite sum. The trace formulation
`c L α β γ = (χ.matrix α β γ ^ L).trace` is then available through
`HasChiTracePowerForm.eq_trace_matrix_pow`.

This is the Lean-level form of the target identity of
[CPGSV17, Thm IV.13(ii)] for the blocked MPDO structure coefficients. It is a
*binary* predicate on the pair `(c, χ)` rather than an existential in `χ`, so
that callers can carry a specific witness `χ` around explicitly; an
existential version `∃ χ, HasChiTracePowerForm c χ` is available on demand. -/
def HasChiTracePowerForm {I : Type*}
    (c : ℕ → I → I → I → ℂ) (χ : DiagonalChiFamily I) : Prop :=
  ∀ L : ℕ, ∀ α β γ : I, c L α β γ = χ.tracePowerCoeff α β γ L

/-- Convenience reformulation: under trace-power compatibility, the
structure coefficient at size `L` equals the trace of the `L`-th matrix power of
the corresponding `χ`. -/
theorem HasChiTracePowerForm.eq_trace_matrix_pow {I : Type*}
    {c : ℕ → I → I → I → ℂ} {χ : DiagonalChiFamily I}
    (h : HasChiTracePowerForm c χ) (L : ℕ) (α β γ : I) :
    c L α β γ = (χ.matrix α β γ ^ L).trace := by
  rw [h L α β γ, χ.trace_matrix_pow]

end MPOTensor

end
