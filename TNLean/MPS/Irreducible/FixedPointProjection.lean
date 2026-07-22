/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Transfer
import TNLean.Algebra.HermitianHelpers
import TNLean.Algebra.PosSemidefSupport
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.FixedPoint.SupportInvariance

import Mathlib.Analysis.Matrix.Spectrum

import Mathlib.Tactic.NoncommRing

-- For FixedPointSplit theorems (exists_twoBlock_decomp_of_lowerZero etc.)
import TNLean.MPS.Structure.InvariantSubspaceDecomp

/-!
# Fixed point ⇒ invariant support projection (MPS transfer map)

This module implements the fixed-point-to-support-projection step used in
canonical-form existence proofs for matrix product states.

If $\rho \succeq 0$ is a fixed point of the transfer map
$$E_A(X) = \sum_i A_i X A_i^\dagger,$$
then the support projection $P = \mathrm{supp}(\rho)$ is invariant under each Kraus operator:
$$(1-P) A_i P = 0.$$

In Pérez-García, Verstraete, Wolf, and Cirac, this is the first half of the
singular-fixed-point case in the proof of Theorem Th:TIcanonical: lines 771–774
introduce the spectral support projection $P_R$, and lines 775–783 prove the
invariant relation by a positivity contradiction.  The finite-ring trace split
is the subsequent step, lines 785–815, and is handled by the
invariant-subspace decomposition results.  Thus the results here should be used
before, not instead of, the source trace-splitting argument.

References:
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 (singular positive fixed point gives an invariant
  support projection)
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ## Fixed point ⇒ invariant support projection -/

/-- If `ρ` is positive semidefinite and fixed by the MPS transfer map, then its
support projection is invariant under every tensor matrix. -/
theorem lowerZero_of_posSemidef_fixedPoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    let P := supportProj (D := D) ρ hρ_psd
    IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
  have hρ_fix' : Kraus.map A ρ = ρ := by
    simpa [Kraus.map, transferMap_apply] using hρ_fix
  simpa [Kraus.stationaryProj, supportProj] using
    (Kraus.lowerZero_of_posSemidef_fixedPoint A ρ hρ_psd hρ_fix')

/-! ## Nontriviality lemmas for the support projection

These lemmas connect the support projection to the nondegeneracy of the original
matrix, and are essential for the "strict dimension decrease" argument used when
iterating the canonical-form splitting step.

References:
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 for the support projection and lines 785–815 for the
  finite-ring trace split whose recursive blocks have smaller dimensions.
* Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608,
  lines 201–217: invariant subspaces are split into diagonal blocks in the
  canonical-form construction.
-/



/-!
## Non-scalar fixed point → singular positive fixed point

The next lemma isolates the second fixed-point split in the proof of
PGVWC07 Theorem `Th:TIcanonical`, lines 819--826.  After a block has been
put in the unital normalization, a non-scalar Hermitian fixed point can be
shifted by its largest eigenvalue to give a positive fixed point which is
singular and nonzero.  The preceding support-projection theorem can then split
the block further.
-/

section NonScalarFixedPoint

variable {d D : ℕ}

private lemma max_shift_not_posDef [Nonempty (Fin D)]
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.IsHermitian) :
    ¬ ((↑(maxEigenvalue hX) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - X).PosDef := by
  classical
  intro h_pd
  set U : Matrix (Fin D) (Fin D) ℂ := ↑hX.eigenvectorUnitary
  have hU_unit : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [U] using Matrix.UnitaryGroup.det_isUnit hX.eigenvectorUnitary
  have h_diag_pd :
      (Matrix.diagonal (fun j => (↑(maxEigenvalue hX - hX.eigenvalues j) : ℂ)) :
        Matrix (Fin D) (Fin D) ℂ).PosDef := by
    have h_pd' := h_pd
    rw [smul_one_sub_hermitian_spectral hX (maxEigenvalue hX)] at h_pd'
    rw [show Uᴴ = star U by simp [Matrix.star_eq_conjTranspose]] at h_pd'
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hU_unit).mp h_pd'
  rw [Matrix.posDef_diagonal_iff] at h_diag_pd
  obtain ⟨i₀, hi₀⟩ := maxEigenvalue_achieved hX
  have := h_diag_pd i₀
  have hzero : maxEigenvalue hX - hX.eigenvalues i₀ = 0 := by
    exact sub_eq_zero.mpr hi₀.symm
  simp [hzero] at this

/-- A non-scalar Hermitian fixed point of a unital MPS transfer map yields a
nonzero singular positive fixed point.

This is the formal fixed-point shift used in Pérez-García, Verstraete, Wolf,
and Cirac, Theorem `Th:TIcanonical`, proof lines 819--826.  The paper writes
`I - λ₁⁻¹ X`; the equivalent scalar-free form used here is
`λ_max I - X`, which avoids a separate sign assumption on the largest
eigenvalue. -/
theorem exists_singular_posSemidef_fixedPoint_of_unital_nonScalar_fixedPoint
    [Nonempty (Fin D)]
    (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (h_unital : transferMap (d := d) (D := D) A 1 = 1)
    (hX_herm : X.IsHermitian)
    (hX_fix : transferMap (d := d) (D := D) A X = X)
    (hX_nonscalar : ¬ ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ transferMap (d := d) (D := D) A ρ = ρ ∧
        ρ ≠ 0 ∧ ¬ ρ.PosDef := by
  classical
  let c : ℝ := maxEigenvalue hX_herm
  let ρ : Matrix (Fin D) (Fin D) ℂ := (↑c : ℂ) • 1 - X
  have hρ_psd : ρ.PosSemidef := by
    simpa [ρ, c] using maxEigenvalue_smul_one_sub_posSemidef hX_herm
  have hρ_not_pd : ¬ ρ.PosDef := by
    simpa [ρ, c] using max_shift_not_posDef (D := D) hX_herm
  have hρ_fix : transferMap (d := d) (D := D) A ρ = ρ := by
    change transferMap (d := d) (D := D) A ((↑c : ℂ) • 1 - X) = (↑c : ℂ) • 1 - X
    rw [map_sub, map_smul, h_unital, hX_fix]
  have hρ_ne : ρ ≠ 0 := by
    intro hρ_zero
    apply hX_nonscalar
    refine ⟨(↑c : ℂ), ?_⟩
    have hsub : (↑c : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) - X = 0 := by
      simpa [ρ] using hρ_zero
    exact (sub_eq_zero.mp hsub).symm
  exact ⟨ρ, hρ_psd, hρ_fix, hρ_ne, hρ_not_pd⟩

end NonScalarFixedPoint

/-!
## Fixed point → 2-block decomposition

This section covers the canonical-form reduction step

> PSD fixed point → invariant support projection → two-block direct sum.

Concretely, if $\rho \succeq 0$ satisfies $E_A(\rho)=\rho$, then the support
projection $P := \mathrm{supp}(\rho)$ is invariant under the Kraus operators `(A i)`, i.e.
`(1 - P) * A i * P = 0`. Applying `exists_twoBlock_decomp_of_lowerZero`, we obtain an
explicit two-block block-diagonal tensor which is MPV-equivalent to `A`.

References:
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 for the support projection and lines 785–815 for the
  finite-ring trace split.
* Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608,
  lines 201–217 for the corresponding
  invariant-subspace block splitting in the canonical-form construction.
-/

/-- If `ρ` is a PSD fixed point of the transfer map, then `A` is MPV-equivalent to a
2-block block-diagonal tensor.

This is just the composition
`lowerZero_of_posSemidef_fixedPoint` + `exists_twoBlock_decomp_of_lowerZero`.
-/
theorem exists_twoBlock_decomp_of_posSemidef_fixedPoint
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ) :
    ∃ (n m : ℕ) (_ : n + m = D)
      (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
      SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  classical
  let P : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hP : IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
    simpa [P] using
      (lowerZero_of_posSemidef_fixedPoint (d := d) (D := D) A ρ hρ_psd hρ_fix)
  exact exists_twoBlock_decomp_of_lowerZero (d := d) (D := D) A P hP.1 hP.2

/-- **Strict dimension decrease**: If `ρ` is a PSD fixed point of the transfer map,
`ρ ≠ 0`, and `ρ` is not positive definite, then `A` is MPV-equivalent to a
two-block block-diagonal tensor where **both** block bond dimensions are
strictly less than `D`.

This is the key recursion step in the canonical form existence proof:
each iteration strictly reduces the bond dimension.

The proof composes:
1. `lowerZero_of_posSemidef_fixedPoint` — support projection is invariant,
2. `supportProj_ne_zero_of_ne_zero` — `P ≠ 0` from `ρ ≠ 0`,
3. `supportProj_ne_one_of_not_posDef` — `P ≠ 1` from `¬ρ.PosDef`,
4. `exists_twoBlock_decomp_of_lowerZero_strict` — strict dimension bounds.

References:
* Pérez-García, Verstraete, Wolf, and Cirac, Theorem Th:TIcanonical,
  proof lines 771–783 for deriving the invariant support projection and
  lines 785–815 for the trace split into two smaller blocks.
* Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608,
  lines 201–217 for the invariant-subspace direct-sum step in the
  canonical-form construction.
-/
theorem exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict
    (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ_psd : ρ.PosSemidef)
    (hρ_fix : transferMap (d := d) (D := D) A ρ = ρ)
    (hρ_ne : ρ ≠ 0)
    (hρ_not_pd : ¬ ρ.PosDef) :
    ∃ n m : ℕ, ∃ _ : n + m = D, n < D ∧ m < D ∧
      ∃ (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
        SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  -- Step 1: obtain the invariant support projection
  let P : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hP_inv : IsOrthogonalProjection P ∧ (∀ i : Fin d, (1 - P) * A i * P = 0) := by
    simpa [P] using
      (lowerZero_of_posSemidef_fixedPoint (d := d) (D := D) A ρ hρ_psd hρ_fix)
  -- Step 2: P ≠ 0 from ρ ≠ 0
  have hP0 : P ≠ 0 := supportProj_ne_zero_of_ne_zero ρ hρ_psd hρ_ne
  -- Step 3: P ≠ 1 from ¬ρ.PosDef
  have hP1 : P ≠ 1 := supportProj_ne_one_of_not_posDef ρ hρ_psd hρ_not_pd
  -- Step 4: apply strict decomposition
  exact exists_twoBlock_decomp_of_lowerZero_strict A P hP_inv.1 hP_inv.2 hP0 hP1

/-- A non-scalar Hermitian fixed point of a unital transfer map gives a strict
two-block decomposition.

This composes the fixed-point shift from PGVWC07 Theorem `Th:TIcanonical`,
lines 819--826, with the support-projection split from lines 771--815.  The
source phrase "fixed point different from the identity" is implemented here as
"non-scalar fixed point", since scalar multiples of the identity are fixed by
every unital linear map and do not produce a nontrivial support projection. -/
theorem exists_twoBlock_decomp_of_unital_nonScalar_fixedPoint
    [Nonempty (Fin D)]
    (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (h_unital : transferMap (d := d) (D := D) A 1 = 1)
    (hX_herm : X.IsHermitian)
    (hX_fix : transferMap (d := d) (D := D) A X = X)
    (hX_nonscalar : ¬ ∃ c : ℂ, X = c • (1 : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ n m : ℕ, ∃ _ : n + m = D, n < D ∧ m < D ∧
      ∃ (A₁ : MPSTensor d n) (A₂ : MPSTensor d m),
        SameMPV₂ A (twoBlockTensor (d := d) (n := n) (m := m) A₁ A₂) := by
  obtain ⟨ρ, hρ_psd, hρ_fix, hρ_ne, hρ_not_pd⟩ :=
    exists_singular_posSemidef_fixedPoint_of_unital_nonScalar_fixedPoint
      (d := d) (D := D) A X h_unital hX_herm hX_fix hX_nonscalar
  exact exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict
    (d := d) (D := D) A ρ hρ_psd hρ_fix hρ_ne hρ_not_pd

end MPSTensor
