/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalFormOfCanonicalFormII
import TNLean.MPS.MPU.Equivalence
import TNLean.MPS.MPU.Examples.ShiftSwap
import TNLean.MPS.MPU.Examples.SwapPath
import TNLean.MPS.MPU.Examples.ShiftPublicIndex
import TNLean.MPS.MPU.AdjointSimpleContraction
import TNLean.MPS.MPU.TensorProductCanonicalForm
import TNLean.MPS.MPDO.SectorEtaPositivity
import TNLean.MPS.MPDO.BondSimilarity

/-!
# The two shift products are strictly equivalent

Let `T` be the right shift on `ℂ^d`. The tensors `Q₂ = T† ⊗ T` and `Q₃ = T ⊗ T†` of
arXiv:1703.09188, eq. (58), lines 1980--2001, are in canonical form and strictly equivalent.
The path from `Q₂` to `Q₃` runs in two steps through matrix product unitaries of bond dimension
`d²`. First the physical legs are conjugated along the continuous unitary path `S(x)` from the
identity to the factor swap `S`; this preserves the MPU property because the periodic operators
are conjugated by `S(x)^{⊗N}`. Then the bond space is conjugated along the same path; this leaves
every periodic operator unchanged by cyclicity of the trace. The endpoint is `Q₃`, since the
letters of `Q₃` are the sitewise-exchanged letters of `Q₂` conjugated by `S` on the bond.

The source proves the analogous statement for the ancilla-extended tensors by the physical path
alone (arXiv:1703.09188, lines 2138--2151), because there the third tensor is defined as the
sitewise exchange of the second; the bond step is added for the chapter's `Q₃ = T ⊗ T†`
(chapter Example 7.9, "Two strictly equivalent shifts").

## Main results

* `MPOTensor.IsMPU.conjugatePhysical`: conjugating the physical legs by a unitary preserves the
  MPU property.
* `MPOTensor.continuous_conjugatePhysical`: physical conjugation is continuous.
* `MPOTensor.conjugatePhysical_permMatrix`: conjugation by a permutation matrix relabels the
  physical legs.
* `MPOTensor.IsMPU.bondConj`, `MPOTensor.continuous_bondConj`: unitary conjugation of the bond.
* `MPOTensor.shiftExampleU₂_isMPUCanonicalForm`, `MPOTensor.shiftExampleU₃_isMPUCanonicalForm`.
* `MPOTensor.shiftExampleU₂_strictlyEquivalent_shiftExampleU₃`.
-/

open scoped Matrix
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-! ### Physical conjugation -/

/-- The sitewise power `u^{⊗N}` of a one-site matrix, in configuration coordinates. -/
private noncomputable def chainPower (N : ℕ) (u : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  Matrix.of fun σ σ' => ∏ n, u (σ n) (σ' n)

private theorem chainPower_mul (N : ℕ) (u v : Matrix (Fin d) (Fin d) ℂ) :
    chainPower N (u * v) = chainPower N u * chainPower N v := by
  ext a c
  simp only [Matrix.mul_apply, chainPower, Matrix.of_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

private theorem chainPower_one (N : ℕ) :
    chainPower N (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext a b
  simp only [chainPower, Matrix.of_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨x, hx⟩ := Function.ne_iff.mp hab
    simp only [hab, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

private theorem chainPower_conjTranspose (N : ℕ) (u : Matrix (Fin d) (Fin d) ℂ) :
    chainPower N uᴴ = (chainPower N u)ᴴ := by
  ext a b
  simp [chainPower, Matrix.conjTranspose_apply, star_prod]

private theorem chainPower_mem_unitaryGroup (N : ℕ) {u : Matrix (Fin d) (Fin d) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    chainPower N u ∈ Matrix.unitaryGroup (Fin N → Fin d) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, ← chainPower_conjTranspose,
    ← chainPower_mul, ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hu, chainPower_one]

/-- Physical conjugation by a unitary preserves the MPU property: the periodic operator of the
conjugated tensor is `u^{⊗N} U^{(N)} (u^{⊗N})†`.

Source: arXiv:1703.09188, lines 2138--2151 (the path `S(x)` acting on the physical legs);
chapter Example 7.9. -/
theorem IsMPU.conjugatePhysical {U : MPOTensor d D} (hU : IsMPU U)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    IsMPU (conjugatePhysical U u) := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  rw [mpo_conjugatePhysical_eq]
  have hP := chainPower_mem_unitaryGroup N hu
  exact mul_mem (mul_mem hP (hU N hN)) (Unitary.star_mem hP)

/-- Physical conjugation is continuous in the conjugating matrix: every entry of every letter
is a polynomial in the entries of the matrix and their conjugates.

Source: arXiv:1703.09188, lines 2138--2151; chapter Example 7.9. -/
theorem continuous_conjugatePhysical (U : MPOTensor d D) :
    Continuous fun u : Matrix (Fin d) (Fin d) ℂ => conjugatePhysical U u := by
  refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun β =>
    continuous_pi fun α => ?_
  exact ((continuous_id.matrix_mul continuous_const).matrix_mul
    continuous_id.matrix_conjTranspose).matrix_elem i j

/-- Physical conjugation by the identity is trivial. -/
theorem conjugatePhysical_one (U : MPOTensor d D) : conjugatePhysical U 1 = U := by
  funext i j
  ext β α
  simp [conjugatePhysical, physicalSlice]

/-- Physical conjugation by the permutation matrix of `σ` relabels both physical legs by `σ`.

Source: arXiv:1703.09188, lines 2138--2151 (the swap `S` exchanges the two spins of a site);
chapter Example 7.9. -/
theorem conjugatePhysical_permMatrix (U : MPOTensor d D) (σ : Equiv.Perm (Fin d)) :
    conjugatePhysical U (σ.permMatrix ℂ) = reindexPhysical σ U := by
  funext i j
  ext β α
  simp [conjugatePhysical, physicalSlice, reindexPhysical, Matrix.mul_apply,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.symm_apply_eq]

/-! ### Bond conjugation -/

/-- Bond conjugation by a unitary preserves the MPU property, since it leaves every periodic
operator unchanged.

Source: arXiv:1703.09188, Theorem `FundamentalMPU`, lines 624--648 (the "if" direction);
chapter Example 7.9. -/
theorem IsMPU.bondConj {U : MPOTensor d D} (hU : IsMPU U)
    (z : Matrix (Fin D) (Fin D) ℂ) (hz : z ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    IsMPU (fun i j => z * U i j * zᴴ) := by
  intro N hN
  rw [← mpo_eq_of_conj (M := U) (G := z) (H := zᴴ) (mem_unitaryGroup_iff.mp hz)
    (mem_unitaryGroup_iff'.mp hz) (fun _ _ => rfl) N]
  exact hU N hN

/-- Bond conjugation is continuous in the conjugating matrix.

Source: chapter Example 7.9. -/
theorem continuous_bondConj (U : MPOTensor d D) :
    Continuous fun z : Matrix (Fin D) (Fin D) ℂ =>
      (fun i j => z * U i j * zᴴ : MPOTensor d D) :=
  continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_conjTranspose

/-! ### The swap path in the coordinates of the shift products -/

private theorem reindex_mem_unitaryGroup {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) {A : Matrix m m ℂ}
    (hA : A ∈ Matrix.unitaryGroup m ℂ) : reindex e e A ∈ Matrix.unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff] at hA ⊢
  rw [star_eq_conjTranspose, conjTranspose_reindex, reindex_apply, reindex_apply,
    submatrix_mul_equiv, ← star_eq_conjTranspose, hA, submatrix_one_equiv]

/-- The swap path `S(x)` on `ℂ^d ⊗ ℂ^d`, in the coordinates `Fin (d * d)`. -/
noncomputable def swapPathFin (d : ℕ) (x : ℝ) : Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  reindex finProdFinEquiv finProdFinEquiv (Matrix.swapPath d x)

/-- Every point of the swap path is unitary. -/
theorem swapPathFin_mem_unitaryGroup (d : ℕ) (x : ℝ) :
    swapPathFin d x ∈ Matrix.unitaryGroup (Fin (d * d)) ℂ :=
  reindex_mem_unitaryGroup _ (Matrix.swapPath_mem_unitaryGroup d x)

/-- The swap path is continuous. -/
theorem continuous_swapPathFin (d : ℕ) : Continuous (swapPathFin d) :=
  (Matrix.continuous_swapPath d).matrix_reindex _ _

/-- The exchange of the two spins of a site, in the coordinates `Fin (d * d)`. -/
def siteSwap (d : ℕ) : Equiv.Perm (Fin (d * d)) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

/-- The endpoint of the swap path is the permutation matrix of the site exchange. -/
theorem swapPathFin_one (d : ℕ) : swapPathFin d 1 = (siteSwap d).permMatrix ℂ := by
  ext a b
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp [swapPathFin, siteSwap, swapMatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    and_comm]

/-- The letters of `Q₃` are the sitewise-exchanged letters of `Q₂` conjugated by the swap on
the bond.

Source: arXiv:1703.09188, eq. (58), lines 1980--2001; chapter Example 7.9. -/
theorem shiftExampleU₃_eq_bondConj (d : ℕ) :
    shiftExampleU₃ d = fun i j => swapPathFin d 1 *
      reindexPhysical (siteSwap d) (shiftExampleU₂ d) i j * (swapPathFin d 1)ᴴ := by
  funext i j
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  have h := congrArg (reindexAlgEquiv ℂ ℂ finProdFinEquiv)
    (shiftExampleU₃_physicalSwap_eq_swapMatrix_mul_shiftExampleU₂_mul_swapMatrix d a₂ a₁ b₂ b₁)
  rw [map_mul, map_mul] at h
  simp only [coe_reindexAlgEquiv, reindex_apply, submatrix_submatrix, Equiv.symm_symm,
    Equiv.self_comp_symm, submatrix_id_id] at h
  simpa [swapPathFin, siteSwap, reindexPhysical, swapMatrix_conjTranspose] using h

/-! ### The two shift products -/

/-- `Q₂ = T† ⊗ T` is in canonical form.

Source: arXiv:1703.09188, eq. (58), lines 1980--2001, and canonical form, lines 259--267;
chapter Example 7.9. -/
theorem shiftExampleU₂_isMPUCanonicalForm (d : ℕ) [NeZero d] :
    MPSTensor.IsMPUCanonicalForm (shiftExampleU₂ d).toMPSTensor := by
  obtain ⟨h, -⟩ := rightShiftTensor_exists_canonicalFormII d
  exact (h.physicalAdjointTensor.tensorProduct h).isMPUCanonicalForm

/-- `Q₃ = T ⊗ T†` is in canonical form.

Source: arXiv:1703.09188, eq. (58), lines 1980--2001, and canonical form, lines 259--267;
chapter Example 7.9. -/
theorem shiftExampleU₃_isMPUCanonicalForm (d : ℕ) [NeZero d] :
    MPSTensor.IsMPUCanonicalForm (shiftExampleU₃ d).toMPSTensor := by
  obtain ⟨h, -⟩ := rightShiftTensor_exists_canonicalFormII d
  exact (h.tensorProduct h.physicalAdjointTensor).isMPUCanonicalForm

/-- **Two strictly equivalent shifts.** `Q₂ = T† ⊗ T` and `Q₃ = T ⊗ T†` are strictly
equivalent at the common bond dimension `d²`: the physical path `x ↦ S(x) · Q₂` followed by the
bond path `x ↦ S(x) (S · Q₂) S(x)†` stays among matrix product unitaries.

Source: arXiv:1703.09188, eq. (58), lines 1980--2001, and the proposition on the symmetry
phases of the ancilla-dressed U₂, U₃, lines 2138--2151; chapter Example 7.9, "Two strictly
equivalent shifts". -/
theorem shiftExampleU₂_strictlyEquivalent_shiftExampleU₃ (d : ℕ) [NeZero d] :
    StrictlyEquivalent (shiftExampleU₂ d) (shiftExampleU₃ d) rfl := by
  refine StrictlyEquivalent.of_fixedBond rfl (shiftExampleU₂_isMPUCanonicalForm d)
    (shiftExampleU₃_isMPUCanonicalForm d) ?_
  have hQ₂ := shiftExampleU₂_isMPU d
  have hP : IsMPU (conjugatePhysical (shiftExampleU₂ d) (swapPathFin d 1)) :=
    hQ₂.conjugatePhysical _ (swapPathFin_mem_unitaryGroup d 1)
  refine JoinedIn.trans (y := conjugatePhysical (shiftExampleU₂ d) (swapPathFin d 1)) ?_ ?_
  · refine JoinedIn.ofLine
      (f := fun x => conjugatePhysical (shiftExampleU₂ d) (swapPathFin d x))
      ((continuous_conjugatePhysical _).comp (continuous_swapPathFin d)).continuousOn
      ?_ rfl ?_
    · simp only [swapPathFin, Matrix.swapPath_zero, reindex_apply, submatrix_one_equiv,
        conjugatePhysical_one, finCongr_refl, Equiv.refl_symm]
      rfl
    · rintro _ ⟨x, -, rfl⟩
      exact hQ₂.conjugatePhysical _ (swapPathFin_mem_unitaryGroup d x)
  · refine JoinedIn.ofLine
      (f := fun x => (fun i j => swapPathFin d x *
        conjugatePhysical (shiftExampleU₂ d) (swapPathFin d 1) i j * (swapPathFin d x)ᴴ :
          MPOTensor (d * d) (d * d)))
      ((continuous_bondConj _).comp (continuous_swapPathFin d)).continuousOn ?_ ?_ ?_
    · funext i j
      simp [swapPathFin]
    · rw [shiftExampleU₃_eq_bondConj, swapPathFin_one, conjugatePhysical_permMatrix]
    · rintro _ ⟨x, -, rfl⟩
      exact hP.bondConj _ (swapPathFin_mem_unitaryGroup d x)

end MPOTensor
