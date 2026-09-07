/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.MPDO.CZXTensor

/-!
# The exact CZX operator preserves the blocked GHZ state

arXiv:2502.20257, lines 4660–4670, states that the CZX MPU leaves the GHZ
MPS invariant, with once-blocked sectors $|00\rangle$ and $|11\rangle$.
We use the existing GHZ tensor and physical blocking, transported by the
existing two-site index equivalence to the CZX alphabet ordered as $2a+b$.
The exact CZX operator interchanges the two constant configurations with
phase one. No on-site symmetry, fusion, or classification assertion is made.
-/

noncomputable section

open scoped BigOperators Matrix

namespace MPOTensor.CZX

/-- The actual GHZ tensor blocked once, in the CZX physical order $2a+b$.
Source: arXiv:2502.20257, lines 4660–4670. -/
def blockedGHZTensor : MPSTensor 4 2 :=
  Kraus.reindexPhysical (twoSiteBlockEquiv 2) (MPSTensor.blockTensor MPSTensor.ghzTensor 2)

/-- The two once-blocked GHZ sectors are precisely $|00\rangle$ and
$|11\rangle$, as displayed in arXiv:2502.20257, lines 4660–4670. -/
theorem blockTensor_ghzSectorTensor_apply (x : Fin 2) (i : Fin 4) :
    MPSTensor.blockTensor (MPSTensor.ghzSectorTensor x) 2 (twoSiteBlockEquiv 2 i) =
      if i = finProdFinEquiv (x, x) then 1 else 0 := by
  fin_cases x <;> fin_cases i <;>
    norm_num [MPSTensor.blockTensor, Kraus.blockTensor, twoSiteBlockEquiv,
      Kraus.wordOfBlock, MPSTensor.ghzSectorTensor, finProdFinEquiv, Fin.divNat, Fin.modNat]

private theorem blockedGHZTensor_apply (i : Fin 4) :
    blockedGHZTensor i = Matrix.diagonal (fun x : Fin 2 ↦
      if i = finProdFinEquiv (x, x) then (1 : ℂ) else 0) := by
  fin_cases i <;>
    norm_num [blockedGHZTensor, Kraus.reindexPhysical, MPSTensor.blockTensor,
      Kraus.blockTensor, twoSiteBlockEquiv, Kraus.wordOfBlock,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Pi.single_apply]

private theorem evalWord_blockedGHZTensor {N : ℕ} (s : Fin N → Fin 4) :
    Kraus.evalWord blockedGHZTensor (List.ofFn s) =
      Matrix.diagonal (fun x : Fin 2 ↦ ∏ n,
        if s n = finProdFinEquiv (x, x) then (1 : ℂ) else 0) := by
  induction N with
  | zero => simp [Matrix.diagonal_one]
  | succ N ih =>
    rw [List.ofFn_succ, Kraus.evalWord_cons, blockedGHZTensor_apply, ih,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    simp [Fin.prod_univ_succ]

/-- The MPV of the actual once-blocked GHZ tensor is the sum of the constant
$00$ and $11$ configurations. Source: arXiv:2502.20257, lines 4660–4670. -/
theorem mpv_blockedGHZTensor {N : ℕ} :
    (MPSTensor.mpv blockedGHZTensor : (Fin N → Fin 4) → ℂ) =
      Pi.single (fun _ ↦ 0) 1 + Pi.single (fun _ ↦ 3) 1 := by
  funext s
  rw [MPSTensor.mpv, MPSTensor.coeff, evalWord_blockedGHZTensor, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two, Fintype.prod_boole, Pi.add_apply, Pi.single_apply]
  have h0 : finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) = (0 : Fin 4) := rfl
  have h3 : finProdFinEquiv ((1 : Fin 2), (1 : Fin 2)) = (3 : Fin 4) := rfl
  rw [h0, h3]
  simp only [← funext_iff]

private theorem cyclicPhase_ghz_constant {N : ℕ} [NeZero N] (x : Fin 2) :
    (-1 : ℂ) ^ cyclicExponent (fun _ : Fin N ↦ finProdFinEquiv (x, x)) = 1 := by
  have he : ∀ x : Fin 2,
      edgeExponent (finProdFinEquiv (x, x)) (siteBits (finProdFinEquiv (x, x))).1 =
        4 * x.val := by decide
  simp only [cyclicExponent, he, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_comm, pow_mul]
  fin_cases x <;> norm_num

/-- The exact CZX operator leaves the actual once-blocked GHZ MPV invariant
at every positive chain length. The physical indices are transported through
the maintained two-site blocking equivalence, not a numerical cast.
Source: arXiv:2502.20257, lines 4660–4670. -/
theorem mpo_tensor_mulVec_blockedGHZ {N : ℕ} [NeZero N] :
    mpo tensor N *ᵥ (fun s : Fin N → Fin 4 ↦
      MPSTensor.mpv (MPSTensor.blockTensor MPSTensor.ghzTensor 2)
        (fun n ↦ twoSiteBlockEquiv 2 (s n))) =
      (fun s : Fin N → Fin 4 ↦
        MPSTensor.mpv (MPSTensor.blockTensor MPSTensor.ghzTensor 2)
          (fun n ↦ twoSiteBlockEquiv 2 (s n))) := by
  have hv : (fun s : Fin N → Fin 4 ↦
      MPSTensor.mpv (MPSTensor.blockTensor MPSTensor.ghzTensor 2)
        (fun n ↦ twoSiteBlockEquiv 2 (s n))) = MPSTensor.mpv blockedGHZTensor := by
    funext s
    exact (MPSTensor.mpv_reindexPhysical _ _ s).symm
  rw [hv, mpv_blockedGHZTensor, Matrix.mulVec_add, mpo_tensor,
    Matrix.monomial_mulVec_single, Matrix.monomial_mulVec_single]
  have hc0 : complement N (fun _ ↦ 0) = (fun _ ↦ 3) := by
    funext n
    exact show complementSite 0 = 3 from by decide
  have hc3 : complement N (fun _ ↦ 3) = (fun _ ↦ 0) := by
    funext n
    exact show complementSite 3 = 0 from by decide
  rw [hc0, hc3]
  have hp0 := cyclicPhase_ghz_constant (N := N) 0
  have hp3 := cyclicPhase_ghz_constant (N := N) 1
  change (-1 : ℂ) ^ cyclicExponent (fun _ : Fin N ↦ 0) = 1 at hp0
  change (-1 : ℂ) ^ cyclicExponent (fun _ : Fin N ↦ 3) = 1 at hp3
  rw [hp0, hp3, one_smul, one_smul, add_comm]

end MPOTensor.CZX
