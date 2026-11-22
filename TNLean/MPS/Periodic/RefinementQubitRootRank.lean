/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Channel.Schwarz.Closure
import QICLean.Channel.PSDConeAutomorphism.InjectivePositiveMapRank
import QICLean.Kraus.ChoiRankSpan
import TNLean.MPS.Periodic.RootWordSpan
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse

/-!
# Bounded roots for qubit channels

Every qubit channel has Choi rank at most that of each positive power.
Consequently channel divisibility gives refinement for every tensor of bond
dimension two, including singular and reducible transfer maps. This proves
the bond-dimension-two case of arXiv:1708.00029, Theorem 4.1, converse.
The general higher-dimensional singular selection problem remains open;
see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix BigOperators

private abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

private def detPolar : LinearMap.BilinForm ℂ QubitMatrix :=
  LinearMap.mk₂ ℂ
    (fun A B => A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1)
    (by intro A B C; simp only [Matrix.add_apply]; ring)
    (by intro c A B; simp only [Matrix.smul_apply, smul_eq_mul]; ring)
    (by intro A B C; simp only [Matrix.add_apply]; ring)
    (by intro c A B; simp only [Matrix.smul_apply, smul_eq_mul]; ring)

private theorem detPolar_symm (A B : QubitMatrix) : detPolar A B = detPolar B A := by
  simp only [detPolar, LinearMap.mk₂_apply]
  ring

private theorem detPolar_left_nondegenerate (A : QubitMatrix)
    (hA : ∀ B, detPolar A B = 0) : A = 0 := by
  have h00 := hA (Matrix.single 1 1 1)
  have h01 := hA (Matrix.single 1 0 1)
  have h10 := hA (Matrix.single 0 1 1)
  have h11 := hA (Matrix.single 0 0 1)
  simp [detPolar] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using h01
  · simpa using h10
  · simpa using h11

namespace Matrix

/-- An all-singular complex subspace of `2 × 2` matrices has dimension at
most two. Polarization of determinant makes the subspace isotropic for a
nondegenerate bilinear form on a four-dimensional space. This supplies
the low-dimensional root-rank argument for arXiv:1708.00029, Theorem 4.1. -/
theorem finrank_le_two_of_forall_det_eq_zero_fin_two
    (S : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    (hDet : ∀ X ∈ S, X.det = 0) : Module.finrank ℂ S ≤ 2 := by
  have hNondeg : detPolar.Nondegenerate := by
    refine ⟨detPolar_left_nondegenerate, ?_⟩
    intro A hA
    apply detPolar_left_nondegenerate A
    intro B
    rw [detPolar_symm]
    exact hA B
  have hLe : S ≤ detPolar.orthogonal S := by
    intro A hA
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro B hB
    have hAB := hDet (B + A) (S.add_mem hB hA)
    have hA' := hDet A hA
    have hB' := hDet B hB
    simp only [Matrix.det_fin_two, Matrix.add_apply] at hAB hA' hB'
    change B 0 0 * A 1 1 + B 1 1 * A 0 0 - B 0 1 * A 1 0 - B 1 0 * A 0 1 = 0
    linear_combination hAB - hA' - hB'
  have hDim := Submodule.finrank_mono hLe
  have hTotal : Module.finrank ℂ QubitMatrix = 4 := by simp [Module.finrank_matrix]
  rw [LinearMap.BilinForm.finrank_orthogonal hNondeg, hTotal] at hDim
  change Module.finrank ℂ S ≤ 4 - Module.finrank ℂ S at hDim
  omega

end Matrix

private theorem channel_injective_of_choiRank_le_one {D : ℕ}
    {F : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)} (hF : IsChannel F)
    (hRank : Channel.choiRank F ≤ 1) : Function.Injective F := by
  obtain ⟨K, hK⟩ := Channel.hasKrausCard_mono
    (Channel.hasKrausCard_choiRank_of_cp hF.cp) hRank
  have hNorm : (K 0)ᴴ * K 0 = 1 := by
    simpa using kraus_sum_conjTranspose_mul_of_tp K F hK hF.tp
  have hMap (X : Matrix (Fin D) (Fin D) ℂ) : F X = K 0 * X * (K 0)ᴴ := by
    simpa using hK X
  have hInv (X : Matrix (Fin D) (Fin D) ℂ) :
      (K 0)ᴴ * (K 0 * X * (K 0)ᴴ) * K 0 = X := by
    calc
      _ = ((K 0)ᴴ * K 0) * X * ((K 0)ᴴ * K 0) := by noncomm_ring
      _ = X := by simp only [hNorm, Matrix.one_mul, Matrix.mul_one]
  intro X Y hXY
  have h := congrArg (fun Z => (K 0)ᴴ * Z * K 0) hXY
  simpa only [hMap, hInv] using h

namespace Channel

/-- Every qubit channel has Choi rank at most that of every positive
power. No irreducibility or invertibility assumption is needed. This
proves the full bond-dimension-two root-rank step in arXiv:1708.00029,
Theorem 4.1, converse, lines 812--818. -/
theorem choiRank_le_pow_fin_two
    {F : Module.End ℂ (Matrix (Fin 2) (Fin 2) ℂ)} (hF : IsChannel F)
    {p : ℕ} (hp : 0 < p) : choiRank F ≤ choiRank (F ^ p) := by
  by_cases hSmall : choiRank (F ^ p) ≤ 1
  · have hPowInj : Function.Injective (F ^ p) :=
      channel_injective_of_choiRank_le_one ⟨hF.cp.pow p, hF.tp.pow p⟩ hSmall
    have hInj : Function.Injective F := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
      intro X Y hXY
      apply hPowInj
      simp only [pow_succ, Module.End.mul_apply, hXY]
    exact choiRank_le_pow_of_injective hF.cp hInj hp
  by_cases hRank : choiRank F ≤ 2
  · omega
  obtain ⟨r, A, hA, _⟩ := hF.exists_kraus_map_eq_and_normalized
  have hDim : 2 < Module.finrank ℂ (Kraus.wordSpan A 1) := by
    have h := choiRank_mapLM_eq_finrank_wordSpan_one A
    rw [← hA] at h
    omega
  obtain ⟨X, hX, hUnit⟩ : ∃ X ∈ Kraus.wordSpan A 1, IsUnit X := by
    by_contra! hNoUnit
    have hDet (X : QubitMatrix) (hX : X ∈ Kraus.wordSpan A 1) : X.det = 0 := by
      have h := hNoUnit X hX
      rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at h
    have hLe := Matrix.finrank_le_two_of_forall_det_eq_zero_fin_two
      (Kraus.wordSpan A 1) hDet
    omega
  calc
    choiRank F = Module.finrank ℂ (Kraus.wordSpan A 1) := by
      rw [hA, choiRank_mapLM_eq_finrank_wordSpan_one]
    _ ≤ Module.finrank ℂ (Kraus.wordSpan A p) :=
      Kraus.wordSpan_one_finrank_le_of_isUnit_mem_wordSpan_one A hp hX hUnit
    _ = choiRank (Kraus.transferMap (Kraus.blockTensor A p)) := by
      rw [choiRank_mapLM_eq_finrank_wordSpan_one, Kraus.wordSpan_blockTensor_one]
    _ = choiRank (F ^ p) := by rw [MPSTensor.transferMap_blockTensor, hA]

end Channel

namespace MPSTensor

/-- Every tensor of bond dimension two is refinable whenever its transfer
map is channel-divisible. The target may be singular or reducible; no
bounded-root hypothesis is assumed. This proves the bond-dimension-two
case of arXiv:1708.00029, Theorem 4.1, converse. -/
theorem isPRefinable_of_isPDivisibleChannel_fin_two
    {d p : ℕ} (B : MPSTensor d 2) (hp : 0 < p)
    (hDiv : IsPDivisibleChannel (Kraus.transferMap B) p) : IsPRefinable B p := by
  obtain ⟨F, hF, hpow⟩ := hDiv
  have hRank : Channel.choiRank F ≤ d := by
    calc
      Channel.choiRank F ≤ Channel.choiRank (F ^ p) := Channel.choiRank_le_pow_fin_two hF hp
      _ = Channel.choiRank (Kraus.transferMap B) := congrArg Channel.choiRank hpow.symm
      _ ≤ d := Channel.choiRank_le_of_hasKrausCard ⟨B, by intro X; simp⟩
  exact isPRefinable_of_channel_root_hasKrausRankLE B hp F hpow
    ⟨Channel.choiRank F, hRank, Channel.hasKrausCard_choiRank_of_cp hF.cp⟩

end MPSTensor
