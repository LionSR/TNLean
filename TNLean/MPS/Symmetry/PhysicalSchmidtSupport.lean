/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.VaryingBondPhysicalCharacter
import TNLean.MPS.Preparation.BlockedPolar
import QICLean.Algebra.MatrixRankClosed

/-!
# Physical Schmidt supports near a change of minimal bond dimension

For a one-site injective tensor, the periodic two-site vector has Schmidt
rank equal to the square of the bond dimension. Continuity of the physical
ground vectors therefore makes their minimal injective bond dimensions
lower semicontinuous. These are finite-chain consequences in the context of
arXiv:1010.3732, Section II.F.2, lines 1059–1068, and Appendix C,
lines 2653–2717. They do not identify a single-bond canonical support or
derive continuous canonical data from a physical gap.
-/

open scoped Matrix Topology

namespace MPSTensor

/-- The coefficient matrix for the one-site cut of the periodic two-site
vector. Source context: arXiv:1010.3732, Section II.F.2 and Appendix C. -/
def twoSiteSchmidtMatrix {d D : ℕ} (A : MPSTensor d D) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => Matrix.trace (A i * A j)

private theorem twoSiteSchmidtMatrix_eq_mul {d D : ℕ} (A : MPSTensor d D) :
    twoSiteSchmidtMatrix A = physicalMatrix A *
      (physicalMatrix A)ᵀ.submatrix Prod.swap id := by
  ext i j
  simp [twoSiteSchmidtMatrix, physicalMatrix, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type]

/-- One-site injectivity gives Schmidt rank `D²` across the one-site cut
of the two-site ring. Source context: arXiv:1010.3732, Section II.F.2,
lines 1059–1068, and Appendix C, lines 2653–2717. -/
theorem rank_twoSiteSchmidtMatrix_of_isInjective {d D : ℕ}
    {A : MPSTensor d D} (hA : Kraus.IsInjective A) :
    (twoSiteSchmidtMatrix A).rank = D ^ 2 := by
  classical
  obtain ⟨R, hR⟩ := (physicalMatrix A).mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (injective_physicalMatrix_mulVec_of_isInjective hA))
  have hRP : LinearMap.toMatrix' R * physicalMatrix A = 1 := by
    simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_id,
      LinearMap.toMatrix'_toLin'] using congrArg LinearMap.toMatrix' hR
  have hInv : LinearMap.toMatrix' R * twoSiteSchmidtMatrix A *
      (LinearMap.toMatrix' R)ᵀ.submatrix id Prod.swap = 1 := by
    rw [twoSiteSchmidtMatrix_eq_mul, ← Matrix.mul_assoc, hRP, Matrix.one_mul]
    rw [← Matrix.submatrix_mul _ _ Prod.swap id Prod.swap Function.bijective_id,
      ← Matrix.transpose_mul, hRP, Matrix.transpose_one]
    exact Matrix.submatrix_one Prod.swap Prod.swap_injective
  apply le_antisymm
  · rw [twoSiteSchmidtMatrix_eq_mul]
    simpa only [Fintype.card_prod, Fintype.card_fin, ← pow_two] using
      (Matrix.rank_mul_le_left (physicalMatrix A)
        ((physicalMatrix A)ᵀ.submatrix Prod.swap id)).trans
        (Matrix.rank_le_card_width (physicalMatrix A))
  · simpa only [hInv, Matrix.rank_one, Fintype.card_prod, Fintype.card_fin,
      ← pow_two] using
      (Matrix.rank_mul_le_left (LinearMap.toMatrix' R * twoSiteSchmidtMatrix A)
        ((LinearMap.toMatrix' R)ᵀ.submatrix id Prod.swap)).trans
        (Matrix.rank_mul_le_right (LinearMap.toMatrix' R) (twoSiteSchmidtMatrix A))

/-- The coefficient matrix is the two-site periodic vector, reindexed by
the two physical letters. Source context: arXiv:1010.3732, Section II.F.2. -/
theorem twoSiteSchmidtMatrix_apply_eq_mpv {d D : ℕ} (A : MPSTensor d D)
    (i j : Fin d) : twoSiteSchmidtMatrix A i j = mpv A ![i, j] := by
  simp [twoSiteSchmidtMatrix, mpv, coeff, Kraus.evalWord_cons,
    Kraus.evalWord_nil]

/-- The two-site coefficient matrix depends continuously on the tensor.
Source context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem continuous_twoSiteSchmidtMatrix {T : Type*} [TopologicalSpace T] {d D : ℕ}
    (A : T → MPSTensor d D) (hA : Continuous A) :
    Continuous fun t => twoSiteSchmidtMatrix (A t) := by
  exact continuous_pi fun i => continuous_pi fun j =>
    (((continuous_apply i).comp hA).matrix_mul ((continuous_apply j).comp hA)).matrix_trace

/-- Equality of nonzero two-site rays preserves their Schmidt rank, even
for different bond dimensions. Source context: arXiv:1010.3732, Section II.F.2
and Appendix C, lines 2653–2717. -/
theorem SamePositiveMpvRay.rank_twoSiteSchmidtMatrix_eq {d D E : ℕ}
    {A : MPSTensor d D} {B : MPSTensor d E} (h : SamePositiveMpvRay A B)
    (hne : (mpv A : (Fin 2 → Fin d) → ℂ) ≠ 0) :
    (twoSiteSchmidtMatrix A).rank = (twoSiteSchmidtMatrix B).rank := by
  have hmem : (mpv A : (Fin 2 → Fin d) → ℂ) ∈
      Submodule.span ℂ {(mpv B : (Fin 2 → Fin d) → ℂ)} :=
    h 2 (by omega) ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcne : c ≠ 0 := fun hz => hne (by simpa only [hz, zero_smul] using hc.symm)
  have hC : twoSiteSchmidtMatrix A = c • twoSiteSchmidtMatrix B := by
    ext i j
    simpa only [twoSiteSchmidtMatrix_apply_eq_mpv, Matrix.smul_apply, Pi.smul_apply]
      using congrFun hc.symm ![i, j]
  exact hC ▸ Matrix.rank_smul_of_mem_nonZeroDivisors (twoSiteSchmidtMatrix B)
    (mem_nonZeroDivisors_of_ne_zero hcne)

/-- Near a parameter with an injective representative of bond dimension
`D₀`, every injective representative has bond dimension at least `D₀`.
This justifies the local dimension-direction assertion in arXiv:1010.3732,
Section II.F.2, lines 1059–1068. It uses the two-site physical vector and
does not construct a single-bond canonical support. -/
theorem ExactMPSGroundPath.eventually_minimalBondDimension_ge
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    (t₀ : unitInterval) {D₀ : ℕ} (hD₀ : 0 < D₀)
    (A₀ : MPSTensor d D₀) (hA₀ : Kraus.IsInjective A₀)
    (hRay₀ : SamePositiveMpvRay (Q.tensor t₀) A₀) :
    ∀ᶠ t : unitInterval in 𝓝 t₀, ∀ (D : ℕ) (A : MPSTensor d D),
      Kraus.IsInjective A → SamePositiveMpvRay (Q.tensor t) A → D₀ ≤ D := by
  have hcont := continuous_twoSiteSchmidtMatrix (fun t : unitInterval => Q.tensor t)
    (Q.continuous.comp_continuous continuous_subtype_val (fun t => t.property))
  have hRank₀ := (hRay₀.rank_twoSiteSchmidtMatrix_eq
    (Q.nonzero t₀ t₀.property 2 (by omega))).trans
      (rank_twoSiteSchmidtMatrix_of_isInjective hA₀)
  have hnear := hcont.lowerSemicontinuous_matrix_rank t₀ (D₀ ^ 2 - 1)
    (by simpa only [hRank₀] using Nat.sub_lt (pow_pos hD₀ 2) zero_lt_one)
  filter_upwards [hnear] with t ht D A hA hRay
  have hRank := (hRay.rank_twoSiteSchmidtMatrix_eq
    (Q.nonzero t t.property 2 (by omega))).trans
      (rank_twoSiteSchmidtMatrix_of_isInjective hA)
  have hsq : D₀ ^ 2 ≤ D ^ 2 := by omega
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hsq

end MPSTensor
