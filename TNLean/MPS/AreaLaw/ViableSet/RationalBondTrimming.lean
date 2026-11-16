/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalTensorApproximation
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ViabilityStability
import TNLean.MPS.AreaLaw.ViableSet.SizeBondTrimming

/-!
# Rational approximation after independent bond trimming

At a positive cut, every column selected by size trimming has norm at most one.
Independent Schmidt trimming preserves this bound. The trimmed family therefore
admits a simultaneous rational approximation on the same virtual spaces, with one
explicit dyadic precision and no increase in cardinality or bond dimension.

The approximation is chosen before a ground pair is supplied. For each ground pair,
the normalized trimmed witness has overlap at least `7 / 12`; its unnormalized
norm is at least `37 / 48`. A mesh depending only on the uniform environment
dimension absorbs the rationalization error and preserves `1 / 2`-viability.

This is an auxiliary finite-precision form of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Claim `c:trim`, lines 549–559. It records
existence and coordinate-height bounds, rather than an arithmetic running time.

**Local fix (trimming radius):** The quadratic radius is the correction recorded at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.

**Scope restriction (positive cuts and library bond constants):** The cut has
positive length and the local dimension is at least two. The constant-cut bond
and matrix-net bounds are those recorded in `docs/paper-gaps/lvv13_constant_bond.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Size trimming followed by independent Schmidt trimming admits rational tensor
data at an explicit common height. The rational family is chosen before every
ground pair, has no more members than the size-trimming selection, and remains
half-viable whenever the original family has the required small viability error.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559, with the corrections
and quantitative scope stated in the module docstring. -/
theorem ChainHamiltonian.exists_rational_size_bond_trimmed_family
    {L q n : ℕ} (h : ChainHamiltonian L q 1 1)
    (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : n + 1 ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q (n + 1))) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let m := bondTrimmingRadius L (lvvReferenceBond q Δ L)
    let θ : ℝ := 37 / (1152 * (Real.sqrt D + 1))
    let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 m) : ℝ) ^ (n + 2) *
      (n + 2) * 2 ^ (n + 1)
    let t := Nat.clog 2 ⌈K / θ⌉₊
    ∃ T : Finset (LeftBlockVector L q (n + 1)),
      T.card ≤ (h.sizeTrimmingSelection hq Δ S).card ∧
      (∀ w ∈ T, Nonempty
        (RationalLeftOpenMPSRepresentationOfHeight (2 ^ (2 * t + 5)) m w)) ∧
      (∀ v ∈ bondTrimSet hi m (h.sizeTrimmingSelection hq Δ S),
        ∃ w ∈ T, ‖v - w‖ ≤ θ) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState h.operator E₀ Γ Δ →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q (n + 1))) →
        IsViable Γ (1 / 2) (T : Set (LeftBlockVector L q (n + 1))) := by
  classical
  intro c D m θ K t
  let U := h.sizeTrimmingSelection hq Δ S
  let B := bondTrimSet hi m U
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hBnorm : ∀ v ∈ B, ‖v‖ ≤ 1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact (norm_leftSchmidtTrim_le hi m u).trans
      (h.norm_le_one_of_mem_sizeTrimmingSelection hq Δ S hu)
  obtain ⟨T, hcard, hdata, hcover⟩ :=
    exists_rational_leftFamily_approximation_of_norm_le_one B hi
      (fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m U hv) hBnorm hθ
  refine ⟨T, hcard.trans (card_bondTrimSet_le hi m U), hdata, hcover, ?_⟩
  intro E₀ Γ hgs hviable
  obtain ⟨_, r, W, u, hW, hrD, hu, hcols, hΓu⟩ :=
    h.isViable_sizeTrimmingSelection hpos hL hq hΔ S E₀ Γ hgs hviable
  obtain ⟨v, hv, hvMPS, hΓv⟩ :=
    exists_bond_trimming_reference (by omega) hΔ (by omega) h hgs
  have hΓu' : 1 - 1 / 12 ≤
      ‖⟪Γ, (blockSplit L q (n + 1)).symm (rightApply W u)⟫_ℂ‖ := by
    rw [blockSplit_symm_eq]
    exact hΓu
  obtain ⟨hnorm, _, _, hoverlap, _⟩ :=
    bondTrimSet_witness_with_reserve hi U u W hW hu hcols Γ hgs.1 hΓu'
      v hv hΓv (lvvReferenceBond q Δ L)
      (fun k hk0 hki ↦ hvMPS.rank_cutMatrix_le hk0 (lt_of_lt_of_le hki hi))
  let u' := leftColumnwiseSchmidtTrim hi m u
  have hrawnorm : ‖(blockSplit L q (n + 1)).symm (rightApply W u')‖ = ‖u'‖ := by
    rw [(blockSplit L q (n + 1)).symm.norm_map, norm_rightApply_eq_of_isometry W hW]
  have hphysical : physicalRightApply W u' =
      (blockSplit L q (n + 1)).symm (rightApply W u') :=
    (blockSplit_symm_eq (n + 1) (rightApply W u')).symm
  have hnorm' : 37 / 48 ≤ ‖u'‖ := by
    rw [← hrawnorm]
    exact hnorm
  have hoverlap' : 7 / 12 ≤
      ‖⟪((‖u'‖⁻¹ : ℝ) : ℂ) • physicalRightApply W u', Γ⟫_ℂ‖ := by
    rw [hphysical, ← hrawnorm, norm_inner_symm]
    exact hoverlap
  have hmesh : θ ≤ 37 / (1152 * (Real.sqrt r + 1)) := by
    have hsqrt : Real.sqrt (r : ℝ) ≤ Real.sqrt (D : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hrD)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hsqrt])
  exact isViable_half_of_approximating_trimmed_leftFamily hgs.1 hθ.le hmesh
    B T hcover W hW u'
    (fun a ↦ leftColumnwiseSchmidtTrim_column_mem hi m U u hcols a) hnorm' hoverlap'

end TNLean.MPS.AreaLaw
