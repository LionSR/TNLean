/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.ApproximateCertificates
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.CanonicalSearch
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.CompressedSolutions
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.LeadingVectorPrecision
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.PowerIteration
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.RationalSearch
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.Selection
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.ViableVector.UniformCertificates
import TNLean.MPS.AreaLaw.ViableSet.BondTrimming
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.BondTrimmingBound
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.RationalTensor.RationalTensorApproximation
import TNLean.MPS.AreaLaw.GroundStateAlgorithm.RationalTensor.ViabilityStability

/-!
# Size and bond trimming before the ground vector is supplied

Take the size-trimming selection of the Hamiltonian, gap parameter and input family, and
independently trim every selected vector through its internal bonds: the output is the
family `bondTrimSet hi m (h.sizeTrimmingSelection hq Δ S)` of these trimmings, a function of
the input family alone. It is chosen before the ground-state energy or ground vector, has
polynomial cardinality and a polynomial matrix product state bond bound, and is
`1 / 2`-viable whenever the input is viable at the small error required by the
size-trimming step.

**Local fix (trimming radius):** The bond radius is `(48 L)² r(L)` in place of the printed
`48 L r(L)`, from the corrected overlap-loss estimate recorded at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.

**Scope restriction (library bond constants):** The size bound uses the library constant-cut
bond and corrected matrix-net exponent, as documented in
`docs/paper-gaps/lvv13_constant_bond.tex`. The sharper AKLV dependence is not asserted here.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Claim `c:2`, lines
520–527, and Claim `c:trim`, lines 549–559. The reference supplied by Lemma `l:mpsapprox`,
lines 325–328, is used only to estimate the overlap lost during the actual column trimmings.

It also contains the following results.

* `ManyBody.ChainInteraction.exists_rational_size_bond_trimmed_family`: rational approximation after
  independent bond trimming.
-/

open scoped Matrix.Norms.L2Operator
open Matrix
open scoped InnerProductSpace ComplexOrder
open ManyBody (IsGapped groundSpace ChainInteraction)

namespace TNLean.MPS.AreaLaw

section SizeBondTrimming

/-- **Size trimming with any admissible nets and solver, followed by bond trimming**, is
`1 / 2`-viable whenever the input is `c / L`-viable. Library-bond version of LVV13,
`algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559, with the documented radius
correction, for every solver of the convex program returning optimal solutions. -/
theorem _root_.ManyBody.ChainInteraction.isViable_bondTrimSet_sizeTrimmingSelectionWith {L q i : ℕ}
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ 1)
        (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : i ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q i))
    {net : (m : ℕ) → Finset (Matrix (CutSite L q i × Fin m) (CutSite L q i × Fin m) ℂ)}
    (hnet : h.IsAdmissibleNet Δ net)
    {sol : (m : ℕ) → Matrix (CutSite L q i × Fin m) (CutSite L q i × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q i × CutSite L q i) × Fin m)}
    (hsol : h.IsAdmissibleSolver hq Δ S sol)
    (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Γ‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Γ})
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q i))) :
    IsViable Γ (1 / 2) (bondTrimSet hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
      (h.sizeTrimmingSelectionWith hq Δ S net sol) : Set (LeftBlockVector L q i)) := by
  classical
  obtain ⟨_, r, W, u, hW, _, hu, hcols, hΓu⟩ :=
    h.isViable_sizeTrimmingSelectionWith hh hhJ hpos hL hq hΔ S hnet hsol E₀ Γ hΩ hgap hspan hviable
  obtain ⟨v, hv, hvMPS, hΓv⟩ :=
    exists_bond_trimming_reference (by omega) hΔ (by omega) h hh hhJ hΩ hgap hspan
  have hΓu' : 1 - 1 / 12 ≤ ‖⟪Γ, (blockSplit L q i).symm (rightApply W u)⟫_ℂ‖ := by
    rw [blockSplit_symm_eq]
    exact hΓu
  have htrim := isViableMPS_bondTrimSet_of_columns hi
    (h.sizeTrimmingSelectionWith hq Δ S net sol) u W hW
    hu hcols Γ hΩ hΓu' v hv hΓv (lvvReferenceBond q Δ L)
    (fun k hk0 hki ↦ hvMPS.rank_cutMatrix_le hk0 (lt_of_lt_of_le hki hi))
  exact htrim.2.2

/-- **Size trimming followed by bond trimming.** Independently trimming each member of the
size-trimming selection through the internal bonds at the radius `m` gives the family
`bondTrimSet hi m (h.sizeTrimmingSelection hq Δ S) = {trim_m u : u ∈ selection}`, which is
`5 / 12`-viable whenever the input is `c / L`-viable, leaving a further `1 / 12` reserve
for approximation. The selection and its trimming are
functions of the Hamiltonian, the gap parameter and the input family, fixed before every
ground pair. This is the library-bond version of LVV13, `algo53.tex`, Claims `c:2` and
`c:trim`, lines 520–559, with the documented radius correction. -/
theorem _root_.ManyBody.ChainInteraction.isViable_bondTrimSet_sizeTrimmingSelection_with_reserve
    {L q i : ℕ}
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ 1)
        (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : i ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q i)) (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Γ‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Γ})
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q i))) :
    IsViable Γ (5 / 12) (bondTrimSet hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
      (h.sizeTrimmingSelection hq Δ S) : Set (LeftBlockVector L q i)) := by
  classical
  obtain ⟨_, r, W, u, hW, _, hu, hcols, hΓu⟩ :=
    h.isViable_sizeTrimmingSelection hh hhJ hpos hL hq hΔ S E₀ Γ hΩ hgap hspan hviable
  obtain ⟨v, hv, hvMPS, hΓv⟩ :=
    exists_bond_trimming_reference (by omega) hΔ (by omega) h hh hhJ hΩ hgap hspan
  have hΓu' : 1 - 1 / 12 ≤ ‖⟪Γ, (blockSplit L q i).symm (rightApply W u)⟫_ℂ‖ := by
    rw [blockSplit_symm_eq]
    exact hΓu
  have htrim := isViableMPS_bondTrimSet_of_columns_with_reserve hi
    (h.sizeTrimmingSelection hq Δ S) u W hW hu hcols Γ hΩ hΓu' v hv hΓv
    (lvvReferenceBond q Δ L)
    (fun k hk0 hki ↦ hvMPS.rank_cutMatrix_le hk0 (lt_of_lt_of_le hki hi))
  exact htrim.2.2

/-- Size trimming followed by independent bond trimming gives `1 / 2`-viability.
Source: LVV13, `algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559, with the
documented radius correction. -/
theorem _root_.ManyBody.ChainInteraction.isViable_bondTrimSet_sizeTrimmingSelection {L q i : ℕ}
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ 1)
        (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : i ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q i)) (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hΩ : ‖Γ‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Γ})
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q i))) :
    IsViable Γ (1 / 2) (bondTrimSet hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
      (h.sizeTrimmingSelection hq Δ S) : Set (LeftBlockVector L q i)) := by
  obtain ⟨z, hz, hoverlap, hsupport⟩ :=
    h.isViable_bondTrimSet_sizeTrimmingSelection_with_reserve hh hhJ hpos hL hq hi hΔ S E₀ Γ
      hΩ hgap hspan hviable
  exact ⟨z, hz, by linarith, hsupport⟩

/-- The polynomial size-trimming family followed by actual independent bond trimming: the
existence form of `isViable_bondTrimSet_sizeTrimmingSelection`, with the trimmed family
left unnamed. The family is fixed before every ground pair. This is the library-bond
version of LVV13, `algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559, with the
documented radius correction. -/
theorem _root_.ManyBody.ChainInteraction.exists_size_bond_trimmed_family_polynomial {L q i : ℕ}
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ 1)
        (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : i ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q i)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    let C := (D + 1) * D * (2 * A + 1) ^ p
    let m := bondTrimmingRadius L (lvvReferenceBond q Δ L)
    ∃ T : Finset (LeftBlockVector L q i),
      T.card ≤ C * L ^ p ∧ (∀ v ∈ T, IsLeftOpenMPS m v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        ‖Γ‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Γ} →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q i)) →
        IsViable Γ (1 / 2) (T : Set (LeftBlockVector L q i)) := by
  intro c D p A C m
  exact ⟨bondTrimSet hi m (h.sizeTrimmingSelection hq Δ S),
    (card_bondTrimSet_le hi m _).trans (h.card_sizeTrimmingSelection_le_polynomial hL hq hΔ S),
    fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m _ hv,
    fun E₀ Γ hΩ hgap hspan hviable ↦
      h.isViable_bondTrimSet_sizeTrimmingSelection hh hhJ hpos hL hq hi hΔ S E₀ Γ hΩ
          hgap hspan hviable⟩

end SizeBondTrimming

section RationalBondTrimming

/-!
## Rational approximation after independent bond trimming

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

/-- Size trimming followed by independent Schmidt trimming admits rational tensor
data at an explicit common height. The rational family is chosen before every
ground pair, has no more members than the size-trimming selection, and remains
half-viable whenever the original family has the required small viability error.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559, with the corrections
and quantitative scope stated in the module docstring. -/
theorem _root_.ManyBody.ChainInteraction.exists_rational_size_bond_trimmed_family
    {L q n : ℕ} (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ 1)
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
        ‖Γ‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Γ} →
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
  intro E₀ Γ hΩ hgap hspan hviable
  obtain ⟨_, r, W, u, hW, hrD, hu, hcols, hΓu⟩ :=
    h.isViable_sizeTrimmingSelection hh hhJ hpos hL hq hΔ S E₀ Γ hΩ hgap hspan hviable
  obtain ⟨v, hv, hvMPS, hΓv⟩ :=
    exists_bond_trimming_reference (by omega) hΔ (by omega) h hh hhJ hΩ hgap hspan
  have hΓu' : 1 - 1 / 12 ≤
      ‖⟪Γ, (blockSplit L q (n + 1)).symm (rightApply W u)⟫_ℂ‖ := by
    rw [blockSplit_symm_eq]
    exact hΓu
  obtain ⟨hnorm, _, _, hoverlap, _⟩ :=
    bondTrimSet_witness_with_reserve hi U u W hW hu hcols Γ hΩ hΓu'
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
  exact isViable_half_of_approximating_trimmed_leftFamily hΩ hθ.le hmesh
    B T hcover W hW u'
    (fun a ↦ leftColumnwiseSchmidtTrim_column_mem hi m U u hcols a) hnorm' hoverlap'

end RationalBondTrimming

end TNLean.MPS.AreaLaw
