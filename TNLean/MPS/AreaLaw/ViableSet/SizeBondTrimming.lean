/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming
import TNLean.MPS.AreaLaw.ViableSet.BondTrimming
import TNLean.MPS.AreaLaw.ViableSet.BondTrimmingReference

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
-/

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- **Size trimming with any admissible nets and solver, followed by bond trimming**, is
`1 / 2`-viable whenever the input is `c / L`-viable. Library-bond version of LVV13,
`algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559, with the documented radius
correction, for every solver of the convex program returning optimal solutions. -/
theorem ChainHamiltonian.isViable_bondTrimSet_sizeTrimmingSelectionWith {L q i : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : i ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q i))
    {net : (m : ℕ) → Finset (Matrix (CutSite L q i × Fin m) (CutSite L q i × Fin m) ℂ)}
    (hnet : h.IsAdmissibleNet Δ net)
    {sol : (m : ℕ) → Matrix (CutSite L q i × Fin m) (CutSite L q i × Fin m) ℂ →
      EuclideanSpace ℂ ((CutLeft L q i × CutSite L q i) × Fin m)}
    (hsol : h.IsAdmissibleSolver hq Δ S sol)
    (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q i))) :
    IsViable Γ (1 / 2) (bondTrimSet hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
      (h.sizeTrimmingSelectionWith hq Δ S net sol) : Set (LeftBlockVector L q i)) := by
  classical
  obtain ⟨_, r, W, u, hW, _, hu, hcols, hΓu⟩ :=
    h.isViable_sizeTrimmingSelectionWith hpos hL hq hΔ S hnet hsol E₀ Γ hgs hviable
  obtain ⟨v, hv, hvMPS, hΓv⟩ :=
    exists_bond_trimming_reference (by omega) hΔ (by omega) h hgs
  have hΓu' : 1 - 1 / 12 ≤ ‖⟪Γ, (blockSplit L q i).symm (rightApply W u)⟫_ℂ‖ := by
    rw [blockSplit_symm_eq]
    exact hΓu
  have htrim := isViableMPS_bondTrimSet_of_columns hi
    (h.sizeTrimmingSelectionWith hq Δ S net sol) u W hW
    hu hcols Γ hgs.1 hΓu' v hv hΓv (lvvReferenceBond q Δ L)
    (fun k hk0 hki ↦ hvMPS.rank_cutMatrix_le hk0 (lt_of_lt_of_le hki hi))
  exact htrim.2.2

/-- **Size trimming followed by bond trimming.** Independently trimming each member of the
size-trimming selection through the internal bonds at the radius `m` gives the family
`bondTrimSet hi m (h.sizeTrimmingSelection hq Δ S) = {trim_m u : u ∈ selection}`, which is
`1 / 2`-viable whenever the input is `c / L`-viable. The selection and its trimming are
functions of the Hamiltonian, the gap parameter and the input family, fixed before every
ground pair. This is the library-bond version of LVV13, `algo53.tex`, Claims `c:2` and
`c:trim`, lines 520–559, with the documented radius correction. -/
theorem ChainHamiltonian.isViable_bondTrimSet_sizeTrimmingSelection {L q i : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : i ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q i)) (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q i))) :
    IsViable Γ (1 / 2) (bondTrimSet hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
      (h.sizeTrimmingSelection hq Δ S) : Set (LeftBlockVector L q i)) := by
  let : NeZero q := ⟨by omega⟩
  have hc : 0 < (Δ / 169) ^ 2 := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < (Δ / 169) ^ 2 / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  exact h.isViable_bondTrimSet_sizeTrimmingSelectionWith hpos hL hq hi hΔ S
    (fun _ _ Y hY ↦ exists_mem_rectangularTraceNormNet hη Y hY)
    (fun m ↦ isAdmissibleLeadingVector_boundaryLeadingVector _ _ m _) E₀ Γ hgs hviable

/-- The polynomial size-trimming family followed by actual independent bond trimming: the
existence form of `isViable_bondTrimSet_sizeTrimmingSelection`, with the trimmed family
left unnamed. The family is fixed before every ground pair. This is the library-bond
version of LVV13, `algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559, with the
documented radius correction. -/
theorem ChainHamiltonian.exists_size_bond_trimmed_family_polynomial {L q i : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
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
        IsGappedGroundState h.operator E₀ Γ Δ →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q i)) →
        IsViable Γ (1 / 2) (T : Set (LeftBlockVector L q i)) := by
  intro c D p A C m
  exact ⟨bondTrimSet hi m (h.sizeTrimmingSelection hq Δ S),
    (card_bondTrimSet_le hi m _).trans (h.card_sizeTrimmingSelection_le_polynomial hL hq hΔ S),
    fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m _ hv,
    fun E₀ Γ hgs hviable ↦ h.isViable_bondTrimSet_sizeTrimmingSelection hpos hL hq hi hΔ S E₀ Γ
      hgs hviable⟩

end TNLean.MPS.AreaLaw
