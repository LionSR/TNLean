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

Choose the finite size-trimming family from the Hamiltonian, gap parameter and input family.
Independently trim every retained vector through its internal bonds. The resulting family is
still chosen before the ground-state energy or ground vector. It has polynomial cardinality
and a polynomial matrix product state bond bound, and it is `1 / 2`-viable whenever the input
is viable at the small error required by the size-trimming step.

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

/-- The polynomial size-trimming family followed by actual independent bond trimming.
The family is fixed before every ground pair. This is the library-bond version of LVV13,
`algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559, with the documented radius correction. -/
theorem ChainHamiltonian.exists_size_bond_trimmed_family_polynomial {L q i : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) (hi : i ≤ L) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q i)) (b : ℕ)
    (hS : ∀ v ∈ S, IsLeftOpenMPS b v) :
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
  classical
  intro c D p A C m
  obtain ⟨T, hcard, _, _, hgood⟩ :=
    h.exists_size_trimmed_column_family_polynomial hpos hL hq hΔ S b hS
  refine ⟨bondTrimSet hi m T, (card_bondTrimSet_le hi m T).trans hcard,
    fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m T hv, ?_⟩
  intro E₀ Γ hgs hviable
  obtain ⟨_, r, W, u, hW, _, hu, hcols, hΓu⟩ := hgood E₀ Γ hgs hviable
  obtain ⟨v, hv, hvMPS, hΓv⟩ :=
    exists_bond_trimming_reference (by omega) hΔ (by omega) h hgs
  have hΓu' : 1 - 1 / 12 ≤ ‖⟪Γ, (blockSplit L q i).symm (rightApply W u)⟫_ℂ‖ := by
    rw [blockSplit_symm_eq]
    exact hΓu
  have htrim := isViableMPS_bondTrimSet_of_columns hi T u W hW hu hcols Γ hgs.1 hΓu'
    v hv hΓv (lvvReferenceBond q Δ L)
    (fun k hk0 hki ↦ hvMPS.rank_cutMatrix_le hk0 (lt_of_lt_of_le hki hi))
  exact htrim.2.2

end TNLean.MPS.AreaLaw
