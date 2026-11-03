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

Choose the finite size-trimming selection `T₀`, a family in the span of the input family,
from the Hamiltonian, gap parameter and input family. Independently trim every retained
vector through its internal bonds: the output is the named family `bondTrimSet hi m T₀` of
these trimmings. It is still chosen before the ground-state energy or ground vector, has
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

/-- **Size trimming followed by named bond trimming.** The size-trimming selection `T₀`, a
family of at most `C L ^ p` vectors in the span of the input family, is fixed before every
ground pair. Independently trimming each of its members through the internal bonds at the
radius `m` gives the family `bondTrimSet hi m T₀ = {trim_m u : u ∈ T₀}`, which is
`1 / 2`-viable whenever the input is `c / L`-viable. This is the library-bond version of
LVV13, `algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559, with the documented radius
correction. -/
theorem ChainHamiltonian.exists_size_trimmed_family_bondTrimSet_polynomial {L q i : ℕ}
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
    ∃ T₀ : Finset (LeftBlockVector L q i),
      T₀.card ≤ C * L ^ p ∧
      (T₀ : Set (LeftBlockVector L q i)) ⊆
        Submodule.span ℂ (S : Set (LeftBlockVector L q i)) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState h.operator E₀ Γ Δ →
        IsViable Γ (c / L) (S : Set (LeftBlockVector L q i)) →
        IsViable Γ (1 / 2) (bondTrimSet hi m T₀ : Set (LeftBlockVector L q i)) := by
  classical
  intro c D p A C m
  obtain ⟨T₀, hcard, hspan, _, hgood⟩ :=
    h.exists_size_trimmed_column_family_polynomial hpos hL hq hΔ S b hS
  refine ⟨T₀, hcard, hspan, ?_⟩
  intro E₀ Γ hgs hviable
  obtain ⟨_, r, W, u, hW, _, hu, hcols, hΓu⟩ := hgood E₀ Γ hgs hviable
  obtain ⟨v, hv, hvMPS, hΓv⟩ :=
    exists_bond_trimming_reference (by omega) hΔ (by omega) h hgs
  have hΓu' : 1 - 1 / 12 ≤ ‖⟪Γ, (blockSplit L q i).symm (rightApply W u)⟫_ℂ‖ := by
    rw [blockSplit_symm_eq]
    exact hΓu
  have htrim := isViableMPS_bondTrimSet_of_columns hi T₀ u W hW hu hcols Γ hgs.1 hΓu'
    v hv hΓv (lvvReferenceBond q Δ L)
    (fun k hk0 hki ↦ hvMPS.rank_cutMatrix_le hk0 (lt_of_lt_of_le hki hi))
  exact htrim.2.2

/-- The polynomial size-trimming family followed by actual independent bond trimming: the
existence form of `exists_size_trimmed_family_bondTrimSet_polynomial`, with the trimmed
family left unnamed. The family is fixed before every ground pair. This is the
library-bond version of LVV13, `algo53.tex`, Claims `c:2` and `c:trim`, lines 520–559,
with the documented radius correction. -/
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
  intro c D p A C m
  obtain ⟨T₀, hcard, -, hgood⟩ :=
    h.exists_size_trimmed_family_bondTrimSet_polynomial hpos hL hq hi hΔ S b hS
  exact ⟨bondTrimSet hi m T₀, (card_bondTrimSet_le hi m T₀).trans hcard,
    fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m T₀ hv, hgood⟩

end TNLean.MPS.AreaLaw
