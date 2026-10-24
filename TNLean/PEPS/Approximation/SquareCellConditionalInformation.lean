/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CellConditionalInformation
import TNLean.PEPS.Approximation.AngularInformationBound
import TNLean.PEPS.Approximation.AngularGridCells

/-!
# Conditional information of a square-lattice cell

The cell estimate on finite integer domains transfers to the original square
lattice by relabeling sites and translating all positions by `(1, 1)`. The state,
full-system gap and conditioning regions are preserved, and so are the named constants
`cellInformationConstant` and `cellInformationExponent`
(`cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt`).

**Scope restriction (sublinear collar bound):** The sublinear collar bound is an
explicit premise of the results of this module; the named-constant form also takes
the amplification bound at given constants as a premise, which
`amplificationBoundAt_collarAmplification` supplies at named constants. This is a
conditional step toward polynomial-PEPS Lemma 3.2; it does not supply the collar estimate. See
`docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`.

Source: polynomial-PEPS manuscript, `02-information.tex`, Lemma 3.2,
lines 163–178, and Proposition 3.4, lines 688–737.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open TNLean.PEPS.AreaLaw
open TNLean.PEPS.AreaLaw.Geometry

open Classical in
/-- **The cell bound of Lemma 3.2 on the square for a family of states,** with prefactor `C₁`
and exponent `K` at the clearance coefficient `c`: for every state `Ω` of the family, every cell
`G` of the grid of side `s ≥ 1`, every union `B` of other cells and every region `E` outside
`G ∪ B` at distance at least `c s` from the closed cell, `I_Ω(G : E | B) ≤ C₁ (1 + log s)^K`.
Source: `02-information.tex`, Lemma 3.2, lines 161–178. -/
def SquareCellInformationBound (q : ℕ) (G : ∀ L : ℕ, StateSpace L q → Prop) (c C₁ K : ℝ) :
    Prop :=
  ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)), m₀ ∉ A →
    ∀ (L : ℕ) (Ω : StateSpace L q), G L Ω →
      let Gc : Finset (Vertex L) :=
        Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
      let B : Finset (Vertex L) := Finset.univ.filter
        (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
      ∀ E : Finset (Vertex L), E ⊆ (Gc ∪ B)ᶜ →
        (∀ x ∈ closure (AngularGrid.cell o s m₀),
          ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
        FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
          Ω Gc E B ≤ C₁ * (1 + Real.log s) ^ K

open Classical in
/-- **The cell bound on the square from the cell bound on the integer square.** If, for a state
`Ω` of the square, the cell bound of Lemma 3.2 holds for its placement on the integer square
with the grid origin `o - (1, 1)`, then it holds on the square with the origin `o`. A common
translation by `(1, 1)` identifies the two placements of the sites.
Source: `02-information.tex`, Lemma 3.2, lines 161–178, and its application in
Proposition 3.4, lines 688–737. -/
theorem cell_conditionalMutualInformation_le_square_of_rectangle {q L : ℕ}
    (Ω : StateSpace L q) {s c C₀ : ℝ} (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ))
    (hbound : ∀ E : Finset (Site (rectangularDomain L L)),
      E ⊆ (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          x.val ∈ CellPartition.cellSample (o - (1, 1)) s m₀) ∪
        Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          CellPartition.cellIndex (o - (1, 1)) s (integerPoint x.val) ∈ A))ᶜ →
      (∀ x ∈ closure (CellPartition.box (CellPartition.cellCorner (o - (1, 1)) s m₀) s),
        ∀ y ∈ E, c * s ≤ dist x (integerPoint y.val)) →
      FiniteProduct.conditionalMutualInformation
        (fun _ : Site (rectangularDomain L L) ↦ Fin q) (squareAreaLawState Ω)
        (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          x.val ∈ CellPartition.cellSample (o - (1, 1)) s m₀)) E
        (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          CellPartition.cellIndex (o - (1, 1)) s (integerPoint x.val) ∈ A)) ≤ C₀) :
    let G : Finset (Vertex L) :=
      Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
    let B : Finset (Vertex L) := Finset.univ.filter
      (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
    ∀ E : Finset (Vertex L), E ⊆ (G ∪ B)ᶜ →
      (∀ x ∈ closure (AngularGrid.cell o s m₀),
        ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
      FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
        Ω G E B ≤ C₀ := by
  intro G B E hE hclear
  let σ := rectangleSiteEquiv L L
  let o' : ℝ × ℝ := o - (1, 1)
  have hpos (v : Vertex L) :
      integerPoint (σ v).val + (1, 1) = sitePosition L v := by
    simp [σ, integerPoint, sitePosition, rectangleSiteEquiv_val, rectangleEmbedding]
  have hindex (x : ℝ × ℝ) :
      CellPartition.cellIndex o' s x = AngularGrid.owner o s (x + (1, 1)) := by
    unfold CellPartition.cellIndex AngularGrid.owner
    congr 2 <;> simp only [o', Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;>
      ring
  have hboxshift (x : ℝ × ℝ) :
      x ∈ CellPartition.box (CellPartition.cellCorner o' s m₀) s ↔
        x + (1, 1) ∈ AngularGrid.cell o s m₀ := by
    simp only [CellPartition.box, CellPartition.cellCorner, AngularGrid.cell, o',
      Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      add_mul, one_mul]
    constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith only [h₁, h₂, h₃, h₄]
  have hG : (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
      x.val ∈ CellPartition.cellSample o' s m₀)) = G.map σ.toEmbedding := by
    ext y
    obtain ⟨v, rfl⟩ := σ.surjective y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, G, CellPartition.cellSample, CellPartition.mem_latticeBox,
      hboxshift, hpos]
  have hB : (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
      CellPartition.cellIndex o' s (integerPoint x.val) ∈ A)) = B.map σ.toEmbedding := by
    ext y
    obtain ⟨v, rfl⟩ := σ.surjective y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, B, hindex, hpos]
  have hcl : Set.MapsTo (fun x : ℝ × ℝ ↦ x + (1, 1))
      (closure (CellPartition.box (CellPartition.cellCorner o' s m₀) s))
      (closure (AngularGrid.cell o s m₀)) :=
    (show Set.MapsTo (fun x : ℝ × ℝ ↦ x + (1, 1))
      (CellPartition.box (CellPartition.cellCorner o' s m₀) s)
      (AngularGrid.cell o s m₀) from fun x hx ↦ (hboxshift x).mp hx).closure
      (continuous_id.add continuous_const)
  rw [hG, hB] at hbound
  have hE' : E.map σ.toEmbedding ⊆ (G.map σ.toEmbedding ∪ B.map σ.toEmbedding)ᶜ := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    apply Finset.mem_compl.mpr
    intro hyGB
    exact Finset.mem_compl.mp (hE hv) (by
      simpa only [← Finset.map_union, Finset.mem_map_equiv, Equiv.toEmbedding_apply,
        Equiv.symm_apply_apply] using hyGB)
  have hclear' : ∀ x ∈ closure (CellPartition.box (CellPartition.cellCorner o' s m₀) s),
      ∀ y ∈ E.map σ.toEmbedding, c * s ≤ dist x (integerPoint y.val) := by
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    have hh := hclear (x + (1, 1)) (hcl hx) v hv
    simpa only [Equiv.toEmbedding_apply, ← hpos, dist_add_right] using hh
  have hfinal := hbound (E.map σ.toEmbedding) hE' hclear'
  simpa only [squareAreaLawState, show rectangleConfigurationEquiv L L q =
    σ.arrowCongr (Equiv.refl (Fin q)) from rfl,
    FiniteProduct.conditionalMutualInformation, ← Finset.map_union,
    finiteProductEntropy_relabel] using hfinal

open Classical in
/-- **Lemma 3.2 on the original open square, with named constants.** Under the range-one
sublinear collar bound with constant `C` and threshold `N`, and the range-one amplification
bound at the input constant `max(C, 1)` and order `1` with constant `C_a` and threshold `N_a`,
the cell conditional-information bound holds on the original open square, with sites at
`(i + 1, j + 1)`, with the prefactor `cellInformationConstant q c C_tpl N C_a N_a` and the
exponent `cellInformationExponent c C_tpl N C_a N_a` of the integer-domain estimate. A common
translation identifies this placement with the integer-domain placement, so the constants are
unchanged.

Source: polynomial-PEPS Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
lines 161–178, and its application in Proposition 3.4, lines 688–737. -/
theorem cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt
    {q : ℕ} {J Δ D₀ Ctpl C Ca : ℝ} {N Na : ℕ}
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N)
    (hamp : AreaLaw.AmplificationBoundAt q 1 J Δ (max C 1) 1 Ca Na) {c : ℝ} (hc : 0 < c) :
    ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)),
      m₀ ∉ A →
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        let G : Finset (Vertex L) :=
          Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
        let B : Finset (Vertex L) := Finset.univ.filter
          (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
        ∀ E : Finset (Vertex L), E ⊆ (G ∪ B)ᶜ →
          (∀ x ∈ closure (AngularGrid.cell o s m₀),
            ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
          FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
            Ω G E B ≤ cellInformationConstant q c Ctpl N Ca Na *
              (1 + Real.log s) ^ cellInformationExponent c Ctpl N Ca Na := by
  have hcell := cell_conditionalMutualInformation_le_of_sublinearCollarBoundAt hcol hamp hc
  intro s hs o m₀ A hm₀ L h E₀ Ω hΩ
  exact cell_conditionalMutualInformation_le_square_of_rectangle Ω o m₀ A
    (hcell s hs (o - (1, 1)) m₀ A hm₀ (rectangularDomain L L) h.toAreaLawHamiltonian E₀
      (squareAreaLawState Ω) (h.isGappedGroundState_toAreaLawHamiltonian hΩ))

open Classical in
/-- **Lemma 3.2 on the original open square, at the named amplification constants.** Under
the range-one sublinear collar bound with constant `C` and threshold `N`, the conclusion of
`cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt` holds with the
amplification constant `collarAmplificationConstant q 1 J Δ C` and threshold
`collarAmplificationThreshold q 1 J Δ C`. The collar bound remains a premise until its
constant and threshold are named.

Source: polynomial-PEPS Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
lines 161–178; area-law Proposition 10.2 (`prop:amplification`), `09-amplification.tex`,
lines 261–296. -/
theorem cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt_explicit
    {q : ℕ} {J Δ D₀ Ctpl C : ℝ} {N : ℕ} (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N) {c : ℝ} (hc : 0 < c) :
    ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)),
      m₀ ∉ A →
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        let G : Finset (Vertex L) :=
          Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
        let B : Finset (Vertex L) := Finset.univ.filter
          (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
        ∀ E : Finset (Vertex L), E ⊆ (G ∪ B)ᶜ →
          (∀ x ∈ closure (AngularGrid.cell o s m₀),
            ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
          FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
            Ω G E B ≤ cellInformationConstant q c Ctpl N (collarAmplificationConstant q 1 J Δ C)
              (collarAmplificationThreshold q 1 J Δ C) *
              (1 + Real.log s) ^ cellInformationExponent c Ctpl N
                (collarAmplificationConstant q 1 J Δ C)
                (collarAmplificationThreshold q 1 J Δ C) :=
  cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt hcol
    (amplificationBoundAt_collarAmplification hΔ C) hc

open Classical in
/-- The cell conditional-information bound on the original open square, with
sites at `(i + 1, j + 1)`. The same ground vector, full-system gap and arbitrary
union of conditioning cells are retained. A common translation identifies this
placement with the integer-domain placement. The constants are
`cellInformationConstant` and `cellInformationExponent`
(`cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt`), at the collar
constant and threshold and at the amplification constant and threshold
`collarAmplificationConstant` and `collarAmplificationThreshold`.

Source: polynomial-PEPS Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
lines 163–178, and its application in Proposition 3.4, lines 688–737. -/
theorem exists_cell_conditionalMutualInformation_le_square_of_sublinearCollarBound
    {q : ℕ} {J Δ D₀ Ctpl : ℝ} (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBound q 1 J Δ D₀ Ctpl) {c : ℝ} (hc : 0 < c) :
    ∃ C₁ K : ℝ, 0 < C₁ ∧ 0 ≤ K ∧
      ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)),
        m₀ ∉ A →
        ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
          h.IsGappedGroundState E₀ Ω Δ →
          let G : Finset (Vertex L) :=
            Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
          let B : Finset (Vertex L) := Finset.univ.filter
            (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
          ∀ E : Finset (Vertex L), E ⊆ (G ∪ B)ᶜ →
            (∀ x ∈ closure (AngularGrid.cell o s m₀),
              ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
            FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
              Ω G E B ≤ C₁ * (1 + Real.log s) ^ K := by
  obtain ⟨C, N, Ca, Na, hcol, hamp⟩ :=
    exists_sublinearCollarBoundAt_amplificationBoundAt hΔ hcol
  exact ⟨_, _, cellInformationConstant_pos q c Ctpl N Ca Na,
    (cellInformationExponent_pos c Ctpl N Ca Na).le,
    cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt hcol hamp hc⟩

end TNLean.PEPS.Approximation
