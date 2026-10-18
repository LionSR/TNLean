/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRunTemplate
import TNLean.PEPS.AreaLaw.Geometry.IsolatedStars
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendants

/-!
# Templates for belt tiles and replacements

The belt tiles and the replacements of Proposition 11.2 have exact templates
in the sense of Definition 9.3. A belt tile of layer `k` is a run of the fan of
a fine cell of side `u = t_k`. Its lattice sample is a template with piece size
`s₀ = u`, scanner scale `n = ⌈C_B u⌉` and at most eight triangles. A replacement
with removal half-side `u` is a run of the eight-triangle fan of its removal
square, of side `2 u`, whose triangles join the center to the corners and side
midpoints. Its lattice sample is a template with `s₀ = 2 u`, `n = ⌈C_B u⌉` and
at most eight triangles. This includes a run of angle greater than `π` (a wide
sector) and the whole square (a homogeneous square). The single constant
`C_B = 32 C_tpl` serves both kinds; it depends only on `C_tpl` and is fixed
before the stopping scale `S_*` and the lower layer index `k₀`. Finally, the
dilation count `L = ⌊n ^ (1 - ℓ)⌋` is `o(u)`.

A replacement birth region is defined as the image under `x ↦ v + u • x` of a
run of the normalized fan on `[-1, 1]²`. When `u = 2 ^ m` with `m : ℕ`, the
image is the region of a run of the actual fan of the cell of side `2 u`
centered at `v`; `cellFanRunRegion_centered_image` records this, and the
existing fan-run template then applies.

**Scope restriction (lattice point and stopping scale):** `initialBelt_exists_template`,
`repairReplacement_exists_template` and `exists_belt_replacement_templates` assume that
the region contains a lattice point, which Definition 9.3 needs for a nonempty template,
and the replacement statements assume `S_* ≥ 1`. The source applies these templates only
to regions meeting the cut and chooses `S_*` large. The lattice-point premise is
discharged for every belt tile or replacement whose current region at some later
generation meets the cut by `repairStage_exists_integerPoint_mem_birth_of_oldInclusion`
(`RepairBirthLatticePoint.lean`), and the premise `S_* ≥ 1` by the choice `S_* ≥ 2`
in `twoFamilyDecomposition` (`TwoFamilyAssembly.lean`). Documented in
`docs/paper-gaps/arealaw2d_belt_replacement_template_scope.tex`.

## Main statements

* `cellFanRunRegion_centered_image`: a transported normalized fan run is an
  actual fan run of the centered cell.
* `initialBelt_exists_template`: the template of an initial belt tile.
* `repairReplacement_exists_template`: the template of a replacement of any
  generation.
* `exists_belt_replacement_templates`: one constant `C_B` for both kinds.
* `eventually_beltReplacementScaleLimit`: `⌊⌈C_B u⌉ ^ (1 - ℓ)⌋ = o(u)`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, lines 731–740, with
  the fan runs (lines 299–318), the replacement instructions (lines 393–417)
  and the threshold order (lines 756–762); the template fields are those of
  Definition 9.3 (`scanner:template`, `08-scanner.tex`, lines 546–564).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Transport of the normalized fan -/

/-- The scaling `x ↦ c + r • x` with `r ≠ 0` is injective. -/
private theorem centeredScaling_injective (c : ℝ × ℝ) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (fun x : ℝ × ℝ ↦ c + r • x) :=
  fun _ _ h ↦ smul_right_injective _ hr (add_left_cancel h)

/-- The scaling carries the normalized segment starts to the actual ones. -/
private theorem cellFanStart_centered (c : ℝ × ℝ) (ℓ : ℕ) (split : Fin 4 → Bool)
    (s : CellFanSlot split) :
    cellFanStart (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0) split s =
      c + ((2 : ℝ) ^ ℓ / 2) • cellFanStart (-1, -1) 1 (0, 0) split s := by
  rw [cellFanStart_eq, cellFanStart_eq]
  ext <;> simp [cellFanCenter]

/-- The scaling carries the normalized segment ends to the actual ones. -/
private theorem cellFanEnd_centered (c : ℝ × ℝ) (ℓ : ℕ) (split : Fin 4 → Bool)
    (s : CellFanSlot split) :
    cellFanEnd (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0) split s =
      c + ((2 : ℝ) ^ ℓ / 2) • cellFanEnd (-1, -1) 1 (0, 0) split s := by
  rw [cellFanEnd_eq, cellFanEnd_eq]
  ext <;> simp [cellFanCenter]

/-- The run graph of a centered actual fan is the run graph of the normalized
fan with the same split and colors.
Auxiliary to area-law Section 11, lines 313–318 and 404–417. -/
theorem cellFanRunGraph_centered (c : ℝ × ℝ) (ℓ : ℕ) (split : Fin 4 → Bool)
    (family : CellFanSlot split → Fin 2) :
    cellFanRunGraph (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0) split family =
      cellFanRunGraph (-1, -1) 1 (0, 0) split family := by
  have hinj := centeredScaling_injective c (r := (2 : ℝ) ^ ℓ / 2) (by positivity)
  ext i j
  simp only [cellFanRunGraph, cellFanStart_centered, cellFanEnd_centered, hinj.eq_iff]

/-- Transport of a connected component along an equality of graphs keeps its
support. -/
private theorem supp_map_ofLE {V : Type*} {G G' : SimpleGraph V} (h : G = G')
    (hle : G ≤ G') (R : G.ConnectedComponent) :
    (R.map (SimpleGraph.Hom.ofLE hle)).supp = R.supp := by
  subst h
  induction R using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    ext w
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- **A transported normalized fan run is an actual fan run.** The image of a
run of the normalized fan on `[-1, 1]²` under `x ↦ c + (2 ^ ℓ / 2) • x` is the
region of a run of the actual fan of the cell of side `2 ^ ℓ` centered at `c`.
Auxiliary to area-law Section 11, lines 404–417 ("a union of at most eight of
the triangles from the center to side corners and midpoints") and 735–737. -/
theorem cellFanRunRegion_centered_image (c : ℝ × ℝ) (ℓ : ℕ) (split : Fin 4 → Bool)
    (family : CellFanSlot split → Fin 2)
    (R : CellFanRun (-1, -1) 1 (0, 0) split family) :
    ∃ R' : CellFanRun (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0) split family,
      cellFanRunRegion (c.1 - (2 : ℝ) ^ ℓ / 2, c.2 - (2 : ℝ) ^ ℓ / 2) ℓ (0, 0) split family R' =
        (fun x : ℝ × ℝ ↦ c + ((2 : ℝ) ^ ℓ / 2) • x) ''
          cellFanRunRegion (-1, -1) 1 (0, 0) split family R := by
  have hG := (cellFanRunGraph_centered c ℓ split family).symm
  refine ⟨R.map (SimpleGraph.Hom.ofLE hG.le), ?_⟩
  simp only [cellFanRunRegion, Set.image_iUnion₂, cellFanPolygon_region_eq_image]
  rw [supp_map_ofLE hG]

/-! ### Belt tiles -/

/-- **Templates of initial belt tiles.** For `C_tpl ≥ 1` and `C_B ≥ 16 C_tpl`,
the lattice sample of an initial belt tile of layer `k` is exactly the point
set of a template with piece size `s₀ = u = t_k` and scanner scale
`n = ⌈C_B u⌉`, made of at most eight sampled fan triangles. A lattice point in
the tile supplies the nonemptiness required by Definition 9.3; the source uses
these templates only for identifiers whose final regions meet the cut (lines
776–779).
Source: area-law Section 11, `10-geometry.tex`, lines 731–734 and 737–739,
with the belt fan runs of lines 299–318 and Definition 9.3 (`scanner:template`,
`08-scanner.tex`, lines 546–564). -/
theorem initialBelt_exists_template (Ctpl CB : ℝ) (hCtpl : 1 ≤ Ctpl)
    (hCB : 16 * Ctpl ≤ CB) (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (x : InitialRegionIndex o k₀ Z C a b hC h₀) (s) (hxs : x = Sum.inr (Sum.inr s))
    (w : ℤ × ℤ) (hw : integerPoint w ∈ initialBirthRegion o k₀ Z C a b hC h₀ x) :
    ∃ T : Template Ctpl ⌈CB * (2 : ℝ) ^ fineScaleIndex s.1.val⌉₊
        (2 ^ fineScaleIndex s.1.val),
      T.pieceCount ≤ 8 ∧
        ∀ y : ℤ × ℤ, y ∈ T.points ↔
          integerPoint y ∈ initialBirthRegion o k₀ Z C a b hC h₀ x := by
  obtain ⟨⟨k, hk⟩, ⟨z, hz⟩, R⟩ := s
  subst hxs
  exact CellFanRun.exists_template Ctpl CB hCtpl hCB o _ z _ _ R w hw

/-! ### Replacements -/

/-- A removal half-side at least one is a natural power of two. -/
theorem exists_nat_eq_repairHalfSide {S : ℝ} (h : 1 ≤ repairHalfSide S) :
    ∃ m : ℕ, repairHalfSide S = (2 : ℝ) ^ m := by
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((one_le_zpow_iff_right₀ one_lt_two).mp h)
  exact ⟨m, by rw [repairHalfSide, hm, zpow_natCast]⟩

/-- **Template of a transported fan run.** Let `u = d(S) ≥ 1`. For
`C_tpl ≥ 1` and `C_B ≥ 32 C_tpl`, the lattice sample of a replacement birth
region with removal half-side `u` is exactly the point set of a template with
piece size `s₀ = 2 u` and scanner scale `n = ⌈C_B u⌉`, made of at most eight
sampled triangles from the center of the removal square to its corners and
side midpoints. Every run is covered, including one of angle greater than `π`
and the whole square.
Source: area-law Section 11, `10-geometry.tex`, lines 734–739, with the
replacement runs of lines 404–417 and Definition 9.3 (`scanner:template`). -/
theorem repairReplacementBirthRegion_exists_template (Ctpl CB : ℝ) (hCtpl : 1 ≤ Ctpl)
    (hCB : 32 * Ctpl ≤ CB) {ι : Type*} (v : ℝ × ℝ) (S : ℝ) (hS : 1 ≤ repairHalfSide S)
    (ξ : ι → Fin 2) (σ : RepairFanSlot → ι) (H : RepairFanRun ξ σ) (w : ℤ × ℤ)
    (hw : integerPoint w ∈ repairReplacementBirthRegion v S ξ σ H) :
    ∃ s₀ : ℕ, (s₀ : ℝ) = 2 * repairHalfSide S ∧
      ∃ T : Template Ctpl ⌈CB * repairHalfSide S⌉₊ s₀,
        T.pieceCount ≤ 8 ∧
          ∀ y : ℤ × ℤ, y ∈ T.points ↔
            integerPoint y ∈ repairReplacementBirthRegion v S ξ σ H := by
  obtain ⟨m, hm⟩ := exists_nat_eq_repairHalfSide hS
  have hhalf : (2 : ℝ) ^ (m + 1) / 2 = repairHalfSide S := by
    rw [hm, pow_succ]
    ring
  obtain ⟨R', hR'⟩ := cellFanRunRegion_centered_image v (m + 1) repairFanSplit
    (repairExteriorColor ξ σ) H
  have hbirth : repairReplacementBirthRegion v S ξ σ H =
      cellFanRunRegion (v.1 - (2 : ℝ) ^ (m + 1) / 2, v.2 - (2 : ℝ) ^ (m + 1) / 2) (m + 1)
        (0, 0) repairFanSplit (repairExteriorColor ξ σ) R' := by
    rw [hR', hhalf]
    rfl
  rw [hbirth] at hw ⊢
  have hn : ⌈CB * repairHalfSide S⌉₊ = ⌈CB / 2 * (2 : ℝ) ^ (m + 1)⌉₊ := by
    rw [← hhalf]
    ring_nf
  refine ⟨2 ^ (m + 1), ?_, ?_⟩
  · push_cast
    rw [← hhalf]
    ring
  rw [hn]
  exact CellFanRun.exists_template Ctpl (CB / 2) hCtpl (by linarith) _ (m + 1) (0, 0)
    repairFanSplit _ R' w hw

section Stages

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- **Templates of replacements.** Let `S_* ≥ 1`, `C_tpl ≥ 1` and
`C_B ≥ 32 C_tpl`. Every replacement of generation `j + 1`, with parent mark `m`
and removal half-side `u = d(S_m)`, whose birth region contains a lattice point,
has lattice sample exactly the point set of a template with piece size
`s₀ = 2 u`, scanner scale `n = ⌈C_B u⌉` and at most eight sampled triangles.
These are the forms `s₀ ≤ 2 u` and `n ≤ ⌈C_B u⌉` used by
`descendant_birthTemplate_cutClearance`. The lower bound on `S_*` is part of the
source's choice of a large stopping scale (lines 380–394 and 549–552); the
lattice point supplies the nonemptiness of Definition 9.3, as for belt tiles.
Source: area-law Section 11, `10-geometry.tex`, lines 734–739, with the
replacement instructions of lines 393–417. -/
theorem repairReplacement_exists_template (hS : 1 ≤ Sstar) (Ctpl CB : ℝ)
    (hCtpl : 1 ≤ Ctpl) (hCB : 32 * Ctpl ≤ CB) (j : ℕ) (x : (𝔇 (j + 1)).regionIndex)
    (m : (𝔇 j).markIndex) (hx : repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m)
    (w : ℤ × ℤ) (hw : integerPoint w ∈ (𝔇 (j + 1)).birth x) :
    ∃ s₀ : ℕ, (s₀ : ℝ) = 2 * repairHalfSide ((𝔇 j).scale m) ∧
      ∃ T : Template Ctpl ⌈CB * repairHalfSide ((𝔇 j).scale m)⌉₊ s₀,
        T.pieceCount ≤ 8 ∧
          ∀ y : ℤ × ℤ, y ∈ T.points ↔ integerPoint y ∈ (𝔇 (j + 1)).birth x := by
  let P : Set (ℝ × ℝ) → Prop := fun B ↦ integerPoint w ∈ B →
    ∃ s₀ : ℕ, (s₀ : ℝ) = 2 * repairHalfSide ((𝔇 j).scale m) ∧
      ∃ T : Template Ctpl ⌈CB * repairHalfSide ((𝔇 j).scale m)⌉₊ s₀,
        T.pieceCount ≤ 8 ∧ ∀ y : ℤ × ℤ, y ∈ T.points ↔ integerPoint y ∈ B
  revert x
  let : Nonempty (𝔇 j).regionIndex := ⟨(𝔇 j).dummy⟩
  change ∀ x : RepairRegionIndex j (𝔇 j).scale Sstar (𝔇 j).color
      (repairCurrentAssignments (𝔇 j).current (𝔇 j).location (𝔇 j).scale),
    Sum.elim (fun _ ↦ none) (fun q ↦ some q.2.1.val) x = some m →
      P (repairNextBirthRegion j (𝔇 j).birth (𝔇 j).location (𝔇 j).scale Sstar (𝔇 j).color
        (repairCurrentAssignments (𝔇 j).current (𝔇 j).location (𝔇 j).scale) x)
  rintro (i | ⟨_, ⟨p, hp⟩, H⟩) hx
  · simp at hx
  · obtain rfl : p = m := by simpa using hx
    exact repairReplacementBirthRegion_exists_template Ctpl CB hCtpl hCB _ _
      (le_trans hS hp) _ _ H w

end Stages

/-! ### One scale constant for both kinds -/

/-- **Belt and replacement templates with one scale constant.** For every
`C_tpl ≥ 1` there is one constant `C_B > 0`, depending only on `C_tpl`, such
that the following hold for every geometric datum, every lower layer index
`k₀` and every stopping scale `S_* ≥ 1`.
* Every initial belt tile of layer `k` containing a lattice point has a
  template with `s₀ = u = t_k`, `n = ⌈C_B u⌉` and at most eight pieces.
* Every replacement with removal half-side `u` whose birth region contains a
  lattice point has a template with `s₀ = 2 u`, `n = ⌈C_B u⌉` and at most eight
  pieces.
In both cases the template fields give `n ≥ C_tpl N₀ (s₀ + 1)` and
`diam_∞ T ≤ n`. The constant is `C_B = 32 C_tpl`; it is fixed before `S_*` and
`k₀`, as in the threshold order of lines 761–762.
Source: area-law Section 11, `10-geometry.tex`, lines 731–739 and 761–762. -/
theorem exists_belt_replacement_templates (Ctpl : ℝ) (hCtpl : 1 ≤ Ctpl) :
    ∃ CB : ℝ, 0 < CB ∧
      (∀ (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
        (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (x : InitialRegionIndex o k₀ Z C a b hC h₀) s,
        x = Sum.inr (Sum.inr s) → ∀ w : ℤ × ℤ,
          integerPoint w ∈ initialBirthRegion o k₀ Z C a b hC h₀ x →
          ∃ T : Template Ctpl ⌈CB * (2 : ℝ) ^ fineScaleIndex s.1.val⌉₊
              (2 ^ fineScaleIndex s.1.val),
            T.pieceCount ≤ 8 ∧
              ∀ y : ℤ × ℤ, y ∈ T.points ↔
                integerPoint y ∈ initialBirthRegion o k₀ Z C a b hC h₀ x) ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ), 1 ≤ Sstar →
        ∀ (j : ℕ) (x : (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).regionIndex)
          (m : (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex),
          repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m → ∀ w : ℤ × ℤ,
          integerPoint w ∈ (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).birth x →
          ∃ s₀ : ℕ,
            (s₀ : ℝ) = 2 * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m) ∧
            ∃ T : Template Ctpl
                ⌈CB * repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale m)⌉₊ s₀,
              T.pieceCount ≤ 8 ∧
                ∀ y : ℤ × ℤ, y ∈ T.points ↔
                  integerPoint y ∈ (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).birth x := by
  refine ⟨32 * Ctpl, by linarith, fun o k₀ Z C a b hC h₀ x s hxs w hw ↦ ?_,
    fun o Λ A C k₀ hC h₀ Sstar hS j x m hx w hw ↦ ?_⟩
  · exact initialBelt_exists_template Ctpl _ hCtpl (by linarith) o k₀ Z C a b hC h₀ x s hxs w hw
  · exact repairReplacement_exists_template o Λ A C k₀ hC h₀ Sstar hS Ctpl _ hCtpl le_rfl
      j x m hx w hw

/-! ### The dilation count -/

/-- **The dilation count is `o(u)`.** For every `C_B` and `ε > 0`, every
sufficiently large `u` satisfies `⌊⌈C_B u⌉ ^ (1 - ℓ)⌋ ≤ ε u`. This is the
statement `L = ⌊n ^ (1 - ℓ)⌋ = o(u)` for the belt and replacement scanner scale
`n = ⌈C_B u⌉`, with `u = t_k` for a belt tile and `u` the removal half-side for
a replacement.
Source: area-law Section 11, `10-geometry.tex`, line 740, with
`L = ⌊n ^ (1 - ℓ)⌋` as in `geometry:primary-limits` (lines 725–729). -/
theorem eventually_beltReplacementScaleLimit (CB : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop,
      (⌊(⌈CB * u⌉₊ : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤ ε * u := by
  have hℓ : (0 : ℝ) < Exponents.geometryEll := by norm_num [Exponents.geometryEll]
  have hℓ1 : (0 : ℝ) ≤ 1 - Exponents.geometryEll := by norm_num [Exponents.geometryEll]
  set e : ℝ := 1 - (Exponents.geometryEll : ℝ)
  set B : ℝ := max CB 0 + 1
  have hB : 0 < B := by positivity
  have hBe : 0 < B ^ e := Real.rpow_pos_of_pos hB e
  have hlim := tendsto_rpow_neg_atTop hℓ
  filter_upwards [hlim.eventually (ge_mem_nhds (div_pos hε hBe)), eventually_ge_atTop 1]
    with u hu hu1
  have hu0 : 0 < u := by linarith
  have hceil : (⌈CB * u⌉₊ : ℝ) ≤ B * u := by
    have hmono : (⌈CB * u⌉₊ : ℝ) ≤ ⌈max CB 0 * u⌉₊ := by
      exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left CB 0) hu0.le)
    have hlt := Nat.ceil_lt_add_one (mul_nonneg (le_max_right CB 0) hu0.le)
    nlinarith
  have hsplit : u ^ e = u ^ (-(Exponents.geometryEll : ℝ)) * u := by
    rw [← Real.rpow_add_one hu0.ne']
    congr 1
    ring
  calc (⌊(⌈CB * u⌉₊ : ℝ) ^ e⌋₊ : ℝ) ≤ (⌈CB * u⌉₊ : ℝ) ^ e :=
        Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) e)
    _ ≤ (B * u) ^ e := Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hℓ1
    _ = B ^ e * (u ^ (-(Exponents.geometryEll : ℝ)) * u) := by
        rw [Real.mul_rpow hB.le hu0.le, hsplit]
    _ ≤ B ^ e * (ε / B ^ e * u) := by gcongr
    _ = ε * u := by field_simp

end TNLean.PEPS.AreaLaw.Geometry
