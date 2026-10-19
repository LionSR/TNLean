/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.EncodedFrame

/-!
# The statement of the adaptive patch constraint

Proposition 4.1 `prop:patch` supplies, near every center `z` of the plane and at every scale
`0 < u ≤ B₀ log L`, nested-cylinder data whose projector `P` satisfies `‖(1 - P)Ω‖ ≤ L^{-p}`, with
at most `C L^c` cylinder terms. This file states that proposition, with its constants chosen
before the size, the Hamiltonian and the ground vector, and the interface through which the
encoded frames of the dyadic protocol consume it. No proof of the proposition is asserted here.

## Main definitions

* `EncodedFrame.SquarePatch.cylSum`: the sum `∑_{j,ℓ} |v_{jℓ}⟩⟨v_{jℓ}|_{X_j} ⊗ 1` of the
  cylinder projectors of `eq:patch-cylinder-projection`, without the empty-outer convention of
  `SquarePatch.proj`.
* `EncodedFrame.SquarePatch.translate`: the same nested-cylinder data after translating the site
  positions and the center by one vector.
* `EncodedFrame.HasAdaptivePatch`: the conclusion of Proposition 4.1 at one center and scale.
* `EncodedFrame.AdaptivePatchSupply`: that conclusion at every center and admissible scale, for
  one sheet.
* `EncodedFrame.patchAt`: a fixed choice of the supplied patch at every center and scale, so that
  a given center and radius receive the same patch on every sheet.
* `Approximation.latticePos`, `Approximation.cellCenterPos`: the sites of `Λ_L = {1, …, L}²` and
  their translates to the cell centers `(i + 1/2, j + 1/2)`, `0 ≤ i, j < L`.
* `Approximation.AdaptivePatchConstraint`: Proposition 4.1 as a proposition.

## Main results

* `EncodedFrame.SquarePatch.proj_eq_cylSum`: with a nonempty outer sample, the projector of the
  patch is the cylinder sum.
* `EncodedFrame.SquarePatch.norm_act_proj_sub_le`: the error of the projector of a patch is at
  most that of its cylinder sum.
* `EncodedFrame.HasAdaptivePatch.translate`: the conclusion is invariant under translation.
* `Approximation.AdaptivePatchConstraint.supply_cellCenterPos`: Proposition 4.1 supplies patches
  on the cell-center sites used by the dyadic protocol.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Proposition 4.1 `prop:patch`,
  `03-patches.tex`, lines 11–49; the lattice `Λ_L = {1, …, L}²`, `00-introduction.tex`,
  lines 21–25; the translation of the sites to the cell centers, `06-geometry.tex`, lines 62–63;
  the use of one adaptive choice for every sheet, `06-geometry.tex`, lines 114–118.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The statements
here are formalized independently from the manuscript; no upstream Lean text was reused.
-/

open Matrix
open TNLean.Lattice (siteLift)

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Transport of site vectors along an equality of site sets -/

/-- Transport of a vector on the sites of `D` to the sites of an equal set `D'`. -/
def castSiteVec {D D' : Finset ι} (h : D = D') (v : EuclideanSpace ℂ (D → Fin q)) :
    EuclideanSpace ℂ (D' → Fin q) :=
  cast (congrArg (fun D : Finset ι => EuclideanSpace ℂ (D → Fin q)) h) v

omit [Fintype ι] in
theorem norm_castSiteVec {D D' : Finset ι} (h : D = D') (v : EuclideanSpace ℂ (D → Fin q)) :
    ‖castSiteVec h v‖ = ‖v‖ := by
  subst h
  rfl

theorem siteLift_rankOne_castSiteVec {D D' : Finset ι} (h : D = D')
    (v : EuclideanSpace ℂ (D → Fin q)) :
    siteLift D' (rankOne (castSiteVec h v)) = siteLift D (rankOne v) := by
  subst h
  rfl

namespace SquarePatch

variable {pos : ι → ℝ × ℝ} (p : SquarePatch pos q)

/-! ### The cylinder sum -/

/-- The sum `∑_{j,ℓ} |v_{jℓ}⟩⟨v_{jℓ}|_{X_j} ⊗ 1` of the cylinder projectors of the patch.
Unlike `SquarePatch.proj`, it carries no convention for an empty outer sample.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 36–45 (`eq:patch-cylinder-projection`). -/
def cylSum : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  ∑ s : (j : Fin p.n) × Fin (p.dim j), siteLift (p.sample s.1) (rankOne (p.vec s.1 s.2))

/-- With a nonempty outer sample, the projector of a patch is its cylinder sum. -/
theorem proj_eq_cylSum (h : p.outer.Nonempty) : p.proj = p.cylSum := by
  have : IsEmpty {_u : Unit // p.outer = ∅} := ⟨fun u => h.ne_empty u.2⟩
  rw [proj, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, zero_add, cylSum]
  exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun _ => h) _ _ fun _ => rfl

/-- The error of the projector of a patch on a vector is at most that of its cylinder sum: the
two agree for a nonempty outer sample, and the projector is the identity otherwise. -/
theorem norm_act_proj_sub_le (ψ : EuclideanSpace ℂ (ι → Fin q)) :
    ‖act p.proj ψ - ψ‖ ≤ ‖act (1 - p.cylSum) ψ‖ := by
  rcases p.outer.eq_empty_or_nonempty with h | h
  · rw [p.proj_of_outer_eq_empty h, act_one, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [p.proj_eq_cylSum h, act_sub, act_one, norm_sub_rev]

/-- The number of tags of a patch is at most `max 1 (∑_j d_j)`. -/
theorem card_tag_le_max : Fintype.card p.Tag ≤ max 1 (∑ j, p.dim j) := by
  rcases p.outer.eq_empty_or_nonempty with h | h
  · rw [p.card_tag_of_outer_eq_empty h]
    exact le_max_left _ _
  · rw [p.card_tag_of_outer_nonempty h]
    exact le_max_right _ _

/-! ### Translation -/

omit [DecidableEq ι] in
theorem squareSample_translate (pos : ι → ℝ × ℝ) (w c : ℝ × ℝ) (r : ℝ) :
    squareSample pos c r = squareSample (fun x => pos x + w) (c + w) r := by
  ext x
  simp [squareSample, dist_add_right]

/-- The nested-cylinder data of a patch after translating the site positions and the center by
`w`. The square samples, hence the vectors and projectors, are unchanged. -/
def translate (w : ℝ × ℝ) : SquarePatch (fun x => pos x + w) q where
  center := p.center + w
  scale := p.scale
  scale_pos := p.scale_pos
  n := p.n
  radius := p.radius
  radius_mono := p.radius_mono
  scale_le_radius := p.scale_le_radius
  radius_le := p.radius_le
  dim := p.dim
  vec j ℓ := castSiteVec (squareSample_translate pos w p.center (p.radius j)) (p.vec j ℓ)
  norm_vec j ℓ := (norm_castSiteVec _ _).trans (p.norm_vec j ℓ)
  orthogonal s s' h := by
    rw [siteLift_rankOne_castSiteVec, siteLift_rankOne_castSiteVec]
    exact p.orthogonal s s' h

@[simp] theorem translate_center (w : ℝ × ℝ) : (p.translate w).center = p.center + w := rfl

@[simp] theorem translate_scale (w : ℝ × ℝ) : (p.translate w).scale = p.scale := rfl

@[simp] theorem translate_dim (w : ℝ × ℝ) : (p.translate w).dim = p.dim := rfl

theorem translate_outer (w : ℝ × ℝ) : (p.translate w).outer = p.outer :=
  (squareSample_translate pos w p.center _).symm

theorem cylSum_translate (w : ℝ × ℝ) : (p.translate w).cylSum = p.cylSum := by
  refine Finset.sum_congr rfl fun s _ => ?_
  exact siteLift_rankOne_castSiteVec (squareSample_translate pos w p.center (p.radius s.1))
    (p.vec s.1 s.2)

end SquarePatch

/-! ### The conclusion of Proposition 4.1 -/

/-- **Conclusion of Proposition 4.1 at one center and scale.** Nested-cylinder data at the
center `z` with radii between `u` and `2u`, at most `C L^c` cylinder terms in total, and
cylinder sum `P` with `‖(1 - P)Ω‖ ≤ L^{-p}`. That `P` is an orthogonal projection supported on
the sample of the square of radius `2u` follows from the fields of `SquarePatch`.

Polynomial-PEPS manuscript, Proposition 4.1 `prop:patch`, `03-patches.tex`, lines 26–49. -/
def HasAdaptivePatch (pos : ι → ℝ × ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q)) (C c p : ℝ)
    (L : ℕ) (z : ℝ × ℝ) (u : ℝ) : Prop :=
  ∃ P : SquarePatch pos q, P.center = z ∧ P.scale = u ∧
    ((∑ j, P.dim j : ℕ) : ℝ) ≤ C * (L : ℝ) ^ c ∧ ‖act (1 - P.cylSum) Ω‖ ≤ (L : ℝ) ^ (-p)

/-- The conclusion of Proposition 4.1 is invariant under translating the site positions and the
center by one vector. -/
theorem HasAdaptivePatch.translate {pos : ι → ℝ × ℝ} {Ω : EuclideanSpace ℂ (ι → Fin q)}
    {C c p : ℝ} {L : ℕ} {z : ℝ × ℝ} {u : ℝ} (h : HasAdaptivePatch pos Ω C c p L z u)
    (w : ℝ × ℝ) : HasAdaptivePatch (fun x => pos x + w) Ω C c p L (z + w) u := by
  obtain ⟨P, hz, hu, hd, he⟩ := h
  exact ⟨P.translate w, by rw [P.translate_center, hz], hu, hd, by rwa [P.cylSum_translate]⟩

/-- **Proposition 4.1 on one sheet.** The conclusion of Proposition 4.1 at every center `z` and
every scale `0 < u ≤ B₀ log L`.

Polynomial-PEPS manuscript, Proposition 4.1 `prop:patch`, `03-patches.tex`, lines 26–33. -/
def AdaptivePatchSupply (pos : ι → ℝ × ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q))
    (B₀ C c p : ℝ) (L : ℕ) : Prop :=
  ∀ z : ℝ × ℝ, ∀ u : ℝ, 0 < u → u ≤ B₀ * Real.log L → HasAdaptivePatch pos Ω C c p L z u

section PatchAt

variable {pos : ι → ℝ × ℝ} {Ω : EuclideanSpace ℂ (ι → Fin q)} {B₀ C c p : ℝ} {L : ℕ}
  (S : AdaptivePatchSupply pos Ω B₀ C c p L) (z : ℝ × ℝ) {u : ℝ}
  (hu : 0 < u ∧ u ≤ B₀ * Real.log L)

/-- A fixed choice of the patch supplied at the center `z` and scale `u`. It depends only on the
center and the scale, so a given center and radius receive the same patch on every sheet.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 114–118. -/
def patchAt : SquarePatch pos q := (S z u hu.1 hu.2).choose

@[simp] theorem patchAt_center : (patchAt S z hu).center = z := (S z u hu.1 hu.2).choose_spec.1

@[simp] theorem patchAt_scale : (patchAt S z hu).scale = u := (S z u hu.1 hu.2).choose_spec.2.1

theorem sum_dim_patchAt_le : ((∑ j, (patchAt S z hu).dim j : ℕ) : ℝ) ≤ C * (L : ℝ) ^ c :=
  (S z u hu.1 hu.2).choose_spec.2.2.1

theorem norm_act_one_sub_cylSum_patchAt_le :
    ‖act (1 - (patchAt S z hu).cylSum) Ω‖ ≤ (L : ℝ) ^ (-p) :=
  (S z u hu.1 hu.2).choose_spec.2.2.2

/-- The projector of a supplied patch has error at most `L^{-p}`. -/
theorem norm_act_proj_patchAt_sub_le : ‖act (patchAt S z hu).proj Ω - Ω‖ ≤ (L : ℝ) ^ (-p) :=
  ((patchAt S z hu).norm_act_proj_sub_le Ω).trans (norm_act_one_sub_cylSum_patchAt_le S z hu)

/-- A supplied patch has at most `max 1 (C L^c)` tags. -/
theorem card_tag_patchAt_le :
    (Fintype.card (patchAt S z hu).Tag : ℝ) ≤ max 1 (C * (L : ℝ) ^ c) := by
  have h := (patchAt S z hu).card_tag_le_max
  have h' : (Fintype.card (patchAt S z hu).Tag : ℝ) ≤
      max 1 ((∑ j, (patchAt S z hu).dim j : ℕ) : ℝ) := by
    exact_mod_cast h
  exact h'.trans (max_le_max le_rfl (sum_dim_patchAt_le S z hu))

end PatchAt

end TNLean.PEPS.EncodedFrame

namespace TNLean.PEPS.Approximation

open EncodedFrame

/-- The position of a site of `Λ_L = {1, …, L}²`: the zero-based coordinates `(i, j)` are the
point `(i + 1, j + 1)`.

Polynomial-PEPS manuscript, `00-introduction.tex`, lines 21–22. -/
def latticePos (L : ℕ) (v : SquareLatticeVertex L L) : ℝ × ℝ :=
  (((v.1 : ℕ) : ℝ) + 1, ((v.2 : ℕ) : ℝ) + 1)

/-- The cell-center position `(i + 1/2, j + 1/2)` of a site, `0 ≤ i, j < L`: the lattice
translated as in the dyadic protocol.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 62–63. -/
def cellCenterPos (L : ℕ) (v : SquareLatticeVertex L L) : ℝ × ℝ :=
  (((v.1 : ℕ) : ℝ) + 1 / 2, ((v.2 : ℕ) : ℝ) + 1 / 2)

theorem latticePos_add_eq_cellCenterPos (L : ℕ) :
    (fun v => latticePos L v + (-(1 / 2), -(1 / 2))) = cellCenterPos L := by
  funext v
  simp only [latticePos, cellCenterPos, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

/-- **Proposition 4.1 (Adaptive patch constraint).** Fix `q ≥ 2`, `J, Δ > 0`, `B₀ > 0` and
`p > 0`. There are constants `C, c > 0` such that for every `L ≥ 2`, every square Hamiltonian
with bounds `J` and every gapped unit ground vector `Ω` with gap `Δ`, every center `z` of the
plane and every `0 < u ≤ B₀ log L` admit nested-cylinder data with radii between `u` and `2u`, at
most `C L^c` cylinder terms, and cylinder projector `P` with `‖(1 - P)Ω‖ ≤ L^{-p}`.

It enters the dyadic protocol as a hypothesis here; the proposition is proved as
`adaptivePatchConstraint` in `TNLean.PEPS.Approximation.PolynomialPEPSTheorem`.

Polynomial-PEPS manuscript, Proposition 4.1 `prop:patch`, `03-patches.tex`, lines 26–49, with
the parameters of Theorem 1.1 fixed as in `01-preliminaries.tex`, lines 3–10. -/
def AdaptivePatchConstraint : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ → ∀ B₀ p : ℝ, 0 < B₀ → 0 < p →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ → AdaptivePatchSupply (latticePos L) Ω B₀ C c p L

/-- Translating the sites to the cell centers preserves the supply of patches. -/
theorem AdaptivePatchSupply.cellCenterPos {L q : ℕ} {Ω : StateSpace L q} {B₀ C c p : ℝ}
    (S : AdaptivePatchSupply (latticePos L) Ω B₀ C c p L) :
    AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c p L := by
  intro z u hu hu'
  have h := (S (z + (1 / 2, 1 / 2)) u hu hu').translate (-(1 / 2), -(1 / 2))
  rw [latticePos_add_eq_cellCenterPos] at h
  convert h using 1
  ext <;> simp

/-- **Proposition 4.1 on the cell-center sites.** Under Proposition 4.1, the constants `C, c`
chosen for `q, J, Δ, B₀, p` supply patches on the cell-center sites of every gapped unit ground
vector.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–49, and `06-geometry.tex`, lines 62–63. -/
theorem AdaptivePatchConstraint.supply_cellCenterPos (H : AdaptivePatchConstraint) {q : ℕ}
    (hq : 2 ≤ q) {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) {B₀ p : ℝ} (hB₀ : 0 < B₀) (hp : 0 < p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ → AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c p L := by
  obtain ⟨C, c, hC, hc, hall⟩ := H q hq J Δ hJ hΔ B₀ p hB₀ hp
  exact ⟨C, c, hC, hc, fun L hL h E₀ Ω hΩ =>
    AdaptivePatchSupply.cellCenterPos (hall L hL h E₀ Ω hΩ)⟩

end TNLean.PEPS.Approximation
