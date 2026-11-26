/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionEntropy
import TNLean.PEPS.Approximation.Guides.AngularSeparationBridges
import TNLean.PEPS.Tensor.SquareLattice.Basic
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.PEPS.Approximation.Cells.AngularAnnularCells
import QICLean.ManyBody.Entropy.RegionStrongSubadditivity

/-!
# Information under angular separation

Proposition 3.4 (`prop:angular`) of the polynomial-PEPS manuscript bounds the mutual information
`I_Ω(X : E)` of a gapped ground vector by `L^{-p}` when `X` is separated from `E` by
`a max{D log L, min(n, d_V)}`. This module records that assertion as the proposition
`AngularInformationBound`, in the source's form. `AngularInformationFromGap` proves it from
the original Hamiltonian and full-system gap, using the cell estimate established in
`CellConditionalInformationFromGap`. The bulk births, deaths and exchanges of Section 7 may
use the proposition as a premise independently of its proof.

## Main definitions

* `sitePosition`: the site `(i, j)` of the open square, placed at `(i + 1, j + 1)`, so that the
  physical sites form `Λ_L = {1, …, L}²`.
* `AngularInformationBound`: Proposition 3.4, for fixed `q`, `J` and `Δ`.
* `IsAngularScale`: the conclusion of Proposition 3.4 at one integer accuracy `p`, for one slope
  `D` and one size threshold `L₀`, for every state of a family `G`, and for sites placed at any
  common translation of `Λ_L`.

## Main results

* `IsAngularScale.of_sitePosition`: the conclusion of Proposition 3.4 for one slope and threshold
  at the sites `Λ_L` gives an angular scale.
* `AngularInformationBound.exists_isAngularScale`: Proposition 3.4 supplies such a slope and
  threshold. Section 7 places the sites at the cell centers `(i + 1/2, j + 1/2)`
  (`06-geometry.tex`, lines 62–63), a translation of `Λ_L`; the statement is invariant under a
  common translation of the sites and the marked points.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 3.4 `prop:angular`,
  `02-information.tex`, lines 635–658; the model, `00-introduction.tex`, lines 21–49; the use at
  accuracy `L^{-60}`, `06-geometry.tex`, lines 440–445.

## The finite annular information induction

At each dyadic scale, the old selected cells and the current enlarged
exterior lie inside the two regions controlled at the preceding scale.
The first old group is empty. The exact finite set of new cells has one
uniform cardinality bound. A reset estimate at each scale consequently
gives the same information bound at every scale, including the last one.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`,
lines 681–785, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The per-scale reset estimate is an explicit premise of this induction
lemma; it is supplied by the separate cell and information-reset estimates.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (Config Qudits SquareLatticeVertex)

section

open scoped Matrix.Norms.L2Operator

open ManyBody (SquareLatticeVertex SquareInteraction)

noncomputable section

namespace TNLean.PEPS.Approximation

open Set

open ManyBody (IsGapped groundSpace)

/-- The site `(i, j)` of the open square of side `L`, placed in the plane at `(i + 1, j + 1)`, so
that the sites form `Λ_L = {1, …, L}²`. Source: `00-introduction.tex`, line 21. -/
def sitePosition (L : ℕ) (v : SquareLatticeVertex L L) : ℝ × ℝ :=
  (((v.1 : ℕ) : ℝ) + 1, ((v.2 : ℕ) : ℝ) + 1)

/-- **Proposition 3.4 (information under angular separation).** Fix `q`, `J` and `Δ`. For every
`a > 0`, `A₀ ≥ 1`, integer `m₀ ≥ 0` and `p > 0` there are `D` and a size threshold `L₀` such that
the following holds for every `L ≥ L₀`, every Hamiltonian of the model on the open square of
side `L` with a unit ground vector `Ω` and full-system gap `Δ`, every set `V` of at most `m₀`
marked points in the plane, every pair of disjoint sets `X`, `E` of sites, and every scale `n`
with `D log L ≤ n ≤ A₀ L` and `diam_∞ X ≤ A₀ n`: if every `x ∈ X` lies at sup distance at least
`a max{D log L, min(n, d_V(x))}` from `E`, with `d_∅ = +∞`, then `I_Ω(X : E) ≤ L^{-p}`.

The constants `D` and `L₀` are chosen before the marked points, the sets and the Hamiltonian,
as in the source. The separation is stated pointwise (`AngularSeparation`), which handles an
empty `E` with the source's convention that distances to the empty set are infinite;
`cappedMarkDistance` implements `min(n, d_V)` with `d_∅ = +∞`. The diameter bound is stated
pairwise. Its proof is given in `TNLean.PEPS.Approximation.AngularInformationFromGap`.

Source: polynomial-PEPS Proposition 3.4 `prop:angular`, `02-information.tex`, lines 635–658,
with the conventions of lines 4–13, under `eq:model` and `eq:global-gap`
(`00-introduction.tex`, lines 21–49). -/
def AngularInformationBound (q : ℕ) (J Δ : ℝ) : Prop :=
  ∀ a A₀ : ℝ, 0 < a → 1 ≤ A₀ → ∀ m₀ : ℕ, ∀ p : ℝ, 0 < p →
    ∃ D L₀ : ℝ, ∀ L : ℕ, L₀ ≤ L →
      ∀ h : SquareInteraction L q, h.hamiltonian.IsHermitian → (∀ i, ‖h.term i‖ ≤ J) → ∀ E₀ : ℝ,
          ∀ Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ V : Finset (ℝ × ℝ), V.card ≤ m₀ →
        ∀ X E : Finset (SquareLatticeVertex L L), Disjoint X E →
        ∀ n : ℝ, D * Real.log L ≤ n → n ≤ A₀ * L →
          (∀ x ∈ X, ∀ y ∈ X, dist (sitePosition L x) (sitePosition L y) ≤ A₀ * n) →
          AngularSeparation (sitePosition L '' X) (sitePosition L '' E) n (D * Real.log L) a V →
          ManyBody.regionMutualInformation Ω X E ≤
            (L : ℝ) ^ (-p)

/-- **One slope and one threshold for Proposition 3.4 at accuracy `L^{-p}`.** For every
`L ≥ L₀`, every state `Ω` of the family `G`, every placement
`pos` of the sites at a common translation `c` of `Λ_L`, every set `V` of at most `m₀` marked
points and all disjoint `X`, `E` and `n` as in Proposition 3.4, the angular separation measured
with `pos` gives `I_Ω(X : E) ≤ L^{-p}`. The statement of Proposition 3.4 is the family
`IsSquareGroundState q J Δ` of unit gapped ground vectors of the model.

Source: `02-information.tex`, lines 635–658, used at `p = 60` in `06-geometry.tex`,
lines 440–445. -/
def IsAngularScale (q : ℕ)
    (G : ∀ L : ℕ, EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)) → Prop) (a A₀ : ℝ)
    (m₀ p : ℕ)
    (D L₀ : ℝ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L →
    ∀ Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)), G L Ω →
      ∀ (pos : SquareLatticeVertex L L → ℝ × ℝ) (c : ℝ × ℝ),
        (∀ v, pos v = sitePosition L v + c) →
      ∀ V : Finset (ℝ × ℝ), V.card ≤ m₀ →
      ∀ X E : Finset (SquareLatticeVertex L L), Disjoint X E →
      ∀ n : ℝ, D * Real.log L ≤ n → n ≤ A₀ * L →
        (∀ x ∈ X, ∀ y ∈ X, dist (pos x) (pos y) ≤ A₀ * n) →
        AngularSeparation (pos '' X) (pos '' E) n (D * Real.log L) a V →
        ManyBody.regionMutualInformation Ω X E ≤
          (L : ℝ) ^ (-(p : ℤ))

/-- **A slope and threshold of Proposition 3.4 at the sites `Λ_L` give an angular scale.** If
the conclusion of Proposition 3.4 at accuracy `L^{-p}` holds for the slope `D` and threshold
`L₀` for every state of a family `G` with the sites placed at `Λ_L`, then it holds for sites
placed at any common translation of `Λ_L`; the marked points are translated with the sites.
Source: `02-information.tex`, lines 635–658; `06-geometry.tex`, lines 62–63 and 440–445. -/
theorem IsAngularScale.of_sitePosition {q : ℕ}
    {G : ∀ L : ℕ, EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)) → Prop}
    {a A₀ D L₀ : ℝ} {m₀ p : ℕ}
    (hD : ∀ L : ℕ, L₀ ≤ L →
      ∀ Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)), G L Ω →
        ∀ V : Finset (ℝ × ℝ), V.card ≤ m₀ →
        ∀ X E : Finset (SquareLatticeVertex L L), Disjoint X E →
        ∀ n : ℝ, D * Real.log L ≤ n → n ≤ A₀ * L →
          (∀ x ∈ X, ∀ y ∈ X, dist (sitePosition L x) (sitePosition L y) ≤ A₀ * n) →
          AngularSeparation (sitePosition L '' X) (sitePosition L '' E) n (D * Real.log L) a V →
          ManyBody.regionMutualInformation Ω X E ≤
            (L : ℝ) ^ (-(p : ℝ))) :
    IsAngularScale q G a A₀ m₀ p D L₀ := by
  classical
  intro L hL Ω hΩ pos c hpos V hV X E hXE n hn hnL hdiam hsep
  have himage : ∀ S : Set (SquareLatticeVertex L L),
      (· + -c) '' (pos '' S) = sitePosition L '' S := by
    intro S
    rw [image_image]
    exact image_congr fun v _ => by rw [hpos, add_neg_cancel_right]
  have hI := hD L hL Ω hΩ (V.image (· + -c)) ((Finset.card_image_le).trans hV) X E hXE n
    hn hnL (fun x hx y hy => by simpa only [hpos, dist_add_right] using hdiam x hx y hy)
    (by simpa only [himage] using hsep.translate (-c))
  have hpow : (L : ℝ) ^ (-(p : ℝ)) = (L : ℝ) ^ (-(p : ℤ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rwa [hpow] at hI

/-- **Proposition 3.4 supplies a slope and a threshold at every positive integer accuracy,** for
sites placed at any common translation of `Λ_L`. The marked points are translated with the
sites. Source: `02-information.tex`, lines 635–658; `06-geometry.tex`, lines 62–63 and
440–445. -/
theorem AngularInformationBound.exists_isAngularScale {q : ℕ} {J Δ : ℝ}
    (hang : AngularInformationBound q J Δ) {a A₀ : ℝ} (ha : 0 < a) (hA₀ : 1 ≤ A₀) (m₀ : ℕ)
    {p : ℕ} (hp : 0 < p) :
    ∃ D L₀ : ℝ, IsAngularScale q (IsSquareGroundState q J Δ) a A₀ m₀ p D L₀ := by
  obtain ⟨D, L₀, hD⟩ := hang a A₀ ha hA₀ m₀ p (by exact_mod_cast hp)
  exact ⟨D, L₀, IsAngularScale.of_sitePosition fun L hL Ω ⟨h, hh, hhJ, E₀, hΩ, hgap, hspan⟩ ↦
    hD L hL h hh hhJ E₀ Ω hΩ hgap hspan⟩

end TNLean.PEPS.Approximation
end

end

section

open ManyBody (SquareLatticeVertex)

namespace TNLean.PEPS.Approximation

open AngularGrid

open Classical in
/-- The literal annular induction with its per-scale reset estimate stated
explicitly. All physical inclusions, the initial empty group, the new-cell
count, and the final removal of padding follow from the geometric data.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 681–785. -/
theorem mutualInformation_le_of_annular_reset {L q : ℕ}
    (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))) (hΩ : ‖Ω‖ = 1)
    {X E : Finset (SquareLatticeVertex L L)}
    {n t a a' d A₀ ε : ℝ} {V : Finset (ℝ × ℝ)} {m₀ : ℕ}
    (hn : 0 < n) (ha : 0 ≤ a) (ha' : 0 < a') (ha'a : a' < a / 100)
    (hd : 0 < d) (hda' : d < a' / 4) (hε : 0 ≤ ε)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X,
      dist (sitePosition L x) (sitePosition L y) ≤ A₀ * n)
    (hV : V.card ≤ m₀)
    (hsep : AngularSeparation (sitePosition L '' X) (sitePosition L '' E) n t a V)
    (c : DyadicCutoff n t) :
    let sample : Set (ℝ × ℝ) → Finset (SquareLatticeVertex L L) :=
      fun Z ↦ Finset.univ.filter (fun v ↦ sitePosition L v ∈ Z)
    let A : ℕ → Set (ℝ × ℝ) :=
      cumulativeLayer (sitePosition L '' X) n V c.last
    let s : ℕ → ℝ := dyadicScale n
    let R : ℕ → Set (ℝ × ℝ) → Finset (SquareLatticeVertex L L) :=
      fun j Z ↦ sample (selectedRegion (0, 0) (d * s j) ((3 / 2) * a' * s j) Z)
    let C : ℕ → Finset (SquareLatticeVertex L L) :=
      fun j ↦ sample (near ((3 / 2) * a' * s j) (sitePosition L '' E))
    let R₀ : ℕ → Finset (SquareLatticeVertex L L) :=
      fun j ↦ sample (near (a' * s j) (A j))
    let C₀ : ℕ → Finset (SquareLatticeVertex L L) :=
      fun j ↦ sample (near (a' * s j) (sitePosition L '' E))
    (∀ j : ℕ, j ≤ c.last → ∀ Aold : Set (ℝ × ℝ), Aold ⊆ A j →
      ∀ S : Finset (ℤ × ℤ),
        (∀ i, i ∈ S ↔
          touches (0, 0) (d * s j) ((3 / 2) * a' * s j) (A j) i ∧
          ¬ touches (0, 0) (d * s j) ((3 / 2) * a' * s j) Aold i) →
        S.card ≤ (m₀ + 1) * (2 * ⌈(max A₀ 2 + (3 / 2) * a') / d⌉₊ + 3) ^ 2 →
        ManyBody.regionMutualInformation Ω (R j Aold) (C j) ≤ ε →
        ManyBody.regionMutualInformation Ω (R₀ j) (C₀ j) ≤ ε) →
      ManyBody.regionMutualInformation Ω X E ≤ ε := by
  classical
  intro sample A s R C R₀ C₀ hstep
  have hmono (P P' Q Q' : Finset (SquareLatticeVertex L L))
      (hP : P ⊆ P') (hQ : Q ⊆ Q') (hPQ : Disjoint P' Q') :
      ManyBody.regionMutualInformation Ω P Q ≤
        ManyBody.regionMutualInformation Ω P' Q' := by
    have hleft := ManyBody.regionMutualInformation_mono_left
      (fun _ ↦ Fin q) Ω P P' Q hP (hPQ.mono_right hQ)
    have hright := ManyBody.regionMutualInformation_mono_left
      (fun _ ↦ Fin q) Ω Q Q' P' hQ hPQ.symm
    exact hleft.trans (by simpa only [ManyBody.regionMutualInformation,
      Finset.union_comm, add_comm] using hright)
  have hsep' (j : ℕ) (hj : j ≤ c.last) (x : ℝ × ℝ) (hx : x ∈ A j)
      (y : ℝ × ℝ) (hy : y ∈ sitePosition L '' E) :
      (a / 2) * s j ≤ dist x y := by
    simpa only [div_mul_eq_mul_div] using
      cumulativeLayer_separation c hn.le ha hsep hj hx hy
  have hdisj (j : ℕ) (hj : j ≤ c.last) : Disjoint (R₀ j) (C₀ j) := by
    have hRC := angular_physical_disjoint (o := (0, 0)) Set.univ
      ha' ha'a hd hda' (dyadicScale_pos hn j) (hsep' j hj)
    have hcore := angular_core_subsets (o := (0, 0)) Set.univ (A j)
      (sitePosition L '' E) ha'.le hd (dyadicScale_pos hn j)
    exact Finset.disjoint_left.mpr fun v hvR hvC ↦
      Set.disjoint_left.mp hRC
        (hcore.1 ⟨Set.mem_univ _, (Finset.mem_filter.mp hvR).2⟩)
        (hcore.2 ⟨Set.mem_univ _, (Finset.mem_filter.mp hvC).2⟩)
  have hdiam' : ∀ x ∈ sitePosition L '' X, ∀ y ∈ sitePosition L '' X,
      dist x y ≤ A₀ * n := by
    simpa only [Set.forall_mem_image, Finset.mem_coe] using hdiam
  have hI : ∀ j : ℕ, j ≤ c.last →
      ManyBody.regionMutualInformation Ω (R₀ j) (C₀ j) ≤ ε := by
    intro j
    induction j with
    | zero =>
        intro hj
        obtain ⟨S, hS, hcard⟩ := exists_annularLayer_selectedIndices
          (r := (3 / 2) * a') hn hd hdiam' hV (0, 0) c.last 0
        refine hstep 0 hj ∅ (Set.empty_subset _) S ?_ hcard ?_
        · simpa [A, s, touches, near] using hS
        · have hRempty : R 0 ∅ = ∅ := by
            simp [R, sample, selectedRegion, touches, near]
          simpa only [hRempty, ManyBody.regionMutualInformation, Finset.empty_union,
            ManyBody.regionEntropy_empty (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω hΩ,
            zero_add, sub_self] using hε
    | succ j ih =>
        intro hj
        obtain ⟨S, hS, hcard⟩ := exists_annular_newIndices
          (r := (3 / 2) * a') hn hd hdiam' hV (0, 0) c.last j
        apply hstep (j + 1) hj (A j)
          (cumulativeLayer_mono _ _ _ _ (Nat.le_succ j)) S hS hcard
        have hscale : 2 * a' * s (j + 1) = a' * s j := by
          simpa only [s, mul_assoc, mul_left_comm] using
            congrArg (fun z : ℝ ↦ a' * z) (two_mul_dyadicScale_succ n j)
        have hR : R (j + 1) (A j) ⊆ R₀ j := fun v hv ↦
          Finset.mem_filter.mpr ⟨Finset.mem_univ v, by
            simpa only [hscale] using old_selectedRegion_subset
              (o := (0, 0)) (s := s (j + 1)) (A j) ha' hd hda'
              (dyadicScale_pos hn (j + 1)) (Finset.mem_filter.mp hv).2⟩
        have hC : C (j + 1) ⊆ C₀ j := fun v hv ↦
          Finset.mem_filter.mpr ⟨Finset.mem_univ v, by
            simpa only [hscale] using exterior_near_subset
              (s := s (j + 1)) (sitePosition L '' E) ha'.le
              (dyadicScale_pos hn (j + 1)).le (Finset.mem_filter.mp hv).2⟩
        exact (hmono _ _ _ _ hR hC (hdisj j ((Nat.le_succ j).trans hj))).trans
          (ih ((Nat.le_succ j).trans hj))
  have hX : X ⊆ R₀ c.last := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, sitePosition L v,
      by simpa only [A, cumulativeLayer_last hn.le] using
        (Set.mem_image_of_mem (sitePosition L) hv),
      by simpa only [dist_self] using
        mul_nonneg ha'.le (dyadicScale_pos hn c.last).le⟩
  have hE : E ⊆ C₀ c.last := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, sitePosition L v,
      Set.mem_image_of_mem (sitePosition L) hv,
      by simpa only [dist_self] using
        mul_nonneg ha'.le (dyadicScale_pos hn c.last).le⟩
  exact (hmono _ _ _ _ hX hE (hdisj c.last le_rfl)).trans (hI c.last le_rfl)

end TNLean.PEPS.Approximation

end
