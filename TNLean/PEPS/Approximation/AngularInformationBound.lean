/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.FiniteProduct
import TNLean.PEPS.Approximation.AngularSeparationBridges
import TNLean.PEPS.Approximation.Basic

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
  `D` and one size threshold `L₀`, and for sites placed at any common translation of `Λ_L`.

## Main results

* `AngularInformationBound.exists_isAngularScale`: Proposition 3.4 supplies such a slope and
  threshold. Section 7 places the sites at the cell centers `(i + 1/2, j + 1/2)`
  (`06-geometry.tex`, lines 62–63), a translation of `Λ_L`; the statement is invariant under a
  common translation of the sites and the marked points.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 3.4 `prop:angular`,
  `02-information.tex`, lines 635–658; the model, `00-introduction.tex`, lines 21–49; the use at
  accuracy `L^{-60}`, `06-geometry.tex`, lines 440–445.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Set

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
      ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ V : Finset (ℝ × ℝ), V.card ≤ m₀ →
        ∀ X E : Finset (SquareLatticeVertex L L), Disjoint X E →
        ∀ n : ℝ, D * Real.log L ≤ n → n ≤ A₀ * L →
          (∀ x ∈ X, ∀ y ∈ X, dist (sitePosition L x) (sitePosition L y) ≤ A₀ * n) →
          AngularSeparation (sitePosition L '' X) (sitePosition L '' E) n (D * Real.log L) a V →
          FiniteProduct.mutualInformation (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω X E ≤
            (L : ℝ) ^ (-p)

/-- **One slope and one threshold for Proposition 3.4 at accuracy `L^{-p}`.** For every
`L ≥ L₀`, every Hamiltonian of the model with gapped unit ground vector `Ω`, every placement
`pos` of the sites at a common translation `c` of `Λ_L`, every set `V` of at most `m₀` marked
points and all disjoint `X`, `E` and `n` as in Proposition 3.4, the angular separation measured
with `pos` gives `I_Ω(X : E) ≤ L^{-p}`.

Source: `02-information.tex`, lines 635–658, used at `p = 60` in `06-geometry.tex`,
lines 440–445. -/
def IsAngularScale (q : ℕ) (J Δ a A₀ : ℝ) (m₀ p : ℕ) (D L₀ : ℝ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L →
    ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
      h.IsGappedGroundState E₀ Ω Δ →
      ∀ (pos : SquareLatticeVertex L L → ℝ × ℝ) (c : ℝ × ℝ),
        (∀ v, pos v = sitePosition L v + c) →
      ∀ V : Finset (ℝ × ℝ), V.card ≤ m₀ →
      ∀ X E : Finset (SquareLatticeVertex L L), Disjoint X E →
      ∀ n : ℝ, D * Real.log L ≤ n → n ≤ A₀ * L →
        (∀ x ∈ X, ∀ y ∈ X, dist (pos x) (pos y) ≤ A₀ * n) →
        AngularSeparation (pos '' X) (pos '' E) n (D * Real.log L) a V →
        FiniteProduct.mutualInformation (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω X E ≤
          (L : ℝ) ^ (-(p : ℤ))

/-- **Proposition 3.4 supplies a slope and a threshold at every positive integer accuracy,** for
sites placed at any common translation of `Λ_L`. The marked points are translated with the
sites. Source: `02-information.tex`, lines 635–658; `06-geometry.tex`, lines 62–63 and
440–445. -/
theorem AngularInformationBound.exists_isAngularScale {q : ℕ} {J Δ : ℝ}
    (hang : AngularInformationBound q J Δ) {a A₀ : ℝ} (ha : 0 < a) (hA₀ : 1 ≤ A₀) (m₀ : ℕ)
    {p : ℕ} (hp : 0 < p) : ∃ D L₀ : ℝ, IsAngularScale q J Δ a A₀ m₀ p D L₀ := by
  classical
  obtain ⟨D, L₀, hD⟩ := hang a A₀ ha hA₀ m₀ p (by exact_mod_cast hp)
  refine ⟨D, L₀, fun L hL h E₀ Ω hΩ pos c hpos V hV X E hXE n hn hnL hdiam hsep => ?_⟩
  have himage : ∀ S : Set (SquareLatticeVertex L L),
      (· + -c) '' (pos '' S) = sitePosition L '' S := by
    intro S
    rw [image_image]
    exact image_congr fun v _ => by rw [hpos, add_neg_cancel_right]
  have hI := hD L hL h E₀ Ω hΩ (V.image (· + -c)) ((Finset.card_image_le).trans hV) X E hXE n
    hn hnL (fun x hx y hy => by simpa only [hpos, dist_add_right] using hdiam x hx y hy)
    (by simpa only [himage] using hsep.translate (-c))
  have hpow : (L : ℝ) ^ (-(p : ℝ)) = (L : ℝ) ^ (-(p : ℤ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rwa [hpow] at hI

end TNLean.PEPS.Approximation
