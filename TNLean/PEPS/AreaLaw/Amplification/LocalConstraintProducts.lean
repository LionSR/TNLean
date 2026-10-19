/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ConstraintWordLists
import TNLean.PEPS.AreaLaw.Amplification.ConstraintWordTruncation
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelSpatialOmission

/-!
# Local constraint products

This module states Lemma 10.1 of the area-law manuscript in the generality of the
source. Let `k_i` be positive contractions on a finite domain `Λ ⊆ ℤ²`, anchored at
`a_i` with at most `μ` labels per site, with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}`
for every `l ≥ 0`. On one realization of independent rate-one Poisson clocks, let `D` be
the chronological product of the roots `G_i = (I - k_i)^{1/2}` over all events, later
factors on the left, `D_ret` the product over the events with `d_Λ(a_i, S) ≤ r`, and `L`
the product of the radius-`r` roots `(I - E_{N_r(a_i)} k_i)^{1/2}` over the same events.
Then `E‖D_ret - L‖ ≤ C' t |S| (1 + r)² e^{-c' r^α}`, every `L` is a contraction supported
on `N_{2r}(S)`, and, if every `k_i` annihilates a unit vector `Ω` and `B` acts on `S` and
a finite spectator, `E‖(D - D_ret) B (Ω ⊗ ξ)‖ ≤ C' t |S| ‖B‖ e^{v t - c' r^α}` for every
unit spectator vector `ξ`. All three products are read off the same full Poisson word,
and the constants depend only on `C`, `c`, `α` and `μ`.

The two estimates are proved in `ConstraintWordTruncation` and
`LatticeChannelSpatialOmission`; here they are put on one clock realization through the
list description of the retained product in `ConstraintWordLists`.

## Main statements

* `TNLean.PEPS.AreaLaw.exists_domainLocalConstraintProducts`: Lemma 10.1.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 10.1 (`lem:amplification-local-products`), `09-amplification.tex`, lines 42–72
  (statement) and 74–235 (proof), at revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean text is reused.
-/

open Matrix MeasureTheory QuantumCircuit
open scoped Kronecker NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- **Local constraint products** (Lemma 10.1, `lem:amplification-local-products`,
`09-amplification.tex`, lines 42–72, proof at lines 74–235).
For tail constants `C ≥ 0`, `c > 0`, `0 < α ≤ 1` and a multiplicity bound `μ ≥ 0` there
are `A ≥ 0` and `γ, v > 0` with the following property. Let `k_i` be positive
contractions on a finite domain `Λ`, anchored at `a_i` with at most `μ` labels per site,
with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all `l`. Fix `S ⊆ Λ`, an integer `r`
and `t ≥ 0`, and retain the labels with `d_Λ(a_i, S) ≤ r`. On each realization `w` of
the full Poisson word, let `D(w)` be the product of the roots `(I - k_i)^{1/2}` over all
events in occurrence order, later factors on the left, `D_ret(w)` the product over the
retained events, and `L(w)` the product of the roots `(I - E_{N_r(a_i)} k_i)^{1/2}` over
the retained events. Then

* `E‖D_ret - L‖ ≤ A t |S| (1 + r)² e^{-γ r^α}`, and every `L(w)` is a contraction
  supported on `N_{2r}(S)`;
* if `k_i Ω = 0` for a unit vector `Ω` and `B` acts on `S` and a finite spectator, then
  `E‖(D - D_ret) B (Ω ⊗ ξ)‖ ≤ A t |S| ‖B‖ e^{v t - γ r^α}` for every unit spectator
  vector `ξ`.

Both norms are integrable for the Poisson-word law. The constants precede the local
dimension, domain, labels, anchors, constraints, spectator, `S`, `r` and `t`. The source
assumes `S` nonempty and `r ≥ 1`; neither is needed here. -/
theorem exists_domainLocalConstraintProducts {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ)
    (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ A γ v : ℝ, 0 ≤ A ∧ 0 < γ ∧ 0 < v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → Site Λ) (k : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (S : Finset (Site Λ)) (r : ℕ) (t : ℝ≥0),
        let P := fun i : κ => a i ∈ graphNeighborhood Λ r S
        let G := fun i : κ => CFC.sqrt (1 - k i)
        let Gr := fun i : κ =>
          CFC.sqrt (1 - siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i))
        let ret := fun w : PoissonWord.Word κ => (List.ofFn w.2).filter fun i => decide (P i)
        let D := fun w : PoissonWord.Word κ => ((List.ofFn w.2).reverse.map G).prod
        let Dret := fun w : PoissonWord.Word κ => ((ret w).reverse.map G).prod
        let L := fun w : PoissonWord.Word κ => ((ret w).reverse.map Gr).prod
        (Integrable (fun w => ‖Dret w - L w‖) (PoissonWord.measure κ t) ∧
          (∫ w, ‖Dret w - L w‖ ∂PoissonWord.measure κ t) ≤
            A * t * S.card * (1 + (r : ℝ)) ^ 2 * Real.exp (-(γ * (r : ℝ) ^ α))) ∧
        (∀ w, ‖L w‖ ≤ 1 ∧
          L w ∈ supportedOperators q (graphNeighborhood Λ (2 * r) S : Set (Site Λ))) ∧
        ∀ (Ω : StateSpace Λ q), ‖Ω‖ = 1 → (∀ i, k i *ᵥ WithLp.ofLp Ω = 0) →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux]
          (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            supportedOperators q (S : Set (Site Λ))) →
          ∀ (ξ : Aux → ℂ), ‖WithLp.toLp 2 ξ‖ = 1 →
            let F := fun w : PoissonWord.Word κ =>
              ‖WithLp.toLp 2 (((D w - Dret w) ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ
                (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2))‖
            Integrable F (PoissonWord.measure κ t) ∧
            (∫ w, F w ∂PoissonWord.measure κ t) ≤
              A * t * S.card * ‖B‖ * Real.exp (v * t - γ * (r : ℝ) ^ α) := by
  obtain ⟨At, γt, hAt, hγt, htr⟩ := exists_domainConstraintWord_truncation (α := α) hC hμ hc
  obtain ⟨Ao, v, γo, hAo, hv, hγo, hom⟩ := exists_domainConstraintWord_omission hC hμ hc hα hα₁
  refine ⟨max At Ao, min γt γo, v, hAt.trans (le_max_left _ _), lt_min hγt hγo, hv, ?_⟩
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail S r t P G Gr ret D Dret L
  classical
  have hDret (w : PoissonWord.Word κ) : contractionWord (fun i : {i // P i} => k i)
      (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2 = Dret w :=
    contractionWord_partitionWords_fst P k w
  have hLw (w : PoissonWord.Word κ) : contractionWord
      (fun i : {i // P i} => siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i))
      (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2 = L w :=
    contractionWord_partitionWords_fst P
      (fun i => siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)) w
  have e : (fun w : PoissonWord.Word κ => ‖Dret w - L w‖) = fun w =>
      ‖contractionWord (fun i : {i // P i} => k i)
          (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2 -
        contractionWord
          (fun i : {i // P i} => siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i))
          (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2‖ :=
    funext fun w => by rw [hDret, hLw]
  obtain ⟨hint, hle, hL⟩ := htr Λ κ a k hk₀ hk₁ hfiber htail S r t
  refine ⟨⟨by rw [e]; exact hint, ?_⟩, fun w => by rw [← hLw]; exact hL w, ?_⟩
  · rw [e]
    refine hle.trans ?_
    gcongr
    · exact le_max_left _ _
    · exact min_le_left _ _
  intro Ω hΩ hkΩ Aux _ _ B hB ξ hξ F
  obtain ⟨hFint, hFle⟩ := hom Λ κ a k hk₀ hk₁ hfiber htail Ω hΩ hkΩ Aux S B hB ξ hξ r t
  have hF : (fun w => ‖WithLp.toLp 2
      (((D w ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)) -
        ((Dret w ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)))‖) =
      F := by
    funext w
    have hsub : (D w - Dret w) ⊗ₖ (1 : Matrix Aux Aux ℂ) =
        D w ⊗ₖ (1 : Matrix Aux Aux ℂ) - Dret w ⊗ₖ (1 : Matrix Aux Aux ℂ) := by
      rw [eq_sub_iff_add_eq, ← add_kronecker, sub_add_cancel]
    simp only [F, hsub, sub_mulVec]
  rw [← hF]
  refine ⟨hFint, hFle.trans ?_⟩
  gcongr
  · exact le_max_right _ _
  · exact min_le_right _ _

end TNLean.PEPS.AreaLaw
