/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Dynamics.GraphLocalization
import TNLean.Circuit.EntropySupport
import TNLean.Circuit.SiteExpectation

/-!
# Localization of the dynamics onto graph neighborhoods, for the site expectation

Let an interaction `Φ` on the sites `ι`, each of local dimension `q`, have Hermitian terms,
supports of graph diameter at most `R` and at most `v_R` sites, and term norms meeting any site
summing to at most `b₀`, and let the graph have polynomial sphere growth `K_g (d + 1)^k`. Then
the Heisenberg evolution of an operator `A` is approximated by its normalized partial-trace
expectation `E_K = siteExpectation q K` onto a graph neighborhood `K` of its support:

* onto the ball `N_l(a i)` about the anchor of a support `T i`,
  `‖τ_t(A) - E_{N_l(a i)}(τ_t(A))‖ ≤ ‖A‖ min(2, C e^{v|t| - l/2})`;
* onto the union `N_l(S)` of the balls about an arbitrary finite support `S`,
  `‖τ_t(A) - E_{N_l(S)}(τ_t(A))‖ ≤ C |S|^2 ‖A‖ K_g T_k exp(v|t| - l/2)`.

This is the estimate `eq:quasilocal-lr-ce` of OpenAI, *A two-dimensional area law from a global
spectral gap*, Lemma 4.1 (`03-quasilocal.tex`, lines 65–68 and 117–128), and an ingredient of
the TNLean one-dimensional note, Lemma `lem:LR` (`part2a_mps_information.tex`,
lines 267–309).

QICLean proves both estimates for the region expectation `ManyBody.regionExpectation`
(`QICLean.ManyBody.Dynamics.GraphLocalization`). The site expectation is the same normalized
partial trace, `QuantumCircuit.siteExpectation_eq_regionExpectation`, and the estimates below
are the QICLean ones rewritten along that equation. They are kept, with the equation, for the
TNLean statements written with `siteExpectation`, until `siteExpectation` is replaced by
`ManyBody.regionExpectation` (follow-up F12 of
`docs/audits/2026-11-17_qiclean_pin_2e9f93d7_followups.md`).

## Main results

* `QuantumCircuit.siteExpectation_eq_regionExpectation`: the site expectation is the region
  expectation.
* `QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphBall_le`: localization onto the
  ball about an anchor.
* `QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le`: localization onto
  the natural-radius neighborhood of an arbitrary finite support.
-/

open NormedSpace ManyBody
open scoped Matrix.Norms.L2Operator Nat

namespace QuantumCircuit

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized partial-trace expectation onto `K` of the sites `ι`, each of local dimension
`q`, is the region expectation of `ManyBody`: both are
`E_K(B) = q^{-|ι \ K|} Tr_{ι \ K}(B) ⊗ 1_{ι \ K}` (OpenAI area law, `eq:quasilocal-ce`,
`03-quasilocal.tex`, lines 19–25). No hypothesis on `q` is needed.

This is a transitional bridge between two definitions of one notion. It is used only where a
`siteExpectation` statement meets a `regionExpectation` one, and it is deleted together with
`siteExpectation` in follow-up F12 of
`docs/audits/2026-11-17_qiclean_pin_2e9f93d7_followups.md`. -/
theorem siteExpectation_eq_regionExpectation (K : Finset ι)
    (B : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    siteExpectation q K B = regionExpectation (X := fun _ : ι ↦ Fin q) K B := by
  have hglue (u : K → Fin q) (ρ : {x // x ∉ K} → Fin q) :
      glueCfg K u ρ = (cutEquiv (fun _ : ι ↦ Fin q) K).symm (u, ρ) := by
    funext x
    by_cases hx : x ∈ K
    · rw [cutEquiv_symm_apply_mem _ _ hx]
      simp [glueCfg, hx]
    · rw [cutEquiv_symm_apply_not_mem _ _ hx]
      simp [glueCfg, hx]
  have hagree (σ τ : ι → Fin q) :
      AgreeOff (d := q) (Subtype.val : K → ι) σ τ ↔ ∀ v ∉ K, σ v = τ v :=
    ⟨fun h v hv ↦ h v fun j hj ↦ hv (hj ▸ j.2), fun h v hv ↦ h v fun hvK ↦ hv ⟨v, hvK⟩ rfl⟩
  have hcard : (Fintype.card (ComplConfig (fun _ : ι ↦ Fin q) K) : ℂ) =
      (q : ℂ) ^ Fintype.card {x // x ∉ K} := by
    simp [ComplConfig, Fintype.card_pi, Finset.prod_const, Finset.card_univ]
  ext σ τ
  rw [regionExpectation_apply, siteExpectation, Matrix.smul_apply, embedOp_apply, smul_eq_mul,
    hcard]
  simp only [hagree, traceOutside, Matrix.of_apply, hglue]
  rfl

/-- **Localization onto graph balls**, explicit form. Source: OpenAI area law,
Lemma 4.1, `eq:quasilocal-lr-ce` (`03-quasilocal.tex`, lines 65–68 and
117–128), for a general finite graph with sphere growth `K_g (d+1)^k`. -/
theorem norm_heisenberg_sub_siteExpectation_graphBall_le
    {κ : Type*} [Fintype κ] {T : κ → Finset ι}
    (G : SimpleGraph ι) (Φ : Interaction (fun _ : ι ↦ Fin q) T) (a : κ → ι)
    (ha : ∀ k, a k ∈ T k) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
    (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (d : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = d).card : ℝ) ≤ Kg * ((d : ℝ) + 1) ^ kg)
    (i : κ) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ : ι ↦ Fin q) (T i)) (l : ℕ) (t : ℝ) :
    ‖heisenbergEvolution Φ.hamiltonian t A -
        siteExpectation q (graphBall G (a i) l) (heisenbergEvolution Φ.hamiltonian t A)‖ ≤
      ‖A‖ * min 2
        (2 * Real.exp R * Kg * (2 ^ kg * kg ! * Real.exp (1 / 2) /
            (1 - Real.exp (-(1 / 2)))) *
          Real.exp (2 * vR * b₀ * Real.exp (2 * R) * |t| - l / 2)) := by
  rw [siteExpectation_eq_regionExpectation]
  exact norm_heisenberg_sub_regionExpectation_graphBall_le G Φ a ha hHerm R hDiam vR hCard b₀
    hBudget Kg kg hGrowth i hA l t

/-- Localization onto the natural-radius neighborhood of an arbitrary finite
initial support. Constants depend only on the interaction bounds and polynomial
sphere growth, with no diameter bound on the initial support. Source: TNLean
one-dimensional note, Lemma `lem:LR` (`part2a_mps_information.tex`, lines 267–309). -/
theorem norm_heisenberg_sub_siteExpectation_graphNeighborhood_le
    {κ : Type*} [Fintype κ] {T : κ → Finset ι}
    (G : SimpleGraph ι) (Φ : Interaction (fun _ : ι ↦ Fin q) T) (a : κ → ι)
    (ha : ∀ k, a k ∈ T k) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
    (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (d : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = d).card : ℝ) ≤ Kg * ((d : ℝ) + 1) ^ kg)
    (S : Finset ι) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ : ι ↦ Fin q) S) (l : ℕ) (t : ℝ) :
    ‖heisenbergEvolution Φ.hamiltonian t A -
        siteExpectation q (S.biUnion fun x => graphBall G x l)
          (heisenbergEvolution Φ.hamiltonian t A)‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖A‖ * Kg *
        (2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
        Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * |t| - l / 2) := by
  rw [siteExpectation_eq_regionExpectation]
  exact norm_heisenberg_sub_regionExpectation_graphNeighborhood_le G Φ a ha hHerm R hDiam vR
    hCard b₀ hBudget Kg kg hGrowth S hA l t

end QuantumCircuit
