/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ChebyshevSpectralProjector
import TNLean.MPS.AreaLaw.TwoWindowPolynomialRank

/-!
# The Chebyshev spectral projector at two cuts

Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`
(lines 809–853), apply the degree-`k` Chebyshev polynomial of Definition `def:Cheby-AGSP`
(lines 789–803) to a Hamiltonian of the form `eq:H-mid-cut` (lines 813–821): two windows of
`2ℓ` nearest-neighbour terms about two cuts and three bulk operators. The theorem asserts four
things about the resulting operator `K`: it has the eigenvectors of `H` (item 1), it keeps the
eigenvalues near `η₀` close to `1` and shrinks those above `η₁` to at most `√Δ` with
`Δ = 4 exp (-4 k √(γ / (‖H‖ - η₀)))` (items 2–3), its operator Schmidt rank across the two
cuts is `(dk)^{O(ℓ + k/ℓ)}`, and at a cut inside a bulk region it is `B̃^{O(k)}` (item 4).

This file joins the existing spectral statement for an abstract self-adjoint operator
(`Submodule.exists_isSpectralProjector_chebyshev_one_sub_le`) and the rank estimates for every
polynomial of degree at most `k` in a two-window family
(`operatorSchmidtRank_aeval_two_window_le_pow` and the three bulk-cut estimates), for one and
the same polynomial applied to the actual two-window Hamiltonian.

**Local fix (closed spectral conditions, positivity, slope, bulk constant):** the spectral
conditions are the closed ones `λ ≤ η₀ → 1 ≤ p(λ)` and `η₁ ≤ λ → p(λ)² ≤ Δ`; positivity of
`K` is not asserted, because the unsquared filter need not be positive; the printed slope
`O(k |λ - η₀| √Δ / (γ ‖H‖))` of item 2 is replaced by `k |λ - η₀| / √(γ (u - η₀))`, which holds
on the whole range `λ ≤ η₁`; and the bulk-cut bound is `(B + 2) ^ (k + 1)`. The upper spectral
bound `u` replaces `‖H‖`, which is one admissible choice of `u`. See the companion notes
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf,
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_near_ground_slope.pdf.

**Local fix (word count):** the two-cut rank retains the additional `+1` in the ordered-gap
count, https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

The matrix-product-operator bond dimensions and the running time of the construction
(Proposition `prop:Cheby-AGSP-eff`, lines 1311–1333) are separate assertions.
-/

open Polynomial Matrix TNLean.Lattice TNLean.Lattice.Sheet QuantumCircuit

noncomputable section

namespace TNLean.MPS.AreaLaw.ALVV

/-- The squared Chebyshev contraction in the printed form `4 exp (-4 k √x)`. -/
private theorem two_mul_exp_sq_eq (k x : ℝ) :
    (2 * Real.exp (-2 * k * Real.sqrt x)) ^ 2 = 4 * Real.exp (-4 * k * Real.sqrt x) := by
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  ring_nf

open Classical in
/-- **Theorem 4.2: the Chebyshev projector of a two-window Hamiltonian** (ALVV,
arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, lines 809–853, for `H` of the form
`eq:H-mid-cut`, lines 813–821).

Let `H = ∑ α, F α` on `(ℂ^q)^{⊗ L}` be Hermitian, with two windows of `2ℓ` terms, each supported
on two consecutive sites starting at `a + r` and `b + r`, and three bulk operators supported on
`[0, a]`, `[a + 2ℓ, b]` and `[b + 2ℓ, L)`. Let all eigenvalues of `H` be at most `u`, let
`η₀ < η₁ ≤ u`, `γ = η₁ - η₀`, and `k ≥ 1`. Then there is one real polynomial `p` of degree `k`
with `p(η₀) = 1` such that `K = p(H)`
* is a spectral projector for `(H, η₀, η₁)` relative to the eigenbasis of `H`, with
  `Δ = 4 exp (-4 k √(γ / (u - η₀)))` (items 1 and 3);
* has eigenvalue `p(λ) ≥ 1 - k |λ - η₀| / √(γ (u - η₀))` for every eigenvalue `λ ≤ η₁` of `H`
  (item 2);
* has operator Schmidt rank at most `(q k) ^ (17 (ℓ + ⌊k / (2ℓ)⌋))` across the middle region
  `[a + ℓ + δ, b + ℓ + 1)` for `δ ∈ {0, 1}` (the rank `D` at the two cuts);
* has operator Schmidt rank at most `(B + 2) ^ (k + 1)` at any cut inside one bulk region at which
  that bulk operator has rank at most `B` (item 4).

**Local fix (closed spectral conditions, positivity, slope, bulk constant, word count):** see the
module docstring and the companion notes
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf,
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf,
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_near_ground_slope.pdf and
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf. -/
theorem exists_two_window_chebyshev_spectral_projector
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1) (hℓ : 1 ≤ ℓ)
    (hH : (∑ α, F α).IsHermitian)
    (k : ℕ) (hk : 1 ≤ k) {η₀ η₁ u : ℝ} (h01 : η₀ < η₁) (h1u : η₁ ≤ u)
    (hupper : ∀ j, (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH).eigenvalues
      finrank_euclideanSpace j ≤ u) :
    let H := ∑ α, F α
    let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    let eig := hS.eigenvalues finrank_euclideanSpace
    let Δ := 4 * Real.exp (-4 * (k : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))
    ∃ p : ℝ[X], p.natDegree = k ∧ p.eval η₀ = 1 ∧
      let K := aeval H (p.map (algebraMap ℝ ℂ))
      Submodule.IsSpectralProjector (Matrix.toEuclideanCLM (𝕜 := ℂ) K)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) H) (hS.eigenvectorBasis finrank_euclideanSpace) eig
        (fun j ↦ p.eval (eig j)) η₀ η₁ Δ ∧
      (∀ j, eig j ≤ η₁ →
        1 - k * |eig j - η₀| / √((η₁ - η₀) * (u - η₀)) ≤ p.eval (eig j)) ∧
      (∀ δ : Fin 2,
        let J := interval L (a + ℓ + δ.val) (b + ℓ + 1)
        operatorSchmidtRank (K.reindex (sheetSplit q J) (sheetSplit q J)) ≤
          (q * k) ^ (17 * (ℓ + k / (2 * ℓ)))) ∧
      (∀ c B : ℕ,
        let S := interval L 0 c
        ((c ≤ a ∧ operatorSchmidtRank
            ((F (Sum.inr 0)).reindex (sheetSplit q S) (sheetSplit q S)) ≤ B) ∨
          (a + 2 * ℓ + 1 ≤ c ∧ c ≤ b ∧ operatorSchmidtRank
            ((F (Sum.inr 1)).reindex (sheetSplit q S) (sheetSplit q S)) ≤ B) ∨
          (b + 2 * ℓ + 1 ≤ c ∧ operatorSchmidtRank
            ((F (Sum.inr 2)).reindex (sheetSplit q S) (sheetSplit q S)) ≤ B)) →
        operatorSchmidtRank (K.reindex (sheetSplit q S) (sheetSplit q S)) ≤
          (B + 2) ^ (k + 1)) := by
  intro H hS eig Δ
  have hupper' : ∀ j, hS.eigenvalues finrank_euclideanSpace j ≤ u := hupper
  obtain ⟨p, hdeg, hp0, hK, hnear⟩ :=
    Submodule.exists_isSpectralProjector_chebyshev_one_sub_le
      (Matrix.toEuclideanCLM (𝕜 := ℂ) H) hS finrank_euclideanSpace k h01 h1u hupper'
  have hΔ : (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))) ^ 2 = Δ :=
    two_mul_exp_sq_eq _ _
  have hmapdeg : (p.map (algebraMap ℝ ℂ)).natDegree ≤ k := by
    rw [natDegree_map]
    exact hdeg.le
  refine ⟨p, hdeg, hp0, ?_, hnear, ?_, ?_⟩
  · have hcomm : Matrix.toEuclideanCLM (𝕜 := ℂ) (aeval H (p.map (algebraMap ℝ ℂ))) =
        aeval (Matrix.toEuclideanCLM (𝕜 := ℂ) H) (p.map (algebraMap ℝ ℂ)) :=
      (aeval_algHom_apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)) H
        (p.map (algebraMap ℝ ℂ))).symm
    rw [hcomm, ← hΔ]
    exact hK
  · intro δ
    have h := operatorSchmidtRank_aeval_two_window_le_pow F hleft hright hL hM hR hab hb hℓ k hk
      _ hmapdeg δ
    dsimp only at h ⊢
    convert h
  · intro c B S hcase
    rcases hcase with ⟨hca, hB⟩ | ⟨hac, hcb, hB⟩ | ⟨hbc, hB⟩
    · convert operatorSchmidtRank_aeval_two_window_left_cut_le F hleft hright hM hR
        (by omega) hca hB k _ hmapdeg
    · convert operatorSchmidtRank_aeval_two_window_middle_cut_le F hleft hright hL hR
        hac hcb hB k _ hmapdeg
    · convert operatorSchmidtRank_aeval_two_window_right_cut_le F hleft hright hL hM
        (by omega) hbc hB k _ hmapdeg

end TNLean.MPS.AreaLaw.ALVV
