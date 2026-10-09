/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualEnergyTerms
import QICLean.Analysis.RootChannel

/-!
# Marginal tails of the actual truncated physical Hamiltonian

The positive terms remain centered at the original unit vector `Ω`. Given a
gapped ground vector `Ωt` of their actual truncated physical sum, every regional
state of that same vector satisfies the supported-family moment and tail bounds.
The term norm bound is one, the gap is `g / 2`, and the resulting parameter is
`2 / g`, where `g = Δ / positiveNormalization 1 (Δ / 2) J`.

The budget is the literal geometric `cutBudget`, with every original admissible
support label retained. No cut containment, history condition, termwise kernel
equation or auxiliary identity extension enters the ground-state hypothesis.
Existence of the truncated ground vector and uniform geometric budget estimates
are separate statements.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 3.1 (`02-initial.tex`, lines 34–69), applied to the truncation in
`03-quasilocal.tex`, lines 417–426, as in `08-scanner.tex`, lines 400–414.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)

/-- Lemma 3.1's moment bound for the actual truncated physical sum. The only
ground-state premise concerns the sum, while positivity, Hermitian symmetry,
norm and designated support are derived from the actual terms. The original
vector `Ω` still centers those terms. Source: `08-scanner.tex`, lines 400–414. -/
theorem log_surprisalMoment_truncated_reducedState_le
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e : ℝ} {Ωt : StateSpace Λ q}
    (hgs : IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (X : Finset (Site Λ)) {u : ℝ}
    (hu : |u| ≤ Entropy.tailRadius (2 / (Δ / positiveNormalization 1 (Δ / 2) J))
      (cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X)) :
    Real.log (Entropy.surprisalMoment (reducedState_isHermitian Λ q Ωt X).eigenvalues u) ≤
      u * regionalEntropy Λ q Ωt X +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
          cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X * u ^ 2 := by
  have hc := fun i => S.truncatedEnergyTerm_mem_Icc h Ω hΔ hΩ L i
  have hg : 0 < (Δ / positiveNormalization 1 (Δ / 2) J) / 2 :=
    half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  have hθ : (1 : ℝ) / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) =
      2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by
    rw [div_div_eq_mul_div, one_mul]
  have hB := cutBudget_eq_cutLogBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X
  obtain ⟨hΩt, heig, hgap⟩ := hgs
  replace heig : toEuclideanLin (∑ i, S.truncatedEnergyTerm h Ω Δ L i) Ωt =
      (e : ℂ) • Ωt := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
    exact heig
  simpa only [hθ, ← hB, regionalEntropy] using
    (Entropy.log_surprisalMoment_cut_le (n := fun _ : Site Λ => q) (B := X)
      (fun i => S.truncatedEnergyTerm_isSupportedOn h Ω hgraph hanchor hΔ L i)
      (fun i => (Matrix.nonneg_iff_posSemidef.mp (hc i).1).isHermitian)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun i => Matrix.norm_le_one_of_nonneg_of_le_one (hc i).1 (hc i).2)
      hΩt hg heig hgap (partialTraceRight_cutVector Ωt X)
      (reducedState_isHermitian Λ q Ωt X) (by simpa only [hθ, ← hB] using hu))

/-- Lemma 3.1's tail bound for every cut of the same actual truncated ground
vector. The cut may meet retained components outside the truncation set, and
the threshold may be any real number. Source: `08-scanner.tex`, lines 400–414. -/
theorem surprisalTail_truncated_reducedState_le
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e : ℝ} {Ωt : StateSpace Λ q}
    (hgs : IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (X : Finset (Site Λ)) (w : ℝ) :
    Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
        (regionalEntropy Λ q Ωt X) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
            cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X))))) := by
  have hc := fun i => S.truncatedEnergyTerm_mem_Icc h Ω hΔ hΩ L i
  have hg : 0 < (Δ / positiveNormalization 1 (Δ / 2) J) / 2 :=
    half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  have hθ : (1 : ℝ) / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) =
      2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by
    rw [div_div_eq_mul_div, one_mul]
  have hB := cutBudget_eq_cutLogBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X
  obtain ⟨hΩt, heig, hgap⟩ := hgs
  replace heig : toEuclideanLin (∑ i, S.truncatedEnergyTerm h Ω Δ L i) Ωt =
      (e : ℂ) • Ωt := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
    exact heig
  simpa only [hθ, ← hB, regionalEntropy] using
    (Entropy.surprisalTail_cut_le (n := fun _ : Site Λ => q) (B := X)
      (fun i => S.truncatedEnergyTerm_isSupportedOn h Ω hgraph hanchor hΔ L i)
      (fun i => (Matrix.nonneg_iff_posSemidef.mp (hc i).1).isHermitian)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun i => Matrix.norm_le_one_of_nonneg_of_le_one (hc i).1 (hc i).2)
      hΩt hg heig hgap (partialTraceRight_cutVector Ωt X)
      (reducedState_isHermitian Λ q Ωt X) w)

end TNLean.PEPS.AreaLaw.Scan.CollarScan
