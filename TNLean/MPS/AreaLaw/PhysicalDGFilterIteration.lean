/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalFilterIteration
import TNLean.MPS.AreaLaw.PhysicalDGFilterTrimming

/-!
# Finite refinement of the same physical root

One fixed reference and threshold control every actual raw-filter-and-trim
iterate. The target is the full original ground space throughout. The
stable scalar recurrence reaches every positive requested error, while
the literal spaces retain the original dimension budget and their actual
trimmed spanning vectors.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640,
and its final refinement argument, lines 1809–1817. Physical reference
selection and Ritz extraction are separate applications. No printed
iteration count or algorithmic running time is asserted here.

**Local fix (normalized gain):** The raw operation is compared with its
nonzero normalized multiple as in `docs/paper-gaps/alvv16_final_filter_gain.tex`.
The proof uses the corrected error recurrence.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A positive finite number of actual raw-filter-and-trim steps reaches
the requested error for the original full ground space. The one common
reference and threshold precede the initial candidate. The terminal space
is a literal iterate of that candidate, with unchanged dimension budget.
Supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1809–1817. -/
theorem exists_physical_dg_filterTrimIterate_isCloseTo
    {L q : ℕ} (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (mu nu gamma : ℝ) (hgamma : 0 < gamma) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let M := ‖H‖
    let K := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - M⁻¹ • H)
    let c := gamma / (M - mu)
    ∀ (D : ℕ), 1 ≤ D →
    ∀ (U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
      (epsilon rho xi delta0 : ℝ),
    0 ≤ epsilon → 0 < rho → rho ≤ 1 → 0 < xi → 0 ≤ delta0 → delta0 ≤ 1 / 2 →
    Submodule.IsCloseTo epsilon G U → Submodule.IsCloseTo epsilon U G →
    (∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x)) →
    epsilon ≤ c ^ 2 * rho / 1024 →
    xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)) ≤ c * rho / 48 →
    ∀ (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))),
    Submodule.IsCloseTo delta0 (nativeFullIntervalSpace L q S) G →
    ∃ n : ℕ, 0 < n ∧
      Submodule.IsCloseTo rho
        (nativeFullIntervalSpace L q (fullIntervalFilterTrimIterate L q K xi S n)) G ∧
      Module.finrank ℂ (fullIntervalFilterTrimIterate L q K xi S n) ≤ Module.finrank ℂ S ∧
      IsIntervalSpanWithRankBound L q 0 L (Module.finrank ℂ S) xi
        (fullIntervalFilterTrimIterate L q K xi S n) := by
  intro H hH hmu hnu hmunu hgap G M K c D hD U epsilon rho xi delta0
    hepsilon hrho hrho1 hxi hdelta0 hdelta0half hGU hUG hU hepsilonBudget hxiBudget S hS
  obtain ⟨_hM, _hden, hc, hc1, _hfix, _hKGo, _hhigh⟩ :=
    physical_dg_normalized_ground_filter_spec h h0 mu nu gamma hgamma hmu hnu hmunu hgap
  change 0 < c at hc
  change c ≤ 1 at hc1
  let u : ℕ → ℝ := Nat.rec delta0 (fun _ d ↦ (1 - c / 4) * d + c * rho / 8)
  have hstep : ∀ n, u n ≤ 1 / 2 → u (n + 1) ≤ (1 - c / 4) * u n + c * rho / 8 :=
    fun _ _ ↦ le_rfl
  have hstable := Real.filter_trim_iterate_le hc hc1 hrho.le hrho1 u hdelta0half hstep
  have hu0 : ∀ n, 0 ≤ u n := by
    intro n
    induction n with
    | zero => exact hdelta0
    | succ n ih =>
      exact add_nonneg (mul_nonneg (by linarith) ih) (by positivity)
  have hall : ∀ n, Submodule.IsCloseTo (u n)
      (nativeFullIntervalSpace L q (fullIntervalFilterTrimIterate L q K xi S n)) G := by
    intro n
    induction n with
    | zero => exact hS
    | succ n ih =>
      exact isCloseTo_nativeFullIntervalSpace_filterTrimStep_of_physical_dg
        h h0 mu nu gamma hgamma hmu hnu hmunu hgap D hD U epsilon rho xi (u n)
        hepsilon hxi (hu0 n) (hstable.1 n) hGU hUG hU hepsilonBudget hxiBudget _ ih
  obtain ⟨n, hn⟩ := Real.exists_filter_trim_iteration hc hc1 hrho hrho1 u hdelta0half hstep
  have hterminal : u (n + 1) ≤ rho := by
    change (1 - c / 4) * u n + c * rho / 8 ≤ rho
    calc
      _ ≤ (1 - c / 4) * rho + c * rho / 8 :=
        add_le_add (mul_le_mul_of_nonneg_left hn (show 0 ≤ 1 - c / 4 by linarith)) le_rfl
      _ ≤ rho := by nlinarith [mul_nonneg hc.le hrho.le]
  exact ⟨n + 1, Nat.succ_pos _, (hall (n + 1)).of_le hterminal,
    finrank_fullIntervalFilterTrimIterate_le K xi S _,
    isIntervalSpanWithRankBound_fullIntervalFilterTrimIterate_succ hxi K S le_rfl n⟩

end TNLean.MPS.AreaLaw
