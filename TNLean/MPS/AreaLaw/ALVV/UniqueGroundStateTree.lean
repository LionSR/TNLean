/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ALVV.PhysicalSoftTreeRefinement

/-!
# The resampling tree for a frustration-free chain with a unique ground state

ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855, treats a
frustration-free chain whose ground state `Γ` is unique and separated by a gap `γ`. Its
improvement over Theorem `t:alg1` is a running time; the mathematical output is again a
`δ`-viable approximation of the ground space by matrix product states. Such a chain is
the case of Assumption (DG) with ground energy `0` and ground-space dimension `1`, so the
physical resampling tree and its refinement apply verbatim.

This file identifies the closed spectral span at energy `0` with the line spanned by `Γ`
and records the refined output of the successful root in that form: on an event of
failure probability at most `1/(L+1)²`, the refinement of the actual root yields a line
of matrix product states mutually `η/2`-close to `ℂ Γ`.

**Scope restriction (degenerate-gap tree):** the per-node families are the families of
the degenerate-gap tree, not the frustration-free family of Theorem `t:aisff`; hence the
per-node dimension is the degenerate-gap count `max (q^width) (D² · K · 2 · (L+2)²)`
rather than the source's constant `D s²`, and no running time is asserted. See
`docs/paper-gaps/alvv16_unique_ground_state_tree.tex`.
-/

open ManyBody (interval)

open MeasureTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.ALVV

/-- For a positive chain whose kernel is the line spanned by `Γ ≠ 0`, the closed spectral
span at energy `0` is that line, provided no eigenvalue lies strictly between `0` and a
positive `γ`. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855. -/
theorem spectralSpanLE_zero_eq_span_singleton {σ : Type*} [Fintype σ] [DecidableEq σ]
    {H : Matrix σ σ ℂ} (hH : H.IsHermitian) {gamma : ℝ} (hgamma : 0 < gamma)
    (Γ : EuclideanSpace ℂ σ) (hΓ : H *ᵥ Γ.ofLp = 0)
    (huniq : ∀ x : EuclideanSpace ℂ σ, H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ)
    (hgap : ∀ z ∈ spectrum ℝ H, z = 0 ∨ gamma ≤ z) :
    Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues 0 = ℂ ∙ Γ := by
  have hlow : ∀ z ∈ spectrum ℝ H, (0 : ℝ) ≤ z := fun z hz ↦
    (hgap z hz).elim (fun h ↦ h.ge) (fun h ↦ hgamma.le.trans h)
  apply le_antisymm
  · intro x hx
    apply huniq
    have h0 := hH.sub_ground_smul_one_eq_zero_on_spectralSpanLE hlow x hx
    rw [zero_smul, sub_zero] at h0
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using
      congrArg WithLp.ofLp h0
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_spectralSpanLE_of_eigenvector hH.eigenvectorBasis hH.eigenvalues
      (Matrix.toEuclideanLin H) (fun j ↦ ?_) Γ 0 0 ?_ le_rfl
    · apply WithLp.ofLp_injective 2
      simp [Matrix.ofLp_toLpLin, hH.mulVec_eigenvectorBasis]
    · apply WithLp.ofLp_injective 2
      simp [Matrix.ofLp_toLpLin, hΓ]

/-- A nonzero vector of the kernel puts `0` in the real spectrum. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855. -/
theorem zero_mem_spectrum_of_mulVec_eq_zero {σ : Type*} [Fintype σ] [DecidableEq σ]
    {H : Matrix σ σ ℂ} (hH : H.IsHermitian) {gamma : ℝ} (hgamma : 0 < gamma)
    (Γ : EuclideanSpace ℂ σ) (hΓ0 : Γ ≠ 0) (hΓ : H *ᵥ Γ.ofLp = 0)
    (hgap : ∀ z ∈ spectrum ℝ H, z = 0 ∨ gamma ≤ z) :
    (0 : ℝ) ∈ spectrum ℝ H := by
  by_contra hnot
  have hpos : ∀ j, 0 < hH.eigenvalues j := fun j ↦ by
    rcases hgap _ (hH.eigenvalues_mem_spectrum_real j) with h | h
    · exact absurd (h ▸ hH.eigenvalues_mem_spectrum_real j) hnot
    · exact hgamma.trans_le h
  have hmem : Γ ∈ Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues 0 := by
    refine Submodule.mem_spectralSpanLE_of_eigenvector hH.eigenvectorBasis hH.eigenvalues
      (Matrix.toEuclideanLin H) (fun j ↦ ?_) Γ 0 0 ?_ le_rfl
    · apply WithLp.ofLp_injective 2
      simp [Matrix.ofLp_toLpLin, hH.mulVec_eigenvectorBasis]
    · apply WithLp.ofLp_injective 2
      simp [Matrix.ofLp_toLpLin, hΓ]
  have hempty : {j | hH.eigenvalues j ≤ 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun j hj ↦ (hpos j).not_ge hj
  have hbot : Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues 0 = ⊥ := by
    rw [Submodule.spectralSpanLE, hempty, Set.image_empty, Submodule.span_empty]
  rw [hbot, Submodule.mem_bot] at hmem
  exact hΓ0 hmem

open Classical in
/-- **The refined output for a unique frustration-free ground state.** Let `H = ∑ hᵢ` be a
nearest-neighbour chain with `0 ≤ hᵢ ≤ 1`, frustration free with ground state `Γ ≠ 0`
(`H Γ = 0`), unique (every vector of the kernel is a multiple of `Γ`), and with spectral gap
`γ > 0` (every other spectral value is at least `γ`). The physical soft families on the actual
resampling tree have a measurable success event of failure probability at most `1/(L+1)²`.
For every `η > 0` the refinement of the actual root on that event, with its Ritz extraction,
gives a line mutually `η/2`-close to `ℂ Γ`, consisting of matrix product states of bond
dimension `Bscale · count²`, with `count ≤ Ccount (2(L+1))²` and
`Bscale ≤ C (2(L+1)(1+1/η))^k`.

Existence form of ALVV, arXiv:1602.08828v2, Theorem `t:unique`, lines 1829–1855; the running
time is not formalized. -/
theorem exists_unique_ground_state_refined_ritz_approximation
    (q : ℕ) (hq : 2 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ u Ccount : ℕ, 2 ≤ u ∧ 1 ≤ Ccount ∧ ∃ K : ℕ, 1 ≤ K ∧ ∃ C : ℝ, 0 < C ∧ ∃ kexp : ℕ,
    let ell := u ^ 8
    let m := u ^ 10
    let k := u ^ 16
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let width := 4 * ell
    ∀ (L : ℕ)
      (Φ : ManyBody.BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1)
      (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
    let H := Φ.hamiltonian
    Γ ≠ 0 → H *ᵥ Γ.ofLp = 0 →
    (∀ x : EuclideanSpace ℂ (Fin L → Fin q), H *ᵥ x.ofLp = 0 → x ∈ ℂ ∙ Γ) →
    (∀ z ∈ spectrum ℝ H, z = 0 ∨ gamma ≤ z) →
    let G := ℂ ∙ Γ
    let threshold := K * (1 + 1) * (L + 2) ^ 2
    let rounds := q * L
    let count := max (q ^ width) (D ^ 2 * threshold)
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (1 - ‖H‖⁻¹ • H)
    ∃ xiInit : ℝ, 0 < xiInit ∧
    ∃ hwidth : 1 ≤ width,
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      let thresholdFamily := fun _ : LongIntervalIndex L width ↦ threshold
      let Good := canonicalIntervalResamplingGood D rounds hwidth thresholdFamily N F xiInit G 0 L
      MeasurableSet Good ∧
      intervalResamplingMeasure L q rounds Goodᶜ ≤ ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2) ∧
      count ≤ Ccount * ((L + 1) * (1 + 1)) ^ 2 ∧
      ∀ eta : ℝ, 0 < eta →
      let Z := ((L : ℝ) + 1) * ((1 : ℝ) + 1) * (1 + 1 / eta)
      ∃ (roundsRef : ℕ) (xiRef : ℝ) (Bscale : ℕ), 0 < xiRef ∧ (Bscale : ℝ) ≤ C * Z ^ kexp ∧
        ∀ U ∈ Good,
          let S0 := balancedIntervalSpace (canonicalIntervalResamplingOperation
            D rounds thresholdFamily N F xiInit U) width hwidth 0 L
          let S := fullIntervalFilterTrimIterate L q Kraw xiRef S0 roundsRef
          let W := nativeFullIntervalSpace L q S
          let hH : H.IsHermitian :=
            (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
          let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) 1
          Module.finrank ℂ S ≤ count ∧ R ≤ W ∧ Module.finrank ℂ R = 1 ∧
            Submodule.IsCloseTo (eta / 2) G R ∧ Submodule.IsCloseTo (eta / 2) R G ∧
            ∀ v ∈ R, IsOpenMPS L q (Bscale * count ^ 2) (fun x ↦ v x) := by
  classical
  obtain ⟨u, Ccount, hu, hCcount, K, hK, C, hC, kexp, hall⟩ :=
    exists_physical_soft_tree_refined_ritz_approximation q hq gamma hgamma
  refine ⟨u, Ccount, hu, hCcount, K, hK, C, hC, kexp, ?_⟩
  intro ell m k D width L Φ h0 h1 Γ H hΓ0 hΓ huniq hgap
  let hH : H.IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hGeq := spectralSpanLE_zero_eq_span_singleton hH hgamma Γ hΓ huniq hgap
  have hmu := zero_mem_spectrum_of_mulVec_eq_zero hH hgamma Γ hΓ0 hΓ hgap
  have hgap' : ∀ z ∈ spectrum ℝ H, z = 0 ∨ 0 + gamma ≤ z := by
    simpa only [zero_add] using hgap
  have key := hall L Φ h0 h1 0 hmu hgap'
  have hrank : Module.finrank ℂ (ℂ ∙ Γ) = 1 := finrank_span_singleton hΓ0
  dsimp only at key ⊢
  rw [hGeq, hrank] at key
  simpa only [Nat.cast_one] using key

end TNLean.MPS.AreaLaw.ALVV
