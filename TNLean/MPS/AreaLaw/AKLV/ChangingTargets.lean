/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ChangingTargetStep

/-!
# One coherent changing-target AKLV sequence

An actual favorable clipped filter initializes a product vector. Each next
state is the phase-aligned normalized image of the actual preceding state
under a polynomial in the next clipped Hamiltonian. One dependent recursion
chooses the whole sequence, and the rank budget is the product of the sharp
operator-Schmidt rank bounds.

Source: AKLV, arXiv:1301.1162v1, Lemma `l:5`, lines 1003--1052.

**Scope restriction (available window and actual gap):** The fixed physical
window must fit in the chain and have at least six interactions; the actual
first excited energy is part of the physical data. The favorable initial
width is at least 21. These restrictions are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`. The exact product rank
budget is established; the source's summed logarithmic
rank estimate, optimized accuracy-dependent enlarged window, and final
entropy and MPS estimates are separate results.
-/

open Matrix Polynomial
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The initial state is an actual normalized polynomial image of a product
vector for the clipped target. AKLV, arXiv:1301.1162v1, lines 1016--1024.
The product overlap is with the clipped target, as in `Initialization`. -/
def IsAKLVSequenceInitialization {L q : ℕ} (a s : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (e : Fin 3 → ℝ) (g : ℝ) (Ω x : EuclideanSpace ℂ (Fin L → Fin q)) : Prop :=
  let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e
    (aklvLogarithmicThreshold g) Finset.univ
  ∃ (E : ℝ) (φ χ : EuclideanSpace ℂ (Fin L → Fin q))
      (p : Polynomial ℝ) (c : ℂ)
      (vL : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L (a + s / 2)) → ℂ)
      (vR : ((v : {v : Fin L // v ∉ leftBlock L (a + s / 2)}) → Fin q) → ℂ),
    ‖φ‖ = 1 ∧ toEuclideanLin B φ = (E : ℂ) • φ ∧
    ‖φ - Ω‖ ^ 2 ≤ Real.exp (-aklvLogarithmicThreshold g / 16) / 100 ∧
    p.natDegree = s ^ 2 ∧ p.eval E = 1 ∧ ‖χ‖ = 1 ∧
    Entropy.cutVector (leftBlock L (a + s / 2)) χ =
      WithLp.toLp 2 (fun z ↦ vL z.1 * vR z.2) ∧
    let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
    toEuclideanLin K φ = φ ∧ toEuclideanLin K χ ≠ 0 ∧ ‖c‖ = 1 ∧
    x = c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ

/-- The physical initialization followed by actual dyadic refinements gives
one sequence with the exact normalized-image relation on every edge and the
product rank bound. AKLV Lemma `l:5`, lines 1003--1052, in the explicit
available-window and actual-gap scope of the module. -/
theorem exists_aklv_physical_changing_target_sequence :
    ∃ A : ℝ, 1 ≤ A ∧ 21 ≤ A ∧
      ∀ (L q a : ℕ)
        (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h j) (interval L j.val (j.val + 2))) →
      (∀ j, 0 ≤ h j) → (∀ j, h j ≤ 1) → ‖Ω‖ = 1 →
      (∑ j, h j) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      ((∑ j, h j) - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ (∑ j, h j) →
      let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let s : ℕ := ⌈A * u ^ 2 / g⌉₊
      a + s + 1 ≤ L →
      2 ≤ q ∧ g ≤ 1 ∧ 21 ≤ s ∧
      Real.log (((q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) : ℕ) : ℝ) ≤
        198 * (A + 1) * (6 + 2 * Real.log (A + 1)) / g * u ^ 3 ∧
      ∃ (e : Fin 3 → ℝ) (E0 : ℝ) (ψ : ℕ → EuclideanSpace ℂ (Fin L → Fin q)),
        (∃ z : (Fin L → Fin q) → ℂ, star z ⬝ᵥ z = 1 ∧
          (∀ j, aklvNormalizationHamiltonians a s h j *ᵥ z = (e j : ℂ) • z) ∧
          ∀ j, (aklvNormalizationHamiltonians a s h j - (e j : ℂ) • 1).PosSemidef) ∧
        E0 + (∑ j, e j) = mu ∧ 0 ≤ E0 ∧ E0 ≤ 6 ∧
        (∀ i, ‖ψ i‖ = 1 ∧ ‖ψ i - Ω‖ ^ 2 ≤ aklvSequenceWeight i / 16 ∧
          schmidtRank (WithLp.ofLp (Entropy.cutVector
            (leftBlock L (a + s / 2)) (ψ i))) ≤ aklvSequenceRankBound q g s i) ∧
        IsAKLVSequenceInitialization a s h e g Ω (ψ 0) ∧
        ∀ i, IsAKLVSequenceStep a s h e g Ω i (ψ i) (ψ (i + 1)) := by
  classical
  obtain ⟨A, hA, hA21, hinit⟩ := exists_aklv_physical_product_initialization
  refine ⟨A, hA, hA21, ?_⟩
  intro L q a h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited u s ha
  obtain ⟨hq, hg1, hs, hlogD, e, E0, E, φ, p,
      hregional, hEeq, hE0, hE6, _hBpos, _hBnorm, _hE, hφ,
      heigen, _hprojector, hclose, hdegree, hpE, hfix, _hrankK,
      χ, vL, vR, c, hχ, hproduct, _hoverlap, hKχ, hc, hψunit, hψrank, _hψφ, hψΩ⟩ :=
    hinit L q a h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited ha
  let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h e
    (aklvLogarithmicThreshold g) Finset.univ
  let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
  let ψ0 := c • (‖toEuclideanLin K χ‖⁻¹ : ℂ) • toEuclideanLin K χ
  have hinitRelation : IsAKLVSequenceInitialization a s h e g Ω ψ0 :=
    ⟨E, φ, χ, p, c, vL, vR, hφ, heigen, hclose, hdegree,
      hpE, hχ, hproduct, hfix, hKχ, hc, rfl⟩
  let State (i : ℕ) := {x : EuclideanSpace ℂ (Fin L → Fin q) //
    ‖x‖ = 1 ∧ ‖x - Ω‖ ^ 2 ≤ aklvSequenceWeight i / 16 ∧
      schmidtRank (WithLp.ofLp (Entropy.cutVector (leftBlock L (a + s / 2)) x)) ≤
        aklvSequenceRankBound q g s i}
  change 21 ≤ s at hs
  change ‖ψ0‖ = 1 at hψunit
  change ‖ψ0 - Ω‖ ^ 2 ≤ 1 / 16 at hψΩ
  let initial : State 0 := by
    refine ⟨ψ0, hψunit, ?_, ?_⟩
    · simpa only [(aklvSequenceWeight_zero_succ 0).1] using hψΩ
    · rw [(aklvSequenceRankBound_zero_succ q g s 0).1]
      exact hψrank
  have hstep (i : ℕ) (x : State i) :
      ∃ y : State (i + 1), IsAKLVSequenceStep a s h e g Ω i x.val y.val := by
    obtain ⟨y, hyunit, hyΩ, hyrank, hrelation⟩ :=
      exists_aklv_dyadic_filtered_output (by omega) ha h hsupp h0 h1
        mu g Ω hΩ hground hgap hg hexcited e hregional i x.val x.property.1 x.property.2.1
    have hrank : schmidtRank (WithLp.ofLp
        (Entropy.cutVector (leftBlock L (a + s / 2)) y)) ≤
          aklvSequenceRankBound q g s (i + 1) := by
      rw [(aklvSequenceRankBound_zero_succ q g s i).2]
      exact hyrank.trans (Nat.mul_le_mul_left _ x.property.2.2)
    exact ⟨⟨y, hyunit, hyΩ, hrank⟩, hrelation⟩
  let advance (i : ℕ) (x : State i) : State (i + 1) := Classical.choose (hstep i x)
  let run : (i : ℕ) → State i := Nat.rec initial (fun i x ↦ advance i x)
  refine ⟨hq, hg1, hs, hlogD, e, E0, (fun i ↦ (run i).val),
    hregional, hEeq, hE0, hE6, (fun i ↦ (run i).property), ?_, ?_⟩
  · exact hinitRelation
  · intro i
    exact Classical.choose_spec (hstep i (run i))

end TNLean.MPS.AreaLaw
