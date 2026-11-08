/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorSum
import TNLean.Lattice.GraphDegreeTail
import TNLean.Lattice.GaussianTruncationDecayBound

/-!
# Low-energy decay for a separate family of local observables

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1548–1564 and 1678–1708,
applies the low-energy commutator estimate to the localized operators `M_i`. Their
supports may be larger than those of the Hamiltonian generators. The generator range
and cardinality determine the velocity; the observable support cardinality determines
the prefactor, and its diameter determines the correction from support separation
to the distance between anchors.

**Scope restriction (geometric growth):** the two physical observable-decay theorems
use a polynomial sphere bound, absent from source lines 169–190, through the current
partial-trace localization estimate. They remain valid auxiliary estimates. The
growth-free physical-metric version of eq. `blecm`, including the actual truncated
operators, is proved in `LowEnergyMetricCommutator.lean`. The scalar time-window
and anchor-conversion lemmas now live in `GaussianTruncationDecayBound` and
`GraphDegreeTail`. See `docs/paper-gaps/hastings05_geometric_growth_scope.tex` for
the separate false unrestricted summation claim.
-/

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace Nat Topology

namespace TNLean.Lattice

private theorem gaussian_error_prefactor (a w b n g c e : ℝ) :
    2 * b * (a * n ^ 2 * w * g * c * e + 2 * w * e) + 2 * w * b * e =
      (2 * a * n ^ 2 * g * c + 6) * w * b * e := by ring

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
  (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
  (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)

include ha hHerm hSupport hDiam hCard hBudget

set_option maxHeartbeats 400000 in
-- The explicit Gaussian prefactor comparison expands several nested products and real casts.
set_option backward.isDefEq.respectTransparency false in
/-- The exponential low-energy commutator estimate for arbitrary separated local
observables. The observable support cardinality `vObs` is independent of the generator
cardinality `vR`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm`,
lines 1548–1601. -/
theorem norm_groundCompression_observables_commutator_le_exp [NeZero d]
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    (S : Finset ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (vObs : ℕ) (hSCard : S.card ≤ vObs)
    (l : ℕ) (Y : Set ι)
    (hY : Disjoint ((S.biUnion fun x => graphBall G x l : Finset ι) : Set ι) Y)
    (hB : B ∈ supportedOperators d Y) :
    ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀ B -
      groundCompression (∑ k, h k) E₀ B * groundCompression (∑ k, h k) E₀ W‖ ≤
        commutatorConst R vObs b₀ |Kg| kg * ‖W‖ * ‖B‖ *
          Real.exp (-(commutatorRate R vR b₀ ΔE * l)) := by
  have hKg : 0 ≤ |Kg| := abs_nonneg Kg
  have hGrowthAbs : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r => (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  set v := lrVelocity R vR b₀ with hv
  have hv1 : 1 ≤ v := one_le_lrVelocity R vR b₀
  set γ := commutatorRate R vR b₀ ΔE with hγ
  set T : ℝ := l / (4 * v) with hT
  have hT0 : 0 ≤ T := by positivity
  set q : ℝ := T * ΔE with hq
  have hq0 : 0 ≤ q := by positivity
  have hb := norm_groundCompression_commutator_le_graphNeighborhood G X a ha h hHerm hSupport R
    hDiam vR hCard b₀ hBudget |Kg| kg hGrowthAbs hq0 hΔE hH hgap S hW l Y hY hB hT0
  set A : ℝ := 2 + 4 * |b₀| * Real.exp (2 * R)
  set Ck : ℝ := 2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))
  have hA : 0 ≤ A := by positivity
  have hCk : 0 ≤ Ck := by
    have h1 : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by linarith
    positivity
  have hW0 := norm_nonneg W
  have hB0 := norm_nonneg B
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hbounds := commutator_time_window_exp_bounds
    (lt_of_lt_of_le zero_lt_one hv1) hΔE hl
  change Real.exp (v * T - l / 2) ≤ Real.exp (-(γ * l)) ∧
    Real.exp (-(T * ΔE) ^ 2 / (2 * q)) ≤ Real.exp (-(γ * l)) ∧
    Real.exp (-q / 2) ≤ Real.exp (-(γ * l)) at hbounds
  obtain ⟨e1, e2, e3⟩ := hbounds
  have hS : (S.card : ℝ) ^ 2 ≤ (vObs : ℝ) ^ 2 := by
    have : (S.card : ℝ) ≤ vObs := by exact_mod_cast hSCard
    gcongr
  set E := Real.exp (-(γ * l))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine hb.trans ?_
  calc 2 * ‖B‖ * (A * (S.card : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * T - l / 2) +
        2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q))) +
        2 * ‖W‖ * ‖B‖ * Real.exp (-q / 2)
      ≤ 2 * ‖B‖ * (A * (vObs : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck * E + 2 * ‖W‖ * E) +
        2 * ‖W‖ * ‖B‖ * E := by
        have hcoef : A * (S.card : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck ≤
            A * (vObs : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hA) hW0) hKg) hCk
        have hc1 : 0 ≤ A * (vObs : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck := by positivity
        have ht1 := mul_le_mul hcoef e1 (Real.exp_pos _).le hc1
        have ht2 := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ 2 * ‖W‖)
        have ht3 := mul_le_mul_of_nonneg_left e3 (by positivity : 0 ≤ 2 * ‖W‖ * ‖B‖)
        exact add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity : 0 ≤ 2 * ‖B‖)) ht3
    _ = commutatorConst R vObs b₀ |Kg| kg * ‖W‖ * ‖B‖ * E := by
        unfold commutatorConst
        exact gaussian_error_prefactor A ‖W‖ ‖B‖ vObs |Kg| Ck E


set_option backward.isDefEq.respectTransparency false in
/-- Exponential decay between arbitrary local observables in the distance between
anchors. The velocity uses the Hamiltonian generator parameters `R,vR`; the observable
support parameters `Robs,vObs` enter only the prefactor and support-separation correction.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm`, lines 1548–1601,
with the actual truncated observables `M_i` allowed as the family `W`. -/
theorem norm_groundCompression_observables_commutator_le_exp_edist [NeZero d]
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    {η : Type*} (Y : η → Finset ι) (c : η → ι) (hc : ∀ i, c i ∈ Y i)
    (W : η → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hW : ∀ i, W i ∈ supportedOperators d (Y i : Set ι))
    (Robs : ℕ) (hYDiam : ∀ i, ∀ x ∈ Y i, ∀ y ∈ Y i, G.edist x y ≤ Robs)
    (vObs : ℕ) (hYCard : ∀ i, (Y i).card ≤ vObs) (i j : η) :
    ‖groundCompression (∑ k, h k) E₀ (W j) * groundCompression (∑ k, h k) E₀ (W i) -
      groundCompression (∑ k, h k) E₀ (W i) * groundCompression (∑ k, h k) E₀ (W j)‖ ≤
        commutatorConst R vObs b₀ |Kg| kg *
          Real.exp (commutatorRate R vR b₀ ΔE * (2 * Robs + 1)) * ‖W j‖ * ‖W i‖ *
          (if G.edist (c j) (c i) = ⊤ then 0 else
            Real.exp (-(commutatorRate R vR b₀ ΔE * ((G.edist (c j) (c i)).toNat : ℝ)))) := by
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  have hC : 2 ≤ commutatorConst R vObs b₀ |Kg| kg :=
    (by norm_num : (2 : ℝ) ≤ 6).trans (six_le_commutatorConst R vObs b₀ (abs_nonneg Kg) kg)
  apply le_anchorDecay_of_separated_exp hγ hC (norm_nonneg _) (norm_nonneg _)
    Robs (G.edist (c j) (c i)) (norm_groundCompression_commutator_le_two_mul _ _ _ _)
  intro l hlt
  exact norm_groundCompression_observables_commutator_le_exp G X a ha h hHerm hSupport R
    hDiam vR hCard b₀ hBudget Kg kg hGrowth hΔE hH hgap (Y j) (hW j) vObs (hYCard j)
    l (Y i : Set ι)
    (disjoint_biUnion_graphBall_of_lt_edist G Y c hc Robs hYDiam i j l hlt) (hW i)


end TNLean.Lattice
