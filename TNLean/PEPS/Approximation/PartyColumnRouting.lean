/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ProductReferenceDensityError
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.ColumnSelection
import TNLean.PEPS.Approximation.PartyColumnInput
import TNLean.PEPS.Approximation.DyadicRoutingPEPS

/-!
# A column of the party network, routed onto the square

This file follows the source order of Section 8: Lemma 8.1 fixes one product-basis input
column of the operator network on the party graph, and Lemma 8.2 then routes the resulting
ket network onto the open `L × L` square. The column itself, for an arbitrary finite set of
parties, is in `TNLean.PEPS.Approximation.PartyColumnInput`: if `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, a
column `σ|z⟩` is nonzero and within `2 η` of `Ω` after normalization, up to a phase.
Routing that ket network on dyadic anchors gives a PEPS with the same contraction, positive
bond dimensions, and every bond dimension at most `(C₁ L ^ k) ^ χ` when every link dimension
is at most `C₁ L ^ k`; this is equation `eq:final-bond`.

The column may also be selected from the product-reference estimates of Section 8.1, with
the compression error measured against the physical density of the same joint vector.

**Scope restriction (supplied network and estimates):** The operator party network, its
dyadic placement, the bounds of Lemma 8.2 (`InGrid`,
`BlockBounded`, `DegreeBounded`, `SeparationBounded`), and the trace-norm estimate are
hypotheses on an arbitrary network here. They are verified for the network constructed from
the protocol and the compression theorem in
`dyadicOperatorNetworkAt_of_dyadicProtocolBoundsAt`, as recorded in
`docs/paper-gaps/polypeps_routing_network_bounds.tex` and
`docs/paper-gaps/polypeps_product_reference_column.tex`.

## Main results

* `TNLean.PEPS.Approximation.exists_squarePEPS_of_fixInput_dyadicRouting`: the selected
  column, routed onto the square, is a nonzero PEPS with bonds at most `(max D 1) ^ χ`.
* `TNLean.PEPS.Approximation.exists_squarePEPS_of_product_reference_dyadicRouting`: the
  same after the product-reference estimate.
* `TNLean.PEPS.Approximation.hasPEPSApproximation_of_fixInput_dyadicRouting`: with link
  dimensions at most `C₁ L ^ k`, the conclusion of Theorem 1.1 at one size, with bonds at
  most `(C₁ L ^ k) ^ χ`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.1, Lemma 8.1 `lem:columns`, Lemma 8.2
  `lem:routing`, and `eq:final-bond`, `07-assembly.tex:21–177`, immutable revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These are original proofs; no OpenAI Lean
  code is copied or adapted.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation


/-- A nonzero contraction forces every bond dimension to be positive: a zero dimension makes
the sum over virtual configurations empty.

Source: Polynomial-PEPS manuscript (Sept 24 2026), the nonzero PEPS of Theorem 1.1
`thm:main`, `00-introduction.tex:50–51`. -/
theorem _root_.TNLean.PEPS.Tensor.bondDim_pos_of_pepsVector_ne_zero {L q : ℕ}
    {T : Tensor (squareLatticeGraph L L) q} (h : pepsVector T ≠ 0) (e : Edge _) :
    0 < T.bondDim e := by
  refine Nat.pos_of_ne_zero fun hD ↦ h ?_
  have : IsEmpty (VirtualConfig T) := ⟨fun a ↦ absurd (a e).isLt (by omega)⟩
  ext σ
  simp [pepsVector, stateCoeff]

variable {L q : ℕ} {P Λ : Type*} [Fintype P] [DecidableEq P] [Fintype Λ] [DecidableEq Λ]

/-- **Column, then routing.** Fix a column of an operator party network on dyadic anchors as
in Lemma 8.1, then route the resulting ket network as in Lemma 8.2. If at most `B` parties
are attached to any dyadic block, every party has at most `Δ` links, every link separation is
at most `c` times either endpoint scale, every link dimension is at most `D`, and the operator
`σ`, read at the folded anchors, satisfies `‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1`, then there is a nonzero
PEPS on the open `L × L` square with positive bond dimensions at most `(max D 1) ^ χ`,
`χ = 8 (2 c + 1) B Δ`, whose contraction is the selected column and whose normalization is
within `2 η` of `Ω` up to a phase.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.1 `lem:columns`, the paragraph
`07-assembly.tex:96–99`, Lemma 8.2 `lem:routing`, and `eq:final-bond`,
`07-assembly.tex:67–177`. -/
theorem exists_squarePEPS_of_fixInput_dyadicRouting (hL : 0 < L)
    (N : PartyNetwork P Λ (q * q)) (A : DyadicPlacement P) (hgrid : A.InGrid (paddedSide L))
    {B Δ c D : ℕ} (hB : A.BlockBounded B) (hΔ : DyadicPlacement.DegreeBounded N.src N.tgt Δ)
    (hsep : A.SeparationBounded N.src N.tgt c) (hdim : ∀ ℓ, N.dim ℓ ≤ D)
    (Ω : StateSpace L q) (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.rectangularTraceNorm
      (N.operatorCoeff (fun p ↦ foldVertex hL (A.anchor p)) - Matrix.euclideanOuterProduct Ω Ω)
        ≤ η)
    (hη : η < 1) :
    ∃ T : Tensor (squareLatticeGraph L L) q,
      (∀ e, 0 < T.bondDim e) ∧ (∀ e, T.bondDim e ≤ (max D 1) ^ (8 * (2 * c + 1) * B * Δ)) ∧
      pepsVector T ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖pepsVector T‖⁻¹ : ℝ) : ℂ) • pepsVector T -
        Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ 2 * η := by
  obtain ⟨z, ψ, hψ, hne, θ, hθ⟩ :=
    N.exists_fixInput_of_rectangularTraceNorm_sub_pure_le _ Ω hΩ hσ hη
  obtain ⟨T, hT, hbond⟩ := exists_squarePEPS_of_dyadicRouting hL
    (N.fixInput (fun p ↦ foldVertex hL (A.anchor p)) z) A hgrid hB hΔ hsep hdim
  have hvec : pepsVector T = ψ := by
    ext σ
    simp only [pepsVector, EuclideanSpace.equiv]
    exact (hT σ).trans (hψ σ).symm
  have hT0 : pepsVector T ≠ 0 := hvec ▸ hne
  refine ⟨T, Tensor.bondDim_pos_of_pepsVector_ne_zero hT0, hbond, hT0, θ, ?_⟩
  rw [hvec, Complex.ofReal_inv]
  exact hθ

/-- **Column after the product reference, then routing.** Suppose the joint vector `Ψ`
satisfies `‖Ψ‖ ≤ 1` and `‖Ψ - Ω ⊗ Ξ‖ ≤ ε` with `1 - δ ≤ ‖Ξ‖ ≤ 1`, and the operator `σ` of the
operator party network satisfies `‖σ - Tr_private |Ψ⟩⟨Ψ|‖₁ ≤ κ` with
`α = κ + 2 ε + 2 δ < 1`. Under the routing bounds of Lemma 8.2, there is a nonzero PEPS on the
open square with positive bond dimensions at most `(max D 1) ^ χ`, whose normalization is
within `2 α` of `Ω` up to a phase. The two estimates concern the same joint vector.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1 `eq:reference-junk`,
`eq:protocol-density`, `eq:compressed-density`, Lemma 8.1 `lem:columns`, and Lemma 8.2
`lem:routing`, `07-assembly.tex:21–177`. -/
theorem exists_squarePEPS_of_product_reference_dyadicRouting (hL : 0 < L)
    (N : PartyNetwork P Λ (q * q)) (A : DyadicPlacement P) (hgrid : A.InGrid (paddedSide L))
    {B Δ c D : ℕ} (hB : A.BlockBounded B) (hΔ : DyadicPlacement.DegreeBounded N.src N.tgt Δ)
    (hsep : A.SeparationBounded N.src N.tgt c) (hdim : ∀ ℓ, N.dim ℓ ≤ D)
    {b : Type*} [Fintype b] (Ψ : EuclideanSpace ℂ (Configuration L q × b))
    (Ω : StateSpace L q) (Ξ : EuclideanSpace ℂ b)
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1) {ε δ κ : ℝ}
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ ε) (hlower : 1 - δ ≤ ‖Ξ‖)
    (hcompression : Matrix.rectangularTraceNorm
      (N.operatorCoeff (fun p ↦ foldVertex hL (A.anchor p)) -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ)) ≤ κ)
    (hsmall : κ + 2 * ε + 2 * δ < 1) :
    ∃ T : Tensor (squareLatticeGraph L L) q,
      (∀ e, 0 < T.bondDim e) ∧ (∀ e, T.bondDim e ≤ (max D 1) ^ (8 * (2 * c + 1) * B * Δ)) ∧
      pepsVector T ≠ 0 ∧
      ∃ θ : ℝ, ‖((‖pepsVector T‖⁻¹ : ℝ) : ℂ) • pepsVector T -
        Complex.exp ((θ : ℂ) * Complex.I) • Ω‖ ≤ 2 * (κ + 2 * ε + 2 * δ) :=
  exists_squarePEPS_of_fixInput_dyadicRouting hL N A hgrid hB hΔ hsep hdim Ω hΩ
    (Matrix.rectangularTraceNorm_sub_pure_le_of_product_reference _ Ψ Ω Ξ hΨ hΩ hΞ herror
      hlower hcompression) hsmall

/-- **Column, then routing, with polynomial links.** If every link dimension of the operator
party network is at most `C₁ L ^ k` with `C₁ ≥ 1` and `k ≥ 0`, the routing bounds of
Lemma 8.2 hold, and the operator read at the folded anchors satisfies
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ η < 1` with `2 η ≤ L⁻¹`, then `Ω` has a native PEPS approximation whose
bond dimensions are at most `(C₁ L ^ k) ^ χ = C₁ ^ χ L ^ (k χ)`, `χ = 8 (2 c + 1) B Δ`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 8.1 `lem:columns`, Lemma 8.2
`lem:routing`, and `eq:final-bond`, `07-assembly.tex:67–177`; the PEPS convention and target
error of Theorem 1.1 `thm:main`, `00-introduction.tex:21–57`. -/
theorem hasPEPSApproximation_of_fixInput_dyadicRouting (hL : 0 < L)
    (N : PartyNetwork P Λ (q * q)) (A : DyadicPlacement P) (hgrid : A.InGrid (paddedSide L))
    {B Δ c : ℕ} (hB : A.BlockBounded B) (hΔ : DyadicPlacement.DegreeBounded N.src N.tgt Δ)
    (hsep : A.SeparationBounded N.src N.tgt c) {C₁ k : ℝ} (hC₁ : 1 ≤ C₁) (hk : 0 ≤ k)
    (hdim : ∀ ℓ, (N.dim ℓ : ℝ) ≤ C₁ * (L : ℝ) ^ k)
    (Ω : StateSpace L q) (hΩ : ‖Ω‖ = 1) {η : ℝ}
    (hσ : Matrix.rectangularTraceNorm
      (N.operatorCoeff (fun p ↦ foldVertex hL (A.anchor p)) - Matrix.euclideanOuterProduct Ω Ω)
        ≤ η)
    (hη : η < 1) (hηL : 2 * η ≤ (L : ℝ)⁻¹) :
    HasPEPSApproximation (C₁ ^ (8 * (2 * c + 1) * B * Δ))
      (k * (8 * (2 * c + 1) * B * Δ : ℕ)) L q Ω := by
  set χ := 8 * (2 * c + 1) * B * Δ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLk : 1 ≤ (L : ℝ) ^ k := Real.one_le_rpow hL1 hk
  have hbound0 : 0 ≤ C₁ * (L : ℝ) ^ k := by positivity
  have hdimN : ∀ ℓ, N.dim ℓ ≤ ⌊C₁ * (L : ℝ) ^ k⌋₊ := fun ℓ ↦ Nat.le_floor (hdim ℓ)
  obtain ⟨T, hpos, hbond, hne, θ, hθ⟩ :=
    exists_squarePEPS_of_fixInput_dyadicRouting hL N A hgrid hB hΔ hsep hdimN Ω hΩ hσ hη
  refine ⟨T, hpos, fun e ↦ ?_, hne, θ, hθ.trans hηL⟩
  have hmax : ((max ⌊C₁ * (L : ℝ) ^ k⌋₊ 1 : ℕ) : ℝ) ≤ C₁ * (L : ℝ) ^ k := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (Nat.floor_le hbound0) (hLk.trans (le_mul_of_one_le_left (by positivity) hC₁))
  calc (T.bondDim e : ℝ) ≤ ((max ⌊C₁ * (L : ℝ) ^ k⌋₊ 1 ^ χ : ℕ) : ℝ) := by
        exact_mod_cast hbond e
    _ ≤ (C₁ * (L : ℝ) ^ k) ^ χ := by
        rw [Nat.cast_pow]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hmax χ
    _ = C₁ ^ χ * (L : ℝ) ^ (k * (χ : ℕ)) := by
        rw [mul_pow, Real.rpow_mul_natCast (Nat.cast_nonneg L)]

end TNLean.PEPS.Approximation
