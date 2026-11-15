/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledErrorReduction
import TNLean.MPS.AreaLaw.ViableSet.RationalOrthonormalFamily

/-!
# Rational output of sampled error reduction

Apply the sampled error-reduction theorem with target error `δ / 2`, and
round an orthonormal basis of each resulting retained span with viability
loss at most `δ / 2`. The output consists of rational open-chain tensors
with an explicit common parameter height and viability error `δ`.

The same sample supplies all positive-cut decompositions and their internal
operator Schmidt-rank bounds. Orthonormalization and rationalization enlarge
the bond bound by at most the cardinality bound of the exact output family.
The sampling constants retain their dependence on the supplied ground energy.
This result asserts neither a polynomial running time nor rationality of the
Hamiltonian entries.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claim `c:errorreduction`, lines 580–592, and Corollary `c:agsp`, lines 626–649.

**Local fix (witness normalization):** The exact error-reduction theorem uses
the correction documented in `docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.
The rational-output statement is an auxiliary finite-precision consequence
at positive cuts.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace TNLean.MPS.AreaLaw

/-- Sampling at half the final target accuracy leaves a half-target reserve for
rationalization of the retained span. The sampled words, cut decompositions
and simultaneous internal rank bounds are those of the exact construction.
Source: LVV13, `algo53.tex`, Claim `c:errorreduction`, lines 580–592, and
Corollary `c:agsp`, lines 626–649, with the correction stated above. -/
theorem exists_rational_sampled_errorReduction {L q : ℕ} [NeZero L] (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let η := δ / 16
    let m := ⌈((L - E₀) / Δ) * Real.log (1 / η)⌉₊
    let ℓ := sampledProjectorWordCount q L E₀ η m
    let D := q ^ (2 * sampledProjectorLetterBound L ℓ m)
    ∃ I : Fin ℓ → Fin m → Fin L,
      ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 8 ∧
      ∀ n : ℕ, n + 1 ≤ L → ∃ (N : ℕ) (A : Fin N → LeftBlockMatrix L q (n + 1))
        (B : Fin N → RightBlockMatrix L q (n + 1)),
        N ≤ ℓ * D ∧ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (n + 1))
          (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B j ∧
        (∀ j k, 0 < k → k < n + 1 → operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin (n + 1) ↦ q) (leftBlock (n + 1) k)
            ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D) ∧
        ∀ (s b : ℕ) (S : Finset (LeftBlockVector L q (n + 1))),
          IsViableMPS Γ s b (1 / 2) S →
          let V := errorReductionSet Finset.univ A S
          let b' := V.card * max 1 (D * max 1 b)
          let θ : ℝ := (δ / 2) / (2 * (V.card + 1))
          let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 b') : ℝ) ^ (n + 2) *
            (n + 2) * 2 ^ (n + 1)
          let t := Nat.clog 2 ⌈K / θ⌉₊
          ∃ T : Finset (LeftBlockVector L q (n + 1)),
            T.card ≤ V.card ∧ b' ≤ (ℓ * D * s) * max 1 (D * max 1 b) ∧
            (∀ w ∈ T, Nonempty
              (RationalLeftOpenMPSRepresentationOfHeight (2 ^ (2 * t + 5)) b' w)) ∧
            IsViableMPS Γ (ℓ * D * s) ((ℓ * D * s) * max 1 (D * max 1 b)) δ T := by
  classical
  intro η m ℓ D
  have hexact := exists_sampled_errorReduction hq h hs h0 h1 hgs hΔ
    (δ := δ / 2) (by positivity) (by linarith)
  dsimp only at hexact
  rw [show δ / 2 / 8 = δ / 16 by ring] at hexact
  obtain ⟨I, hproj, hcuts⟩ := hexact
  refine ⟨I, ?_, ?_⟩
  · simpa only [show δ / 2 / 4 = δ / 8 by ring] using hproj
  · intro n hn
    obtain ⟨N, A, B, hN, hdec, hleft, hgood⟩ := hcuts (n + 1) hn
    refine ⟨N, A, B, hN, hdec, hleft, ?_⟩
    intro s b S hS V b' θ K t
    have hV := hgood s b S hS
    obtain ⟨T, hcard, hdata, hviable⟩ :=
      exists_rational_leftFamily_approximation_of_orthonormalization V hn hV.2.1
        (ε := δ / 2) (by positivity) (by linarith)
    have hbond : b' ≤ (ℓ * D * s) * max 1 (D * max 1 b) :=
      Nat.mul_le_mul_right _ hV.1
    refine ⟨T, hcard, hbond, hdata, hcard.trans hV.1, ?_, ?_⟩
    · intro w hw
      obtain ⟨R⟩ := hdata w hw
      exact IsOpenMPS.mono R.data.isLeftOpenMPS (max_le_max_left 1 hbond)
    · simpa only [show δ / 2 + δ / 2 = δ by ring] using hviable Γ (δ / 2) hgs.1 hV.2.2

end TNLean.MPS.AreaLaw
