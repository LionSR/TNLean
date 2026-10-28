/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Gluing
import QICLean.Analysis.DominantEigenvectorUniqueness

/-!
# Bounds for every dominant eigenvector on the chain

The energy and overlap estimates in chain gluing hold for every supplied unit eigenvector
of the left density matrix whose eigenvalue exceeds one half. The existing chain theorem
supplies one such vector, and phase uniqueness transfers its estimates to any other choice.
The physical extension through the right isometry and the cut coordinates is linear.

This is an auxiliary choice-independent form of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505.
-/

open Matrix
open scoped Matrix Kronecker Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- Every supplied unit eigenvector of the left density matrix with eigenvalue larger than
one half satisfies the chain gluing energy and overlap bounds. Auxiliary choice-independent
form of LVV13, `algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem leading_eigenvector_bounds_chain [NeZero q] {k : ℕ}
    {HL K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k)) {D : Finset (Fin L)}
    (hK : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) K D)
    (hDA : Disjoint D (leftBlock L (k - 1))) {E₀ Δ e τ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ)
    (hgs : IsGappedGroundState (HL + K) E₀ Γ Δ) {m : ℕ} (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (hW : Wᴴ * W = 1) (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin (HL + K) w⟫_ℂ).re ≤ E₀ + e)
    {σ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hopt : (σ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re ≤
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    (hτ : rectangularTraceNorm
      (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) ≤ τ)
    (h4 : 4 * (e + ‖K‖ * τ) < Δ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (μ : ℝ) (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u) (hμ : 1 / 2 < μ) :
      (⟪WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k),
          toEuclideanLin (HL + K) (WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E₀ + 2 * (e + ‖K‖ * τ) ∧
      1 - 2 * (e + ‖K‖ * τ) / Δ ≤
        ‖⟪Γ, WithLp.toLp 2 ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)⟫_ℂ‖ := by
  classical
  obtain ⟨v, ν, hv, hvσ, hν, hvE, hvov⟩ :=
    exists_leading_eigenvector_chain hHL hK hDA hΔ hgs W hW x hwx hwE hσ htr hopt hτ h4
  obtain ⟨-, z, hz, huz⟩ :=
    hσ.eigenvalue_eq_and_exists_unit_smul_of_gt_half htr hv hu hvσ huσ hν hμ
  let J := (1 : Matrix (CutLeft L q k × CutSite L q k)
    (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W
  have hphys : WithLp.toLp 2 ((J *ᵥ WithLp.ofLp u) ∘ gluingCut L q k) =
      z • WithLp.toLp 2 ((J *ᵥ WithLp.ofLp v) ∘ gluingCut L q k) := by
    apply WithLp.ofLp_injective 2
    ext i
    simp only [huz, WithLp.ofLp_smul, mulVec_smul,
      Function.comp_apply, Pi.smul_apply]
  have hphase : z * (starRingEnd ℂ) z = (1 : ℂ) := by
    simpa only [hz, one_pow, Complex.ofReal_one] using Complex.mul_conj' z
  dsimp only [J] at hphys
  rw [hphys]
  constructor
  · simpa only [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      hphase, one_mul] using hvE
  · simpa only [inner_smul_right, norm_mul, hz, one_mul] using hvov

end TNLean.MPS.AreaLaw
