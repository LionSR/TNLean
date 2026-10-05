/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.StringOrderScalarPhase
import TNLean.MPS.Examples.AKLTPhysicalStringOrder
import TNLean.MPS.Examples.ClusterPhysicalStringOrder
import TNLean.MPS.Symmetry.PhysicalStringBlockOrder

/-!
# Physical string-order phase regressions

These examples distinguish the printed nonidentity-twist condition from the
explicit projective convention, retain the AKLT and cluster physical witnesses,
and test scalar phase removal at fixed endpoints.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447,
  display `SOP`, Theorem 1, lines 278–291, and Examples 1–2.
-/

open scoped Matrix TNOperatorSpace

open MPSTensor

-- Scalar twists satisfy the printed nonidentity condition, but are excluded
-- from the corrected global string-order predicate.
example : (∃ u x y : Matrix (Fin 4) (Fin 4) ℂ,
    u * uᴴ = 1 ∧ u ≠ 1 ∧
      HasPhysicalStringOrderWith stringPhaseTensor ((1 / 2 : ℂ) • 1) x y u) :=
  stringPhaseTensor_literal_criterion_counterexample.1

example : ¬ HasPhysicalStringOrder stringPhaseTensor ((1 / 2 : ℂ) • 1) :=
  stringPhaseTensor_not_hasPhysicalStringOrder

-- Both non-scalar physical examples retain their original correlators.
example : HasPhysicalStringOrder akltPGWSVC08Tensor ((1 / 2 : ℂ) • 1) :=
  akltPGWSVC08_hasPhysicalStringOrder

example : HasPhysicalStringOrder clusterBlockedRMP ((1 / 2 : ℂ) • 1) :=
  clusterBlockedRMP_hasPhysicalStringOrder

-- Removing a phase from a nonidentity scalar can produce the identity.
example : (-1 : ℂ)⁻¹ • (-1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by simp

-- Rephasing preserves fixed-endpoint string magnitude for every tensor.
example {d D : ℕ} (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (x y u : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ) (hμ : ‖μ‖ = 1) :
    HasPhysicalStringOrderWith A Λ x y (μ • u) ↔
      HasPhysicalStringOrderWith A Λ x y u :=
  hasPhysicalStringOrderWith_smul_twist_iff A Λ x y u μ hμ

-- Unlike inequality with the identity, nonscalarity survives phase removal.
example {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ) (hμ : μ ≠ 0) :
    (∀ c : ℂ, μ • u ≠ c • 1) ↔ (∀ c : ℂ, u ≠ c • 1) := by
  constructor
  · intro h c hc
    apply h (μ * c)
    simp [hc, smul_smul]
  · intro h c hc
    apply h (μ⁻¹ * c)
    have h' := congrArg (fun M => μ⁻¹ • M) hc
    simpa [smul_smul, hμ] using h'

-- The endpoint support is exactly D² while every individual middle N is retained.
example {d D : ℕ} (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛunit : IsUnit Λ)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    ∃ x y : Matrix (Fin (D ^ 2) → Fin d) (Fin (D ^ 2) → Fin d) ℂ,
      ∀ (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ),
        Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) x
          (twistedTransferIter A u N (physicalObservableTransfer A (D ^ 2) y 1))) =
            stringOrderBoundaryParam A u Λ X Y N :=
  exists_physicalStringBlockEndpoints A hA Λ hΛunit hΛfix hNorm X Y

-- Literal products of Hermitian one-site operators, not general block operators.
example {d D : ℕ} (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛunit : IsUnit Λ) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (V : Matrix (Fin D) (Fin D) ℂ) (hV : V * Vᴴ = 1) :
    ∃ x y : Fin (D ^ 2) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (x i).IsHermitian) ∧ (∀ i, (y i).IsHermitian) ∧
        Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker x) V) ≠ 0 ∧
        Matrix.trace
          (Λ * Vᴴ * physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker y) 1) ≠ 0 :=
  exists_isHermitian_physicalStringProductEndpoints A hA Λ hΛunit hΛtr hΛfix hNorm V hV

-- Source purity supplies normality internally; no one-site injectivity input is allowed here.
example {d D : ℕ} [NeZero D] (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (hRad : spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
        (twistedTransferMap A u)) = 1) :
    ∃ x y : Fin (D ^ 2) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (x i).IsHermitian) ∧ (∀ i, (y i).IsHermitian) ∧ ∃ s : ℝ, 0 < s ∧
        Filter.Tendsto (fun N : ℕ => ‖Matrix.trace
          (Λ * physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker x)
            (twistedTransferIter A u N
              (physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker y) 1)))‖)
          Filter.atTop (nhds s) :=
  pureCanonical_exists_isHermitian_physicalStringProductOrder
    A Λ hΛpos hΛtr hΛfix hNorm hPure u hu hRad
