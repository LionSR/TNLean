/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalStringBlockEndpoints
import TNLean.MPS.Symmetry.PhysicalStringAsymptotics
import QICLean.Channel.Peripheral.AdjointSpectrum
import QICLean.Kraus.Wielandt.Primitivity.StronglyIrreducibleToFullWordSpan

/-!
# String order with dimension-bounded physical endpoints

Under the source pure canonical hypotheses, a peripheral physical twist has
nonzero string order with products of Hermitian one-site operators on D² sites
at each endpoint. The supplied twist and every individual middle length are
retained. There is no one-site injectivity assumption.

Source: arXiv:0802.0447, lines 112–122, 155–162 and 278–291.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, *String Order and Symmetries in
  Quantum Spin Lattices*, arXiv:0802.0447, lines 112–122 and 278–291.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace
open Filter

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Source canonical spectral purity implies normality. The argument applies
primitive-channel word-span fullness to the adjoint family, then reverses words.
No one-site injectivity is assumed.

Source: arXiv:0802.0447, lines 155–162 and 289–291. -/
theorem isNormal_of_pureCanonical [NeZero D]
    (A : MPSTensor d D) (Λ : Mat) (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Mat),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1) :
    Kraus.IsNormal A := by
  obtain ⟨hIrr, hPrim⟩ :=
    pureCanonical_isIrreducibleMap_and_isPrimitive A Λ hΛpos hΛfix hNorm hPure
  let B : MPSTensor d D := fun i => (A i)ᴴ
  have hTP : Kraus.IsTP B := by simpa [B, Kraus.transferMap_apply] using hNorm
  have hIrrB : IsIrreducibleMap (Kraus.transferMap B) :=
    Kraus.isIrreducibleMap_mapLM_conjTranspose A hIrr
  have hPrimB : IsPrimitive (Kraus.transferMap B) := by
    change peripheralEigenvalues (Kraus.mapLM (fun i => (A i)ᴴ)) = {1}
    rw [Kraus.peripheralEigenvalues_mapLM_conjTranspose,
      show peripheralEigenvalues (Kraus.mapLM A) = {1} from hPrim]
    simp
  obtain ⟨n, hn, hInj⟩ :=
    (Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP B hTP).mp
      (Kraus.hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive B hTP hIrrB hPrimB)
  exact ⟨n, hn, Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose hInj⟩

/-- In the source pure canonical regime, both virtual boundaries have physical
representatives on D² sites. This is the finite endpoint realization used after
Theorem 1 of arXiv:0802.0447, with no injectivity hypothesis added to the source.
The equality retains every individual middle length.

Source: arXiv:0802.0447, lines 155–162 and 278–291. -/
theorem pureCanonical_exists_physicalStringBlockEndpoints [NeZero D]
    (A : MPSTensor d D) (Λ : Mat) (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Mat),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1) (X Y : Mat) :
    ∃ x y : Matrix (Fin (D ^ 2) → Fin d) (Fin (D ^ 2) → Fin d) ℂ,
      ∀ (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ),
        Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) x
          (twistedTransferIter A u N (physicalObservableTransfer A (D ^ 2) y 1))) =
            stringOrderBoundaryParam A u Λ X Y N :=
  exists_physicalStringBlockEndpoints A
    (isNormal_of_pureCanonical A Λ hΛpos hΛfix hNorm hPure)
    Λ hΛpos.isUnit hΛfix hNorm X Y

/-- The limiting magnitude for physical endpoints of arbitrary finite support.
The middle length counts individual sites, and the peripheral phase is removed
only inside the proof of convergence of the magnitude.

Source: arXiv:0802.0447, lines 241–255 and 278–291. -/
theorem physicalStringBlock_norm_tendsto
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) (n m : ℕ)
    (x : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
    (y : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    Tendsto (fun N : ℕ => ‖Matrix.trace (Λ * physicalObservableTransfer A n x
      (twistedTransferIter A u N (physicalObservableTransfer A m y 1)))‖) atTop
      (nhds (‖Matrix.trace (Λ * Vᴴ * physicalObservableTransfer A m y 1)‖ *
        ‖Matrix.trace (Λ * physicalObservableTransfer A n x V)‖)) := by
  let Φ : Mat →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    ((LinearMap.mulLeft ℂ Λ).comp (physicalObservableTransfer A n x))
  have hlim := twistedTransferIter_phase_adjusted_tendsto
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm u V μ hV hμ hInter
    (physicalObservableTransfer A m y 1)
  have hΦ (Z : Mat) : Φ Z = Matrix.trace (Λ * physicalObservableTransfer A n x Z) := rfl
  have h : Tendsto
      (fun N : ℕ => Φ ((μ ^ N)⁻¹ •
        twistedTransferIter A u N (physicalObservableTransfer A m y 1)))
      atTop (nhds (Φ (Matrix.trace (Λ * Vᴴ * physicalObservableTransfer A m y 1) • V))) :=
    ((LinearMap.toContinuousLinearMap Φ).continuous.tendsto _).comp hlim
  simp only [map_smul] at h
  simpa only [hΦ, smul_eq_mul, norm_mul, norm_inv, norm_pow, hμ,
    one_pow, inv_one, one_mul] using h.norm

/-- At every peripheral physical twist, a pure canonical finitely correlated
state has products of one-site Hermitian endpoint operators on D² sites with
positive limiting string magnitude. The supplied twist is unchanged and every
individual middle length is included.

This statement concerns a fixed twist. An existential nontrivial physical
symmetry must separately exclude all scalar multiples of the identity.

Source: arXiv:0802.0447, lines 112–122, 155–162 and 278–291. -/
theorem pureCanonical_exists_isHermitian_physicalStringProductOrder
    [NeZero D] (A : MPSTensor d D)
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Mat),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (hRad : spectralRadius ℂ (Module.End.toContinuousLinearMap Mat
      (twistedTransferMap A u)) = 1) :
    ∃ x y : Fin (D ^ 2) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (x i).IsHermitian) ∧ (∀ i, (y i).IsHermitian) ∧ ∃ s : ℝ, 0 < s ∧
        Tendsto (fun N : ℕ => ‖Matrix.trace
          (Λ * physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker x)
            (twistedTransferIter A u N
              (physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker y) 1)))‖)
          atTop (nhds s) := by
  obtain ⟨hIrr, hPrim⟩ :=
    pureCanonical_isIrreducibleMap_and_isPrimitive A Λ hΛpos hΛfix hNorm hPure
  have hA := isNormal_of_pureCanonical A Λ hΛpos hΛfix hNorm hPure
  obtain ⟨V, μ, hV, hμ, hInter⟩ :=
    (twistedTransfer_spectralRadius_eq_one_iff_intertwiner A hIrr u hu hNorm).mp hRad
  obtain ⟨x, y, hxH, hyH, hx, hy⟩ := exists_isHermitian_physicalStringProductEndpoints
    A hA Λ hΛpos.isUnit hΛtr hΛfix hNorm V hV
  refine ⟨x, y, hxH, hyH, _, mul_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx), ?_⟩
  exact physicalStringBlock_norm_tendsto A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
    (D ^ 2) (D ^ 2) (Matrix.finKronecker x) (Matrix.finKronecker y) u V μ hV hμ hInter

end MPSTensor
