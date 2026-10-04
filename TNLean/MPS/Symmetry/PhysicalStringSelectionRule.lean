/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalStringAsymptotics
import TNLean.MPS.Symmetry.PhysicalStringEndpoints

/-!
# Physical endpoint selection at a fixed string twist

These results formalize the endpoint coefficient criterion in PGWSVC08,
arXiv:0802.0447, lines 241–276, for a fixed physical twist with a specified
peripheral virtual intertwiner. They do not assert the existential Theorem 1
over nontrivial twists, nor change `HasPhysicalStringOrder` or its convention
for the identity action modulo scalar phases.

**Scope restriction (fixed physical twist):** The theorem does not quantify
over nontrivial twists or identify scalar phases with the identity action.
The remaining global equivalence and its interface question are recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- For a fixed unitary twist and peripheral intertwiner, physical one-site
endpoints with positive limiting string magnitude exist exactly when one of
the source's physical-letter trace coefficients is nonzero.
Supporting result for arXiv:0802.0447, lines 257–276. -/
theorem exists_hasPhysicalStringOrderWith_iff_letter_coefficient
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    (∃ x y, HasPhysicalStringOrderWith A Λ x y u) ↔
      ∃ n m : Fin d, Matrix.trace (V * Λ * A n * (A m)ᴴ) ≠ 0 := by
  have hμne : μ ≠ 0 := Complex.ne_zero_of_norm_eq_one hμ
  calc
    (∃ x y, HasPhysicalStringOrderWith A Λ x y u) ↔
        ∃ x y, Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) ≠ 0 ∧
          Matrix.trace (Λ * twistedTransferMap A x V) ≠ 0 := by
      apply exists_congr
      intro x
      apply exists_congr
      intro y
      exact hasPhysicalStringOrderWith_iff_endpoint_coefficients
        A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm x y u V μ hV hμ hInter
    _ ↔ ∃ n m : Fin d, Matrix.trace (V * Λ * A n * (A m)ᴴ) ≠ 0 :=
      exists_physicalStringEndpoints_iff A Λ V (μ⁻¹ • u) hΛpos.isHermitian
        (phaseShiftedPhysicalUnitary_mul_conjTranspose u μ hu hμ) hV
        (rotatePhysical_phaseShift A u V μ hμne hInter)

/-- Source canonical spectral-purity form of the physical selection rule.
Irreducibility is derived from faithful stationary density and the simple
peripheral eigenspace. The twist and its virtual intertwiner stay fixed.
Supporting result for arXiv:0802.0447, lines 257–276. -/
theorem pureCanonical_physicalString_selection_rule
    [NeZero D] (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    (∀ x y, HasPhysicalStringOrderWith A Λ x y u ↔
      Matrix.trace (Λ * Vᴴ * twistedTransferMap A y 1) ≠ 0 ∧
      Matrix.trace (Λ * twistedTransferMap A x V) ≠ 0) ∧
    ((∃ x y, HasPhysicalStringOrderWith A Λ x y u) ↔
      ∃ n m : Fin d, Matrix.trace (V * Λ * A n * (A m)ᴴ) ≠ 0) := by
  have hIrr : IsIrreducibleMap (Kraus.transferMap A) :=
    isIrreducibleMap_of_canonical_fixedSpace A Λ hΛpos hΛfix hNorm fun X hX => by
      rcases eq_or_ne X 0 with rfl | hXne
      · exact ⟨0, by simp⟩
      · exact (hPure 1 X hXne (by simp) (by simpa using hX)).2
  have hPrim : IsPrimitive (Kraus.transferMap A) := by
    apply isPrimitive_of_unique_norm_one (Kraus.transferMap A) 1 hNorm one_ne_zero
    intro ev hEig hev
    obtain ⟨X, hX⟩ := hEig.exists_hasEigenvector
    exact (hPure ev X hX.2 hev hX.apply_eq_smul).1
  exact ⟨fun x y => hasPhysicalStringOrderWith_iff_endpoint_coefficients
      A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm x y u V μ hV hμ hInter,
    exists_hasPhysicalStringOrderWith_iff_letter_coefficient
      A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm u hu V μ hV hμ hInter⟩

end MPSTensor
