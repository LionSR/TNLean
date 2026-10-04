/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoSiteChargeCoordinates
import TNLean.PEPS.RegularTwoSitePhysicalChargeMeasurement

/-!
# Nonzero literal two-site charged columns

A remaining boundary leg at each endpoint determines both unknown local
translations. A reconstructed diagonal entry is the character value multiplied
by the two-average normalization. Local G-injective inverses transfer the
resulting nonvanishing to the original physical contraction, without isometry.

Source: SCP10, arXiv:1001.3807, charge detection, lines 2470–2486.
**Scope restriction (remaining-leg witnesses):** The auxiliary statement requires
one remaining leg at each endpoint. Nonvanishing at the identity is derived
for every actual irreducible charge label; the arbitrary-function variant
assumes it explicitly. The results make no assertion for degree-one endpoints, prescribed lattice
geometry or parent Hamiltonians. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A boundary leg at each endpoint resolves both unknown local translations.
Source: SCP10, two-site charge coordinates, lines 2470–2486. -/
theorem regularTwoSiteChargeColumn_diagonal (i : ι) (j : κ)
    (e : {e : ι // e ≠ i}) (f : {e : κ // e ≠ j})
    (χ : G → ℂ) (p k : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSiteChargeColumn i j χ p θ
      ((Equiv.funSplitAt i G).symm (k, θ.1), (Equiv.funSplitAt j G).symm (k, θ.2)) =
        (Fintype.card G : ℂ)⁻¹ ^ 2 * χ (p * k) := by
  classical
  have hx (x : G) : θ.1 = x • θ.1 ↔ x = 1 := by
    constructor
    · intro h
      have he := congrFun h e
      change θ.1 e = x * θ.1 e at he
      apply mul_right_cancel (b := θ.1 e)
      simpa using he.symm
    · rintro rfl
      simp
  have hy (y : G) : θ.2 = y • θ.2 ↔ y = 1 := by
    constructor
    · intro h
      have hf := congrFun h f
      change θ.2 f = y * θ.2 f at hf
      apply mul_right_cancel (b := θ.2 f)
      simpa using hf.symm
    · rintro rfl
      simp
  have hi : (Equiv.funSplitAt i G).symm (k, θ.1) i = k := by simp
  have hj : (Equiv.funSplitAt j G).symm (k, θ.2) j = k := by simp
  have hrI : (fun d : {e : ι // e ≠ i} =>
      (Equiv.funSplitAt i G).symm (k, θ.1) d) = θ.1 := by
    funext d
    simp [d.property]
  have hrJ : (fun d : {e : κ // e ≠ j} =>
      (Equiv.funSplitAt j G).symm (k, θ.2) d) = θ.2 := by
    funext d
    simp [d.property]
  rw [regularTwoSiteChargeColumn_apply]
  dsimp only [Prod.fst, Prod.snd]
  rw [hi, hj, hrI, hrJ]
  simp [hx, hy, regularChargeMatrix]

/-- Every nonzero character value gives a nonzero literal canonical two-site
charged column, provided each endpoint has a remaining boundary leg.
Source: SCP10, charge detection, lines 2470–2486. -/
theorem regularTwoSiteChargeColumn_ne_zero (i : ι) (j : κ)
    [Nonempty {e : ι // e ≠ i}] [Nonempty {e : κ // e ≠ j}]
    (χ : G → ℂ) (hχ : χ 1 ≠ 0) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSiteChargeColumn i j χ p θ ≠ 0 := by
  intro h
  have hc := congrFun h
    ((Equiv.funSplitAt i G).symm (p⁻¹, θ.1),
      (Equiv.funSplitAt j G).symm (p⁻¹, θ.2))
  rw [regularTwoSiteChargeColumn_diagonal i j (Classical.arbitrary _) (Classical.arbitrary _)] at hc
  have hN : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [mul_inv_cancel, Pi.zero_apply] at hc
  exact (mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hN)) hχ) hc

omit [DecidableEq G] in
/-- Local G-injective inverses retain the nonzero two-site charge column on the
original physical spins. Source: SCP10, charge detection, lines 2470–2486.
The remaining-leg assumptions expose both unknown translations. -/
theorem regularTwoSitePhysicalChargeColumn_ne_zero
    {A B : Type*} [Finite A] [Finite B] (i : ι) (j : κ)
    [Nonempty {e : ι // e ≠ i}] [Nonempty {e : κ // e ≠ j}]
    (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGInjective (regularLegRepresentation κ) (regularSiteMap b))
    (χ : G → ℂ) (hχ : χ 1 ≠ 0) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSitePhysicalChargeColumn i j a b χ p θ ≠ 0 := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  obtain ⟨FA, hFA⟩ := ha.exists_regularProjectorCoefficients
  obtain ⟨FB, hFB⟩ := hb.exists_regularProjectorCoefficients
  have hA : FA * (Matrix.of fun s η => a η s) = regularLegProjector ι := by
    ext η ξ
    exact hFA η ξ
  have hB : FB * (Matrix.of fun s η => b η s) = regularLegProjector κ := by
    ext η ξ
    exact hFB η ξ
  have hraw : regularTwoSitePhysicalChargeColumn i j a b χ p θ =
      ((Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)) *ᵥ
        ∑ k : G, χ (p * k) • Pi.single
          ((Equiv.funSplitAt i G).symm (k, θ.1),
            (Equiv.funSplitAt j G).symm (k, θ.2)) 1 := by
    rw [Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
    funext s
    simp [regularTwoSitePhysicalChargeColumn, Matrix.kroneckerMap, mul_assoc]
  have hinverse : (FA ⊗ₖ FB) *ᵥ regularTwoSitePhysicalChargeColumn i j a b χ p θ =
      regularTwoSiteChargeColumn i j χ p θ := by
    rw [hraw, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, hA, hB]
    exact (regularTwoSiteChargeColumn_eq_projector i j χ p θ).symm
  intro hzero
  rw [hzero, Matrix.mulVec_zero] at hinverse
  exact regularTwoSiteChargeColumn_ne_zero i j χ hχ p θ hinverse.symm
/-- Every actual regular irreducible charge has a nonzero two-site physical column
when each endpoint has a remaining leg. Its nonzero character value is derived
from irreducibility. Source: SCP10, charge detection, lines 2470–2486. -/
theorem regularTwoSitePhysicalChargeColumn_ne_zero_of_mem_regularChargeLabels
    {A B : Type*} [Finite A] [Finite B] (i : ι) (j : κ)
    [Nonempty {e : ι // e ≠ i}] [Nonempty {e : κ // e ≠ j}]
    (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGInjective (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGInjective (regularLegRepresentation κ) (regularSiteMap b))
    (χ : G → ℂ)
    (hχ : χ ∈ Representation.irreducibleCharacterFinset
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G))) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    regularTwoSitePhysicalChargeColumn i j a b χ p θ ≠ 0 := by
  obtain ⟨S, hS, rfl, _⟩ := exists_unitary_irreducible_regularChargeLabel χ hχ
  let := hS
  apply regularTwoSitePhysicalChargeColumn_ne_zero i j a b ha hb _ _ p θ
  rw [Representation.char_one, Nat.cast_ne_zero]
  exact (Representation.finrank_pos_of_isIrreducible S.toRepresentation).ne'

end TNLean.PEPS
