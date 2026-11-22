/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MPUPhases.TimeReversalTraceSigns
import TNLean.MPS.MPU.StandardForm.StandardFormDoubling
import TNLean.MPS.MPU.StandardForm.StandardFormFromGates
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalSignIntrinsic
import QICLean.Algebra.Matrix.MonomialMatrix


/-!
# The four time-reversal classes of the example standard forms

For the four gate pairs `(u, v)` of the time-reversal examples of arXiv:1703.09188
(lines 1906--1962), let `W` be the tensor in standard form built from `u` and `v`. This file
proves that `W` is time-reversal invariant, that is, its periodic operators are self-adjoint on
the rings of an even number of standard-form sites (the hypothesis of `PropChiral`,
lines 1201--1252), and computes the second sign `σ⁽²⁾`: the normalized intrinsic trace of the
two-site periodic operator of the blocking of `W` (equation `eq:sigma-from-trace`,
lines 1595--1611). With the first signs `σ⁽¹⁾` of `TimeReversalTraceSigns`:

| `u` | `v` | `σ⁽¹⁾` | `σ⁽²⁾` |
|---|---|---|---|
| `CZ (X ⊗ X)` | `CZ` | `-1` | `-1` |
| `1` | `1` | `1` | `1` |
| `i 1` | `1` | `-1` | `1` |
| `i CZ (X ⊗ X)` | `CZ` | `1` | `-1` |

Here `W` plays the role of the two-site block `𝒰₂` of the convention of
`TwoSiteStandardFormData.timeReversalSign_blocking_parity`, so `σ⁽²⁾` is the intrinsic sign of
the four-site blocking of the underlying MPU.

All gates are monomial matrices with integer phases. The periodic operator is the shifted
`v` layer after the unshifted `u` layer, again monomial. For CZX its permutation flips every
spin, and flipping every spin preserves the product of the `CZ` phases on the `2N` bonds of the
ring, since every spin lies on two bonds; so the operator is self-adjoint. A scalar `i` on `u`
contributes the global phase `i ^ N`, which is real for even `N`.

The second sign is computed from the doubled standard form of `W`
(`TwoSiteStandardFormData.doubled`): its trace is a signed count of fixed points of a
permutation of `256` configurations, evaluated exactly over `ℤ`. A scalar `c` on `u` enters the
doubled unshifted gate as `c²`, hence the trace as `c⁴`; this gives the last two values from the
first two.

## Main results

* `MPOTensor.TimeReversalExamples.timeReversalSigns_czx`, `timeReversalSigns_one`,
  `timeReversalSigns_I_smul_one`, `timeReversalSigns_I_smul_czx`: time-reversal invariance and
  both signs of the four examples.
-/

open scoped Matrix Kronecker
open Matrix

namespace Matrix

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

private theorem kronecker_monomial_intCast (σ : Equiv.Perm ι) (τ : Equiv.Perm κ) (f : ι → ℤ)
    (g : κ → ℤ) :
    monomial σ (fun s ↦ (f s : ℂ)) ⊗ₖ monomial τ (fun s ↦ (g s : ℂ)) =
      monomial (σ.prodCongr τ) (fun p ↦ ((f p.1 * g p.2 : ℤ) : ℂ)) := by
  ext ⟨t₁, t₂⟩ ⟨s₁, s₂⟩
  simp only [kroneckerMap_apply, monomial_apply, Equiv.prodCongr_apply, Prod.map,
    Prod.mk.injEq, Int.cast_mul]
  by_cases h₁ : t₁ = σ s₁ <;> by_cases h₂ : t₂ = τ s₂ <;> simp [h₁, h₂]

private theorem submatrix_monomial_intCast {μ : Type*} [DecidableEq μ] (e f : μ ≃ ι)
    (σ : Equiv.Perm ι) (φ : ι → ℤ) :
    (monomial σ (fun s ↦ (φ s : ℂ))).submatrix e f =
      monomial (f.trans (σ.trans e.symm)) (fun s ↦ (φ (f s) : ℂ)) := by
  ext t s
  simp only [submatrix_apply, monomial_apply]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (by simp [Equiv.eq_symm_apply, h₁]) h₂
  · exact absurd (by simpa [Equiv.eq_symm_apply] using h₂) h₁
  · rfl

private theorem monomial_mul_monomial_intCast [Fintype ι] (σ τ : Equiv.Perm ι) (f g : ι → ℤ) :
    monomial σ (fun s ↦ (f s : ℂ)) * monomial τ (fun s ↦ (g s : ℂ)) =
      monomial (σ * τ) (fun s ↦ ((f (τ s) * g s : ℤ) : ℂ)) := by
  rw [monomial_mul_monomial]
  simp only [Int.cast_mul]

private theorem trace_monomial_intCast [Fintype ι] (σ : Equiv.Perm ι) (f : ι → ℤ) :
    trace (monomial σ (fun s ↦ (f s : ℂ))) =
      ((∑ s, if σ s = s then f s else 0 : ℤ) : ℂ) := by
  rw [trace_monomial]
  push_cast
  rfl

private theorem one_eq_monomial_intCast :
    (1 : Matrix ι ι ℂ) = monomial 1 (fun _ ↦ ((1 : ℤ) : ℂ)) := by
  rw [Int.cast_one, monomial_one]

end Matrix

namespace MPOTensor

namespace TimeReversalExamples

variable {d : ℕ}

/-- Regrouping of four sites `(12)(34)` as `1(23)4`. -/
private def middleRegroup (A B C E : Type*) : (A × B) × (C × E) ≃ (A × (B × C)) × E where
  toFun x := ((x.1.1, (x.1.2, x.2.1)), x.2.2)
  invFun y := ((y.1.1, y.1.2.1), (y.1.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem staircaseMiddle_monomial (σ : Equiv.Perm (Fin d × Fin d))
    (φ : Fin d × Fin d → ℤ) :
    staircaseMiddle (A := Fin d) (E := Fin d) (monomial σ (fun s ↦ (φ s : ℂ))) =
      monomial ((middleRegroup _ _ _ _).trans
          ((((1 : Equiv.Perm (Fin d)).prodCongr σ).prodCongr 1).trans
            (middleRegroup _ _ _ _).symm))
        (fun s ↦ ((1 * φ (s.1.2, s.2.1) * 1 : ℤ) : ℂ)) := by
  have h : staircaseMiddle (A := Fin d) (E := Fin d) (monomial σ (fun s ↦ (φ s : ℂ))) =
      ((((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ monomial σ (fun s ↦ (φ s : ℂ))) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ))).submatrix (middleRegroup _ _ _ _)
          (middleRegroup _ _ _ _) := rfl
  rw [h, one_eq_monomial_intCast, kronecker_monomial_intCast, kronecker_monomial_intCast,
    submatrix_monomial_intCast]
  rfl

private theorem pairSwap_eq_monomial :
    Matrix.reindex (finProdFinEquiv.prodCongr finProdFinEquiv).symm
      (finProdFinEquiv.prodCongr finProdFinEquiv).symm (Matrix.swapMatrix (d * d)) =
      monomial (Equiv.prodComm (Fin d × Fin d) (Fin d × Fin d)) (fun _ ↦ ((1 : ℤ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.prodCongr_apply,
    Prod.map, swapMatrix_apply, monomial_apply, Equiv.prodComm_apply, Prod.swap,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Int.cast_one]

/-- The doubled shifted gate as a relabelled Kronecker product. -/
private theorem doubledV_eq_submatrix (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    doubledV v = ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))).submatrix
      (doubledShiftOutEquiv d).symm (doubledShiftInEquiv d d d).symm := rfl

/-- The doubled unshifted gate as a product of two relabelled Kronecker products. -/
private theorem doubledU_eq_mul (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    doubledU u v =
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))).submatrix
          (doubledOutEquiv d d d).symm (doubledOutEquiv d d d).symm *
        (u ⊗ₖ u).submatrix ((doubledOutEquiv d d d).symm.trans (doubledMidEquiv d d).symm)
          (doubledInEquiv d).symm := by
  rw [doubledU, reindex_apply, ← submatrix_mul_equiv _ _ _ (doubledOutEquiv d d d).symm]
  rfl

private theorem controlledZ_eq_monomial :
    controlledZ = monomial 1 (fun p ↦ ((if p = (1, 1) then -1 else 1 : ℤ) : ℂ)) := by
  ext p q
  simp only [controlledZ, diagonal_apply, monomial_apply, Equiv.Perm.coe_one, id_eq]
  split_ifs <;> simp_all

private theorem pauliXX_eq_monomial :
    pauliX ⊗ₖ pauliX = monomial ((Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.swap 0 1))
      (fun _ ↦ ((1 : ℤ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [pauliX, monomial_apply]

/-- A scalar on the unshifted gate enters the doubled unshifted gate squared. -/
private theorem doubledU_smul_left {ℓ r : ℕ} (c : ℂ) (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    doubledU (c • u) v = (c * c) • doubledU u v := by
  rw [doubledU, doubledU, smul_kronecker, kronecker_smul, smul_smul]
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

/-- The time-reversal sign of the doubled gates of `CZ (X ⊗ X)` and `CZ`. -/
private theorem timeReversalSign_doubled_czx :
    timeReversalSign (doubledU (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ)
      (doubledV controlledZ) = -1 := by
  rw [timeReversalSign, timeReversalTrace, doubledU_eq_mul, doubledV_eq_submatrix,
    controlledZ_eq_monomial, pauliXX_eq_monomial, monomial_mul_monomial_intCast]
  simp only [one_eq_monomial_intCast, kronecker_monomial_intCast, submatrix_monomial_intCast,
    monomial_mul_monomial_intCast, pairSwap_eq_monomial, staircaseMiddle_monomial,
    trace_monomial_intCast]
  have h : ∀ n : ℤ, n = -16 → (((2 * 2 * (2 * 2) : ℕ) : ℂ))⁻¹ * (n : ℂ) = -1 := by
    rintro n rfl
    norm_num
  apply h
  decide +kernel

/-- The time-reversal sign of the doubled gates of `1` and `1`. -/
private theorem timeReversalSign_doubled_one :
    timeReversalSign (doubledU (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1)
      (doubledV 1) = 1 := by
  rw [timeReversalSign, timeReversalTrace, doubledU_eq_mul, doubledV_eq_submatrix]
  simp only [one_eq_monomial_intCast, kronecker_monomial_intCast, submatrix_monomial_intCast,
    monomial_mul_monomial_intCast, pairSwap_eq_monomial, staircaseMiddle_monomial,
    trace_monomial_intCast]
  have h : ∀ n : ℤ, n = 16 → (((2 * 2 * (2 * 2) : ℕ) : ℂ))⁻¹ * (n : ℂ) = 1 := by
    rintro n rfl
    norm_num
  apply h
  decide +kernel

private theorem isUnitaryBetween_monomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (φ : ι → ℂ) (h : ∀ s, star (φ s) * φ s = 1) :
    (monomial σ φ).IsUnitaryBetween :=
  (isUnitaryBetween_iff_mem_unitaryGroup _).mpr (monomial_mem_unitaryGroup σ φ h)

private theorem isUnitaryBetween_controlledZ : controlledZ.IsUnitaryBetween := by
  rw [controlledZ_eq_monomial]
  exact isUnitaryBetween_monomial _ _ fun s ↦ by split_ifs <;> simp

private theorem isUnitaryBetween_czx : (controlledZ * (pauliX ⊗ₖ pauliX)).IsUnitaryBetween := by
  rw [controlledZ_eq_monomial, pauliXX_eq_monomial, monomial_mul_monomial_intCast]
  exact isUnitaryBetween_monomial _ _ fun s ↦ by split_ifs <;> simp

private theorem isUnitaryBetween_one :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).IsUnitaryBetween := by
  rw [one_eq_monomial_intCast]
  exact isUnitaryBetween_monomial _ _ fun s ↦ by simp

private theorem isUnitaryBetween_I_smul {M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hM : M.IsUnitaryBetween) : (Complex.I • M).IsUnitaryBetween := by
  rw [isUnitaryBetween_iff_mem_unitaryGroup, mem_unitaryGroup_iff] at *
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM]
  simp [Complex.conj_I]

/-! ### The second signs -/

/-- **CZX, second sign.** The second sign of the standard form of `CZ (X ⊗ X)` and `CZ` is `-1`.

Source: arXiv:1703.09188, Example `example:czx`, lines 1913--1932, with the sign of equation
`eq:sigma-from-trace`, lines 1595--1611. -/
theorem intrinsicTimeReversalSign_blockTwo_czx :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ)) = -1 := by
  rw [← (standardFormTensorOfGatesData _ _ isUnitaryBetween_czx
    isUnitaryBetween_controlledZ).doubled.timeReversalSign_eq_intrinsic]
  exact timeReversalSign_doubled_czx

/-- The second sign of the standard form of `1` and `1` is `1`.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 1, lines 1950--1952. -/
theorem intrinsicTimeReversalSign_blockTwo_one :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1)) = 1 := by
  rw [← (standardFormTensorOfGatesData _ _ isUnitaryBetween_one
    isUnitaryBetween_one).doubled.timeReversalSign_eq_intrinsic]
  exact timeReversalSign_doubled_one

/-- The second sign of the standard form of `i 1` and `1` is `1`.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 2, lines 1953--1955. -/
theorem intrinsicTimeReversalSign_blockTwo_I_smul_one :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
        1)) = 1 := by
  rw [← (standardFormTensorOfGatesData _ _ (isUnitaryBetween_I_smul isUnitaryBetween_one)
    isUnitaryBetween_one).doubled.timeReversalSign_eq_intrinsic, doubledU_smul_left,
    timeReversalSign_smul_left, timeReversalSign_doubled_one]
  simp

/-- The second sign of the standard form of `i CZ (X ⊗ X)` and `CZ` is `-1`.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 3, lines 1956--1958. -/
theorem intrinsicTimeReversalSign_blockTwo_I_smul_czx :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX)))
        controlledZ)) = -1 := by
  rw [← (standardFormTensorOfGatesData _ _ (isUnitaryBetween_I_smul isUnitaryBetween_czx)
    isUnitaryBetween_controlledZ).doubled.timeReversalSign_eq_intrinsic, doubledU_smul_left,
    timeReversalSign_smul_left, timeReversalSign_doubled_czx]
  simp

/-! ### Time-reversal invariance -/

section Invariance

variable {N : ℕ}

/-- The unshifted layer of a monomial gate with integer phases is monomial. -/
private theorem twoSiteUnshiftedLayer_monomial (σ : Equiv.Perm (Fin d × Fin d))
    (φ : Fin d × Fin d → ℤ) :
    twoSiteUnshiftedLayer (N := N) (monomial σ (fun s ↦ (φ s : ℂ))) =
      monomial (Equiv.piCongrRight fun _ ↦ σ) (fun j ↦ ((∏ x, φ (j x) : ℤ) : ℂ)) := by
  ext h j
  simp only [twoSiteUnshiftedLayer, monomial_apply, Fintype.prod_ite_zero, Int.cast_prod]
  congr 1
  exact propext ⟨fun H ↦ funext H, fun H x ↦ congrFun H x⟩

/-- The shifted layer is the unshifted product of the same gate, read on shifted pairs. -/
private theorem twoSiteShiftedLayer_eq_submatrix [NeZero N]
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoSiteShiftedLayer (N := N) v =
      (twoSiteUnshiftedLayer (N := N) v).submatrix twoSiteShiftedPairEquiv
        twoSiteShiftedPairEquiv := rfl

/-- A scalar on the unshifted gate enters the unshifted layer to the power `N`. -/
private theorem twoSiteUnshiftedLayer_smul (c : ℂ)
    (u : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoSiteUnshiftedLayer (N := N) (c • u) = c ^ N • twoSiteUnshiftedLayer (N := N) u := by
  ext h j
  simp [twoSiteUnshiftedLayer, Finset.prod_mul_distrib]

/-- Self-adjointness of the circuit gives self-adjointness of the periodic operator. -/
private theorem mpo_eq_conjTranspose_of_circuit [NeZero N] {D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (S : TwoSiteStandardFormData W u v)
    (h : (twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u)ᴴ =
      twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u) :
    mpo W N = (mpo W N)ᴴ := by
  have hS := S.mpo_eq_shifted_mul_unshifted (N := N) W u v
  apply (Matrix.reindex (twoSitePairConfigEquiv d N).symm
    (twoSitePairConfigEquiv d N).symm).injective
  rw [← conjTranspose_reindex, hS, h]

/-- A monomial matrix with integer phases whose permutation is an involution preserving the
phases is self-adjoint. -/
private theorem conjTranspose_monomial_intCast_eq_self {ι : Type*} [DecidableEq ι]
    (π : Equiv.Perm ι) (Φ : ι → ℤ) (hπ : ∀ s, π (π s) = s) (hΦ : ∀ s, Φ (π s) = Φ s) :
    (monomial π (fun s ↦ (Φ s : ℂ)))ᴴ = monomial π (fun s ↦ (Φ s : ℂ)) := by
  have hsymm : π.symm = π := Equiv.ext fun s ↦ by rw [Equiv.symm_apply_eq, hπ]
  rw [conjTranspose_monomial, hsymm]
  congr 1
  funext t
  rw [hΦ, star_intCast]

private theorem flip_flip (p : Fin 2 × Fin 2) :
    Prod.map (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
      (Prod.map (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) p) = p := by
  obtain ⟨a, b⟩ := p
  simp

/-- The sign of one site, `(-1)^a`. -/
private def siteSign (a : Fin 2) : ℤ := if a = 1 then -1 else 1

private theorem czPhase_flip (a b : Fin 2) :
    (if (Equiv.swap (0 : Fin 2) 1 a, Equiv.swap (0 : Fin 2) 1 b) = (1, 1) then (-1 : ℤ) else 1) =
      -1 * (if (a, b) = (1, 1) then -1 else 1) * siteSign a * siteSign b := by
  fin_cases a <;> fin_cases b <;> decide

private theorem siteSign_mul_self (a : Fin 2) : siteSign a * siteSign a = 1 := by
  fin_cases a <;> decide

/-- Flipping every spin of a ring of `2N` spins leaves the product of the `CZ` phases on all
bonds unchanged: every spin lies on two bonds, and there is an even number of bonds. -/
private theorem czPhase_bond_flip [NeZero N] (s : Fin N → Fin 2 × Fin 2) :
    (∏ x, if (Equiv.swap (0 : Fin 2) 1 (s x).2, Equiv.swap (0 : Fin 2) 1 (s (x + 1)).1) = (1, 1)
        then (-1 : ℤ) else 1) *
      ∏ x, (if Prod.map (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) (s x) = (1, 1)
        then (-1 : ℤ) else 1) =
    (∏ x, if ((s x).2, (s (x + 1)).1) = (1, 1) then (-1 : ℤ) else 1) *
      ∏ x, if s x = (1, 1) then (-1 : ℤ) else 1 := by
  have hpair : ∀ p : Fin 2 × Fin 2,
      (if Prod.map (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) p = (1, 1)
        then (-1 : ℤ) else 1) =
        -1 * (if p = (1, 1) then -1 else 1) * siteSign p.1 * siteSign p.2 := by
    rintro ⟨a, b⟩
    exact czPhase_flip a b
  simp only [czPhase_flip, hpair, Finset.prod_mul_distrib]
  have hshift : ∏ x : Fin N, siteSign (s (x + 1)).1 = ∏ x, siteSign (s x).1 :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl
  have hneg : (∏ _x : Fin N, (-1 : ℤ)) * ∏ _x : Fin N, (-1 : ℤ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp
  have hsq : ∀ f : Fin N → Fin 2, (∏ x, siteSign (f x)) * ∏ x, siteSign (f x) = 1 := by
    intro f
    rw [← Finset.prod_mul_distrib]
    simp [siteSign_mul_self]
  rw [hshift]
  set B := ∏ x, (if ((s x).2, (s (x + 1)).1) = (1, 1) then (-1 : ℤ) else 1)
  set E := ∏ x, (if s x = (1, 1) then (-1 : ℤ) else 1)
  set C := ∏ x, siteSign (s x).2
  set D := ∏ x, siteSign (s x).1
  linear_combination (B * E * C ^ 2 * D ^ 2) * hneg + (B * E * D ^ 2) * hsq (fun x ↦ (s x).2) +
    (B * E) * hsq (fun x ↦ (s x).1)

private theorem shiftedPerm_one [NeZero N] :
    (twoSiteShiftedPairEquiv (N := N) (ℓ := d) (r := d)).trans
        ((Equiv.piCongrRight fun _ : Fin N ↦ (1 : Equiv.Perm (Fin d × Fin d))).trans
          twoSiteShiftedPairEquiv.symm) = 1 :=
  Equiv.ext fun f ↦ by simp [Equiv.piCongrRight]

/-- The circuit of `CZ (X ⊗ X)` and `CZ` is self-adjoint on every ring. -/
private theorem circuit_czx_selfAdjoint [NeZero N] :
    (twoSiteShiftedLayer (N := N) controlledZ *
        twoSiteUnshiftedLayer (N := N) (controlledZ * (pauliX ⊗ₖ pauliX)))ᴴ =
      twoSiteShiftedLayer (N := N) controlledZ *
        twoSiteUnshiftedLayer (N := N) (controlledZ * (pauliX ⊗ₖ pauliX)) := by
  rw [twoSiteShiftedLayer_eq_submatrix, controlledZ_eq_monomial, pauliXX_eq_monomial,
    monomial_mul_monomial_intCast, twoSiteUnshiftedLayer_monomial,
    twoSiteUnshiftedLayer_monomial, submatrix_monomial_intCast, shiftedPerm_one, one_mul,
    monomial_mul_monomial_intCast, one_mul]
  apply conjTranspose_monomial_intCast_eq_self
  · intro s
    funext x
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, Equiv.prodCongr_apply, flip_flip]
  · intro s
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, Equiv.prodCongr_apply, flip_flip,
      twoSiteShiftedPairEquiv, Equiv.coe_fn_mk, mul_one, Prod.map_fst, Prod.map_snd]
    exact (czPhase_bond_flip s).symm

/-- The circuit of `1` and `1` is self-adjoint on every ring. -/
private theorem circuit_one_selfAdjoint [NeZero N] :
    (twoSiteShiftedLayer (N := N) (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *
        twoSiteUnshiftedLayer (N := N) (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))ᴴ =
      twoSiteShiftedLayer (N := N) (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *
        twoSiteUnshiftedLayer (N := N) (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  rw [twoSiteShiftedLayer_eq_submatrix, one_eq_monomial_intCast, twoSiteUnshiftedLayer_monomial,
    submatrix_monomial_intCast, shiftedPerm_one, monomial_mul_monomial_intCast]
  apply conjTranspose_monomial_intCast_eq_self
  · intro s
    rfl
  · intro s
    rfl

/-- A scalar `i` on the unshifted gate keeps a self-adjoint circuit self-adjoint on rings of an
even number of sites, where `i ^ N` is real. -/
private theorem circuit_I_smul_selfAdjoint [NeZero N] (heven : Even N)
    (u v : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : (twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u)ᴴ =
      twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u) :
    (twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) (Complex.I • u))ᴴ =
      twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) (Complex.I • u) := by
  rw [twoSiteUnshiftedLayer_smul, Matrix.mul_smul, conjTranspose_smul, h, star_pow,
    Complex.star_def, Complex.conj_I, heven.neg_pow]

/-! ### Time-reversal invariance of the four standard forms -/

/-- **CZX, time reversal.** The periodic operators of the standard form of `CZ (X ⊗ X)` and
`CZ` are self-adjoint on every ring, in particular on the rings of an even number of
standard-form sites on which `PropChiral` imposes time reversal (arXiv:1703.09188,
lines 1201--1252). The operator is the shifted `CZ` layer after the unshifted
`CZ (X ⊗ X)` layer, a monomial matrix whose permutation flips every spin; flipping every spin
preserves the product of the `CZ` phases on all `2N` bonds.

Source: arXiv:1703.09188, Example `example:czx`, lines 1913--1930. -/
theorem mpo_czx_eq_conjTranspose (N : ℕ) [NeZero N] :
    mpo (standardFormTensorOfGates (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ) N =
      (mpo (standardFormTensorOfGates (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ) N)ᴴ :=
  mpo_eq_conjTranspose_of_circuit
    (standardFormTensorOfGatesData _ _ isUnitaryBetween_czx isUnitaryBetween_controlledZ)
    circuit_czx_selfAdjoint

/-- The periodic operators of the standard form of `1` and `1` are self-adjoint on every ring.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 1, lines 1950--1952. -/
theorem mpo_one_eq_conjTranspose (N : ℕ) [NeZero N] :
    mpo (standardFormTensorOfGates (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1) N =
      (mpo (standardFormTensorOfGates (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1) N)ᴴ :=
  mpo_eq_conjTranspose_of_circuit
    (standardFormTensorOfGatesData _ _ isUnitaryBetween_one isUnitaryBetween_one)
    circuit_one_selfAdjoint

/-- The periodic operators of the standard form of `i 1` and `1` are self-adjoint on every ring
of an even number of standard-form sites, where the global phase `i ^ N` is real; these are the
lengths of `PropChiral` (arXiv:1703.09188, lines 1201--1252).

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 2, lines 1953--1955. -/
theorem mpo_I_smul_one_eq_conjTranspose (N : ℕ) [NeZero N] (heven : Even N) :
    mpo (standardFormTensorOfGates
        (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) 1) N =
      (mpo (standardFormTensorOfGates
        (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) 1) N)ᴴ :=
  mpo_eq_conjTranspose_of_circuit
    (standardFormTensorOfGatesData _ _ (isUnitaryBetween_I_smul isUnitaryBetween_one)
      isUnitaryBetween_one)
    (circuit_I_smul_selfAdjoint heven _ _ circuit_one_selfAdjoint)

/-- The periodic operators of the standard form of `i CZ (X ⊗ X)` and `CZ` are self-adjoint on
every ring of an even number of standard-form sites, where the global phase `i ^ N` is real.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 3, lines 1956--1958. -/
theorem mpo_I_smul_czx_eq_conjTranspose (N : ℕ) [NeZero N] (heven : Even N) :
    mpo (standardFormTensorOfGates (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX)))
        controlledZ) N =
      (mpo (standardFormTensorOfGates (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX)))
        controlledZ) N)ᴴ :=
  mpo_eq_conjTranspose_of_circuit
    (standardFormTensorOfGatesData _ _ (isUnitaryBetween_I_smul isUnitaryBetween_czx)
      isUnitaryBetween_controlledZ)
    (circuit_I_smul_selfAdjoint heven _ _ circuit_czx_selfAdjoint)

end Invariance

/-! ### The four time-reversal classes -/

/-- **CZX.** The standard form of `u = CZ (X ⊗ X)` and `v = CZ` is time-reversal invariant on
the rings of an even number of standard-form sites and has `σ⁽¹⁾ = σ⁽²⁾ = -1`. Here `σ⁽¹⁾` is
the trace sign of the gates and `σ⁽²⁾` the intrinsic sign of the two-site blocking of the
standard-form tensor.

Source: arXiv:1703.09188, Example `example:czx` and the sentence after it, lines 1913--1932. -/
theorem timeReversalSigns_czx :
    (∀ N : ℕ, 0 < N → Even N →
      mpo (standardFormTensorOfGates (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ) N =
        (mpo (standardFormTensorOfGates (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ) N)ᴴ) ∧
      timeReversalSign (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ = -1 ∧
      intrinsicTimeReversalSign (MPOTensor.blockTwo
        (standardFormTensorOfGates (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ)) = -1 :=
  ⟨fun N hN _ ↦ have : NeZero N := ⟨hN.ne'⟩; mpo_czx_eq_conjTranspose N,
    timeReversalSign_czx, intrinsicTimeReversalSign_blockTwo_czx⟩

/-- **Trivial class.** The standard form of `u = v = 1` is time-reversal invariant and has
`σ⁽¹⁾ = σ⁽²⁾ = 1`.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 1, lines 1950--1952. -/
theorem timeReversalSigns_one :
    (∀ N : ℕ, 0 < N → Even N →
      mpo (standardFormTensorOfGates (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1) N =
        (mpo (standardFormTensorOfGates (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1) N)ᴴ) ∧
      timeReversalSign (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1 = 1 ∧
      intrinsicTimeReversalSign (MPOTensor.blockTwo
        (standardFormTensorOfGates (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1)) = 1 :=
  ⟨fun N hN _ ↦ have : NeZero N := ⟨hN.ne'⟩; mpo_one_eq_conjTranspose N,
    timeReversalSign_one, intrinsicTimeReversalSign_blockTwo_one⟩

/-- **Modified trivial class.** The standard form of `u = i 1` and `v = 1` is time-reversal
invariant on the rings of an even number of standard-form sites and has `σ⁽¹⁾ = -1`,
`σ⁽²⁾ = 1`.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 2, lines 1953--1955. -/
theorem timeReversalSigns_I_smul_one :
    (∀ N : ℕ, 0 < N → Even N →
      mpo (standardFormTensorOfGates
          (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) 1) N =
        (mpo (standardFormTensorOfGates
          (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) 1) N)ᴴ) ∧
      timeReversalSign (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) 1 = -1 ∧
      intrinsicTimeReversalSign (MPOTensor.blockTwo (standardFormTensorOfGates
        (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) 1)) = 1 :=
  ⟨fun N hN heven ↦ have : NeZero N := ⟨hN.ne'⟩; mpo_I_smul_one_eq_conjTranspose N heven,
    timeReversalSign_I_smul_one, intrinsicTimeReversalSign_blockTwo_I_smul_one⟩

/-- **Modified CZX class.** The standard form of `u = i CZ (X ⊗ X)` and `v = CZ` is
time-reversal invariant on the rings of an even number of standard-form sites and has
`σ⁽¹⁾ = 1`, `σ⁽²⁾ = -1`.

Source: arXiv:1703.09188, Example `ex:dagger-all-but-czx`, item 3, lines 1956--1958. -/
theorem timeReversalSigns_I_smul_czx :
    (∀ N : ℕ, 0 < N → Even N →
      mpo (standardFormTensorOfGates (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX)))
          controlledZ) N =
        (mpo (standardFormTensorOfGates (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX)))
          controlledZ) N)ᴴ) ∧
      timeReversalSign (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX))) controlledZ = 1 ∧
      intrinsicTimeReversalSign (MPOTensor.blockTwo (standardFormTensorOfGates
        (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX))) controlledZ)) = -1 :=
  ⟨fun N hN heven ↦ have : NeZero N := ⟨hN.ne'⟩; mpo_I_smul_czx_eq_conjTranspose N heven,
    timeReversalSign_I_smul_czx, intrinsicTimeReversalSign_blockTwo_I_smul_czx⟩

end TimeReversalExamples

end MPOTensor
