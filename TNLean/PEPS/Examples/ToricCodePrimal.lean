/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import TNLean.PEPS.Examples.QuantumDouble

/-!
# The primal toric-code tensor and its virtual parity

Let \(P\) be the map from four virtual qubits to the four physical spins of the primal
quantum-double tensor for \(G=\mathbb Z_2\). Its rows are physical configurations and its
columns are virtual labels, in the order top, right, down, left. The virtual action is the
literal Pauli operator \(Z^{\otimes4}\), with \(Z=\operatorname{diag}(1,-1)\).

This module proves \(P^\dagger P=2\Pi_{\mathrm{even}}\), where
\(\Pi_{\mathrm{even}}=(I+Z^{\otimes4})/2\). Thus \(P\) is injective on the invariant subspace
and preserves its inner products up to the factor \(2\). The proof counts the physical
preimages of a virtual label: there are two for each even-parity label and none otherwise.
These are local statements about one tensor; no torus-sector dimension is asserted here.

**Local fix (normalization):** the source primal tensor has entries \(0\) and \(1\), so its
restriction to the invariant subspace has inner-product factor \(2\). The predicate
`IsGIsometric` retains this factor rather than silently normalizing the tensor.
Documented in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## Implementation notes

The fiber-counting lemmas are proved for arbitrary finite groups and then specialized to
`ToricCodeGroup`. The virtual representation acts on coordinate functions; its generator
is identified with `toricCodePrimalParityMatrix.mulVecLin`.

## References

* arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`,
  `Papers/2011.12127/TN-Review-main.tex` lines 2451–2465. The assertion there about the dual
  color-shift tensor is distinct from the primal isometry proved here.

## Tags

toric code, PEPS, quantum double, virtual symmetry, isometry
-/

open scoped BigOperators Kronecker Matrix ComplexOrder
namespace TNLean.PEPS
private def signCharacter : ToricCodeGroup →* ℂ where
  toFun g := (-1) ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' g h := by
    change (-1 : ℂ) ^ (Multiplicative.toAdd g + Multiplicative.toAdd h).val = _
    rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

/-- The virtual \(\mathbb Z_2\) action on the primal toric-code tensor. Its nontrivial element
acts as \(Z^{\otimes4}\), with fixed subspace the even-parity configurations.
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal` and lines 2464–2465. -/
def toricCodePrimalVirtualRep : Representation ℂ ToricCodeGroup
    ((ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) → ℂ) where
  toFun g := {
    toFun := fun x c =>
      (if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then 1 else signCharacter g) * x c
    map_add' := fun x y => funext fun c => mul_add _ _ _
    map_smul' := fun a x => funext fun c => by simp [mul_left_comm] }
  map_one' := by
    refine LinearMap.ext fun x => funext fun c => ?_
    simp [signCharacter]
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun c => ?_
    change (if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then 1 else
      signCharacter (g * h)) * x c =
      (if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then 1 else signCharacter g) *
        ((if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then 1 else signCharacter h) * x c)
    split_ifs <;> simp [map_mul, mul_assoc]
private theorem signCharacter_eq_if (g : ToricCodeGroup) :
    signCharacter g = if g = 1 then 1 else -1 := by
  change (-1 : ℂ) ^ (Multiplicative.toAdd g).val =
    if Multiplicative.toAdd g = 0 then 1 else -1
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h (Multiplicative.toAdd g) with h0 | h1
  · rw [h0]
    norm_num
  · rw [h1]
    norm_num [ZMod.val_one_eq_one_mod]

private theorem toricCode_inv_eq_self (g : ToricCodeGroup) : g⁻¹ = g := by
  change -Multiplicative.toAdd g = Multiplicative.toAdd g
  generalize Multiplicative.toAdd g = a
  fin_cases a <;> rfl

/-- The virtual Pauli matrix \(Z=\operatorname{diag}(1,-1)\) in the group basis of
\(\mathbb Z_2\). Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
def toricCodeZ : Matrix ToricCodeGroup ToricCodeGroup ℂ :=
  Matrix.diagonal signCharacter

/-- The four-leg virtual parity operator \(Z^{\otimes4}\) of the primal toric-code tensor.
The nested Kronecker products use the virtual order top, right, down, left.
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
def toricCodePrimalParityMatrix :
    Matrix (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup)
      (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) ℂ :=
  toricCodeZ ⊗ₖ (toricCodeZ ⊗ₖ (toricCodeZ ⊗ₖ toricCodeZ))

private theorem toricCodePrimalParityMatrix_eq_diagonal :
    toricCodePrimalParityMatrix = Matrix.diagonal (fun c =>
      if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then (1 : ℂ) else -1) := by
  simp only [toricCodePrimalParityMatrix, toricCodeZ,
    Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext c
  rw [← map_mul, ← map_mul, ← map_mul, signCharacter_eq_if]
  congr 1
  rw [← mul_assoc, ← mul_assoc, mul_eq_one_iff_eq_inv,
    toricCode_inv_eq_self, ← eq_mul_inv_iff_mul_eq, toricCode_inv_eq_self]

/-- The nontrivial group element acts by the literal four-leg Pauli operator.
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
theorem toricCodePrimalVirtualRep_generator :
    toricCodePrimalVirtualRep (Multiplicative.ofAdd (1 : ZMod 2)) =
      toricCodePrimalParityMatrix.mulVecLin := by
  rw [toricCodePrimalParityMatrix_eq_diagonal]
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [toricCodePrimalVirtualRep, Matrix.mulVecLin, signCharacter,
    Matrix.mulVec_diagonal, ZMod.val_one_eq_one_mod]

/-- A virtual vector is invariant exactly when it is supported on labels
\(t r=l b\), or even parity in additive coordinates.
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
theorem mem_invariants_toricCodePrimalVirtualRep_iff
    (x : (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) → ℂ) :
    x ∈ toricCodePrimalVirtualRep.invariants ↔
      ∀ c, c.1 * c.2.1 ≠ c.2.2.2 * c.2.2.1 → x c = 0 := by
  constructor
  · intro hx c hc
    have h := congrFun (hx (Multiplicative.ofAdd (1 : ZMod 2))) c
    have hneg : -x c = x c := by
      simpa [toricCodePrimalVirtualRep, hc, signCharacter, ZMod.val_one_eq_one_mod] using h
    linear_combination -(1 / 2 : ℂ) * hneg
  · intro hx g
    funext c
    change (if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then 1 else signCharacter g) * x c = x c
    split_ifs with hc
    · simp
    · rw [hx c hc, mul_zero]

/-- The orthogonal projection onto the even-parity virtual configurations.
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
def toricCodeEvenProjection :
    Matrix (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup)
      (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) ℂ :=
  Matrix.diagonal (fun c => if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then 1 else 0)

/-- The even-parity projector is \((I+Z^{\otimes4})/2\).
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
theorem toricCodeEvenProjection_eq_half_one_add :
    toricCodeEvenProjection = (1 / 2 : ℂ) • (1 + toricCodePrimalParityMatrix) := by
  rw [toricCodePrimalParityMatrix_eq_diagonal, ← Matrix.diagonal_one,
    Matrix.diagonal_add, ← Matrix.diagonal_smul]
  unfold toricCodeEvenProjection
  congr 1
  funext c
  split_ifs with hc <;> norm_num [hc]

private theorem toricCodeEvenProjection_mulVec_of_invariant
    {x : (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) → ℂ}
    (hx : x ∈ toricCodePrimalVirtualRep.invariants) : toricCodeEvenProjection *ᵥ x = x := by
  funext c
  simp only [toricCodeEvenProjection, Matrix.mulVec_diagonal]
  split_ifs with hc
  · simp
  · rw [(mem_invariants_toricCodePrimalVirtualRep_iff x).1 hx c hc, mul_zero]

variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]

omit [DecidableEq G] [Fintype G] in
/-- Each admissible virtual label has one physical preimage for each choice of its second spin. -/
private theorem primalLabels_param (t r b l : G) (h : t * r = l * b) (a : G) :
    quantumDoublePrimalLabels G (t * a⁻¹, a, a * r, l⁻¹ * t * a⁻¹) = (t, r, b, l) := by
  simp only [quantumDoublePrimalLabels, Prod.mk.injEq]
  refine ⟨by group, by group, ?_, by group⟩
  calc l⁻¹ * t * a⁻¹ * (a * r) = l⁻¹ * (t * r) := by group
    _ = b := by rw [h]; group

private theorem primalLabels_fiber_sum (t r b l : G) (h : t * r = l * b)
    (F : (G × G × G × G) → ℂ) :
    (∑ g : G × G × G × G, if quantumDoublePrimalLabels G g = (t, r, b, l) then F g else 0) =
      ∑ a : G, F (t * a⁻¹, a, a * r, l⁻¹ * t * a⁻¹) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun a _ => (t * a⁻¹, a, a * r, l⁻¹ * t * a⁻¹))
    (fun g _ => g.2.1) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp [primalLabels_param t r b l h a]
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _
    rfl
  · rintro ⟨g₁, g₂, g₃, g₄⟩ hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, quantumDoublePrimalLabels,
      Prod.mk.injEq] at hg
    simp only [Prod.mk.injEq]
    rw [← hg.1, ← hg.2.1, ← hg.2.2.2]
    exact ⟨by group, True.intro, by group, by group⟩
  · intro _ _
    rfl

private theorem primalLabels_fiber_count (t r b l : G) :
    (∑ g : G × G × G × G,
      if quantumDoublePrimalLabels G g = (t, r, b, l) then (1 : ℂ) else 0) =
        if t * r = l * b then (Fintype.card G : ℂ) else 0 := by
  by_cases h : t * r = l * b
  · rw [ite_eq_left h, primalLabels_fiber_sum t r b l h]
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro g _
    split_ifs with hg
    · have hT : quantumDoublePrimalTensor G t r b l g ≠ 0 := by
        simp [quantumDoublePrimalTensor, hg.symm]
      exact (h (quantumDoublePrimalTensor_ne_zero_mul_eq_mul hT)).elim
    · rfl

/-- The primal toric-code map, with physical rows and virtual columns, in the source leg order.
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
def toricCodePrimalMatrix :
    Matrix (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup)
      (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) ℂ :=
  Matrix.of fun s c => quantumDoublePrimalTensor ToricCodeGroup c.1 c.2.1 c.2.2.1 c.2.2.2 s

/-- The virtual Gram matrix of the unnormalized primal toric-code tensor is twice the
 even-parity projector: \(P^\dagger P=2\Pi_{\mathrm{even}}\).
Source: arXiv:2011.12127, Appendix A, equation `eq:app:tcode-rep-primal`. -/
theorem toricCodePrimalMatrix_conjTranspose_mul_self :
    toricCodePrimalMatrixᴴ * toricCodePrimalMatrix = (2 : ℂ) • toricCodeEvenProjection := by
  ext c c'
  by_cases hcc : c = c'
  · subst c'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, toricCodePrimalMatrix,
      Matrix.of_apply, quantumDoublePrimalTensor, toricCodeEvenProjection,
      Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    have hterm (s : ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) :
        star (if c = quantumDoublePrimalLabels ToricCodeGroup s then (1 : ℂ) else 0) *
          (if c = quantumDoublePrimalLabels ToricCodeGroup s then (1 : ℂ) else 0) =
            if quantumDoublePrimalLabels ToricCodeGroup s = c then 1 else 0 := by
      by_cases hc : c = quantumDoublePrimalLabels ToricCodeGroup s <;> simp [hc, eq_comm]
    simp_rw [show (c.1, c.2.1, c.2.2.1, c.2.2.2) = c from rfl, hterm]
    calc
      _ = (if c.1 * c.2.1 = c.2.2.2 * c.2.2.1 then (2 : ℂ) else 0) := by
        simpa only [show Fintype.card ToricCodeGroup = 2 from rfl, Nat.cast_ofNat] using
          primalLabels_fiber_count c.1 c.2.1 c.2.2.1 c.2.2.2
      _ = _ := by split_ifs <;> norm_num
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, toricCodePrimalMatrix,
      Matrix.of_apply, quantumDoublePrimalTensor, toricCodeEvenProjection,
      Matrix.smul_apply, Matrix.diagonal_apply_ne _ hcc, smul_eq_mul, mul_zero]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs with h1 h2
    · exact (hcc (h1.trans h2.symm)).elim
    all_goals simp

private theorem siteMap_toricCodePrimal_apply
    (x : (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) → ℂ)
    (s : ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) :
    siteMap (quantumDoublePrimalTensor ToricCodeGroup) x s =
      x (quantumDoublePrimalLabels ToricCodeGroup s) := by
  simp [siteMap_apply, quantumDoublePrimalTensor]

private theorem primalLabels_even (s : ToricCodeGroup × ToricCodeGroup ×
    ToricCodeGroup × ToricCodeGroup) :
    (quantumDoublePrimalLabels ToricCodeGroup s).1 *
        (quantumDoublePrimalLabels ToricCodeGroup s).2.1 =
      (quantumDoublePrimalLabels ToricCodeGroup s).2.2.2 *
        (quantumDoublePrimalLabels ToricCodeGroup s).2.2.1 := by
  simp [quantumDoublePrimalLabels, mul_assoc]

private theorem toricCodePrimal_inner_of_invariant
    (x : (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) → ℂ)
    {y : (ToricCodeGroup × ToricCodeGroup × ToricCodeGroup × ToricCodeGroup) → ℂ}
    (hy : y ∈ toricCodePrimalVirtualRep.invariants) :
    star (siteMap (quantumDoublePrimalTensor ToricCodeGroup) x) ⬝ᵥ
      siteMap (quantumDoublePrimalTensor ToricCodeGroup) y = (2 : ℂ) * (star x ⬝ᵥ y) := by
  change star (toricCodePrimalMatrix *ᵥ x) ⬝ᵥ (toricCodePrimalMatrix *ᵥ y) = _
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    toricCodePrimalMatrix_conjTranspose_mul_self, Matrix.smul_mulVec,
    toricCodeEvenProjection_mulVec_of_invariant hy, dotProduct_smul, smul_eq_mul]

/-- The primal toric-code tensor is \(\mathbb Z_2\)-injective and \(\mathbb Z_2\)-isometric for
 the action generated by \(Z^{\otimes4}\). The inner-product factor is exactly \(2\).
This is a direct consequence of the primal tensor in arXiv:2011.12127, Appendix A,
equation `eq:app:tcode-rep-primal`; the dual color-shift tensor is treated separately in
`QuantumDouble.lean`. -/
theorem isGIsometric_toricCodePrimalTensor :
    IsGIsometric toricCodePrimalVirtualRep
      (siteMap (quantumDoublePrimalTensor ToricCodeGroup)) where
  invariant g := by
    refine LinearMap.ext fun x => funext fun s => ?_
    rw [LinearMap.comp_apply, siteMap_toricCodePrimal_apply, siteMap_toricCodePrimal_apply]
    change (if _ then 1 else signCharacter g) * _ = _
    rw [ite_eq_left (primalLabels_even s), one_mul]
  injOn_invariants x hx hPx := by
    have h := toricCodePrimal_inner_of_invariant x hx
    rw [hPx, star_zero, zero_dotProduct] at h
    have hz : star x ⬝ᵥ x = 0 := by simpa using h.symm
    exact dotProduct_star_self_eq_zero.mp hz
  exists_inner_eq := ⟨2, by norm_num, fun x _ y hy => toricCodePrimal_inner_of_invariant x hy⟩

end TNLean.PEPS
