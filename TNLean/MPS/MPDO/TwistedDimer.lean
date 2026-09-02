/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import TNLean.MPS.MPDO.PhysicalClosure
import TNLean.MPS.MPDO.ZCL

/-!
# The $\mathbb Z_2$-twisted quantum dimer

**Scope: tensor and local closure formulas.** This file defines an MPO tensor
for the $\mathbb Z_2$-twisted quantum dimer, a project example motivated by the
length-dependence question after Theorem 4.14 of arXiv:1606.00608 (lines
995--1010), and proves entrywise formulas for its one-site and two-site physical
closures and for the physical-trace transfers of its two displayed blocks. The
all-length closed operator identity, positivity, fixed-point channels,
non-simplicity of the tensor, and attachment of fusion data are not asserted
here.

## The tensor

Each site is a pair of qubits $L, R$ together with a flag qubit $f$; the
physical index `i : Fin 8` is read as the bits `(bitL i, bitR i, bitF i)`.  The
bond index `a : Fin 8` is read as `(bitL a, bitR a, bitF a) = (p, p', k)`, where
`k` selects one of two horizontal blocks.  With the bond weights
$x = 7/8$, $y = 1/8$ and the $2 \times 2$ matrices
$C_0 = x P_+ + y P_-$, $C_1 = x P_+ - y P_-$ ($P_\pm = (\mathbb 1 \pm X)/2$),
the physical operator of the bond pair $((p,p',k),(q,q',k))$ is
$$
  \tfrac12\, C_k[p,p']\; E_{pp'} \otimes E_{qq'} \otimes \tau_k,
  \qquad \tau_0 = \mathbb 1,\ \tau_1 = Z,
$$
and the physical operator of a bond pair with different block labels vanishes.
Equivalently, for physical indices $i = (l,r,f)$ and $j = (l',r',f')$ the bond
matrix $M^{ij}$ is the sum over $k$ of the matrix units at
$((l,l',k),(r,r',k))$ with coefficient
$\tfrac12 C_k[l,l']\,(\tau_k)_{ff}\,\delta_{ff'}$ (`coef`).

## Main results

* `physClose1_T` — the one-site physical closure is the sum over $k$ of the
  coefficient times the bond-matrix entry at the transposed matrix unit;
* `physClose2_T` — the two-site closure is gated by the bond-matching
  condition `bitR i₁ = bitL i₂`, `bitR j₁ = bitL j₂` and keeps a common block
  label $k$;
* `physTraceTransfer_block_zero` and `physTraceTransfer_block_one` — the flag
  trace $\operatorname{tr}\tau_1 = 0$ kills the displayed block $k = 1$, while
  the transfer of the displayed block $k = 0$ has an explicit rank-one form.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1, Definition 4.7, Theorem 4.14 and lines 995--1010 (project
  example, not a tensor stated in the source)
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### Bit encodings of the physical and bond indices -/

/-- The index `(l, r, f) ↦ 4 l + 2 r + f` of `Fin 8`. -/
def physIdx (l r f : Fin 2) : Fin 8 := ⟨l.val * 4 + r.val * 2 + f.val, by omega⟩

/-- The first bit of an index of `Fin 8`. -/
def bitL (i : Fin 8) : Fin 2 := ⟨i.val / 4, by omega⟩

/-- The second bit of an index of `Fin 8`. -/
def bitR (i : Fin 8) : Fin 2 := ⟨i.val / 2 % 2, by omega⟩

/-- The third bit of an index of `Fin 8`. -/
def bitF (i : Fin 8) : Fin 2 := ⟨i.val % 2, by omega⟩

@[simp] lemma bitL_physIdx (l r f : Fin 2) : bitL (physIdx l r f) = l := by
  ext; simp only [bitL, physIdx]; omega

@[simp] lemma bitR_physIdx (l r f : Fin 2) : bitR (physIdx l r f) = r := by
  ext; simp only [bitR, physIdx]; omega

@[simp] lemma bitF_physIdx (l r f : Fin 2) : bitF (physIdx l r f) = f := by
  ext; simp only [bitF, physIdx]; omega

lemma physIdx_bits (i : Fin 8) : physIdx (bitL i) (bitR i) (bitF i) = i := by
  ext; simp only [physIdx, bitL, bitR, bitF]; omega

/-- Every index of `Fin 8` is the bit encoding of its three bits. -/
lemma exists_eq_physIdx (i : Fin 8) : ∃ l r f, i = physIdx l r f :=
  ⟨_, _, _, (physIdx_bits i).symm⟩

lemma physIdx_inj {l r f l' r' f' : Fin 2} :
    physIdx l r f = physIdx l' r' f' ↔ l = l' ∧ r = r' ∧ f = f' := by
  constructor
  · intro h
    have h1 := congrArg bitL h
    have h2 := congrArg bitR h
    have h3 := congrArg bitF h
    simp only [bitL_physIdx, bitR_physIdx, bitF_physIdx] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- The bit encoding as an equivalence `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8`. -/
def physEquiv : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 where
  toFun x := physIdx x.1 x.2.1 x.2.2
  invFun i := (bitL i, bitR i, bitF i)
  left_inv := by rintro ⟨l, r, f⟩; simp
  right_inv i := physIdx_bits i

/-! ### Weights and coefficients -/

/-- The bond weight $x = 7/8$ of the rational point. -/
def x : ℝ := 7 / 8

/-- The bond weight $y = 1/8$ of the rational point. -/
def y : ℝ := 1 / 8

/-- The diagonal entry $(x + y)/2$ of $C_0$, equal to the off-diagonal entry of $C_1$. -/
def cDiag : ℝ := (x + y) / 2

/-- The off-diagonal entry $(x - y)/2$ of $C_0$, equal to the diagonal entry of $C_1$. -/
def cOff : ℝ := (x - y) / 2

lemma cDiag_eq : cDiag = 1 / 2 := by norm_num [cDiag, x, y]

lemma cOff_eq : cOff = 3 / 8 := by norm_num [cOff, x, y]

/-- The bond matrices $C_0 = x P_+ + y P_-$ and $C_1 = x P_+ - y P_-$. -/
def Cmat (k p p' : Fin 2) : ℝ := if (p = p' ↔ k = 0) then cDiag else cOff

/-- The flag sign $(\tau_k)_{ff} = (-1)^{kf}$. -/
def tau (k f : Fin 2) : ℝ := if k = 1 ∧ f = 1 then -1 else 1

lemma tau_zero (f : Fin 2) : tau 0 f = 1 := by simp [tau]

lemma tau_one_sum : tau 1 0 + tau 1 1 = 0 := by simp [tau]

/-- The coefficient $\tfrac12 C_k[l,l']\,(\tau_k)_{ff}\,\delta_{ff'}$ of the matrix unit
at the bond pair $((l,l',k),(r,r',k))$ in the physical letter $(i, j)$. -/
def coef (k : Fin 2) (i j : Fin 8) : ℂ :=
  if bitF i = bitF j then ((Cmat k (bitL i) (bitL j) * tau k (bitF i) / 2 : ℝ) : ℂ) else 0

lemma coef_physIdx (k l r f l' r' f' : Fin 2) :
    coef k (physIdx l r f) (physIdx l' r' f') =
      if f = f' then ((Cmat k l l' * tau k f / 2 : ℝ) : ℂ) else 0 := by
  simp [coef]

/-! ### The tensor -/

/-- The $\mathbb Z_2$-twisted quantum dimer: for physical letter `(i, j)`, the bond
matrix is the sum over the block label `k` of the matrix unit at
`((bitL i, bitL j, k), (bitR i, bitR j, k))` with coefficient `coef k i j`. -/
def T : MPOTensor 8 8 := fun i j =>
  ∑ k : Fin 2,
    Matrix.single (physIdx (bitL i) (bitL j) k) (physIdx (bitR i) (bitR j) k) (coef k i j)

/-- The two horizontal blocks, each an MPO tensor with bond dimension four. -/
def block (k : Fin 2) : MPOTensor 8 4 := fun i j =>
  Matrix.single (finProdFinEquiv (bitL i, bitL j)) (finProdFinEquiv (bitR i, bitR j)) (coef k i j)

/-- The tensor is the direct sum of its two blocks along the block label. -/
lemma T_apply_blocks (i j : Fin 8) (p p' k q q' k' : Fin 2) :
    T i j (physIdx p p' k) (physIdx q q' k') =
      if k = k' then block k i j (finProdFinEquiv (p, p')) (finProdFinEquiv (q, q')) else 0 := by
  fin_cases k <;> fin_cases k' <;>
    simp [T, block, Matrix.sum_apply, Matrix.single_apply, physIdx_inj, Fin.sum_univ_two,
      finProdFinEquiv.injective.eq_iff]

/-! ### Physical closures -/

/-- **One-site closure.**  `physClose1 T X i j = ∑ k, coef k i j * X (r-unit) (l-unit)`. -/
theorem physClose1_T (X : Matrix (Fin 8) (Fin 8) ℂ) (i j : Fin 8) :
    physClose1 T X i j =
      ∑ k : Fin 2, coef k i j *
        X (physIdx (bitR i) (bitR j) k) (physIdx (bitL i) (bitL j) k) := by
  simp only [physClose1_apply, T, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul,
    smul_eq_mul]

lemma single_mul_single_ite {a b c e : Fin 8} (u v : ℂ) :
    Matrix.single a b u * Matrix.single c e v =
      if b = c then Matrix.single a e (u * v) else (0 : Matrix (Fin 8) (Fin 8) ℂ) := by
  by_cases h : b = c
  · subst h; simp
  · simp [h]

/-- The bond-matching condition between consecutive letters. -/
def gate (i₁ i₂ : Fin 8) : Prop := bitR i₁ = bitL i₂

instance decidableGate (i₁ i₂ : Fin 8) : Decidable (gate i₁ i₂) :=
  inferInstanceAs (Decidable (bitR i₁ = bitL i₂))

/-- The product of two letters keeps a common block label and is gated by the
bond-matching condition. -/
lemma T_mul_T (i₁ j₁ i₂ j₂ : Fin 8) :
    T i₁ j₁ * T i₂ j₂ =
      if gate i₁ i₂ ∧ gate j₁ j₂ then
        ∑ k : Fin 2, Matrix.single (physIdx (bitL i₁) (bitL j₁) k)
          (physIdx (bitR i₂) (bitR j₂) k) (coef k i₁ j₁ * coef k i₂ j₂)
      else 0 := by
  simp only [T, Fin.sum_univ_two, add_mul, mul_add, single_mul_single_ite, physIdx_inj]
  by_cases h1 : bitR i₁ = bitL i₂ <;> by_cases h2 : bitR j₁ = bitL j₂ <;>
    simp [gate, h1, h2]

/-- **Two-site closure.** -/
theorem physClose2_T (X : Matrix (Fin 8) (Fin 8) ℂ) (i₁ i₂ j₁ j₂ : Fin 8) :
    physClose2 T X (i₁, i₂) (j₁, j₂) =
      if gate i₁ i₂ ∧ gate j₁ j₂ then
        ∑ k : Fin 2, coef k i₁ j₁ * coef k i₂ j₂ *
          X (physIdx (bitR i₂) (bitR j₂) k) (physIdx (bitL i₁) (bitL j₁) k)
      else 0 := by
  rw [physClose2_apply, T_mul_T]
  split_ifs
  · simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_single_mul, smul_eq_mul]
  · simp

/-! ### The physical-trace transfer -/

lemma coef_diag_sum_flag (k l r : Fin 2) :
    ∑ f : Fin 2, coef k (physIdx l r f) (physIdx l r f) =
      if k = 0 then ((Cmat 0 l l : ℝ) : ℂ) else 0 := by
  simp only [coef_physIdx, ite_true, Fin.sum_univ_two]
  fin_cases k
  · simp [tau]
  · simp [tau]; ring

/-- **The physical-trace transfer of the displayed block `k = 1` vanishes**:
the flag trace $\operatorname{tr}\tau_1 = 0$ kills every entry. Thus this block
has nilpotent physical-trace transfer in the sense used by Definition 4.7 of
arXiv:1606.00608, lines 815--822. This does not assert non-simplicity of `T`. -/
theorem physTraceTransfer_block_one : physTraceTransfer (block 1) = 0 := by
  unfold physTraceTransfer
  rw [← Fintype.sum_equiv physEquiv (fun x => block 1 (physEquiv x) (physEquiv x))
    (fun i => block 1 i i) (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, physEquiv, Equiv.coe_fn_mk, block, bitL_physIdx,
    bitR_physIdx]
  ext a b
  simp only [Matrix.sum_apply, Matrix.single_apply]
  have key : ∀ l r : Fin 2, ∑ f : Fin 2, coef 1 (physIdx l r f) (physIdx l r f) = 0 := by
    intro l r
    rw [coef_diag_sum_flag]; simp
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun r _ => ?_
  by_cases h : finProdFinEquiv (l, l) = a ∧ finProdFinEquiv (r, r) = b
  · simp only [h, and_self, ite_true]
    exact key l r
  · simp [h]

/-- The physical-trace transfer of the block `k = 0` is the rank-one bond matrix
$\sum_{l,r} C_0[l,l]\,E_{(l,l),(r,r)}$. -/
theorem physTraceTransfer_block_zero :
    physTraceTransfer (block 0) =
      ∑ l : Fin 2, ∑ r : Fin 2,
        Matrix.single (finProdFinEquiv (l, l)) (finProdFinEquiv (r, r)) ((Cmat 0 l l : ℝ) : ℂ) := by
  unfold physTraceTransfer
  rw [← Fintype.sum_equiv physEquiv (fun x => block 0 (physEquiv x) (physEquiv x))
    (fun i => block 0 i i) (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, physEquiv, Equiv.coe_fn_mk, block, bitL_physIdx,
    bitR_physIdx]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => ?_
  have hsum : ∑ f : Fin 2, coef 0 (physIdx l r f) (physIdx l r f) = ((Cmat 0 l l : ℝ) : ℂ) := by
    rw [coef_diag_sum_flag]; simp
  rw [← hsum]
  simp only [Fin.sum_univ_two, Matrix.single_add]

end MPOTensor.TwistedDimer
