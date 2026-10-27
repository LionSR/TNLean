/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.PairProduct
import TNLean.MPS.AreaLaw.OpenMPS
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Site products and bond-one open-boundary representations

An open-boundary state with internal bond dimensions at most one is a scalar
multiple of a product of one-site coefficients. Conversely, every such
product has a representation with one-dimensional virtual spaces. The scalar
cap includes the empty chain, and zero-dimensional internal bonds give the
zero state.

Pairing the row and column labels at each site gives the corresponding
characterization for operators. Tensor products of one-site matrices, and
in particular every operator supported on a singleton, have bond bound one.
These are elementary supporting facts for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1316–1333; no general MPO bond bound is asserted here.
-/

open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- A site product has an explicit open-boundary representation with every
bond dimension one, including empty chains and empty physical alphabets.
This supplies elementary operator factors used in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem isOpenMPS_prod {L q : ℕ} (f : Fin L → Fin q → ℂ) :
    IsOpenMPS L q 1 (fun w ↦ ∏ v, f v (w v)) := by
  classical
  let A : OBCChainTensor q 1 L :=
    { bondDim := fun _ ↦ 1
      bondDim_le := fun _ ↦ le_rfl
      left_dim := rfl
      right_dim := rfl
      tensor := fun v i _ _ ↦ f v i }
  refine ⟨A, 1, fun _ _ _ ↦ le_rfl, ?_⟩
  intro w
  simp [OBCChainTensor.coeff, A]

/-- A product of one-site operator entries has bond dimension bound one.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem isOpenMPS_operator_entries_prod {L q : ℕ}
    (M : Fin L → Matrix (Fin q) (Fin q) ℂ) :
    IsOpenMPS L (q * q) 1 (fun w ↦
      ∏ v, M v (w v).divNat (w v).modNat) :=
  isOpenMPS_prod (fun v i ↦ M v i.divNat i.modNat)

/-- A tensor product of one-site matrices has bond dimension bound one.
This is the product-operator case of ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem isOpenMPS_operator_entries_rectKronecker {L q : ℕ}
    (M : Fin L → Matrix (Fin q) (Fin q) ℂ) :
    IsOpenMPS L (q * q) 1 (fun w ↦
      Matrix.rectKronecker M
        (fun v ↦ (w v).divNat) (fun v ↦ (w v).modNat)) :=
  isOpenMPS_operator_entries_prod M

/-- An arbitrary operator placed at one site has bond dimension bound one.
No positivity or nonzero local dimension is required. Supporting locality
algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem isOpenMPS_operator_entries_embed_one_site {L q : ℕ} (v : Fin L)
    (X : Matrix (Fin 1 → Fin q) (Fin 1 → Fin q) ℂ) :
    IsOpenMPS L (q * q) 1 (fun w ↦
      QuantumCircuit.embedOp (fun _ : Fin 1 ↦ v) X
        (fun t ↦ (w t).divNat) (fun t ↦ (w t).modNat)) := by
  classical
  let e := fun _ : Fin 1 ↦ v
  have he : Function.Injective e := fun _ _ _ ↦ Subsingleton.elim _ _
  let N : Fin 1 → Matrix (Fin q) (Fin q) ℂ :=
    fun _ i j ↦ X (fun _ ↦ i) (fun _ ↦ j)
  have hX : X = Matrix.rectKronecker N := by
    ext x y
    rw [Matrix.rectKronecker_apply, Fin.prod_univ_one]
    change X x y = X (fun _ ↦ x 0) (fun _ ↦ y 0)
    congr 1 <;> funext i <;> congr 1 <;> exact Subsingleton.elim _ _
  rw [hX, QuantumCircuit.embedOp_rectKronecker he]
  exact isOpenMPS_operator_entries_rectKronecker (Function.extend e N 1)

/-- Every operator supported on a singleton has bond dimension bound one.
Supporting locality algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem isOpenMPS_operator_entries_of_supported_singleton {L q : ℕ} (v : Fin L)
    (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hM : M ∈ QuantumCircuit.supportedOperators q ({v} : Set (Fin L))) :
    IsOpenMPS L (q * q) 1 (fun w ↦
      M (fun t ↦ (w t).divNat) (fun t ↦ (w t).modNat)) := by
  classical
  let e := fun _ : Fin 1 ↦ v
  have he : Function.Injective e := fun _ _ _ ↦ Subsingleton.elim _ _
  have hs : M ∈ QuantumCircuit.supportedOperators q (Set.range e) := by
    simpa only [e, Set.range_const] using hM
  obtain ⟨X, rfl⟩ := QuantumCircuit.exists_embedOp_eq_of_mem_supportedOperators he hs
  exact isOpenMPS_operator_entries_embed_one_site v X

end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

/-- An open-boundary state with internal bond bound one is a scalar multiple
of a site product. This is the bond-one case of the one-dimensional note,
Part IIa, Proposition `prop:VC`, lines 39–62, and an elementary supporting
case for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1316–1333.
No nonzero-state or positive-length hypothesis is required. -/
theorem IsOpenMPS.exists_eq_mul_prod {L q : ℕ}
    {ψ : (Fin L → Fin q) → ℂ} (hψ : IsOpenMPS L q 1 ψ) :
    ∃ c : ℂ, ∃ f : Fin L → Fin q → ℂ,
      ∀ w, ψ w = c * ∏ v, f v (w v) := by
  classical
  obtain ⟨A, c, _hD, hcoeff⟩ := hψ
  by_cases hzero : ∃ k, A.bondDim k = 0
  · obtain ⟨k, hk⟩ := hzero
    refine ⟨0, fun _ _ ↦ 1, ?_⟩
    intro w
    rw [hcoeff w, A.coeff_eq_zero_of_bondDim_eq_zero w k hk]
    simp
  · have hdim (k : Fin (L + 1)) : A.bondDim k = 1 := by
      have hle : A.bondDim k ≤ 1 := by simpa using A.bondDim_le k
      have hne : A.bondDim k ≠ 0 := fun hk ↦ hzero ⟨k, hk⟩
      omega
    let e : ((k : Fin (L + 1)) → Fin (A.bondDim k)) ≃
        (Fin (L + 1) → Fin 1) :=
      Equiv.piCongrRight (fun k ↦ (Fin.castOrderIso (hdim k)).toEquiv)
    let : Unique ((k : Fin (L + 1)) → Fin (A.bondDim k)) := Equiv.unique e
    let α₀ : (k : Fin (L + 1)) → Fin (A.bondDim k) := default
    refine ⟨c, fun v s ↦ A.tensor v s (α₀ v.castSucc) (α₀ v.succ), ?_⟩
    intro w
    simpa only [OBCChainTensor.coeff, Fintype.sum_unique, α₀] using hcoeff w

end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

/-- The paired entries of a bond-one open-boundary operator are a scalar
multiple of a product of one-site matrix entries. This is supporting
bond-one algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1316–1333. Neither a nonzero operator nor positive chain length or
local dimension is required. -/
theorem IsOpenMPS.exists_operator_entries_eq_mul_prod {L q : ℕ}
    {M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hM : IsOpenMPS L (q * q) 1 (fun w ↦
      M (fun v ↦ (w v).divNat) (fun v ↦ (w v).modNat))) :
    ∃ c : ℂ, ∃ A : Fin L → Matrix (Fin q) (Fin q) ℂ,
      ∀ x y, M x y = c * ∏ v, A v (x v) (y v) := by
  obtain ⟨c, f, hf⟩ := hM.exists_eq_mul_prod
  refine ⟨c, fun v i j ↦ f v (finProdFinEquiv (i, j)), ?_⟩
  intro x y
  have hdiv (a b : Fin q) :
      ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)) (a, b)).divNat = a :=
    congrArg Prod.fst
      ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm_apply_apply (a, b))
  have hmod (a b : Fin q) :
      ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)) (a, b)).modNat = b :=
    congrArg Prod.snd
      ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm_apply_apply (a, b))
  simpa only [hdiv, hmod] using
    hf (fun v ↦ (finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)) (x v, y v))

end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

/-- Bond bound one is equivalent to a scalar multiple of a site product,
including zero states, empty alphabets and the empty chain. This is the
bond-one case of the one-dimensional note, Part IIa, Proposition `prop:VC`,
lines 39–62. -/
theorem isOpenMPS_one_iff_exists_eq_mul_prod {L q : ℕ} {ψ : (Fin L → Fin q) → ℂ} :
    IsOpenMPS L q 1 ψ ↔ ∃ c : ℂ, ∃ f : Fin L → Fin q → ℂ,
      ∀ w, ψ w = c * ∏ v, f v (w v) := by
  constructor
  · exact IsOpenMPS.exists_eq_mul_prod
  · rintro ⟨c, f, hf⟩
    have heq : ψ = fun w ↦ c * ∏ v, f v (w v) := funext hf
    rw [heq]
    exact (isOpenMPS_prod f).smul c

end TNLean.MPS.AreaLaw
