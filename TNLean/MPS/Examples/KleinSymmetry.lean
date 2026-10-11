/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RepresentationTheory.Basic
import TNLean.MPS.Examples.CZX.CZXDecoratedTensor
import TNLean.MPS.MPDO.IdentityTensor

/-!
# The printed Klein-four spin-chain symmetry

The operators `U_a = ∏ᵢ CZᵢ,ᵢ₊₁ Zᵢ` and `U_b = ∏ᵢ Xᵢ` of
arXiv:2203.12563, Section 6, `Papers/2203.12563/REsubmission.tex`, lines 1884–1886,
are commuting unitary involutions on every nonempty periodic chain. Their product
is the decorated CZX operator. Explicit MPO tensors generate both operators.

The two invariant subspaces in line 1886 are the spans of the constant-spin
vectors and of the uniform vector together with its image under `U_a`.
The uniform vector is left unnormalized, which does not change its span.
This file proves the operator and subspace statements; the anomaly class of the
representation is identified in `TNLean.MPS.Examples.KleinSymmetryAnomaly`.

The generic construction `MPOTensor.GroupCocycle.kleinEquiv` realizes the type-II
cocycle `ScalarThreeCochain.kleinCocycle` on four-level sites. The operators here act on
qubits, so they are a different realization, and this file does not compare the two.
-/

open scoped Matrix
open CZXCompression

namespace KleinSymmetry

noncomputable section

variable (N : ℕ) [NeZero N]

/-- The diagonal operator `U_a = ∏ᵢ CZᵢ,ᵢ₊₁ Zᵢ` of arXiv:2203.12563, line 1884. -/
def generatorA : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial 1 fun t ↦ (-1 : ℂ) ^ (czExponent t + spinParity t)

/-- The global spin flip `U_b = ∏ᵢ Xᵢ` of arXiv:2203.12563, line 1884. -/
def generatorB : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial (spinFlip N) fun _ ↦ 1

/-- The diagonal generator of arXiv:2203.12563, line 1884, is an involution. -/
theorem generatorA_mul_self : generatorA N * generatorA N = 1 := by
  simp only [generatorA, Matrix.monomial_mul_monomial, one_mul, Equiv.Perm.one_apply,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, Matrix.monomial_one]

omit [NeZero N] in
/-- The spin-flip generator of arXiv:2203.12563, line 1884, is an involution. -/
theorem generatorB_mul_self : generatorB N * generatorB N = 1 := by
  simp only [generatorB, Matrix.monomial_mul_monomial, spinFlip_mul_self,
    mul_one, Matrix.monomial_one]

/-- The product `U_a U_b` is the decorated CZX operator (arXiv:2203.12563, lines 1843, 1884). -/
theorem generatorA_mul_generatorB :
    generatorA N * generatorB N = MPOTensor.mpo czxDecoratedTensor N := by
  simp only [generatorA, generatorB, Matrix.monomial_mul_monomial, one_mul,
    mul_one, mpo_czxDecoratedTensor]

/-- The printed generators commute, as required by arXiv:2203.12563, line 1884. -/
theorem generators_commute : Commute (generatorA N) (generatorB N) := by
  have hab : (generatorA N * generatorB N) * (generatorA N * generatorB N) = 1 := by
    rw [generatorA_mul_generatorB, mpo_czxDecoratedTensor_mul_self]
  have h := congrArg (fun x ↦ generatorA N * x * generatorB N) hab
  simp only [← mul_assoc, generatorA_mul_self, one_mul] at h
  change generatorA N * generatorB N = generatorB N * generatorA N
  simpa only [mul_assoc, generatorB_mul_self, mul_one] using h.symm

/-- The operator `U_a^p U_b^q` for `(p,q) ∈ ℤ₂ × ℤ₂` (arXiv:2203.12563, line 1884). -/
def operator (g : Multiplicative (ZMod 2 × ZMod 2)) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  generatorA N ^ g.toAdd.1.val * generatorB N ^ g.toAdd.2.val

/-- The identity label acts as the identity operator. -/
theorem operator_one : operator N 1 = 1 := by
  simp [operator]

/-- The printed operators satisfy the Klein-four multiplication law at every positive length. -/
theorem operator_mul (g h : Multiplicative (ZMod 2 × ZMod 2)) :
    operator N (g * h) = operator N g * operator N h := by
  have ha2 : generatorA N ^ 2 = 1 := by simpa only [pow_two] using generatorA_mul_self N
  have hb2 : generatorB N ^ 2 = 1 := by simpa only [pow_two] using generatorB_mul_self N
  change generatorA N ^ (g.toAdd.1 + h.toAdd.1).val *
    generatorB N ^ (g.toAdd.2 + h.toAdd.2).val = _
  rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ ha2, ← pow_eq_pow_mod _ hb2,
    pow_add, pow_add]
  exact ((generators_commute N).symm.pow_pow _ _).mul_mul_mul_comm _ _ |>.symm

/-- The diagonal generator fixes both constant-spin states (arXiv:2203.12563, line 1886). -/
theorem generatorA_mulVec_constantBasis (b : Fin 2) :
    generatorA N *ᵥ Pi.single (fun _ : Fin N ↦ b) 1 = Pi.single (fun _ : Fin N ↦ b) 1 := by
  rw [generatorA, Matrix.monomial_mulVec_single]
  fin_cases b <;> simp [czExponent, spinParity, pow_add, ← mul_pow]

omit [NeZero N] in
/-- The spin flip exchanges the two constant-spin states (arXiv:2203.12563, line 1886). -/
theorem generatorB_mulVec_constantBasis (b : Fin 2) :
    generatorB N *ᵥ Pi.single (fun _ : Fin N ↦ b) 1 =
      Pi.single (fun _ : Fin N ↦ b.rev) 1 := by
  rw [generatorB, Matrix.monomial_mulVec_single, one_smul]
  rfl

omit [NeZero N] in
/-- The uniform vector is fixed by the spin flip (arXiv:2203.12563, line 1886). -/
theorem generatorB_mulVec_const (c : ℂ) :
    generatorB N *ᵥ (fun _ ↦ c) = (fun _ ↦ c) := by
  simp [generatorB, Matrix.monomial_mulVec]

/-- The diagonal generator exchanges the uniform and cluster-like vectors
(arXiv:2203.12563, line 1886). -/
theorem generatorA_mulVec_cluster (c : ℂ) :
    generatorA N *ᵥ (generatorA N *ᵥ (fun _ ↦ c)) = (fun _ ↦ c) := by
  rw [Matrix.mulVec_mulVec, generatorA_mul_self, Matrix.one_mulVec]

/-- The cluster-like vector is fixed by the spin flip (arXiv:2203.12563, line 1886). -/
theorem generatorB_mulVec_cluster (c : ℂ) :
    generatorB N *ᵥ (generatorA N *ᵥ (fun _ ↦ c)) =
      generatorA N *ᵥ (fun _ ↦ c) := by
  rw [Matrix.mulVec_mulVec, ← (generators_commute N).eq, ← Matrix.mulVec_mulVec,
    generatorB_mulVec_const]

/-- A bond-two MPO tensor for `U_a`, obtained by flipping the input of the decorated CZX
tensor (arXiv:2203.12563, line 1884). -/
def tensorA : MPOTensor 2 2 := fun i j ↦ czxDecoratedTensor i j.rev

/-- The bond-one spin-flip tensor for `U_b` (arXiv:2203.12563, line 1884). -/
def tensorB : MPOTensor 2 1 := fun i j ↦ MPOTensor.idTensor 2 i j.rev

/-- The bond-two tensor generates the printed diagonal operator at every positive length. -/
theorem mpo_tensorA : MPOTensor.mpo tensorA N = generatorA N := by
  ext s t
  have he : MPOTensor.mpo tensorA N s t =
      MPOTensor.mpo czxDecoratedTensor N s (spinFlip N t) := by
    simp only [MPOTensor.mpo_apply, MPOTensor.mpoMatrixEntry, MPOTensor.evalWord_ofFn]
    rfl
  rw [he, mpo_czxDecoratedTensor_apply]
  have hflip : spinFlip N (spinFlip N t) = t :=
    congrArg (fun e : Equiv.Perm (Fin N → Fin 2) ↦ e t) spinFlip_mul_self
  rw [hflip]
  by_cases h : s = t <;> simp [generatorA, Matrix.monomial_apply, h]

omit [NeZero N] in
/-- The bond-one tensor generates the printed spin flip at every length. -/
theorem mpo_tensorB : MPOTensor.mpo tensorB N = generatorB N := by
  ext s t
  have he : MPOTensor.mpo tensorB N s t =
      MPOTensor.mpo (MPOTensor.idTensor 2) N s (spinFlip N t) := by
    simp only [MPOTensor.mpo_apply, MPOTensor.mpoMatrixEntry, MPOTensor.evalWord_ofFn]
    rfl
  rw [he, MPOTensor.mpo_idTensor]
  simp [generatorB, Matrix.monomial_apply, Matrix.one_apply]

/-- The printed Klein-four representation on periodic spin-chain states
(arXiv:2203.12563, line 1884), using Mathlib’s representation type. -/
def representation : Representation ℂ (Multiplicative (ZMod 2 × ZMod 2))
    ((Fin N → Fin 2) → ℂ) where
  toFun g := (operator N g).mulVecLin
  map_one' := by rw [operator_one]; exact Matrix.mulVecLin_one
  map_mul' g h := by rw [operator_mul]; exact Matrix.mulVecLin_mul _ _

/-- The diagonal generator is unitary. -/
theorem generatorA_mem_unitaryGroup :
    generatorA N ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  apply Matrix.monomial_mem_unitaryGroup
  intro s
  simp [star_pow, ← mul_pow]

omit [NeZero N] in
/-- The spin-flip generator is unitary. -/
theorem generatorB_mem_unitaryGroup :
    generatorB N ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  apply Matrix.monomial_mem_unitaryGroup
  intro s
  simp

/-- Every operator of the printed Klein-four representation is unitary. -/
theorem operator_mem_unitaryGroup (g : Multiplicative (ZMod 2 × ZMod 2)) :
    operator N g ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    (pow_mem (generatorA_mem_unitaryGroup N) _) (pow_mem (generatorB_mem_unitaryGroup N) _)

/-- The span of the two constant-spin vectors in arXiv:2203.12563, line 1886. -/
def constantSpinSpace : Submodule ℂ ((Fin N → Fin 2) → ℂ) :=
  Submodule.span ℂ {Pi.single (fun _ ↦ (0 : Fin 2)) 1,
    Pi.single (fun _ ↦ (1 : Fin 2)) 1}

/-- The span of the uniform vector and its image under `U_a`, as in arXiv:2203.12563,
line 1886. Leaving the uniform vector unnormalized does not change the subspace. -/
def clusterPairSpace : Submodule ℂ ((Fin N → Fin 2) → ℂ) :=
  Submodule.span ℂ {fun _ ↦ (1 : ℂ), generatorA N *ᵥ (fun _ ↦ (1 : ℂ))}

/-- Both printed generators preserve the constant-spin subspace
(arXiv:2203.12563, line 1886). -/
theorem generators_preserve_constantSpinSpace (v : (Fin N → Fin 2) → ℂ)
    (hv : v ∈ constantSpinSpace N) :
    generatorA N *ᵥ v ∈ constantSpinSpace N ∧ generatorB N *ᵥ v ∈ constantSpinSpace N := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, generatorA_mulVec_constantBasis,
    generatorB_mulVec_constantBasis]
  exact ⟨Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩,
    Submodule.mem_span_pair.mpr ⟨b, a, add_comm _ _⟩⟩

/-- Both printed generators preserve the uniform/cluster-like subspace
(arXiv:2203.12563, line 1886). -/
theorem generators_preserve_clusterPairSpace (v : (Fin N → Fin 2) → ℂ)
    (hv : v ∈ clusterPairSpace N) :
    generatorA N *ᵥ v ∈ clusterPairSpace N ∧ generatorB N *ᵥ v ∈ clusterPairSpace N := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, generatorA_mulVec_cluster,
    generatorB_mulVec_const, generatorB_mulVec_cluster]
  exact ⟨Submodule.mem_span_pair.mpr ⟨b, a, add_comm _ _⟩,
    Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩⟩

end

end KleinSymmetry
