/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.RegisterChannelLift
import TNLean.Circuit.Channel.PortRegisters
import Mathlib.Algebra.BigOperators.Fin

/-!
# Native register channels on their physical data wires

Each native alphabet of size `d ^ k` is identified with its `k` local qudit digits.
The identification is sitewise. Placing a native channel on the physical data wires
leaves all port and scratch wires as an explicit identity reference. It preserves
composition, and placing a native operator supported on selected spatial sites is
exactly placement on those sites' physical data digits.

These are coordinate identities for the actual physical operations, not additional
free operations that move information between sites.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit.PortRegisters

noncomputable section

variable {d k N s r : ℕ}

/-- All data digits of an embedded spatial register, ordered by site and then digit. -/
def selectedData (e : Fin s ↪ Fin N) : Fin (s * k) ↪ Fin (N * (1 + k + k)) :=
  finProdFinEquiv.symm.toEmbedding.trans
    { toFun := fun p : Fin s × Fin k => data (e p.1) p.2
      inj' := by
        intro p q h
        have hi : p.1 = q.1 := e.injective (by
          simpa only [site_data] using congrArg (layout N k).site h)
        have ht : p.2 = q.2 := (data (e q.1)).injective (by simpa only [hi] using h)
        exact Prod.ext hi ht }

@[simp] theorem selectedData_apply (e : Fin s ↪ Fin N) (i : Fin s) (t : Fin k) :
    selectedData e (finProdFinEquiv (i, t)) = data (e i) t := by
  change data (e (finProdFinEquiv.symm (finProdFinEquiv (i, t))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i, t))).2 = _
  rw [Equiv.symm_apply_apply]

/-- The embedding of all data digits into the physical port-and-memory layout. -/
def allData (N k : ℕ) : Fin (N * k) ↪ Fin (N * (1 + k + k)) :=
  selectedData (Function.Embedding.refl (Fin N))

@[simp] theorem allData_apply (i : Fin N) (t : Fin k) :
    allData N k (finProdFinEquiv (i, t)) = data i t := selectedData_apply _ i t

/-- Group qudit digits into native basis labels independently at each spatial site. -/
def groupedConfigurations (N k d : ℕ) : (Fin (N * k) → Fin d) ≃ (Fin N → Fin (d ^ k)) where
  toFun x i := finFunctionFinEquiv (fun t => x (finProdFinEquiv (i, t)))
  invFun x p := finFunctionFinEquiv.symm (x (finProdFinEquiv.symm p).1)
    (finProdFinEquiv.symm p).2
  left_inv x := by
    funext p
    obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective p
    simp only [Equiv.symm_apply_apply]
  right_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Read the native basis label stored in each physical data register. -/
def dataConfiguration (x : Fin (N * (1 + k + k)) → Fin d) : Fin N → Fin (d ^ k) :=
  fun i => finFunctionFinEquiv (fun t => x (data i t))

@[simp] theorem selectedData_configuration (e : Fin s ↪ Fin N)
    (x : Fin (N * (1 + k + k)) → Fin d) :
    groupedConfigurations s k d (x ∘ selectedData e) = dataConfiguration x ∘ e := by
  funext i
  change finFunctionFinEquiv (fun t => x (selectedData e (finProdFinEquiv (i, t)))) = _
  simp only [selectedData_apply]
  rfl

@[simp] theorem allData_configuration (x : Fin (N * (1 + k + k)) → Fin d) :
    groupedConfigurations N k d (x ∘ allData N k) = dataConfiguration x :=
  selectedData_configuration (Function.Embedding.refl (Fin N)) x

/-- Change only the basis labels of a native register into their local qudit words. -/
def nativeMatrixEquiv (N k d : ℕ) :
    Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (N * k) → Fin d) (Fin (N * k) → Fin d) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (groupedConfigurations N k d).symm

@[simp] theorem nativeMatrixEquiv_apply
    (A : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ)
    (x y : Fin (N * k) → Fin d) :
    nativeMatrixEquiv N k d A x y =
      A (groupedConfigurations N k d x) (groupedConfigurations N k d y) := rfl

@[simp] theorem nativeMatrixEquiv_conjTranspose
    (A : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    nativeMatrixEquiv N k d Aᴴ = (nativeMatrixEquiv N k d A)ᴴ := rfl

/-- A native operator acts on data wires alone; all ports and scratch digits are untouched. -/
def dataOperator (A : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    Matrix (Fin (N * (1 + k + k)) → Fin d) (Fin (N * (1 + k + k)) → Fin d) ℂ :=
  embedOp (allData N k) (nativeMatrixEquiv N k d A)

theorem dataOperator_apply
    (A : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ)
    (x y : Fin (N * (1 + k + k)) → Fin d) :
    dataOperator A x y =
      if AgreeOff (allData N k) x y then A (dataConfiguration x) (dataConfiguration y) else 0 := by
  simp only [dataOperator, embedOp_apply, nativeMatrixEquiv_apply, allData_configuration]

private theorem agreeOff_selectedData_iff (e : Fin s ↪ Fin N)
    (x y : Fin (N * (1 + k + k)) → Fin d) :
    AgreeOff (selectedData e) x y ↔ AgreeOff (allData N k) x y ∧
      AgreeOff e (dataConfiguration x) (dataConfiguration y) := by
  constructor
  · intro h
    constructor
    · intro w hw
      apply h w
      intro p hp
      obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective p
      exact hw (finProdFinEquiv (e i, t))
        (by simpa only [selectedData_apply, allData_apply] using hp)
    · intro i hi
      apply congrArg finFunctionFinEquiv
      funext t
      apply h (data i t)
      intro p hp
      obtain ⟨⟨a, u⟩, rfl⟩ := finProdFinEquiv.surjective p
      exact hi a (by
        simpa only [selectedData_apply, site_data] using congrArg (layout N k).site hp)
  · rintro ⟨hall, hsites⟩ w hw
    by_cases hwd : w ∈ Set.range (allData N k)
    · obtain ⟨p, rfl⟩ := hwd
      obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective p
      rw [allData_apply] at hw ⊢
      have hi : ∀ a, e a ≠ i := by
        intro a ha
        exact hw (finProdFinEquiv (a, t)) (by simp only [selectedData_apply, ha])
      have hcfg := finFunctionFinEquiv.injective (hsites i hi)
      exact congrFun hcfg t
    · exact hall w fun p hp => hwd ⟨p, hp⟩

/-- A native operator on selected sites becomes the same operator on their physical
qudit digits. The identity holds on the full physical operator space. -/
theorem dataOperator_embedOp (e : Fin s ↪ Fin N)
    (A : Matrix (Fin s → Fin (d ^ k)) (Fin s → Fin (d ^ k)) ℂ) :
    dataOperator (embedOp e A) = embedOp (selectedData e) (nativeMatrixEquiv s k d A) := by
  ext x y
  rw [dataOperator_apply]
  simp only [embedOp_apply, nativeMatrixEquiv_apply, selectedData_configuration,
    agreeOff_selectedData_iff]
  split_ifs <;> simp_all

/-- Reindex native endomorphisms through the sitewise grouping equivalence. -/
def nativeChannelReindex (N k d : ℕ) :
    Module.End ℂ (Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) →*
      Module.End ℂ (Matrix (Fin (N * k) → Fin d) (Fin (N * k) → Fin d) ℂ) :=
  (nativeMatrixEquiv N k d).toLinearEquiv.conjRingEquiv.toMonoidHom

/-- Sitewise basis regrouping sends each Kraus operator through the same matrix equivalence. -/
theorem nativeChannelReindex_kraus
    (A : Fin r → Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    nativeChannelReindex N k d (rectangularKrausMap A) =
      rectangularKrausMap (fun a => nativeMatrixEquiv N k d (A a)) := by
  apply LinearMap.ext
  intro X
  let E := nativeMatrixEquiv N k d
  change E (∑ a, A a * E.symm X * (A a)ᴴ) = ∑ a, E (A a) * X * (E (A a))ᴴ
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_mul, E, nativeMatrixEquiv_conjTranspose, AlgEquiv.apply_symm_apply]

/-- Place native channels on data wires, leaving ports and scratch registers as identity
reference systems. Composition is preserved without inserting any extra operation. -/
def dataChannelLift (N k d : ℕ) :
    Module.End ℂ (Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) →*
      Module.End ℂ (Matrix (Fin (N * (1 + k + k)) → Fin d)
        (Fin (N * (1 + k + k)) → Fin d) ℂ) where
  toFun Φ := registerChannelLift (allData N k) (nativeChannelReindex N k d Φ)
  map_one' := by
    rw [map_one]
    exact registerChannelLift_id _
  map_mul' Φ Ψ := by
    rw [map_mul]
    exact registerChannelLift_comp _ (nativeChannelReindex N k d Ψ) (nativeChannelReindex N k d Φ)

/-- The native channel placement uses exactly the corresponding placed Kraus operators. -/
theorem dataChannelLift_kraus
    (A : Fin r → Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    dataChannelLift N k d (rectangularKrausMap A) =
      rectangularKrausMap (fun a => dataOperator (A a)) := by
  change registerChannelLift (allData N k) (nativeChannelReindex N k d (rectangularKrausMap A)) = _
  rw [nativeChannelReindex_kraus, registerChannelLift_kraus]
  rfl

end

end QuantumCircuit.PortRegisters
