/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPortCodes
import TNLean.Circuit.Channel.PhysicalRegisterEncoding

/-!
# Product data initialization and the explicit zero reference

The concrete product data-code initializer is exactly the physical encoding with its
port/scratch reference prepared in the product zero state. This coordinate identity
connects the arbitrary-reference encoded compiler to actual product-ancilla preparation.
-/

open Matrix
open scoped BigOperators Kronecker

namespace QuantumCircuit

noncomputable section

private theorem registerEncoding_map_single {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ↪ β) (a b : α) (z : ℂ) :
    singleKrausMap (registerEncoding e) (single a b z) = single (e a) (e b) z := by
  ext x y
  rw [singleKrausMap_apply, Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_single_apply_same]
    simp only [registerEncoding, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
      Matrix.conjTranspose_apply, Matrix.single_apply]
    split_ifs <;> simp_all
  · intro j _ hj
    rw [Matrix.mul_single_apply_of_ne z a b x j hj, zero_mul]
  · simp

private theorem reindex_single_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b : α) (z : ℂ) :
    Matrix.reindex e e (single a b z) = single (e a) (e b) z := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply,
    Equiv.eq_symm_apply]

namespace PortRegisters

variable {N k d : ℕ} [NeZero d]

/-- The local data code before adding its port and scratch digits. -/
def bareDataCode (c : Fin d ↪ Fin (d ^ k)) : Fin d ↪ (Fin k → Fin d) :=
  c.trans finFunctionFinEquiv.symm.toEmbedding

omit [NeZero d] in
@[simp] theorem nativeWordCode_bareDataCode (c : Fin d ↪ Fin (d ^ k)) :
    nativeWordCode (bareDataCode c) = c := by
  apply Function.Embedding.ext
  intro x
  exact finFunctionFinEquiv.apply_symm_apply (c x)

private theorem data_word_split (c : Fin d ↪ Fin (d ^ k)) (x : Fin N → Fin d) :
    registerConfigurationSplit (allData N k) (wordCodeConfiguration (dataWordCode c) x) =
      (wordCodeConfiguration (bareDataCode c) x, (0 : DataReference N k d)) := by
  apply Prod.ext
  · funext p
    obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective p
    change wordCodeConfiguration (dataWordCode c) x (allData N k (finProdFinEquiv (i, t))) = _
    rw [allData_apply]
    change wordCodeConfiguration (dataWordCode c) x
      (finProdFinEquiv (i, Fin.castAdd k (Fin.natAdd 1 t))) = _
    change wordCodeConfiguration (dataWordCode c) x
      (finProdFinEquiv (i, Fin.castAdd k (Fin.natAdd 1 t))) =
        wordCodeConfiguration (bareDataCode c) x (finProdFinEquiv (i, t))
    rw [wordCodeConfiguration_apply, dataWordCode_data, wordCodeConfiguration_apply]
    rfl
  · funext j
    rcases j with ⟨j, hj⟩
    change wordCodeConfiguration (dataWordCode c) x j = 0
    obtain ⟨⟨i, u⟩, rfl⟩ := finProdFinEquiv.surjective j
    rw [wordCodeConfiguration_apply]
    revert hj
    refine Fin.addCases (fun u => ?_) (fun t => ?_) u
    · refine Fin.addCases (fun a => ?_) (fun t => ?_) u
      · intro _
        have ha : a = 0 := Subsingleton.elim _ _
        subst a
        exact dataWordCode_port c (x i)
      · intro hj
        exfalso
        apply hj
        refine ⟨finProdFinEquiv (i, t), ?_⟩
        rw [allData_apply]
        rfl
    · intro _
      exact dataWordCode_scratch c (x i) t

/-- Prepare the complementary port/scratch registers in their product zero state. -/
def zeroDataReferencePrep :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix ((Fin N → Fin d) × DataReference N k d)
        ((Fin N → Fin d) × DataReference N k d) ℂ :=
  (Matrix.kroneckerBilinear (R := ℂ)).flip
    (single (0 : DataReference N k d) 0 (1 : ℂ))

/-- The concrete product data initializer equals the physical encoding with a zero
port/scratch reference, as an identity on every logical input operator. -/
theorem wordInitialization_data_eq_physicalEncoding (c : Fin d ↪ Fin (d ^ k)) :
    wordInitialization (N := N) (dataWordCode c) =
      physicalEncoding (OnsiteChannel.encodeRegisters (fun _ : Fin N => c)).map ∘ₗ
        zeroDataReferencePrep := by
  have hbare : wordInitialization (N := N) (bareDataCode c) =
      (nativeMatrixEquiv N k d).toLinearMap ∘ₗ
        (OnsiteChannel.encodeRegisters (fun _ : Fin N => c)).map := by
    rw [wordInitialization_eq, nativeWordCode_bareDataCode]
  apply Matrix.ext_linearMap
  intro a b
  apply LinearMap.ext
  intro z
  let S := registerMatrixSplit (d := d) (allData N k)
  apply S.injective
  change S (wordInitialization (N := N) (dataWordCode c) (single a b z)) =
    S (physicalEncoding (OnsiteChannel.encodeRegisters (fun _ : Fin N => c)).map
      (zeroDataReferencePrep (single a b z)))
  rw [show wordInitialization (N := N) (dataWordCode c) (single a b z) =
      single (wordCodeConfiguration (dataWordCode c) a)
        (wordCodeConfiguration (dataWordCode c) b) z from registerEncoding_map_single _ _ _ _]
  change Matrix.reindex (registerConfigurationSplit (allData N k))
      (registerConfigurationSplit (allData N k))
      (single (wordCodeConfiguration (dataWordCode c) a)
        (wordCodeConfiguration (dataWordCode c) b) z) =
    S (S.symm (tensorMapIdLM ((nativeMatrixEquiv N k d).toLinearMap ∘ₗ
      (OnsiteChannel.encodeRegisters (fun _ : Fin N => c)).map)
      (single a b z ⊗ₖ single (0 : DataReference N k d) 0 (1 : ℂ))))
  rw [S.apply_symm_apply, reindex_single_eq, data_word_split, data_word_split,
    tensorMapIdLM_apply, tensorMapId_kronecker, ← hbare]
  change single _ _ z =
    singleKrausMap (registerEncoding (wordCodeConfiguration (bareDataCode c))) (single a b z) ⊗ₖ
      single (0 : DataReference N k d) 0 (1 : ℂ)
  rw [registerEncoding_map_single, single_kronecker_single, mul_one]

/-- An arbitrary logical channel commutes with preparing its untouched zero reference. -/
theorem tensorMapId_comp_zeroDataReferencePrep
    (Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)) :
    tensorMapIdLM Ψ ∘ₗ (zeroDataReferencePrep (N := N) (k := k) (d := d)) =
      zeroDataReferencePrep ∘ₗ Ψ := by
  apply LinearMap.ext
  intro X
  exact tensorMapId_kronecker Ψ X _

end PortRegisters

end

end QuantumCircuit
