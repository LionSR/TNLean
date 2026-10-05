/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.RegisterEnvironment
import TNLean.Circuit.Channel.PhysicalPortEmbedding
import QICLean.Channel.DeferredEnvironmentTrace

/-!
# Composing physical-port circuits with separate local environments

Two circuits using separate fresh environments embed into one layout containing both
sets of environment wires. Every original wire and communication port is fixed, and
every environment wire retains its spatial owner. The two lifted circuits therefore
compose at the sum of their original intersite depths.
-/

open Matrix
open scoped Kronecker

namespace QuantumCircuit

noncomputable section

variable {d N W A B : ℕ}

/-- An injection between local environments extends by the identity on original wires.
The owner equation ensures that this extension does not transport any wire between sites. -/
def PhysicalPortEmbedding.appendEnvironment (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N) (e : Fin A ↪ Fin B)
    (he : ∀ a, ownerB (e a) = ownerA a) :
    PhysicalPortEmbedding (P.append ownerA) (P.append ownerB) where
  wires := ⟨Fin.append (Fin.castAdd B) (fun a => Fin.natAdd W (e a)), by
    rw [Fin.append_injective_iff]
    refine ⟨(Fin.castAddEmb B).injective,
      (Fin.natAddEmb W).injective.comp e.injective, ?_⟩
    intro i a h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega⟩
  site_wires := by
    intro j
    induction j using Fin.addCases with
    | left j => simp [PhysicalPortLayout.append]
    | right a => simpa [PhysicalPortLayout.append] using he a
  wires_port i := by
    change Fin.append (Fin.castAdd B) (fun a => Fin.natAdd W (e a))
      (Fin.castAdd A (P.port i)) = Fin.castAdd B (P.port i)
    simp

@[simp] theorem PhysicalPortEmbedding.appendEnvironment_wires_old
    (P : PhysicalPortLayout N W) (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N)
    (e : Fin A ↪ Fin B) (he : ∀ a, ownerB (e a) = ownerA a) (i : Fin W) :
    (appendEnvironment P ownerA ownerB e he).wires (Fin.castAdd A i) =
      Fin.castAdd B i := by
  change Fin.append (Fin.castAdd B) (fun a => Fin.natAdd W (e a))
    (Fin.castAdd A i) = _
  exact Fin.append_left _ _ i

@[simp] theorem PhysicalPortEmbedding.appendEnvironment_wires_new
    (P : PhysicalPortLayout N W) (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N)
    (e : Fin A ↪ Fin B) (he : ∀ a, ownerB (e a) = ownerA a) (i : Fin A) :
    (appendEnvironment P ownerA ownerB e he).wires (Fin.natAdd W i) =
      Fin.natAdd W (e i) := by
  change Fin.append (Fin.castAdd B) (fun a => Fin.natAdd W (e a))
    (Fin.natAdd W i) = _
  exact Fin.append_right _ _ i

/-- Include the first environment in a common layout containing both environments. -/
def PhysicalPortLayout.appendLeftEmbedding (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N) :
    PhysicalPortEmbedding (P.append ownerA) (P.append (Fin.append ownerA ownerB)) :=
  PhysicalPortEmbedding.appendEnvironment P ownerA (Fin.append ownerA ownerB)
    (Fin.castAddEmb B) (by intro a; simp)

/-- Include the second environment in the same common layout, skipping the first. -/
def PhysicalPortLayout.appendRightEmbedding (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N) :
    PhysicalPortEmbedding (P.append ownerB) (P.append (Fin.append ownerA ownerB)) :=
  PhysicalPortEmbedding.appendEnvironment P ownerB (Fin.append ownerA ownerB)
    (Fin.natAddEmb A) (by intro b; simp)

/-- Both environments may be retained while running the first circuit and then the
second. The embeddings preserve the original ports, so the intersite depths add. -/
theorem IsPhysicalPortUnitary.appendEnvironment_comp [NeZero N] (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N) {T S : ℕ}
    {U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ}
    {V : Matrix (Fin (W + B) → Fin d) (Fin (W + B) → Fin d) ℂ}
    (hU : IsPhysicalPortUnitary (P.append ownerA) T U)
    (hV : IsPhysicalPortUnitary (P.append ownerB) S V) :
    IsPhysicalPortUnitary (P.append (Fin.append ownerA ownerB)) (T + S)
      (embedOp (P.appendRightEmbedding ownerA ownerB).wires V *
        embedOp (P.appendLeftEmbedding ownerA ownerB).wires U) := by
  simpa only [Nat.add_comm] using
    ((P.appendRightEmbedding ownerA ownerB).unitary hV).mul
      ((P.appendLeftEmbedding ownerA ownerB).unitary hU)

/-- Group the original system and first environment together, with the second environment
last. This is only a coordinate equivalence; physical realizability comes from the
port-preserving embeddings above. -/
def appendEnvironmentConfigurationSplit (W A B d : ℕ) :
    (Fin (W + (A + B)) → Fin d) ≃
      ((Fin W → Fin d) × (Fin A → Fin d)) × (Fin B → Fin d) :=
  ((appendConfigurationSplit W (A + B) d).trans
    (Equiv.prodCongr (Equiv.refl _) (appendConfigurationSplit A B d))).trans
      (Equiv.prodAssoc _ _ _).symm

@[simp] theorem appendEnvironmentConfigurationSplit_symm_apply
    (x : Fin W → Fin d) (a : Fin A → Fin d) (b : Fin B → Fin d) :
    (appendEnvironmentConfigurationSplit W A B d).symm ((x, a), b) =
      Fin.append x (Fin.append a b) := rfl

/-- Tracing the two appended environments separately gives exactly the discard of their
combined wire block, with the original system still in its original order. -/
theorem discardAppendedEnvironment_eq_iterated
    (X : Matrix (Fin (W + (A + B)) → Fin d) (Fin (W + (A + B)) → Fin d) ℂ) :
    discardAppendedEnvironment W (A + B) d X =
      partialTraceRight (partialTraceRight
        (Matrix.reindex (appendEnvironmentConfigurationSplit W A B d)
          (appendEnvironmentConfigurationSplit W A B d) X)) := by
  rw [partialTraceRight_partialTraceRight]
  exact partialTraceRight_submatrix_right (appendConfigurationSplit A B d).symm
    (appendMatrixSplit W (A + B) d X)

/-- Under the three-block configuration split, appending all-zero memory gives exactly
the product of the system operator and the two independent zero-environment states. -/
theorem reindex_appendEnvironmentInput [NeZero d]
    (X : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    Matrix.reindex (appendEnvironmentConfigurationSplit W A B d)
      (appendEnvironmentConfigurationSplit W A B d)
      (appendEnvironmentInput W (A + B) d X) =
        (X ⊗ₖ Matrix.single (0 : Fin A → Fin d) 0 (1 : ℂ)) ⊗ₖ
          Matrix.single (0 : Fin B → Fin d) 0 (1 : ℂ) := by
  classical
  have hzero : (Matrix.single (0 : Fin (A + B) → Fin d) 0 (1 : ℂ)).submatrix
      (appendConfigurationSplit A B d).symm (appendConfigurationSplit A B d).symm =
        Matrix.single (0 : Fin A → Fin d) 0 (1 : ℂ) ⊗ₖ
          Matrix.single (0 : Fin B → Fin d) 0 (1 : ℂ) := by
    rw [Matrix.submatrix_single_equiv, Matrix.single_kronecker_single, mul_one]
    rfl
  simp only [appendEnvironmentInput, LinearMap.comp_apply,
    freshEnvironmentInput_eq_kronecker]
  ext ⟨⟨x, a⟩, b⟩ ⟨⟨y, c⟩, f⟩
  change (X ⊗ₖ Matrix.single (0 : Fin (A + B) → Fin d) 0 (1 : ℂ))
    (appendConfigurationSplit W (A + B) d (Fin.append x (Fin.append a b)))
    (appendConfigurationSplit W (A + B) d (Fin.append y (Fin.append c f))) = _
  rw [appendConfigurationSplit_append, appendConfigurationSplit_append]
  change X x y * Matrix.single (0 : Fin (A + B) → Fin d) 0 (1 : ℂ)
      (Fin.append a b) (Fin.append c f) =
    (X x y * Matrix.single (0 : Fin A → Fin d) 0 (1 : ℂ) a c) *
      Matrix.single (0 : Fin B → Fin d) 0 (1 : ℂ) b f
  have hz := congrFun (congrFun hzero (a, b)) (c, f)
  change Matrix.single (0 : Fin (A + B) → Fin d) 0 (1 : ℂ)
    (Fin.append a b) (Fin.append c f) = _ at hz
  simp only [hz, Matrix.kroneckerMap_apply, mul_assoc]

private def appendLeftWireSum (W A B : ℕ) :
    Fin (W + A) ⊕ Fin B ≃ Fin (W + (A + B)) :=
  (((Equiv.sumCongr (finSumFinEquiv : Fin W ⊕ Fin A ≃ Fin (W + A)).symm
    (Equiv.refl (Fin B))).trans (Equiv.sumAssoc (Fin W) (Fin A) (Fin B))).trans
      (Equiv.sumCongr (Equiv.refl (Fin W)) finSumFinEquiv)).trans finSumFinEquiv

private def appendRightWireSum (W A B : ℕ) :
    Fin (W + B) ⊕ Fin A ≃ Fin (W + (A + B)) :=
  (((Equiv.sumCongr (finSumFinEquiv : Fin W ⊕ Fin B ≃ Fin (W + B)).symm
    (Equiv.refl (Fin A))).trans (Equiv.sumAssoc (Fin W) (Fin B) (Fin A))).trans
      (Equiv.sumCongr (Equiv.refl (Fin W))
        ((Equiv.sumComm (Fin B) (Fin A)).trans finSumFinEquiv))).trans finSumFinEquiv

private theorem appendLeftWireSum_inl (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N) (i : Fin (W + A)) :
    appendLeftWireSum W A B (Sum.inl i) = (P.appendLeftEmbedding ownerA ownerB).wires i := by
  induction i using Fin.addCases <;>
    simp [appendLeftWireSum, PhysicalPortLayout.appendLeftEmbedding]

private theorem appendRightWireSum_inl (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N) (i : Fin (W + B)) :
    appendRightWireSum W A B (Sum.inl i) = (P.appendRightEmbedding ownerA ownerB).wires i := by
  induction i using Fin.addCases <;>
    simp [appendRightWireSum, PhysicalPortLayout.appendRightEmbedding]

private theorem appendEnvironmentConfigurationSplit_left :
    appendEnvironmentConfigurationSplit W A B d =
      (registerSumConfigurationSplit (appendLeftWireSum W A B)).trans
        (Equiv.prodCongr (appendConfigurationSplit W A d) (Equiv.refl _)) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · apply Prod.ext <;> funext i <;>
      simp [appendEnvironmentConfigurationSplit, appendConfigurationSplit,
        registerSumConfigurationSplit, appendLeftWireSum]
  · funext i
    simp [appendEnvironmentConfigurationSplit, appendConfigurationSplit,
      registerSumConfigurationSplit, appendLeftWireSum]

private theorem appendEnvironmentConfigurationSplit_right :
    appendEnvironmentConfigurationSplit W A B d =
      (registerSumConfigurationSplit (appendRightWireSum W A B)).trans
        ((Equiv.prodCongr (appendConfigurationSplit W B d) (Equiv.refl _)).trans
          (Matrix.DeferredEnvironment.freshEnvironmentEquiv
            (Fin W → Fin d) (Fin A → Fin d) (Fin B → Fin d)).symm) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · apply Prod.ext <;> funext i <;>
      simp [appendEnvironmentConfigurationSplit, appendConfigurationSplit,
        registerSumConfigurationSplit, appendRightWireSum,
        Matrix.DeferredEnvironment.freshEnvironmentEquiv, Matrix.rightSplitEquiv]
  · funext i
    simp [appendEnvironmentConfigurationSplit, appendConfigurationSplit,
      registerSumConfigurationSplit, appendRightWireSum,
      Matrix.DeferredEnvironment.freshEnvironmentEquiv, Matrix.rightSplitEquiv]

/-- In system/first/second-environment coordinates, the first lifted circuit acts as
the identity on the entire second environment. -/
theorem reindex_appendLeft_embedOp (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N)
    (U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ) :
    Matrix.reindex (appendEnvironmentConfigurationSplit W A B d)
      (appendEnvironmentConfigurationSplit W A B d)
      (embedOp (P.appendLeftEmbedding ownerA ownerB).wires U) =
        appendMatrixSplit W A d U ⊗ₖ (1 : Matrix (Fin B → Fin d) (Fin B → Fin d) ℂ) := by
  rw [appendEnvironmentConfigurationSplit_left]
  change Matrix.reindex (Equiv.prodCongr (appendConfigurationSplit W A d) (Equiv.refl _))
    (Equiv.prodCongr (appendConfigurationSplit W A d) (Equiv.refl _))
    (Matrix.reindexAlgEquiv ℂ ℂ (registerSumConfigurationSplit (appendLeftWireSum W A B))
      (embedOp (P.appendLeftEmbedding ownerA ownerB).wires U)) = _
  rw [registerSumConfigurationSplit_embedOp _ _ (appendLeftWireSum_inl P ownerA ownerB),
    ← Matrix.kroneckerMap_reindex]
  simp [appendMatrixSplit]

/-- The second lifted circuit acts on the original system and fresh environment,
leaving the earlier environment, and all its correlations, untouched. -/
theorem reindex_appendRight_embedOp (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N)
    (V : Matrix (Fin (W + B) → Fin d) (Fin (W + B) → Fin d) ℂ) :
    Matrix.reindex (appendEnvironmentConfigurationSplit W A B d)
      (appendEnvironmentConfigurationSplit W A B d)
      (embedOp (P.appendRightEmbedding ownerA ownerB).wires V) =
        Matrix.DeferredEnvironment.freshEnvironmentOp (Fin A → Fin d)
          (appendMatrixSplit W B d V) := by
  rw [appendEnvironmentConfigurationSplit_right]
  change Matrix.reindex
    (Matrix.DeferredEnvironment.freshEnvironmentEquiv
      (Fin W → Fin d) (Fin A → Fin d) (Fin B → Fin d)).symm
    (Matrix.DeferredEnvironment.freshEnvironmentEquiv
      (Fin W → Fin d) (Fin A → Fin d) (Fin B → Fin d)).symm
    (Matrix.reindex (Equiv.prodCongr (appendConfigurationSplit W B d) (Equiv.refl _))
      (Equiv.prodCongr (appendConfigurationSplit W B d) (Equiv.refl _))
      (Matrix.reindexAlgEquiv ℂ ℂ (registerSumConfigurationSplit (appendRightWireSum W A B))
        (embedOp (P.appendRightEmbedding ownerA ownerB).wires V))) = _
  rw [registerSumConfigurationSplit_embedOp _ _ (appendRightWireSum_inl P ownerA ownerB),
    ← Matrix.kroneckerMap_reindex]
  simp [appendMatrixSplit, Matrix.DeferredEnvironment.freshEnvironmentOp]

/-- The actual port-preserving lifted product realizes composition with both environment
traces deferred. The system operator and both initial environment operators are arbitrary. -/
theorem appendEnvironment_comp_trace (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N)
    (U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ)
    (V : Matrix (Fin (W + B) → Fin d) (Fin (W + B) → Fin d) ℂ)
    (X : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
    (σ : Matrix (Fin A → Fin d) (Fin A → Fin d) ℂ)
    (τ : Matrix (Fin B → Fin d) (Fin B → Fin d) ℂ) :
    let R := Matrix.reindexAlgEquiv ℂ ℂ (appendEnvironmentConfigurationSplit W A B d)
    let C := embedOp (P.appendRightEmbedding ownerA ownerB).wires V *
      embedOp (P.appendLeftEmbedding ownerA ownerB).wires U
    partialTraceRight (partialTraceRight (R (C * R.symm ((X ⊗ₖ σ) ⊗ₖ τ) * Cᴴ))) =
      partialTraceRight (appendMatrixSplit W B d V *
        (partialTraceRight (appendMatrixSplit W A d U * (X ⊗ₖ σ) *
          (appendMatrixSplit W A d U)ᴴ) ⊗ₖ τ) * (appendMatrixSplit W B d V)ᴴ) := by
  classical
  dsimp only
  let R := Matrix.reindexAlgEquiv ℂ ℂ (appendEnvironmentConfigurationSplit W A B d)
  have hstar (M : Matrix (Fin (W + (A + B)) → Fin d)
      (Fin (W + (A + B)) → Fin d) ℂ) : R Mᴴ = (R M)ᴴ := rfl
  have hleft : R (embedOp (P.appendLeftEmbedding ownerA ownerB).wires U) =
      appendMatrixSplit W A d U ⊗ₖ (1 : Matrix (Fin B → Fin d) (Fin B → Fin d) ℂ) :=
    reindex_appendLeft_embedOp P ownerA ownerB U
  have hright : R (embedOp (P.appendRightEmbedding ownerA ownerB).wires V) =
      Matrix.DeferredEnvironment.freshEnvironmentOp (Fin A → Fin d) (appendMatrixSplit W B d V) :=
    reindex_appendRight_embedOp P ownerA ownerB V
  change partialTraceRight (partialTraceRight (R (_ * R.symm ((X ⊗ₖ σ) ⊗ₖ τ) * _ᴴ))) = _
  simp only [map_mul, hstar, R.apply_symm_apply, hleft, hright]
  exact Matrix.DeferredEnvironment.deferredEnvironment_comp
    (appendMatrixSplit W A d U) (appendMatrixSplit W B d V) X σ τ

/-- The reduced channel of the actual lifted product is the composition of the two
reduced channels. Both environments are prepared at the start and discarded only at
the end; the equality holds on the entire operator space. -/
theorem appendEnvironment_comp_channel [NeZero d] (P : PhysicalPortLayout N W)
    (ownerA : Fin A → Fin N) (ownerB : Fin B → Fin N)
    (U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ)
    (V : Matrix (Fin (W + B) → Fin d) (Fin (W + B) → Fin d) ℂ) :
    discardAppendedEnvironment W (A + B) d ∘ₗ
      singleKrausMap (embedOp (P.appendRightEmbedding ownerA ownerB).wires V *
        embedOp (P.appendLeftEmbedding ownerA ownerB).wires U) ∘ₗ
      appendEnvironmentInput W (A + B) d =
      (discardAppendedEnvironment W B d ∘ₗ singleKrausMap V ∘ₗ
        appendEnvironmentInput W B d) ∘ₗ
      (discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
        appendEnvironmentInput W A d) := by
  classical
  apply LinearMap.ext
  intro X
  let R := Matrix.reindexAlgEquiv ℂ ℂ (appendEnvironmentConfigurationSplit W A B d)
  have hinit : R.symm ((X ⊗ₖ Matrix.single (0 : Fin A → Fin d) 0 (1 : ℂ)) ⊗ₖ
      Matrix.single (0 : Fin B → Fin d) 0 (1 : ℂ)) =
        appendEnvironmentInput W (A + B) d X := by
    apply R.injective
    rw [R.apply_symm_apply]
    exact (reindex_appendEnvironmentInput X).symm
  simp only [LinearMap.comp_apply, singleKrausMap_apply]
  rw [discardAppendedEnvironment_eq_iterated, discardAppendedEnvironment_conj,
    discardAppendedEnvironment_conj]
  simp only [freshEnvironmentInput_eq_kronecker]
  rw [← hinit]
  exact appendEnvironment_comp_trace P ownerA ownerB U V X
    (Matrix.single (0 : Fin A → Fin d) 0 (1 : ℂ))
    (Matrix.single (0 : Fin B → Fin d) 0 (1 : ℂ))

end

end QuantumCircuit
