/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.RegisterChannelLift
import TNLean.Circuit.Channel.OnsiteRegisterEncoding

/-!
# Local channel intertwining under product onsite codes

An independent basis encoding at every site factors into the encoding of a selected
register and the encoding of its complement. If a channel intertwines with the code on
the selected register, its placement therefore intertwines with the global onsite code.
The statement is an equality on all chain operators, with no restriction to product
inputs or to inputs uncorrelated with the complementary sites.
-/

open Matrix
open scoped BigOperators Matrix Kronecker

namespace QuantumCircuit

noncomputable section

variable {s N m q : ℕ}

private theorem rectKronecker_split_apply (e : Fin s ↪ Fin N)
    (A : Fin N → Matrix (Fin q) (Fin m) ℂ) (x : Fin N → Fin q) (y : Fin N → Fin m) :
    rectKronecker A x y =
      rectKronecker (fun j => A (e j)) (x ∘ e) (y ∘ e) *
        rectKronecker (fun j : {j // j ∉ Set.range e} => A j.val)
          (fun j => x j.val) (fun j => y j.val) := by
  change (∏ i, A i (x i) (y i)) =
    (∏ j, A (e j) (x (e j)) (y (e j))) *
      ∏ j : {j // j ∉ Set.range e}, A j.val (x j.val) (y j.val)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ Set.range e)
    (fun i => A i (x i) (y i))]
  congr 1
  let : Fintype (Set.range e) := Subtype.fintype (fun i => i ∈ Set.range e)
  exact (e.toEquivRange.prod_comp (fun j => A j.val (x j.val) (y j.val))).symm

/-- A rectangular product operator factors across the selected/complementary split. -/
theorem reindex_rectKronecker_registerSplit (e : Fin s ↪ Fin N)
    (A : Fin N → Matrix (Fin q) (Fin m) ℂ) :
    Matrix.reindex (registerConfigurationSplit (d := q) e)
      (registerConfigurationSplit (d := m) e) (rectKronecker A) =
        rectKronecker (fun j => A (e j)) ⊗ₖ
          rectKronecker (fun j : {j // j ∉ Set.range e} => A j.val) := by
  ext x y
  obtain ⟨x, rfl⟩ := (registerConfigurationSplit (d := q) e).surjective x
  obtain ⟨y, rfl⟩ := (registerConfigurationSplit (d := m) e).surjective y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp only [kroneckerMap_apply, registerConfigurationSplit_apply]
  exact rectKronecker_split_apply e A x y

/-- Splitting the global encoder gives the tensor product of its selected and
complementary encoders. No communication is introduced by the choice of basis codes. -/
theorem registerMatrixSplit_encodeRegisters (e : Fin s ↪ Fin N)
    (c : Fin N → (Fin m ↪ Fin q))
    (X : Matrix (Fin N → Fin m) (Fin N → Fin m) ℂ) :
    registerMatrixSplit e ((OnsiteChannel.encodeRegisters c).map X) =
      singleKrausMap
        (rectKronecker (fun j => registerEncoding (c (e j))) ⊗ₖ
          rectKronecker (fun j : {j // j ∉ Set.range e} => registerEncoding (c j.val)))
        (registerMatrixSplit e X) := by
  rw [OnsiteChannel.encodeRegisters_map, singleKrausMap_apply]
  let Eout := registerConfigurationSplit (d := q) e
  let Ein := registerConfigurationSplit (d := m) e
  let V := rectKronecker fun i => registerEncoding (c i)
  change Matrix.reindexLinearEquiv ℂ ℂ Eout Eout (V * X * Vᴴ) = _
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ Eout Ein Eout,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ Eout Ein Ein]
  change Matrix.reindex Eout Ein V * registerMatrixSplit e X *
    (Matrix.reindex Eout Ein V)ᴴ = _
  rw [show Matrix.reindex Eout Ein V =
      rectKronecker (fun j => registerEncoding (c (e j))) ⊗ₖ
        rectKronecker (fun j : {j // j ∉ Set.range e} => registerEncoding (c j.val)) from
    reindex_rectKronecker_registerSplit e _]
  rfl

private theorem tensorMapId_singleKraus_intertwine
    {α β δ ε : Type*} [Fintype α] [Fintype β] [Fintype δ] [Fintype ε]
    (V : Matrix β α ℂ) (W : Matrix ε δ ℂ)
    (Φ : Module.End ℂ (Matrix α α ℂ)) (Ψ : Module.End ℂ (Matrix β β ℂ))
    (h : Ψ ∘ₗ singleKrausMap V = singleKrausMap V ∘ₗ Φ) :
    tensorMapIdLM Ψ ∘ₗ singleKrausMap (V ⊗ₖ W) =
      singleKrausMap (V ⊗ₖ W) ∘ₗ tensorMapIdLM Φ := by
  classical
  have hprod (A : Matrix α α ℂ) (B : Matrix δ δ ℂ) :
      singleKrausMap (V ⊗ₖ W) (A ⊗ₖ B) = singleKrausMap V A ⊗ₖ singleKrausMap W B := by
    simp only [singleKrausMap_apply, conjTranspose_kronecker, ← mul_kronecker_mul]
  apply Matrix.ext_linearMap
  intro ⟨a, u⟩ ⟨b, v⟩
  apply LinearMap.ext
  intro z
  change tensorMapIdLM Ψ (singleKrausMap (V ⊗ₖ W) (single (a, u) (b, v) z)) =
    singleKrausMap (V ⊗ₖ W) (tensorMapIdLM Φ (single (a, u) (b, v) z))
  have hsingle : single (a, u) (b, v) z = single a b z ⊗ₖ single u v (1 : ℂ) := by
    rw [single_kronecker_single, mul_one]
  rw [hsingle, hprod, tensorMapIdLM_apply, tensorMapId_kronecker,
    tensorMapIdLM_apply, tensorMapId_kronecker, hprod]
  exact congrArg (fun A => A ⊗ₖ singleKrausMap W (single u v (1 : ℂ)))
    (LinearMap.congr_fun h (single a b z))

/-- Local intertwining with a site's product register code lifts to the whole chain,
including arbitrary correlations among the selected and complementary sites. -/
theorem registerChannelLift_encodeRegisters (e : Fin s ↪ Fin N)
    (c : Fin N → (Fin m ↪ Fin q))
    (Φ : Module.End ℂ (Matrix (Fin s → Fin m) (Fin s → Fin m) ℂ))
    (Ψ : Module.End ℂ (Matrix (Fin s → Fin q) (Fin s → Fin q) ℂ))
    (h : Ψ ∘ₗ (OnsiteChannel.encodeRegisters (fun j => c (e j))).map =
      (OnsiteChannel.encodeRegisters (fun j => c (e j))).map ∘ₗ Φ) :
    registerChannelLift e Ψ ∘ₗ (OnsiteChannel.encodeRegisters c).map =
      (OnsiteChannel.encodeRegisters c).map ∘ₗ registerChannelLift e Φ := by
  have hlocal : Ψ ∘ₗ singleKrausMap (rectKronecker fun j => registerEncoding (c (e j))) =
      singleKrausMap (rectKronecker fun j => registerEncoding (c (e j))) ∘ₗ Φ := by
    simpa only [OnsiteChannel.encodeRegisters_map] using h
  have hglobal := tensorMapId_singleKraus_intertwine
    (rectKronecker fun j => registerEncoding (c (e j)))
    (rectKronecker fun j : {j // j ∉ Set.range e} => registerEncoding (c j.val)) Φ Ψ hlocal
  apply LinearMap.ext
  intro X
  apply (registerMatrixSplit (d := q) e).injective
  change registerMatrixSplit e (registerChannelLift e Ψ
      ((OnsiteChannel.encodeRegisters c).map X)) =
    registerMatrixSplit e ((OnsiteChannel.encodeRegisters c).map (registerChannelLift e Φ X))
  rw [registerMatrixSplit_channelLift, registerMatrixSplit_encodeRegisters,
    registerMatrixSplit_encodeRegisters, registerMatrixSplit_channelLift]
  exact LinearMap.congr_fun hglobal _

end

end QuantumCircuit
