/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding
import QICLean.Channel.KrausCPTP
import QICLean.Channel.TensorMap
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fintype

/-!
# Placing a register channel independently of its Kraus representation

The configurations of a chain split into the selected register and its complementary
wires. Under this explicit equivalence, an embedded operator is its local matrix tensored
with the identity. Consequently, placing every Kraus operator of a local map gives
exactly that map tensored with the identity on the complement, after reindexing.

The identities hold on the whole operator space, including correlations between the
selected register and all complementary wires. In particular, placing a channel does
not depend on which Kraus representation is chosen.
-/

open Matrix
open scoped BigOperators Matrix Kronecker

namespace QuantumCircuit

noncomputable section

variable {d m W r : ℕ}

/-- Split a configuration into its selected register and the complementary wires. -/
def registerConfigurationSplit (e : Fin m ↪ Fin W) :
    (Fin W → Fin d) ≃ (Fin m → Fin d) × ({j // j ∉ Set.range e} → Fin d) :=
  (Equiv.piEquivPiSubtypeProd (fun j => j ∈ Set.range e) (fun _ => Fin d)).trans
    (Equiv.prodCongr (Equiv.arrowCongr e.toEquivRange.symm (Equiv.refl _)) (Equiv.refl _))

@[simp] theorem registerConfigurationSplit_apply (e : Fin m ↪ Fin W) (x : Fin W → Fin d) :
    registerConfigurationSplit e x = (x ∘ e, fun j => x j.val) := rfl

@[simp] theorem registerConfigurationSplit_symm_comp (e : Fin m ↪ Fin W)
    (a : Fin m → Fin d) (b : {j // j ∉ Set.range e} → Fin d) :
    (registerConfigurationSplit e).symm (a, b) ∘ e = a :=
  congrArg Prod.fst ((registerConfigurationSplit e).apply_symm_apply (a, b))

private theorem agreeOff_iff_split_snd (e : Fin m ↪ Fin W) (x y : Fin W → Fin d) :
    AgreeOff e x y ↔ (registerConfigurationSplit e x).2 =
      (registerConfigurationSplit e y).2 := by
  constructor
  · intro h
    funext j
    exact h j.val fun a ha => j.property ⟨a, ha⟩
  · intro h j hj
    exact congrFun h ⟨j, fun ⟨a, ha⟩ => hj a ha⟩

/-- Reindex a chain matrix by its selected register and complementary configurations. -/
def registerMatrixSplit (e : Fin m ↪ Fin W) :
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ ≃ₐ[ℂ]
      Matrix ((Fin m → Fin d) × ({j // j ∉ Set.range e} → Fin d))
        ((Fin m → Fin d) × ({j // j ∉ Set.range e} → Fin d)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (registerConfigurationSplit e)

@[simp] theorem registerMatrixSplit_conjTranspose (e : Fin m ↪ Fin W)
    (X : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    registerMatrixSplit e Xᴴ = (registerMatrixSplit e X)ᴴ := rfl

/-- After the configuration split, an embedded operator is the local operator tensored
with the identity on every complementary wire. -/
theorem registerMatrixSplit_embedOp (e : Fin m ↪ Fin W)
    (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    registerMatrixSplit e (embedOp e A) = A ⊗ₖ 1 := by
  ext ⟨a, b⟩ ⟨c, f⟩
  change embedOp e A ((registerConfigurationSplit e).symm (a, b))
    ((registerConfigurationSplit e).symm (c, f)) = A a c *
      (1 : Matrix ({j // j ∉ Set.range e} → Fin d) ({j // j ∉ Set.range e} → Fin d) ℂ) b f
  rw [embedOp_apply]
  simp only [agreeOff_iff_split_snd, Equiv.apply_symm_apply,
    registerConfigurationSplit_symm_comp, Matrix.one_apply]
  split_ifs <;> simp_all

/-- A chosen relabeling of the complementary configuration space does not change
operator placement. The complement equivalence cannot depend on selected coordinates. -/
theorem registerMatrixSplit_embedOp_reindex_complement {β : Type*}
    [Fintype β] [DecidableEq β] (e : Fin m ↪ Fin W)
    (c : ({j // j ∉ Set.range e} → Fin d) ≃ β)
    (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ
      ((registerConfigurationSplit e).trans (Equiv.prodCongr (Equiv.refl _) c))
      (embedOp e A) = A ⊗ₖ (1 : Matrix β β ℂ) := by
  change Matrix.reindex (Equiv.prodCongr (Equiv.refl _) c)
    (Equiv.prodCongr (Equiv.refl _) c) (registerMatrixSplit e (embedOp e A)) = _
  rw [registerMatrixSplit_embedOp, ← Matrix.kroneckerMap_reindex]
  simp

/-- A wire-sum decomposition identifies its second block with precisely the wires
outside the selected register. -/
def registerComplementOfSum {b : ℕ} (e : Fin m ↪ Fin W)
    (q : Fin m ⊕ Fin b ≃ Fin W) (hq : ∀ i, q (Sum.inl i) = e i) :
    Fin b ≃ {j // j ∉ Set.range e} := by
  let f : Fin b ↪ Fin W := Function.Embedding.inr.trans q.toEmbedding
  have hrange : Set.range f = (Set.range e)ᶜ := by
    have he : (e : Fin m → Fin W) = q ∘ Sum.inl := funext fun i => (hq i).symm
    change Set.range (q ∘ Sum.inr) = (Set.range e)ᶜ
    rw [he, Set.range_comp, Set.range_comp, ← q.image_compl, Set.compl_range_inl]
  exact f.toEquivRange.trans (Set.equivOfEq hrange)

@[simp] theorem registerComplementOfSum_apply_val {b : ℕ} (e : Fin m ↪ Fin W)
    (q : Fin m ⊕ Fin b ≃ Fin W) (hq : ∀ i, q (Sum.inl i) = e i) (j : Fin b) :
    (registerComplementOfSum e q hq j).val = q (Sum.inr j) := rfl

/-- Restrict a wire configuration to the two blocks of an explicit wire-sum equivalence. -/
def registerSumConfigurationSplit {b : ℕ} (q : Fin m ⊕ Fin b ≃ Fin W) :
    (Fin W → Fin d) ≃ (Fin m → Fin d) × (Fin b → Fin d) :=
  (Equiv.arrowCongr q.symm (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The whole wire-sum split, including its independent complementary coordinates,
agrees with the canonical register split followed by complement relabeling. -/
theorem registerSumConfigurationSplit_eq {b : ℕ} (e : Fin m ↪ Fin W)
    (q : Fin m ⊕ Fin b ≃ Fin W) (hq : ∀ i, q (Sum.inl i) = e i) :
    registerSumConfigurationSplit (d := d) q = (registerConfigurationSplit e).trans
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.arrowCongr (registerComplementOfSum e q hq).symm (Equiv.refl _))) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · funext i
    change x (q (Sum.inl i)) = x (e i)
    rw [hq]
  · rfl

/-- Placing an operator on the first wire block is tensoring by the identity on the
second block. This follows from canonical register placement, independently of coordinates. -/
theorem registerSumConfigurationSplit_embedOp {b : ℕ} (e : Fin m ↪ Fin W)
    (q : Fin m ⊕ Fin b ≃ Fin W) (hq : ∀ i, q (Sum.inl i) = e i)
    (A : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (registerSumConfigurationSplit q) (embedOp e A) =
      A ⊗ₖ (1 : Matrix (Fin b → Fin d) (Fin b → Fin d) ℂ) := by
  rw [registerSumConfigurationSplit_eq e q hq]
  exact registerMatrixSplit_embedOp_reindex_complement e _ A

/-- Place a local linear map while acting identically on the complementary wires. -/
def registerChannelLift (e : Fin m ↪ Fin W)
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) :
    Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :=
  (registerMatrixSplit e).symm.toLinearMap ∘ₗ tensorMapIdLM Φ ∘ₗ
    (registerMatrixSplit e).toLinearMap

/-- Splitting a placed map gives its tensor product with the complementary identity. -/
@[simp] theorem registerMatrixSplit_channelLift (e : Fin m ↪ Fin W)
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ))
    (X : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    registerMatrixSplit e (registerChannelLift e Φ X) =
      tensorMapIdLM Φ (registerMatrixSplit e X) :=
  (registerMatrixSplit e).apply_symm_apply _

/-- Placing the identity map leaves the entire chain unchanged. -/
@[simp] theorem registerChannelLift_id (e : Fin m ↪ Fin W) :
    registerChannelLift (d := d) e LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro X
  apply (registerMatrixSplit e).injective
  simp only [registerMatrixSplit_channelLift, tensorMapIdLM_id, LinearMap.id_apply]

/-- Placing local maps preserves their composition exactly. -/
theorem registerChannelLift_comp (e : Fin m ↪ Fin W)
    (Φ Ψ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) :
    registerChannelLift e (Ψ ∘ₗ Φ) =
      registerChannelLift e Ψ ∘ₗ registerChannelLift e Φ := by
  apply LinearMap.ext
  intro X
  apply (registerMatrixSplit e).injective
  simp only [LinearMap.comp_apply, registerMatrixSplit_channelLift, tensorMapIdLM_comp]

private theorem tensorMapIdLM_rectangularKrausMap {δ η : Type*}
    [Fintype δ] [DecidableEq δ] [Fintype η]
    (K : η → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    tensorMapIdLM (δ := δ) (rectangularKrausMap K) =
      rectangularKrausMap (fun j => K j ⊗ₖ (1 : Matrix δ δ ℂ)) := by
  apply Matrix.ext_linearMap
  intro ⟨a, u⟩ ⟨b, v⟩
  apply LinearMap.ext
  intro c
  change tensorMapIdLM (rectangularKrausMap K) (single (a, u) (b, v) c) =
    rectangularKrausMap (fun j => K j ⊗ₖ (1 : Matrix δ δ ℂ)) (single (a, u) (b, v) c)
  have hsingle : single (a, u) (b, v) c =
      single a b c ⊗ₖ single u v (1 : ℂ) := by
    rw [single_kronecker_single, mul_one]
  rw [hsingle, tensorMapIdLM_apply, tensorMapId_kronecker]
  change (∑ j, K j * single a b c * (K j)ᴴ) ⊗ₖ single u v (1 : ℂ) =
    ∑ j, (K j ⊗ₖ 1) * (single a b c ⊗ₖ single u v (1 : ℂ)) * (K j ⊗ₖ 1)ᴴ
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    one_mul, mul_one]
  ext ⟨a', u'⟩ ⟨b', v'⟩
  simp only [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

/-- The representation-independent channel lift is exactly the map obtained by placing
each local Kraus operator. This identity includes all correlations with the complement. -/
theorem registerChannelLift_kraus {η : Type*} [Fintype η] (e : Fin m ↪ Fin W)
    (K : η → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    registerChannelLift e (rectangularKrausMap K) =
      rectangularKrausMap (fun j => embedOp e (K j)) := by
  apply LinearMap.ext
  intro X
  let E := registerMatrixSplit (d := d) e
  apply E.injective
  change E (E.symm (tensorMapIdLM (rectangularKrausMap K) (E X))) =
    E (∑ j, embedOp e (K j) * X * (embedOp e (K j))ᴴ)
  rw [E.apply_symm_apply, tensorMapIdLM_rectangularKrausMap]
  change (∑ j, (K j ⊗ₖ 1) * E X * (K j ⊗ₖ 1)ᴴ) =
    E (∑ j, embedOp e (K j) * X * (embedOp e (K j))ᴴ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul, E, registerMatrixSplit_embedOp, registerMatrixSplit_conjTranspose]

/-- Equal local Kraus maps remain equal after placement, even for different Kraus counts. -/
theorem rectangularKrausMap_embedOp_congr {s : ℕ} (e : Fin m ↪ Fin W)
    (K : Fin r → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (L : Fin s → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (h : rectangularKrausMap K = rectangularKrausMap L) :
    rectangularKrausMap (fun j => embedOp e (K j)) =
      rectangularKrausMap (fun j => embedOp e (L j)) := by
  rw [← registerChannelLift_kraus, ← registerChannelLift_kraus, h]

end

end QuantumCircuit
