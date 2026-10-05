/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PortRouting
import TNLean.Circuit.Channel.PortMatching

/-!
# Channel execution after physical-port register routing

Move the qudits on which a channel acts into one spatial site, execute the channel
locally, and undo the routing. The resulting channel equals the original channel on
all operators. Every other register is restored even when entangled with the input.
Only the forward and backward physical-port circuits contribute to depth.

This is the channel-algebra part of the bounded-register simulation in
Piroli, Styliaris and Cirac's fixed-physical-qudit resource convention
(arXiv:2103.13367, Supplement pp. 7–8).
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d N W m r : ℕ} [NeZero N]

/-- Placing a normalized Kraus family on a register preserves its completeness relation. -/
theorem sum_conjTranspose_embedOp_mul (e : Fin m ↪ Fin W)
    (K : Fin r → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (hK : ∑ j, (K j)ᴴ * K j = 1) :
    ∑ j, (embedOp e (K j))ᴴ * embedOp e (K j) = 1 := by
  let E : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ :=
    { toFun := embedOp e
      map_add' := embedOp_add e
      map_smul' := fun c X => embedOp_smul e c X }
  simp_rw [embedOp_conjTranspose, embedOp_mul e.injective]
  change ∑ j, E ((K j)ᴴ * K j) = 1
  rw [← map_sum E, hK]
  exact embedOp_one e


end QuantumCircuit

/-!
## Sharing one register routing across parallel channels

Conjugation by an actual wire permutation preserves composition of channels. Therefore,
if one physical-port routing moves each member of a commuting channel family into a
single spatial site, all of them can be applied locally between the same forward and
backward routings. The total physical depth is twice the routing depth, not that quantity
multiplied by the number of channels.

This supplies the parallel-layer resource accounting for arXiv:2103.13367,
Supplement pp. 7–8, with a fixed physical-qudit dimension.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d W : ℕ}

/-- Wire permutations act as linear equivalences on the complete operator space. -/
def routingMatrixEquiv (σ : Equiv.Perm (Fin W)) :
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ ≃ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ :=
  Matrix.reindexLinearEquiv ℂ ℂ (Equiv.arrowCongr σ (Equiv.refl _))
    (Equiv.arrowCongr σ (Equiv.refl _))

/-- The matrix reindexing is exactly unitary conjugation by the wire permutation. -/
theorem routingMatrixEquiv_apply (σ : Equiv.Perm (Fin W))
    (X : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    routingMatrixEquiv σ X = permOp σ * X * (permOp σ)ᴴ := by
  rw [permOp_mul_mul_conjTranspose]
  rfl

/-- Inverting the reindexing reverses the actual routing unitary. -/
theorem routingMatrixEquiv_symm_apply (σ : Equiv.Perm (Fin W))
    (X : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :
    (routingMatrixEquiv σ).symm X = (permOp σ)ᴴ * X * permOp σ := by
  change routingMatrixEquiv σ.symm X = _
  rw [routingMatrixEquiv_apply, ← permOp_conjTranspose σ, conjTranspose_conjTranspose]

/-- Conjugation of channels by an actual wire permutation preserves their composition. -/
def routingChannelConj (σ : Equiv.Perm (Fin W)) :
    Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) →*
      Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) :=
  (routingMatrixEquiv σ).conjRingEquiv.toMonoidHom

/-- The channel conjugation has the expected forward-map-inverse formula. -/
theorem routingChannelConj_apply (σ : Equiv.Perm (Fin W))
    (Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)) :
    routingChannelConj σ Φ =
      singleKrausMap (permOp σ) ∘ₗ Φ ∘ₗ singleKrausMap (permOp σ)ᴴ := by
  apply LinearMap.ext
  intro X
  change routingMatrixEquiv σ (Φ ((routingMatrixEquiv σ).symm X)) = _
  simp only [routingMatrixEquiv_apply, routingMatrixEquiv_symm_apply,
    LinearMap.comp_apply, singleKrausMap_apply, conjTranspose_conjTranspose]

/-- Conjugating a channel placed on a register moves its register placement. -/
theorem routingChannelConj_embeddedKraus {m r : ℕ} (σ : Equiv.Perm (Fin W))
    (e : Fin m ↪ Fin W) (K : Fin r → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) :
    routingChannelConj σ (rectangularKrausMap fun j => embedOp e (K j)) =
      rectangularKrausMap (fun j => embedOp (σ ∘ e) (K j)) := by
  apply LinearMap.ext
  intro X
  let U := permOp (d := d) σ
  change routingMatrixEquiv σ
    ((rectangularKrausMap fun j => embedOp e (K j)) ((routingMatrixEquiv σ).symm X)) = _
  rw [routingMatrixEquiv_apply, routingMatrixEquiv_symm_apply]
  change U * (∑ j, embedOp e (K j) * (Uᴴ * X * U) * (embedOp e (K j))ᴴ) * Uᴴ =
    ∑ j, embedOp (σ ∘ e) (K j) * X * (embedOp (σ ∘ e) (K j))ᴴ
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hplace : embedOp (σ ∘ e) (K j) = U * embedOp e (K j) * Uᴴ := by
    rw [permOp_mul_mul_conjTranspose, embedOp_submatrix_perm]
  rw [hplace]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

variable {N : ℕ} [NeZero N]

/-- Undoing a shared routing implements any channel whose conjugate is free onsite. -/
theorem IsPhysicalPortProtocol.of_routed_map (P : PhysicalPortLayout N W)
    {T : ℕ} (σ : Equiv.Perm (Fin W))
    (hσ : IsPhysicalPortUnitary (d := d) P T (permOp σ))
    (Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ))
    (hΦ : IsPhysicalPortProtocol P 0 (routingChannelConj σ Φ)) :
    IsPhysicalPortProtocol P (2 * T) Φ := by
  have h := ((IsPhysicalPortProtocol.unitary hσ).comp hΦ).comp
    (IsPhysicalPortProtocol.unitary hσ.conjTranspose)
  let E := routingMatrixEquiv (d := d) σ
  have hC : singleKrausMap (permOp (d := d) σ) = E.toLinearMap := by
    apply LinearMap.ext
    intro X
    exact (routingMatrixEquiv_apply σ X).symm
  have hD : singleKrausMap (permOp (d := d) σ)ᴴ = E.symm.toLinearMap := by
    apply LinearMap.ext
    intro X
    simp only [singleKrausMap_apply, conjTranspose_conjTranspose]
    exact (routingMatrixEquiv_symm_apply σ X).symm
  have heq : singleKrausMap (permOp σ)ᴴ ∘ₗ
      (routingChannelConj σ Φ ∘ₗ singleKrausMap (permOp σ)) = Φ := by
    rw [hC, hD]
    apply LinearMap.ext
    intro X
    change E.symm (E (Φ (E.symm (E X)))) = Φ X
    rw [E.symm_apply_apply, E.symm_apply_apply]
  rw [heq] at h
  simpa only [Nat.add_zero, ← two_mul] using h

/-- If a certified physical-port routing brings an entire register to one spatial site,
any channel on that register can be executed with twice the routing depth. The equality
is on the complete operator space, not just product or pure input states. -/
theorem IsPhysicalPortProtocol.of_register_routing {m r : ℕ} (P : PhysicalPortLayout N W)
    (e : Fin m ↪ Fin W) (K : Fin r → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)
    (hK : ∑ j, (K j)ᴴ * K j = 1) {T : ℕ} (σ : Equiv.Perm (Fin W))
    (hσ : IsPhysicalPortUnitary (d := d) P T (permOp σ))
    (i : Fin N) (hsite : ∀ j, P.site (σ (e j)) = i) :
    IsPhysicalPortProtocol P (2 * T) (rectangularKrausMap fun j => embedOp e (K j)) := by
  apply IsPhysicalPortProtocol.of_routed_map P σ hσ
  rw [routingChannelConj_embeddedKraus]
  let f : Fin m ↪ Fin W := e.trans σ.toEmbedding
  change IsPhysicalPortProtocol P 0 (rectangularKrausMap fun j => embedOp f (K j))
  apply IsPhysicalPortProtocol.onsite (P := P) i
  · intro j
    apply supportedOperators_mono _ (embedOp_mem_supportedOperators f.injective (K j))
    rintro x ⟨a, rfl⟩
    exact hsite a
  · exact sum_conjTranspose_embedOp_mul f K hK

/-- A commuting family shares one forward and backward routing. In particular, the bound
is independent of the number of disjoint gates in a layer. -/
theorem IsPhysicalPortProtocol.of_routed_family {α : Type*} (P : PhysicalPortLayout N W)
    (s : Finset α)
    (F : α → Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ))
    (hcomm : (s : Set α).Pairwise (Function.onFun Commute F)) {T : ℕ}
    (σ : Equiv.Perm (Fin W)) (hσ : IsPhysicalPortUnitary (d := d) P T (permOp σ))
    (hF : ∀ j ∈ s, IsPhysicalPortProtocol P 0 (routingChannelConj σ (F j))) :
    IsPhysicalPortProtocol P (2 * T) (s.noncommProd F hcomm) := by
  apply of_routed_map P σ hσ
  apply Finset.noncommProd_induction s F hcomm
    (fun Φ => IsPhysicalPortProtocol P 0 (routingChannelConj σ Φ))
  · intro A B hA hB
    rw [map_mul]
    simpa only [Nat.zero_add, Module.End.mul_eq_comp] using hB.comp hA
  · rw [map_one]
    exact one P
  · exact hF

end QuantumCircuit
