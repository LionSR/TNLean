/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.ConfigurationLayers
import TNLean.MPS.Preparation.DepthUpperBound

/-!
# The layers of the depth count act by configuration maps

The block layer and the layer on the pair windows of `TNLean.MPS.Preparation.DepthUpperBound`,
built from gates acting by configuration maps, act by the configuration map changing each block
(`MPSPreparation.blockLayerOp_mulVec_eq_comp`) or each pair window
(`MPSPreparation.pairLayerOp_mulVec_eq_comp`) by its gate. Both are cases of
`QuantumCircuit.noncommProd_embedOp_mulVec_eq_comp`.
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

variable {d : ℕ}

/-! ### The layers of the depth count -/

variable {M N r₁ : ℕ} {ℓ : Fin M → ℕ}

/-- The block layer `⊗ₖ U_k` of gates acting by configuration maps `f k` acts by the
configuration map changing each block by its gate. -/
theorem blockLayerOp_mulVec_eq_comp (hN : ∑ k, ℓ k = N)
    {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ} {f : ∀ k, Cfg d (ℓ k) → Cfg d (ℓ k)}
    (hU : ∀ k v, U k *ᵥ v = v ∘ f k) (v : Cfg d N → ℂ) :
    blockLayerOp hN U *ᵥ v = v ∘ layerCfg (blockSite hN) f :=
  noncommProd_embedOp_mulVec_eq_comp (blockSite_injective hN)
    (fun _ _ h => disjoint_range_blockSite hN h) f U hU _ v

/-- The layer of gates `W_k` on the pair windows, acting by configuration maps `f k`, acts by
the configuration map changing each window `k` by `f k`. -/
theorem pairLayerOp_mulVec_eq_comp (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    {W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    {f : Fin M → Cfg d (r₁ + r₁) → Cfg d (r₁ + r₁)}
    (hW : ∀ k v, W k *ᵥ v = v ∘ f k) (v : Cfg d N → ℂ) :
    pairLayerOp hN hr W *ᵥ v = v ∘ layerCfg (pairSite hN hr) f :=
  noncommProd_embedOp_mulVec_eq_comp (m := fun _ => r₁ + r₁) (pairSite_injective hN hr)
    (fun _ _ h => disjoint_range_pairSite hN hr h) f W hW _ v

end MPSPreparation
