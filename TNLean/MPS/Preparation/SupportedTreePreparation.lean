/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.IsometryTreePreparation
import TNLean.MPS.Preparation.SupportedPolarTree

/-!
# Coherent measurement implementations of supported polar trees

The polar factors of a tensor injective on a common set of virtual pairs admit a physical
measurement implementation with depth proportional to the height of a bounded-leaf tree.
The coordinate inclusion of the support is fixed before the block lengths. One choice of
gates works for all support labels and all their superpositions, including different sectors.

The resource model counts nearest-neighbor unitary layers. Measurement outcomes and on-site
corrections are those of the register teleportation protocol; no branch is post-selected.

Source: arXiv:2307.01696, eq. (16), "Tree-RG circuit with measurements", and
"Long-range MPS using measurements".

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

/-- The physical register tree implements the polar factor on every supported input
simultaneously, including coherent superpositions of distinct canonical sectors. -/
theorem treeBlockOp_apply_supportedCfgPolarIso {d D χ s h n : ℕ} [NeZero d] [NeZero s]
    {w : ℕ → ℕ} (hT : IsTreeLayout h s n w) (A : MPSTensor d D)
    (e : Fin χ ↪ Fin (D * D))
    (hinj : ∀ m, s ≤ m →
      IsInjectiveOn (blockTensor A m) (Set.range (virtualPairEquiv D ∘ e)))
    {ι₀ : Fin χ → Cfg d (s + s)} {enc : Fin χ → Cfg d s}
    (hι₀ : Function.Injective ι₀) (henc : Function.Injective enc)
    (x : Fin χ) (τ : Cfg d n) :
    treeBlockOp hT (supportedCfgPolarIso A e) (supportedMergeIso A e) ι₀ enc τ
      (placeCfg (fun p : Fin (2 ^ 0) => nodeWindow hT 0 p) fun _ => ι₀ x) =
        cfgPolarIso A n τ (e x) := by
  exact treeBlockOp_apply hT (fun m hm => isIsometry_supportedCfgPolarIso (hinj m hm))
    (fun m₁ m₂ hm₁ hm₂ => isIsometry_supportedMergeIso (hinj m₁ hm₁) (hinj m₂ hm₂)
      (hinj _ (by omega)))
    (fun hm₁ hm₂ hn τ x => supportedCfgPolarIso_split (hinj _ hm₁) (hinj _ hm₂) hn τ x)
    hι₀ henc x τ

/-- Supported polar trees on all blocks are implemented by measurement rounds with one
constant fixed before the tensor, tree height, block lengths and supported input vector.
The branch scalar is independent of that vector, and the full physical output is specified.

Source: arXiv:2307.01696, the two paragraphs on tree preparation with measurements and
long-range MPS. This is the supported-tree step, not a canonicalization theorem. -/
theorem exists_rounds_blockLayerOp_supportedPolarTree (d s c : ℕ) [NeZero d] [NeZero s] :
    ∃ C : ℕ, ∀ {D χ : ℕ} (A : MPSTensor d D) (e : Fin χ ↪ Fin (D * D)),
      (∀ m, s ≤ m →
        IsInjectiveOn (blockTensor A m) (Set.range (virtualPairEquiv D ∘ e))) →
      ∀ (h : ℕ) {M N : ℕ} [NeZero N] (ℓ : Fin M → ℕ) (hN : ∑ b, ℓ b = N)
        (w : Fin M → ℕ → ℕ) (hT : ∀ b, IsTreeLayout h s (ℓ b) (w b)),
        (∀ b (p : Fin (2 ^ (h + 1))), leafLen h (ℓ b) (w b) p ≤ c) →
        ∀ (ι₀ : Fin M → Fin χ → Cfg d (s + s)) (enc : Fin χ → Cfg d s),
        (∀ b, Function.Injective (ι₀ b)) → Function.Injective enc →
        ∃ (U : ∀ b, Matrix (Cfg d (ℓ b)) (Cfg d (ℓ b)) ℂ)
          (Rs : List (MeasurementRound d N)),
          (Rs.map MeasurementRound.depth).sum ≤ C * (h + 1) ∧
          MeasurementRound.IsRoundsImplementationOn Rs
            {v | IsZeroOn (treeCentralSites h s hN w) v} (blockLayerOp hN U) ∧
          (∀ m : MeasurementRound.OutcomeHistory Rs, ∃ a : ℂ,
            ∀ v, IsZeroOn (treeCentralSites h s hN w) v →
              MeasurementRound.historyKraus Rs m *ᵥ v = a • ((blockLayerOp hN U) *ᵥ v)) ∧
          ∀ b x τ, U b τ
            (placeCfg (fun p : Fin (2 ^ 0) => nodeWindow (hT b) 0 p) fun _ => ι₀ b x) =
              cfgPolarIso A (ℓ b) τ (e x) := by
  obtain ⟨C, hC⟩ := exists_rounds_blockLayerOp_treeBlockOp d s c
  refine ⟨C, fun {D χ} A e hinj h {M N} _ ℓ hN w hT hbound ι₀ enc hι₀ henc => ?_⟩
  obtain ⟨Rs, hRs, himpl, hscalar⟩ := hC (supportedCfgPolarIso A e) (supportedMergeIso A e)
    h ℓ hN w hT hbound ι₀ enc
  exact ⟨fun b => treeBlockOp (hT b) (supportedCfgPolarIso A e)
      (supportedMergeIso A e) (ι₀ b) enc,
    Rs, hRs, himpl, hscalar, fun b x τ =>
      treeBlockOp_apply_supportedCfgPolarIso (hT b) A e hinj (hι₀ b) henc x τ⟩

end MPSPreparation
