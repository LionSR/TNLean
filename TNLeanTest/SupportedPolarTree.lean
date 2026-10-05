/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SupportedTreePreparation
import TNLean.MPS.Preparation.UnequalTreePreparation

/-! Supported and normal trees share an algebraic physical compiler.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit

run_cmd do
  for name in (← Lean.getEnv).header.moduleNames do
    if name == `TNLean.MPS.CanonicalForm.NormalTensorGauge ||
        name == `TNLean.MPS.Preparation.ApproximationError ||
        name == `TNLean.MPS.Preparation.ApproximatingState ||
        name == `TNLean.MPS.Preparation.FixedPointPairs ||
        name == `TNLean.MPS.Preparation.DepthUpperBound ||
        name == `TNLean.MPS.Preparation.TreeMERA || (`Gametheory).isPrefixOf name then
      throwError "Unexpected convergence dependency: {name}"

-- A nonsquare virtual dimension and an odd parent length with unequal leaves.
example {d D : ℕ} (A : MPSTensor d D) (e : Fin 3 ↪ Fin (D * D))
    (hinj : ∀ m, 2 ≤ m →
      IsInjectiveOn (blockTensor A m) (Set.range (virtualPairEquiv D ∘ e))) :
    ∃ T : IsometryTree d 3 3 1 5, T.matrix = supportedCfgPolarIso A e 5 :=
  exists_isometryTree_matrix_eq_supportedCfgPolarIso A e (by decide) hinj
    1 5 3 (by decide) (by decide)

-- The same tree acts on a complex superposition, not a separately chosen sector.
example {d D χ s h n c : ℕ} (A : MPSTensor d D) (e : Fin χ ↪ Fin (D * D))
    (hs : 0 < s)
    (hinj : ∀ m, s ≤ m →
      IsInjectiveOn (blockTensor A m) (Set.range (virtualPairEquiv D ∘ e)))
    (hlo : 2 ^ h * s ≤ n) (hhi : n ≤ 2 ^ h * c) :
    ∃ T : IsometryTree d χ c h n, ∀ α : Fin χ → ℂ,
      T.matrix *ᵥ α = supportedCfgPolarIso A e n *ᵥ α := by
  obtain ⟨T, hT⟩ := exists_isometryTree_matrix_eq_supportedCfgPolarIso A e hs hinj h n c hlo hhi
  exact ⟨T, fun α => by rw [hT]⟩

-- No positive supported dimension is imposed on the algebraic theorem.
example {d D n : ℕ} (A : MPSTensor d D) (e : Fin 0 ↪ Fin (D * D))
    (hinj : IsInjectiveOn (blockTensor A n) (Set.range (virtualPairEquiv D ∘ e))) :
    (supportedCfgPolarIso A e n).IsIsometry :=
  isIsometry_supportedCfgPolarIso hinj

-- A singleton supported space uses the same genuine-isometry statement.
example {d D n : ℕ} (A : MPSTensor d D) (e : Fin 1 ↪ Fin (D * D))
    (hinj : IsInjectiveOn (blockTensor A n) (Set.range (virtualPairEquiv D ∘ e))) :
    (supportedCfgPolarIso A e n).IsIsometry :=
  isIsometry_supportedCfgPolarIso hinj

-- The previous normal preparation signature is preserved verbatim.
example (d s c : ℕ) [NeZero d] (hs : 2 ≤ s) :
    ∃ C : ℕ, ∀ {D : ℕ} (A : MPSTensor d D),
      (∀ m, s ≤ m → Kraus.IsInjective (blockTensor A m)) →
      ∀ (ω : Fin D × Fin D → ℂ), ∑ p, star (ω p) * ω p = 1 →
      ∀ (h : ℕ) {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
        (hN : ∑ b, ℓ b = N),
        (∀ b, 2 ^ (h + 2) * s ≤ ℓ b) → (∀ b, ℓ b ≤ 2 ^ (h + 1) * c) →
        IsPreparedWithMeasurementRoundsInDepth (C * (h + 1))
          fun x => blockIsometryState A ω hN x :=
  exists_isPreparedWithMeasurementRoundsInDepth_blockIsometryState d s c hs
