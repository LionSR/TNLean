/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalJointSuffixFactorization
import TNLean.Circuit.InitializedRegisterProjection

/-!
# Initialized basis coordinates under a site bijection

A site bijection transports both an initialized basis inclusion and its
selected zero-coordinate set. Equality of the initialized ranges is derived
from their concrete zero-coordinate predicates. No independent initialization
or cleanup identity is assumed.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSPreparation MPSTensor QuantumCircuit

namespace MPUCircuit

/-- Range membership under a site bijection is range membership of the inverse configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mem_range_pullbackBasisEmbedding_iff {d a n : ℕ} {α : Type*}
    (E : α ↪ Cfg d n) (e : Fin a ≃ Fin n) (x : Cfg d a) :
    x ∈ Set.range (pullbackBasisEmbedding E e) ↔ x ∘ e.symm ∈ Set.range E := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    funext i
    have hh := congrFun hp (e.symm i)
    simpa only [pullbackBasisEmbedding_apply, Function.comp_apply,
      Equiv.apply_symm_apply] using hh
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    funext i
    have hh := congrFun hp (e i)
    simpa only [pullbackBasisEmbedding_apply, Function.comp_apply,
      Equiv.symm_apply_apply] using hh

/-- Transport of the selected sites identifies the pulled-back initialized range.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem range_pullbackBasisEmbedding_eq_zeroFlagEmbedding
    {d a n b : ℕ} [NeZero d] {α : Type*}
    (E : α ↪ Cfg d n) (e : Fin a ≃ Fin n) (s : Fin b ↪ Fin a)
    (S : Set (Fin n))
    (hS : Set.range (s.trans e.toEmbedding) = S)
    (hE : ∀ x, x ∈ Set.range E ↔ ∀ i ∈ S, x i = 0) :
    Set.range (pullbackBasisEmbedding E e) = Set.range (zeroFlagEmbedding (d := d) s) := by
  ext x
  rw [mem_range_pullbackBasisEmbedding_iff, mem_range_zeroFlagEmbedding_iff, hE]
  constructor
  · intro hx j
    have hs : e (s j) ∈ S := by
      rw [← hS]
      exact ⟨j, rfl⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hx (e (s j)) hs
  · intro hx i hi
    rw [← hS] at hi
    obtain ⟨j, rfl⟩ := hi
    simpa only [Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply] using hx j

end MPUCircuit
