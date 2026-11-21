/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Model.CleanWorkspace
import TNLean.MPS.MPU.EncodedUniformMergingCircuit
import Mathlib.Logic.Equiv.Set

/-!
# Coordinate identities for prescribed basis inclusions

Two injective basis encodings with the same range have a derived coordinate
bijection. Basis inclusions respect this bijection and products, and they
compose by `Matrix.basisInclusion_mul_basisInclusion`. The final identity
expresses the active joining columns inside the full compatible dilation
encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSPreparation MPSTensor QuantumCircuit
open scoped Kronecker

namespace MPUCircuit

/-- The coordinate bijection determined by equality of the two encoding ranges.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def basisEncodingEquivOfRangeEq {α β ι : Type*}
    (E : α ↪ ι) (F : β ↪ ι) (h : Set.range E = Set.range F) : α ≃ β :=
  ((Equiv.ofInjective E E.injective).trans (Set.equivOfEq h)).trans
    (Equiv.ofInjective F F.injective).symm

/-- The derived coordinate bijection preserves the encoded physical basis vector.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem basisEncodingEquivOfRangeEq_apply {α β ι : Type*}
    (E : α ↪ ι) (F : β ↪ ι) (h : Set.range E = Set.range F) (a : α) :
    F (basisEncodingEquivOfRangeEq E F h a) = E a := by
  exact Equiv.apply_ofInjective_symm F.injective _

/-- The derived coordinate bijection transports the initialized basis matrix.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem basisInclusion_equivOfRangeEq {α β ι : Type*}
    [DecidableEq ι] (E : α ↪ ι) (F : β ↪ ι) (h : Set.range E = Set.range F) :
    (basisInclusion E).submatrix id
      (basisEncodingEquivOfRangeEq E F h).symm = basisInclusion F := by
  ext i b
  have hh := basisEncodingEquivOfRangeEq_apply E F h
    ((basisEncodingEquivOfRangeEq E F h).symm b)
  rw [Equiv.apply_symm_apply] at hh
  simp only [basisInclusion, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
  rw [← hh]


/-- Products of basis inclusions give Kronecker products of their matrices.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem basisInclusion_prodMap {α β ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] (E : α ↪ ι) (F : β ↪ κ) :
    basisInclusion (E.prodMap F) =
      basisInclusion E ⊗ₖ basisInclusion F := by
  ext ⟨i, j⟩ ⟨a, b⟩
  simp only [basisInclusion, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
    Function.Embedding.prodMap, Matrix.kroneckerMap_apply]
  split_ifs <;> simp_all

/-- The active joining columns are included in the full compatible dilation encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem basisInclusion_append_joiningChild {d r q a : ℕ}
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (hd : 2 ≤ d)
    (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q) :
    basisInclusion (appendBasisEmbedding f
      ((joiningChildBasisEmbedding (r := r) hd).trans
        (compatibleBondDilationEmbedding hd e))) =
      basisInclusion (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          basisInclusion (joiningChildBasisEmbedding (r := r) hd)) := by
  let H := (Function.Embedding.refl ρ).prodMap (joiningChildBasisEmbedding (r := r) hd)
  have hH : basisInclusion H =
      (1 : Matrix ρ ρ ℂ) ⊗ₖ
        basisInclusion (joiningChildBasisEmbedding (r := r) hd) := by
    rw [basisInclusion_prodMap]
    simp only [basisInclusion, Function.Embedding.coe_refl, Matrix.submatrix_id_id]
  rw [← hH, basisInclusion_mul_basisInclusion]
  rfl

end MPUCircuit
