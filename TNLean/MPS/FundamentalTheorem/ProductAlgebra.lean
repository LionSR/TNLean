/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.BlockPermutation
import TNLean.MPS.Structure.LinearExtension
import TNLean.MPS.Core.MultiBlock
import TNLean.MPS.FundamentalTheorem.Multi

import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Product algebra equivalence for block MPS tensors

This file constructs the per-block linear extension from `SameMPV` and promotes it to a
product algebra automorphism, then applies the block-permutation decomposition theorem.

## Main results

* `perBlockLinearExtension` — per-block linear map `T_k : M_{D_k} → M_{D_k}` from SameMPV
* `piAlgEquiv` — the assembled product algebra automorphism
* `piAlgEquiv_decomposition` — decomposition as block permutation + inner automorphisms
* `piTrace_mul_right_eq_zero` — nondegeneracy of the product trace pairing
* `piTraceMulRightPi` — per-block Gram map and its injectivity

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac (quant-ph/0608197)
* [CPSV21] Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix product states and projected entangled pair states*, arXiv:2011.12127.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Connecting SameMPV₂ to block-summed trace equalities -/
section SummedTraces

variable {r : ℕ} {dim : Fin r → ℕ}

/-- SameMPV₂ on block-diagonal tensors gives, for each system size N and configuration σ:
`∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)`. -/
theorem sameMPV₂_summed_blocks
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (N : ℕ) (σ : Fin N → Fin d) :
    ∑ k, (μ k) ^ N • mpv (A k) σ = ∑ k, (μ k) ^ N • mpv (B k) σ := by
  rw [← mpv_toTensorFromBlocks_eq_sum μ A σ, ← mpv_toTensorFromBlocks_eq_sum μ B σ]
  exact hSame N σ

end SummedTraces

/-! ### Per-block linear extension and product algebra automorphism -/
section PiAlgEquivConstruction

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- Construct the per-block linear map `T_k : M_{D_k} → M_{D_k}` from per-block SameMPV. -/
noncomputable def perBlockLinearExtension
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ]
    Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
  (linearExtension_exists_unique (hA k) (hSame k)).choose

omit [∀ k, NeZero (dim k)] in
theorem perBlockLinearExtension_spec
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    ∀ i, perBlockLinearExtension A B hA hSame k (A k i) = B k i :=
  (linearExtension_exists_unique (hA k) (hSame k)).choose_spec.1

omit [∀ k, NeZero (dim k)] in
/-- Per-block multiplicativity. -/
theorem perBlockLinearExtension_mul
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    ∀ M N, perBlockLinearExtension A B hA hSame k (M * N) =
      perBlockLinearExtension A B hA hSame k M *
        perBlockLinearExtension A B hA hSame k N :=
  linearExtension_mul (hA k) (hSame k) (perBlockLinearExtension_spec A B hA hSame k)

/-- Per-block T ≠ 0. Uses `trace_ne_zero_of_injective` from `TracePairing`. -/
private theorem perBlockLinearExtension_nonzero
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) : perBlockLinearExtension A B hA hSame k ≠ 0 := by
  intro h0
  exact MPSTensor.trace_ne_zero_of_injective (hA k) (hSame k)
    (fun i => by simpa [h0] using (perBlockLinearExtension_spec A B hA hSame k i).symm)

/-- Per-block bijectivity. -/
theorem perBlockLinearExtension_bijective
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    Function.Bijective (perBlockLinearExtension A B hA hSame k) :=
  linear_mul_endomorphism_bijective _ (perBlockLinearExtension_mul A B hA hSame k)
    (perBlockLinearExtension_nonzero A B hA hSame k)

/-- Per-block T maps 1 to 1. -/
theorem perBlockLinearExtension_one
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    perBlockLinearExtension A B hA hSame k 1 = 1 := by
  set T := perBlockLinearExtension A B hA hSame k
  have hMul := perBlockLinearExtension_mul A B hA hSame k
  obtain ⟨x, hx⟩ := (perBlockLinearExtension_bijective A B hA hSame k).2 1
  have h1 : T 1 = T x * T 1 := by rw [hx, one_mul]
  rw [h1, ← hMul, mul_one, hx]

/-- The assembled product algebra map: apply `T_k` on each block independently. -/
noncomputable def piLinearExtension
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₗ[ℂ]
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
  LinearMap.pi fun k =>
    (perBlockLinearExtension A B hA hSame k).comp (LinearMap.proj k)

omit [∀ k, NeZero (dim k)] in
@[simp] theorem piLinearExtension_apply
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (M : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (k : Fin r) :
    piLinearExtension A B hA hSame M k =
      perBlockLinearExtension A B hA hSame k (M k) := by
  simp [piLinearExtension]

/-- The product algebra map is bijective. -/
theorem piLinearExtension_bijective
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    Function.Bijective (piLinearExtension A B hA hSame) := by
  constructor
  · intro M₁ M₂ h; funext k
    exact (perBlockLinearExtension_bijective A B hA hSame k).1 (by simpa using congrFun h k)
  · intro M
    choose N hN using fun k => (perBlockLinearExtension_bijective A B hA hSame k).2 (M k)
    exact ⟨N, funext fun k => by simp [hN k]⟩

/-- Promote to an algebra homomorphism. -/
noncomputable def piAlgHom
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₐ[ℂ]
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) where
  toFun := piLinearExtension A B hA hSame
  map_one' := funext fun k => by simp [perBlockLinearExtension_one A B hA hSame k]
  map_mul' M N := funext fun k => by
    simp [perBlockLinearExtension_mul A B hA hSame k (M k) (N k)]
  map_zero' := by simp [piLinearExtension]
  map_add' := (piLinearExtension A B hA hSame).map_add
  commutes' c := funext fun k => by
    simp [Algebra.algebraMap_eq_smul_one, perBlockLinearExtension_one A B hA hSame k]

/-- Promote to an algebra equivalence. -/
noncomputable def piAlgEquiv
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) ≃ₐ[ℂ]
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
  AlgEquiv.ofBijective (piAlgHom A B hA hSame)
    (piLinearExtension_bijective A B hA hSame)

/-- The product algebra equivalence agrees with per-block T_k on each component. -/
@[simp]
theorem piAlgEquiv_apply
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (M : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (k : Fin r) :
    piAlgEquiv A B hA hSame M k =
      perBlockLinearExtension A B hA hSame k (M k) := by
  simp [piAlgEquiv, AlgEquiv.ofBijective, piAlgHom, piLinearExtension_apply]

end PiAlgEquivConstruction

/-! ### Decomposition via `algEquiv_pi_matrix_decomposition` -/
section Decomposition

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- The per-block linear extension, when assembled into a product algebra automorphism,
decomposes as a block permutation + per-block inner automorphisms. -/
theorem piAlgEquiv_decomposition
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (σ : Fin r ≃ Fin r) (hDeq : ∀ i, dim (σ i) = dim i)
      (X : ∀ i, GL (Fin (dim i)) ℂ),
    ∀ (i : Fin r) (M : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
        (componentMap (piAlgEquiv A B hA hSame).toRingEquiv σ i M) =
        (X i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * M *
          ((X i)⁻¹ : GL (Fin (dim i)) ℂ) :=
  algEquiv_pi_matrix_decomposition (piAlgEquiv A B hA hSame)

end Decomposition

/-! ### Product trace pairing and per-block Gram map -/
section PiGramMap

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The trace pairing on a finite product of full matrix algebras is nondegenerate. -/
theorem piTrace_mul_right_eq_zero
    (M : ∀ k : Fin r, Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (h : ∀ N : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      ∑ k, Matrix.trace (M k * N k) = 0) :
    M = 0 := by
  classical
  funext k
  apply (Matrix.ext_iff_trace_mul_right (A := M k) (B := 0)).2
  intro N_k
  have hsum := h (Function.update 0 k N_k)
  have htrace : Matrix.trace (M k * N_k) = 0 := by
    rwa [Finset.sum_eq_single k
      (fun j _ hj => by
        rw [Function.update_of_ne hj, Pi.zero_apply, mul_zero, Matrix.trace_zero])
      (fun hk => absurd (Finset.mem_univ k) hk), Function.update_self] at hsum
  simpa using htrace

/-- The per-block Gram map: `M ↦ (k, i) ↦ tr(M_k · A_k i)`. -/
noncomputable def piTraceMulRightPi
    (A : (k : Fin r) → MPSTensor d (dim k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₗ[ℂ]
    (Fin r → Fin d → ℂ) :=
  LinearMap.pi fun k =>
    (traceMulRightPi (A k)).comp (LinearMap.proj k)

@[simp]
lemma piTraceMulRightPi_apply
    (A : (k : Fin r) → MPSTensor d (dim k))
    (M : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (k : Fin r) (i : Fin d) :
    piTraceMulRightPi A M k i = Matrix.trace (M k * A k i) := by
  simp [piTraceMulRightPi, traceMulRightPi]

/-- The per-block Gram map is injective when each `A_k` is injective. -/
theorem piTraceMulRightPi_ker_eq_bot
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k)) :
    (piTraceMulRightPi A).ker = ⊥ := by
  classical
  rw [LinearMap.ker_eq_bot']
  intro M hM; funext k
  exact (LinearMap.ker_eq_bot'.mp (traceMulRightPi_ker_eq_bot (hA k))) (M k)
    (by ext i; simpa using congrFun (congrFun hM k) i)

end PiGramMap

/-! ### Per-block and direct-sum gauge equivalence -/
section FullMultiBlock

variable {r : ℕ} {dim : Fin r → ℕ}

/-- From `∀ k, 𝓥(A_k)=𝓥(B_k)` with each `A_k` injective, obtain both
`∀ k, GaugeEquiv (A k) (B k)` and
`GaugeEquiv (⊕_k μ_k A_k) (⊕_k μ_k B_k)`. -/
lemma fundamentalTheorem_multiBlock_full
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  ⟨fundamentalTheorem_multiBlock_blocks A B hA hSame,
    fundamentalTheorem_multiBlock_global μ A B hA hSame⟩

/-- Extract explicit matrices `X_k` such that `B_k^i = X_k A_k^i X_k⁻¹`. -/
lemma fundamentalTheorem_multiBlock_explicit
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  classical
  let hGauge := fundamentalTheorem_multiBlock_blocks A B hA hSame
  exact ⟨fun k => (hGauge k).choose, fun k => (hGauge k).choose_spec⟩

/-- Decompose the product-algebra automorphism attached to per-block `SameMPV` data. -/
lemma fundamentalTheorem_multiBlock_decomposition
    [∀ k, NeZero (dim k)]
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (σ : Fin r ≃ Fin r) (hDeq : ∀ i, dim (σ i) = dim i)
      (X : ∀ i, GL (Fin (dim i)) ℂ),
    ∀ (i : Fin r) (M : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
        (componentMap (piAlgEquiv A B hA hSame).toRingEquiv σ i M) =
        (X i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * M *
          ((X i)⁻¹ : GL (Fin (dim i)) ℂ) :=
  piAlgEquiv_decomposition A B hA hSame

end FullMultiBlock

/-! ### Single-block separation from `SameMPV₂`

When there is only **one** block (`r = 1`), the `SameMPV₂` condition on block-diagonal tensors
immediately yields per-block `SameMPV`, provided the scaling factor `μ₀` is nonzero.  This is
because the weighted sum `∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` degenerates to
`μ₀^N · mpv(A₀, σ) = μ₀^N · mpv(B₀, σ)`, and dividing by `μ₀^N ≠ 0` gives the result.

This lets us close the gap completely for single-block canonical forms, avoiding the need for
quantum Perron–Frobenius theory in this special case.
-/
section SingleBlockSeparation

variable {dim₀ : ℕ}

/-- For a single block, `SameMPV₂` on the block-diagonal tensor gives `SameMPV` on the block
    tensor, provided the scaling factor is nonzero. -/
lemma sameMPV₂_single_block
    (μ₀ : ℂ) (hμ : μ₀ ≠ 0)
    (A₀ B₀ : MPSTensor d dim₀)
    (hSame₂ : SameMPV₂
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => A₀))
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => B₀))) :
    SameMPV A₀ B₀ := by
  intro N σ
  have := sameMPV₂_summed_blocks (fun _ : Fin 1 => μ₀) (fun _ => A₀) (fun _ => B₀) hSame₂ N σ
  simp only [Fin.sum_univ_one] at this
  exact mul_left_cancel₀ (pow_ne_zero N hμ) this

/-- **Single-block Fundamental Theorem from `SameMPV₂`.**

For canonical forms with one block, `SameMPV₂` (with `μ₀ ≠ 0`) gives full gauge equivalence
without any separation hypothesis. -/
theorem fundamentalTheorem_singleBlock_fromMPV₂
    (μ₀ : ℂ) (hμ : μ₀ ≠ 0)
    (A₀ B₀ : MPSTensor d dim₀)
    (hA : IsInjective A₀)
    (hSame₂ : SameMPV₂
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => A₀))
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => B₀))) :
    GaugeEquiv A₀ B₀ :=
  fundamentalTheorem_singleBlock hA (sameMPV₂_single_block μ₀ hμ A₀ B₀ hSame₂)

end SingleBlockSeparation

/-! ### Equivalence: per-block SameMPV ↔ per-block GaugeEquiv (under injectivity) -/
section Equivalence

variable {r : ℕ} {dim : Fin r → ℕ}

/-- **Per-block SameMPV ↔ per-block GaugeEquiv**, under per-block injectivity.

This is the clean reformulation obtained by applying the single-block Fundamental Theorem to
each block:
the hypothesis that each block `A_k` generates the same MPV family as `B_k` is equivalent to
the conclusion that they are related by per-block gauge transforms. -/
lemma perBlock_sameMPV_iff_gaugeEquiv
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k)) :
    (∀ k, SameMPV (A k) (B k)) ↔ (∀ k, GaugeEquiv (A k) (B k)) :=
  ⟨fun hSame k => fundamentalTheorem_singleBlock (hA k) (hSame k),
   fun hGauge k => (hGauge k).sameMPV⟩

end Equivalence

end MPSTensor
