/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Structure.BlockPermutation
import TNLean.MPS.Structure.LinearExtension
import TNLean.MPS.Core.MultiBlock
import TNLean.MPS.FundamentalTheorem.Multi

import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Product algebra equivalence construction

This file constructs the per-block linear extension from `SameMPV` and promotes it to a
product algebra automorphism, then applies the block-permutation decomposition theorem.

## Main results

* `perBlockLinearExtension` — per-block linear map `T_k : M_{D_k} → M_{D_k}` from SameMPV
* `piAlgEquiv` — the assembled product algebra automorphism
* `piAlgEquiv_decomposition` — decomposition as block permutation + inner automorphisms
* `piTrace_mul_right_eq_zero` — nondegeneracy of the Pi-trace pairing
* `piTraceMulRightPi` — per-block Gram map and its injectivity

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac (quant-ph/0608197)
* [Cirac2017MPS] De las Cuevas, Schuch, Pérez-García, Cirac (arXiv:2011.12127)
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

/-- Per-block T commutes with scalars. -/
theorem perBlockLinearExtension_commutes
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) (c : ℂ) :
    perBlockLinearExtension A B hA hSame k (algebraMap ℂ _ c) = algebraMap ℂ _ c := by
  simp only [Algebra.algebraMap_eq_smul_one, map_smul, perBlockLinearExtension_one A B hA hSame k]

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

/-- The product algebra map sends `A_k i` to `B_k i` in each block. -/
theorem piAlgEquiv_on_single
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) (i : Fin d) :
    piAlgEquiv A B hA hSame (Pi.single k (A k i)) k = B k i := by
  simp [Pi.single_eq_same, perBlockLinearExtension_spec]

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

/-! ### Nondegeneracy of the Pi-trace pairing -/
section PiTraceNondeg

variable {r : ℕ} {dim : Fin r → ℕ}

/-- Nondegeneracy of the Pi-trace pairing. -/
theorem piTrace_mul_right_eq_zero
    (M : ∀ k : Fin r, Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (h : ∀ N : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      ∑ k, Matrix.trace (M k * N k) = 0) :
    M = 0 := by
  classical
  funext k; apply trace_mul_right_eq_zero; intro N_k
  have := h (Function.update 0 k N_k)
  rwa [Finset.sum_eq_single k
    (fun j _ hj => by rw [Function.update_of_ne hj, Pi.zero_apply, mul_zero, Matrix.trace_zero])
    (fun hk => absurd (Finset.mem_univ k) hk), Function.update_self] at this

end PiTraceNondeg

/-! ### Per-block Gram map -/
section PiGramMap

variable {r : ℕ} {dim : Fin r → ℕ}

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

end MPSTensor
