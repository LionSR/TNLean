/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLTOpenPolynomialHamiltonian

/-!
# Singlet and triplet boundary sectors of the open AKLT chain

The physical total spin acts on the two virtual boundary indices by the
commutator representation of spin one half. Consequently the squared total
spin sends a boundary matrix \(X\) to \(2X-\operatorname{tr}(X)1\): scalar
matrices give the singlet and traceless matrices give the triplet.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex`,
lines 1171--1174, the fourfold open-boundary ground space with exactly one
spin-zero state. All chain-length statements use \(N\ge2\), the injectivity
length of the AKLT tensor.

**Scope restriction (chain length):** The spin-sector classification assumes
`2 ≤ N`; the four-dimensional edge-space statement does not cover one site.
See `docs/paper-gaps/rmp_example_parent_hamiltonian_scope.tex`.
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPSTensor

/-- The virtual spin-half generators in the bond basis of `akltTensor`.
They are the Pauli generators conjugated by the first Pauli matrix.
Source: arXiv:2011.12127, lines 1159 and 1171--1174. -/
def akltBoundarySpin : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(1 / 2 : ℂ) • !![0, 1; 1, 0], (1 / 2 : ℂ) • !![0, Complex.I; -Complex.I, 0],
    (1 / 2 : ℂ) • !![-1, 0; 0, 1]]

/-- Acting on one physical spin is the difference of the virtual actions on
its two legs. Source: arXiv:2011.12127, lines 1159 and 1171--1174. -/
theorem aklt_spinOne_commutator (α i : Fin 3) :
    (∑ a, spinOneOperator α i a • akltTensor a) =
      akltTensor i * akltBoundarySpin α - akltBoundarySpin α * akltTensor i := by
  have hsqrt2 : (↑(Real.sqrt 2) : ℂ) = 2 * Complex.invSqrtTwo := by
    apply mul_right_cancel₀ Complex.invSqrtTwo_ne_zero
    rw [Complex.sqrtTwo_mul_invSqrtTwo, mul_assoc, Complex.invSqrtTwo_mul_self]
    norm_num
  fin_cases α <;> fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [spinOneOperator, akltBoundarySpin, akltTensor, Fin.sum_univ_three, hsqrt2] <;>
    ring_nf <;> simp [Complex.invSqrtTwo_sq] <;> ring

private theorem sum_evalWord_update_of_commutator {d D : ℕ}
    (A : MPSTensor d D) (S : Matrix (Fin d) (Fin d) ℂ)
    (J : Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ i, (∑ a, S i a • A a) = A i * J - J * A i)
    (N : ℕ) (σ : Fin N → Fin d) :
    (∑ j : Fin N, ∑ a, S (σ j) a •
      Kraus.evalWord A (List.ofFn (Function.update σ j a))) =
      Kraus.evalWord A (List.ofFn σ) * J - J * Kraus.evalWord A (List.ofFn σ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hzero (a : Fin d) :
        List.ofFn (Function.update σ 0 a) = a :: List.ofFn (fun j => σ j.succ) := by
      rw [List.ofFn_succ]
      congr 1
    have hsucc (j : Fin N) (a : Fin d) :
        List.ofFn (Function.update σ j.succ a) =
          σ 0 :: List.ofFn (Function.update (fun k => σ k.succ) j a) := by
      rw [List.ofFn_succ]
      congr 1
      congr 1
      funext k
      simp [Function.update_apply]
    rw [Fin.sum_univ_succ]
    simp only [hzero, hsucc, Kraus.evalWord_cons]
    have hleft :
        (∑ a, S (σ 0) a • (A a * Kraus.evalWord A (List.ofFn (fun j => σ j.succ)))) =
          (A (σ 0) * J - J * A (σ 0)) *
            Kraus.evalWord A (List.ofFn (fun j => σ j.succ)) := by
      rw [← h]
      simp only [Matrix.sum_mul, Matrix.smul_mul]
    have hright :
        (∑ j : Fin N, ∑ a, S (σ j.succ) a •
          (A (σ 0) * Kraus.evalWord A
            (List.ofFn (Function.update (fun k => σ k.succ) j a)))) =
          A (σ 0) * (Kraus.evalWord A (List.ofFn (fun j => σ j.succ)) * J -
            J * Kraus.evalWord A (List.ofFn (fun j => σ j.succ))) := by
      rw [← ih]
      simp only [Matrix.mul_sum, Matrix.mul_smul]
    rw [hleft, hright, List.ofFn_succ, Kraus.evalWord_cons]
    noncomm_ring

/-- The sum of the physical spin operators acts only at the open virtual
boundaries. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_totalSpin_groundSpaceMap (N : ℕ) (α : Fin 3)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    totalSpin spinOneOperator α (groundSpaceMap akltTensor N X) =
      groundSpaceMap akltTensor N (akltBoundarySpin α * X - X * akltBoundarySpin α) := by
  funext σ
  simp only [totalSpin, LinearMap.sum_apply, Finset.sum_apply, siteOperator_apply,
    groundSpaceMap_apply]
  have h := congrArg (fun M => Matrix.trace (M * X))
    (sum_evalWord_update_of_commutator akltTensor (spinOneOperator α)
      (akltBoundarySpin α) (aklt_spinOne_commutator α) N σ)
  simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul] at h
  rw [h, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  · rw [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- The Casimir of the boundary commutator action is twice the projection onto
traceless matrices. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem akltBoundarySpin_casimir (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ α, (akltBoundarySpin α * (akltBoundarySpin α * X - X * akltBoundarySpin α) -
      (akltBoundarySpin α * X - X * akltBoundarySpin α) * akltBoundarySpin α)) =
      (2 : ℂ) • X - Matrix.trace X • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [akltBoundarySpin, Matrix.mul_apply, Matrix.trace, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

/-- On the open AKLT ground space the physical squared total spin acts by
\(X\mapsto 2X-\operatorname{tr}(X)1\) on the boundary matrix.
Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_totalSpinSq_groundSpaceMap (N : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    totalSpinSq spinOneOperator (groundSpaceMap akltTensor N X) =
      groundSpaceMap akltTensor N ((2 : ℂ) • X - Matrix.trace X • 1) := by
  simp only [totalSpinSq, LinearMap.sum_apply, LinearMap.comp_apply,
    aklt_totalSpin_groundSpaceMap]
  rw [← map_sum, akltBoundarySpin_casimir]

/-- A boundary vector is in the spin-zero sector exactly when its boundary
matrix is scalar. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_totalSpinSq_groundSpaceMap_eq_zero_iff {N : ℕ} (hN : 2 ≤ N)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    totalSpinSq spinOneOperator (groundSpaceMap akltTensor N X) = 0 ↔
      ∃ c : ℂ, X = c • 1 := by
  have hinj := groundSpaceMap_injective_of_isNBlkInjective
    (isNBlkInjective_of_le (by norm_num) aklt_isNBlkInjective_two hN)
  rw [aklt_totalSpinSq_groundSpaceMap]
  constructor
  · intro h
    have hX : (2 : ℂ) • X - Matrix.trace X • 1 = 0 :=
      hinj (by simpa using h)
    refine ⟨Matrix.trace X / 2, ?_⟩
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) hX
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hij ⊢
    linear_combination (1 / 2 : ℂ) * hij
  · rintro ⟨c, rfl⟩
    simp [Matrix.trace_smul, smul_smul, mul_comm]

/-- The spin-zero part of the open AKLT matrix-product space is the singlet
line with scalar boundary matrix. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_groundSpace_inf_ker_totalSpinSq {N : ℕ} (hN : 2 ≤ N) :
    groundSpace akltTensor N ⊓ LinearMap.ker (totalSpinSq spinOneOperator) =
      Submodule.span ℂ {groundSpaceMap akltTensor N 1} := by
  apply le_antisymm
  · rintro ψ ⟨⟨X, rfl⟩, hX⟩
    obtain ⟨c, rfl⟩ := (aklt_totalSpinSq_groundSpaceMap_eq_zero_iff hN X).mp hX
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro ψ hψ
    rcases Set.mem_singleton_iff.mp hψ with rfl
    exact ⟨⟨1, rfl⟩, (aklt_totalSpinSq_groundSpaceMap_eq_zero_iff hN 1).mpr
      ⟨1, by simp⟩⟩

/-- Exactly one independent open AKLT ground state has spin zero.
Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_finrank_groundSpace_inf_ker_totalSpinSq {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      (groundSpace akltTensor N ⊓ LinearMap.ker (totalSpinSq spinOneOperator) :
        Submodule ℂ (NSiteSpace 3 N)) = 1 := by
  rw [aklt_groundSpace_inf_ker_totalSpinSq hN]
  apply finrank_span_singleton
  have hinj := groundSpaceMap_injective_of_isNBlkInjective
    (isNBlkInjective_of_le (by norm_num) aklt_isNBlkInjective_two hN)
  exact fun h => one_ne_zero (hinj (by simpa using h))

/-- The spin-one edge states are precisely the traceless boundary matrices.
The physical squared-spin eigenvalue is \(1(1+1)=2\).
Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_groundSpace_inf_eigenspace_totalSpinSq_two {N : ℕ} (hN : 2 ≤ N) :
    groundSpace akltTensor N ⊓ Module.End.eigenspace (totalSpinSq spinOneOperator) 2 =
      (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).map
        (groundSpaceMap akltTensor N) := by
  have hinj := groundSpaceMap_injective_of_isNBlkInjective
    (isNBlkInjective_of_le (by norm_num) aklt_isNBlkInjective_two hN)
  ext ψ
  constructor
  · rintro ⟨⟨X, rfl⟩, hX⟩
    refine ⟨X, ?_, rfl⟩
    simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hX
    rw [aklt_totalSpinSq_groundSpaceMap, ← map_smul] at hX
    have h := sub_eq_self.mp (hinj hX)
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simpa using h00
  · rintro ⟨X, hX, rfl⟩
    refine ⟨⟨X, rfl⟩, ?_⟩
    have htr : Matrix.trace X = 0 := hX
    simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
    rw [aklt_totalSpinSq_groundSpaceMap, htr]
    simp

/-- The remaining three open-chain edge states form a spin-one triplet.
Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_finrank_groundSpace_inf_eigenspace_totalSpinSq_two {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      (groundSpace akltTensor N ⊓ Module.End.eigenspace (totalSpinSq spinOneOperator) 2 :
        Submodule ℂ (NSiteSpace 3 N)) = 3 := by
  rw [aklt_groundSpace_inf_eigenspace_totalSpinSq_two hN]
  have hinj := groundSpaceMap_injective_of_isNBlkInjective
    (isNBlkInjective_of_le (by norm_num) aklt_isNBlkInjective_two hN)
  rw [← (Submodule.equivMapOfInjective (groundSpaceMap akltTensor N) hinj
    (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ))).finrank_eq]
  have hsurj : Function.Surjective (Matrix.traceLinearMap (Fin 2) ℂ ℂ) := by
    intro c
    exact ⟨Matrix.single 0 0 c, by simp⟩
  have hdim := (Matrix.traceLinearMap (Fin 2) ℂ ℂ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hdim
  norm_num [Module.finrank_matrix] at hdim
  omega

/-- The actual open two-site AKLT parent Hamiltonian has a one-dimensional
spin-zero ground sector, using the standard coefficient realization of the
physical Hilbert space. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_finrank_openParent_ground_spinZero {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      ((LinearMap.ker (openParentHamiltonianES akltTensor 2 N)).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap ⊓
          LinearMap.ker (totalSpinSq spinOneOperator) : Submodule ℂ (NSiteSpace 3 N)) = 1 := by
  have hmap : (groundSpaceES akltTensor N).map
      (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap = groundSpace akltTensor N :=
    (Submodule.map_symm_eq_iff (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N))).mp rfl
  rw [aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN, hmap]
  exact aklt_finrank_groundSpace_inf_ker_totalSpinSq hN

/-- The three other ground states of the actual open AKLT parent Hamiltonian
have total spin one. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem aklt_finrank_openParent_ground_spinOne {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      ((LinearMap.ker (openParentHamiltonianES akltTensor 2 N)).map
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap ⊓
          Module.End.eigenspace (totalSpinSq spinOneOperator) 2 :
            Submodule ℂ (NSiteSpace 3 N)) = 3 := by
  have hmap : (groundSpaceES akltTensor N).map
      (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap = groundSpace akltTensor N :=
    (Submodule.map_symm_eq_iff (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N))).mp rfl
  rw [aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN, hmap]
  exact aklt_finrank_groundSpace_inf_eigenspace_totalSpinSq_two hN

/-- The physical open bilinear-biquadratic AKLT Hamiltonian has exactly one
spin-zero ground state. Source: arXiv:2011.12127, lines 1171--1174. -/
theorem akltOpenHamiltonianES_ground_spinZero_finrank {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      ((Module.End.eigenspace (akltOpenHamiltonianES N)
        (-(2 * (N - 1) / 3) : ℂ)).map
          (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap ⊓
            LinearMap.ker (totalSpinSq spinOneOperator) : Submodule ℂ (NSiteSpace 3 N)) = 1 := by
  rw [akltOpenHamiltonianES_eigenspace_eq_groundSpaceES hN,
    ← aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN]
  exact aklt_finrank_openParent_ground_spinZero hN

/-- The remaining physical open AKLT ground states form a spin-one triplet.
Source: arXiv:2011.12127, lines 1171--1174. -/
theorem akltOpenHamiltonianES_ground_spinOne_finrank {N : ℕ} (hN : 2 ≤ N) :
    Module.finrank ℂ
      ((Module.End.eigenspace (akltOpenHamiltonianES N)
        (-(2 * (N - 1) / 3) : ℂ)).map
          (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap ⊓
            Module.End.eigenspace (totalSpinSq spinOneOperator) 2 :
            Submodule ℂ (NSiteSpace 3 N)) = 3 := by
  rw [akltOpenHamiltonianES_eigenspace_eq_groundSpaceES hN,
    ← aklt_ker_openParentHamiltonianES_two_eq_groundSpaceES hN]
  exact aklt_finrank_openParent_ground_spinOne hN

end MPSTensor
