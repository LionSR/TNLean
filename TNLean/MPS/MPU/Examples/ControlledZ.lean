/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleRankOne
import TNLean.MPS.MPU.SourceCuts
import TNLean.MPS.MPDO.OperatorCyclicSum
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# The next-nearest-neighbour controlled-Z tensor

This file formalizes Example 4.9 of the matrix-product-unitary chapter of the lecture notes
(`docs/lecture-notes/mpu/MPU.tex`): the tensor with physical dimension `2`, bond index
`α = (α₁, α₂) ∈ {0,1}²` and letters
\[
  U^{ij}_{(\alpha_1\alpha_2),(\beta_1\beta_2)}
    = \delta_{ij}\,\delta_{\alpha_2\beta_1}\,\delta_{\beta_2 i}\,(-1)^{\alpha_1 i}.
\]
The example is not in arXiv:1703.09188; it is the chapter's example of an MPU tensor that is
not simple but becomes simple after blocking two sites.

On a ring of `N` sites the operator is diagonal in the product basis, with entries
\(\prod_n (-1)^{i_{n-2} i_n}\); for `N ≥ 3` this is the product of the controlled-\(Z\) gates
between next-nearest neighbours. The tensor itself is not simple, the blocking of two sites is
simple with boundary vectors `Ω` and `Ω / 4`, and both cut ranks equal `4` for the tensor and
for its blocking.

The bond pair `(α₁, α₂)` is encoded in `Fin 4` as `2 α₁ + α₂` through `czBond`, which is
`finProdFinEquiv`.

## Main definitions

* `MPOTensor.czTensor`: the tensor of chapter Example 4.9.

## Main results

* `MPOTensor.mpo_czTensor_apply`, `MPOTensor.mpo_czTensor_apply'`: the diagonal entries of the
  operator on every ring.
* `MPOTensor.czTensor_isMPU`: the tensor generates matrix product unitaries.
* `MPOTensor.not_isMPUSimple_czTensor`: the tensor is not simple.
* `MPOTensor.blockTensor_czTensor_two_isMPUSimple`: its blocking of two sites is simple.
* `MPOTensor.rightRank_czTensor`, `MPOTensor.leftRank_czTensor`,
  `MPOTensor.rightRank_blockTensor_czTensor_two`, `MPOTensor.leftRank_blockTensor_czTensor_two`:
  all four cut ranks equal `4`.

## References

* Lecture notes on matrix product unitaries, chapter `MPU.tex`, Example 4.9.
* Cirac, Perez-Garcia, Schuch, Verstraete, arXiv:1703.09188, Definition III.2 (simplicity) and
  definition `defnrl` (the cut ranks), whose definitions are applied here.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

/-! ### The tensor -/

/-- The bond index `(α₁, α₂)` of the controlled-\(Z\) tensor, encoded as `2 α₁ + α₂`. -/
def czBond : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

/-- The next-nearest-neighbour controlled-\(Z\) tensor of chapter Example 4.9:
\(U^{ij}_{(\alpha_1\alpha_2),(\beta_1\beta_2)}
  = \delta_{ij}\delta_{\alpha_2\beta_1}\delta_{\beta_2 i}(-1)^{\alpha_1 i}\), with the bond pair
encoded by `czBond`. -/
noncomputable def czTensor : MPOTensor 2 4 :=
  fun i j ↦ Matrix.of fun α β ↦
    if i = j ∧ (czBond.symm α).2 = (czBond.symm β).1 ∧ (czBond.symm β).2 = i then
      (-1 : ℂ) ^ (((czBond.symm α).1 : ℕ) * (i : ℕ))
    else 0

/-- The letters of `czTensor` in bond-pair coordinates (chapter Example 4.9). -/
theorem czTensor_apply_czBond (i j a₁ a₂ b₁ b₂ : Fin 2) :
    czTensor i j (czBond (a₁, a₂)) (czBond (b₁, b₂)) =
      if i = j ∧ a₂ = b₁ ∧ b₂ = i then (-1 : ℂ) ^ ((a₁ : ℕ) * (i : ℕ)) else 0 := by
  simp only [czTensor, of_apply, Equiv.symm_apply_apply]

/-- The off-diagonal letters of `czTensor` vanish. -/
theorem czTensor_of_ne {i j : Fin 2} (h : i ≠ j) : czTensor i j = 0 := by
  ext α β
  simp [czTensor, h]

/-- A letter of `czTensor` vanishes unless its right bond is `(α₂, i)`. -/
theorem czTensor_apply_eq_zero {i j : Fin 2} {α β : Fin 4}
    (h : ¬((czBond.symm α).2 = (czBond.symm β).1 ∧ (czBond.symm β).2 = i)) :
    czTensor i j α β = 0 :=
  ite_eq_right_iff.mpr fun h' ↦ absurd h'.2 h

/-- The letters of `czTensor` are real and diagonal, so the tensor is its own physical
adjoint. -/
theorem physicalAdjointTensor_czTensor : physicalAdjointTensor czTensor = czTensor := by
  funext i j
  ext β α
  by_cases h : i = j
  · subst h
    simp [czTensor, apply_ite star]
  · simp [czTensor, h, Ne.symm h]

/-- The vector \(f_i\otimes f_k\) with \(f_i = |0\rangle + (-1)^i|1\rangle\), in bond-pair
coordinates. -/
noncomputable def czVec (i k : Fin 2) : Fin 4 → ℂ := fun α ↦
  (-1 : ℂ) ^ (((czBond.symm α).1 : ℕ) * (i : ℕ)) *
    (-1 : ℂ) ^ (((czBond.symm α).2 : ℕ) * (k : ℕ))

/-- The entries of `czVec` square to one. -/
theorem czVec_mul_self (i k : Fin 2) (α : Fin 4) : czVec i k α * czVec i k α = 1 := by
  rw [czVec, mul_mul_mul_comm, ← mul_pow, ← mul_pow]
  simp

/-- Two diagonal letters multiply to a rank-one matrix,
\(U^{ii}U^{kk} = |f_i f_k\rangle\langle ik|\) (chapter Example 4.9, proof of (b)). -/
theorem czTensor_mul_czTensor (i k : Fin 2) :
    czTensor i i * czTensor k k =
      vecMulVec (czVec i k) (Pi.single (czBond (i, k)) 1) := by
  ext α β
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := czBond.surjective α
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := czBond.surjective β
  rw [mul_apply, ← czBond.sum_comp, Fintype.sum_prod_type]
  fin_cases a₂ <;> fin_cases i <;> fin_cases b₁ <;>
    simp [czTensor_apply_czBond, vecMulVec_apply, Pi.single_apply, czVec]

/-! ### The operator on a ring -/

/-- **The operator of the controlled-\(Z\) tensor** (chapter Example 4.9 (a)). On a ring of `N`
sites the operator is diagonal in the product basis with entries
\(\prod_n (-1)^{i_{n-2} i_n}\), indices modulo `N`. The bond entering site `n` is forced to be
`(s (n - 2), s (n - 1))`. -/
theorem mpo_czTensor_apply (N : ℕ) [NeZero N] (s t : Fin N → Fin 2) :
    mpo czTensor N s t =
      if s = t then ∏ n : Fin N, (-1 : ℂ) ^ ((s (n - 2) : ℕ) * (s n : ℕ)) else 0 := by
  have h2 : ∀ n : Fin N, n - 2 + 1 = n - 1 := fun n ↦ by
    rw [show (2 : Fin N) = 1 + 1 from Fin.ext (by simp [Fin.val_add])]
    abel
  rw [mpo_apply_eq_prod_of_forced_bond czTensor s t (fun n ↦ czBond (s (n - 2), s (n - 1)))
    fun g hg ↦ ?_]
  · split_ifs with hst
    · subst hst
      refine Finset.prod_congr rfl fun n _ ↦ ?_
      have hn : n + 1 - 2 = n - 1 := by rw [← h2 n]; abel
      rw [hn, add_sub_cancel_right, czTensor_apply_czBond]
      simp
    · obtain ⟨n, hn⟩ := Function.ne_iff.mp hst
      exact Finset.prod_eq_zero (Finset.mem_univ n) (by rw [czTensor_of_ne hn]; rfl)
  · by_cases hst : s = t
    · subst hst
      obtain ⟨m, hm⟩ := Function.ne_iff.mp hg
      have hm' : czBond.symm (g m) ≠ (s (m - 2), s (m - 1)) := fun h ↦
        hm (by rw [← h, Equiv.apply_symm_apply])
      by_cases h₂ : (czBond.symm (g m)).2 = s (m - 1)
      · have h₁ : (czBond.symm (g m)).1 ≠ s (m - 2) := fun h ↦ hm' (Prod.ext h h₂)
        by_cases h₃ : (czBond.symm (g (m - 1))).2 = (czBond.symm (g m)).1
        · refine ⟨m - 2, czTensor_apply_eq_zero fun h ↦ h₁ ?_⟩
          rw [h2] at h
          exact h₃.symm.trans h.2
        · refine ⟨m - 1, czTensor_apply_eq_zero fun h ↦ h₃ ?_⟩
          rw [sub_add_cancel] at h
          exact h.1
      · refine ⟨m - 1, czTensor_apply_eq_zero fun h ↦ h₂ ?_⟩
        rw [sub_add_cancel] at h
        exact h.2
    · obtain ⟨n, hn⟩ := Function.ne_iff.mp hst
      exact ⟨n, by rw [czTensor_of_ne hn]; rfl⟩

/-- The operator of chapter Example 4.9 (a) written as the product over `n` of the
controlled-\(Z\) sign \((-1)^{i_n i_{n+2}}\) between sites `n` and `n + 2`. For `N ≥ 3` these
sites are distinct and the operator is \(\prod_n CZ_{n,n+2}\). -/
theorem mpo_czTensor_apply' (N : ℕ) [NeZero N] (s t : Fin N → Fin 2) :
    mpo czTensor N s t =
      if s = t then ∏ n : Fin N, (-1 : ℂ) ^ ((s n : ℕ) * (s (n + 2) : ℕ)) else 0 := by
  rw [mpo_czTensor_apply, Fintype.prod_equiv (Equiv.subRight 2) _
    (fun n ↦ (-1 : ℂ) ^ ((s n : ℕ) * (s (n + 2) : ℕ))) fun n ↦ by simp]

/-- The operator of chapter Example 4.9 (a) as a diagonal matrix. -/
theorem mpo_czTensor (N : ℕ) [NeZero N] :
    mpo czTensor N =
      diagonal fun s ↦ ∏ n : Fin N, (-1 : ℂ) ^ ((s (n - 2) : ℕ) * (s n : ℕ)) := by
  ext s t
  rw [mpo_czTensor_apply, diagonal_apply]

/-- **The controlled-\(Z\) tensor is an MPU tensor** (chapter Example 4.9 (a)): a diagonal
matrix with entries `±1` is unitary. -/
theorem czTensor_isMPU : IsMPU czTensor := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  rw [mpo_czTensor, mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext s
  simp [← Finset.prod_mul_distrib, ← mul_pow]

/-! ### The tensor is not simple -/

/-- The doubled diagonal letters of the controlled-\(Z\) tensor: since the letters are diagonal
and real, \(W^{ij} = U^{ii}\otimes U^{ij}\). -/
theorem mulTensor_czTensor_apply (i j : Fin 2) :
    mulTensor czTensor czTensor i j =
      (czTensor i i ⊗ₖ czTensor i j).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [mulTensor_apply, Fintype.sum_eq_single i fun h hh ↦ by
    rw [czTensor_of_ne (Ne.symm hh), zero_kronecker]]

/-- The product of two diagonal double-layer letters,
\(W^{ii}W^{kk} = U^{ii}U^{kk}\otimes U^{ii}U^{kk}\) (chapter Example 4.9, proof of (b)). -/
theorem doubleLayerTensor_czTensor_mul (i k : Fin 2) :
    doubleLayerTensor czTensor i i * doubleLayerTensor czTensor k k =
      ((czTensor i i * czTensor k k) ⊗ₖ (czTensor i i * czTensor k k)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [doubleLayerTensor, physicalAdjointTensor_czTensor, mulTensor_czTensor_apply,
    mulTensor_czTensor_apply, mul_kronecker_mul,
    submatrix_mul _ _ _ _ _ finProdFinEquiv.symm.bijective]

/-- The row of \(W^{ii}W^{kk}\) at the doubled bond `((0,0), (0,0))` is the covector
\(\langle ik|\otimes\langle ik|\) (chapter Example 4.9, proof of (b)). -/
theorem doubleLayerTensor_czTensor_mul_apply (i k : Fin 2) (y₁ y₂ : Fin 4) :
    (doubleLayerTensor czTensor i i * doubleLayerTensor czTensor k k)
        (finProdFinEquiv (czBond (0, 0), czBond (0, 0))) (finProdFinEquiv (y₁, y₂)) =
      (Pi.single (czBond (i, k)) 1 : Fin 4 → ℂ) y₁ *
        (Pi.single (czBond (i, k)) 1 : Fin 4 → ℂ) y₂ := by
  rw [doubleLayerTensor_czTensor_mul, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, kroneckerMap_apply, czTensor_mul_czTensor, vecMulVec_apply,
    vecMulVec_apply]
  simp [czVec]

/-- **The controlled-\(Z\) tensor is not simple** (chapter Example 4.9 (b)). If `a`, `b` were
simplicity witnesses, the covector \(c = (a|W^{00}\) would satisfy \((c|b) = 1\). The identity
\(W^{ii}W^{00} = W^{ii}|b)(a|W^{00}\) makes `c` a multiple of the covector
\(\langle i0|\otimes\langle i0|\) for `i = 0` and for `i = 1`; these have disjoint supports, so
`c = 0`, a contradiction. -/
theorem not_isMPUSimple_czTensor : ¬IsMPUSimple czTensor := by
  rintro ⟨a, b, h₁, h₂⟩
  set c : Fin (4 * 4) → ℂ := a ᵥ* doubleLayerTensor czTensor 0 0 with hc_def
  have hc : c ⬝ᵥ b = 1 := by
    rw [hc_def, ← dotProduct_mulVec, h₁]
    simp
  have key : ∀ i : Fin 2, ∀ y₁ y₂ : Fin 4, y₁ ≠ czBond (i, 0) →
      c (finProdFinEquiv (y₁, y₂)) = 0 := by
    intro i y₁ y₂ hy
    have h := h₂ i i 0 0
    rw [mul_vecMulVec, vecMulVec_mul] at h
    have e : ∀ q, (doubleLayerTensor czTensor i i * doubleLayerTensor czTensor 0 0)
        (finProdFinEquiv (czBond (0, 0), czBond (0, 0))) q =
          (doubleLayerTensor czTensor i i *ᵥ b)
            (finProdFinEquiv (czBond (0, 0), czBond (0, 0))) * c q := fun q ↦ by
      rw [h, vecMulVec_apply]
    have e₁ := e (finProdFinEquiv (czBond (i, 0), czBond (i, 0)))
    have e₂ := e (finProdFinEquiv (y₁, y₂))
    rw [doubleLayerTensor_czTensor_mul_apply] at e₁ e₂
    simp only [Pi.single_eq_same, mul_one] at e₁
    rw [Pi.single_eq_of_ne hy, zero_mul, eq_comm, mul_eq_zero] at e₂
    exact e₂.resolve_left (left_ne_zero_of_mul (e₁ ▸ one_ne_zero))
  have hc0 : c = 0 := by
    funext q
    obtain ⟨⟨y₁, y₂⟩, rfl⟩ := finProdFinEquiv.surjective q
    by_cases hy : y₁ = czBond (0, 0)
    · refine key 1 y₁ y₂ (hy ▸ fun h ↦ ?_)
      simpa using czBond.injective h
    · exact key 0 y₁ y₂ hy
  rw [hc0, zero_dotProduct] at hc
  exact zero_ne_one hc

/-! ### The blocking of two sites is simple -/

/-- A letter of the blocking of two sites is the product of the two letters of the decoded
words. -/
theorem blockTensor_czTensor_two_apply (I J : Fin (MPSTensor.blockPhysDim 2 2)) :
    blockTensor czTensor 2 I J =
      czTensor (MPSTensor.decodeBlock 2 2 I 0) (MPSTensor.decodeBlock 2 2 J 0) *
        czTensor (MPSTensor.decodeBlock 2 2 I 1) (MPSTensor.decodeBlock 2 2 J 1) := by
  simp [blockTensor_apply, Kraus.wordOfBlock, List.ofFn_succ]

/-- The bond basis vector \(|i_1 i_2\rangle\) of a blocked index \(\mathbf i = (i_1, i_2)\). -/
noncomputable def czBlockBond (I : Fin (MPSTensor.blockPhysDim 2 2)) : Fin 4 :=
  czBond (MPSTensor.decodeBlock 2 2 I 0, MPSTensor.decodeBlock 2 2 I 1)

/-- The vector \(x_{\mathbf i} = f_{i_1} f_{i_2}\) of a blocked index
\(\mathbf i = (i_1, i_2)\). -/
noncomputable def czBlockVec (I : Fin (MPSTensor.blockPhysDim 2 2)) : Fin 4 → ℂ :=
  czVec (MPSTensor.decodeBlock 2 2 I 0) (MPSTensor.decodeBlock 2 2 I 1)

/-- The first entry of every `czBlockVec` is one. -/
theorem czBlockVec_apply_zero (I : Fin (MPSTensor.blockPhysDim 2 2)) :
    czBlockVec I (czBond (0, 0)) = 1 := by
  simp [czBlockVec, czVec]

/-- The letters of the blocking of two sites are
\(\delta_{\mathbf i\mathbf j}|x_{\mathbf i}\rangle\langle y_{\mathbf i}|\) with
\(x_{\mathbf i} = f_{i_1}f_{i_2}\) and \(y_{\mathbf i} = i_1 i_2\) (chapter Example 4.9, proof
of (c)). -/
theorem blockTensor_czTensor_two (I J : Fin (MPSTensor.blockPhysDim 2 2)) :
    blockTensor czTensor 2 I J =
      if I = J then vecMulVec (czBlockVec I) (Pi.single (czBlockBond I) 1) else 0 := by
  rw [blockTensor_czTensor_two_apply]
  split_ifs with h
  · subst h
    exact czTensor_mul_czTensor _ _
  · have hw : MPSTensor.decodeBlock 2 2 I ≠ MPSTensor.decodeBlock 2 2 J := fun e ↦
      h ((MPSTensor.decodeBlockEquiv 2 2).injective (by simpa using e))
    by_cases h0 : MPSTensor.decodeBlock 2 2 I 0 = MPSTensor.decodeBlock 2 2 J 0
    · have h1 : MPSTensor.decodeBlock 2 2 I 1 ≠ MPSTensor.decodeBlock 2 2 J 1 := fun h1 ↦
        hw (funext fun k ↦ by fin_cases k <;> assumption)
      rw [czTensor_of_ne h1, mul_zero]
    · rw [czTensor_of_ne h0, zero_mul]

/-- The doubled vector \(X_{\mathbf i} = \bar x_{\mathbf i}\otimes x_{\mathbf i}\) on the doubled
bond. -/
noncomputable def czBlockX (I : Fin (MPSTensor.blockPhysDim 2 2)) : Fin (4 * 4) → ℂ :=
  fun p ↦ czBlockVec I (finProdFinEquiv.symm p).1 * czBlockVec I (finProdFinEquiv.symm p).2

/-- The doubled covector \(Y_{\mathbf i} = \bar y_{\mathbf i}\otimes y_{\mathbf i}\) on the
doubled bond. -/
noncomputable def czBlockY (I : Fin (MPSTensor.blockPhysDim 2 2)) : Fin (4 * 4) → ℂ :=
  Pi.single (finProdFinEquiv (czBlockBond I, czBlockBond I)) 1

/-- The vectorized identity \(\Omega = \sum_\alpha |\alpha\alpha)\) on the bond space of the
double layer of the blocking. -/
noncomputable def czOmega : Fin (4 * 4) → ℂ := fun p ↦
  if (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm p).2 then 1 else 0

/-- The double-layer letters of the blocking of two sites are
\(W^{\mathbf i\mathbf j} = \delta_{\mathbf i\mathbf j}|X_{\mathbf i})(Y_{\mathbf i}|\)
(chapter Example 4.9, proof of (c)). -/
theorem doubleLayerTensor_blockTensor_czTensor_two (I J : Fin (MPSTensor.blockPhysDim 2 2)) :
    doubleLayerTensor (blockTensor czTensor 2) I J =
      if I = J then vecMulVec (czBlockX I) (czBlockY I) else 0 := by
  rw [doubleLayerTensor, physicalAdjointTensor_blockTensor, physicalAdjointTensor_czTensor,
    mulTensor_apply, Fintype.sum_eq_single I fun H hH ↦ by
      rw [blockTensor_czTensor_two, ite_eq_right (Ne.symm hH), zero_kronecker]]
  split_ifs with h
  · subst h
    ext p q
    obtain ⟨⟨p₁, p₂⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨q₁, q₂⟩, rfl⟩ := finProdFinEquiv.surjective q
    simp only [blockTensor_czTensor_two, ↓reduceIte]
    simp [vecMulVec_apply, czBlockX, czBlockY, Pi.single_apply]
    by_cases h₁ : q₁ = czBlockBond I <;> by_cases h₂ : q₂ = czBlockBond I <;> simp [h₁, h₂]
  · rw [blockTensor_czTensor_two I J, ite_eq_right h, kronecker_zero]
    rfl

/-- Pairing with \(Y_{\mathbf i}\) reads off one coordinate. -/
theorem czBlockY_dotProduct (I : Fin (MPSTensor.blockPhysDim 2 2)) (v : Fin (4 * 4) → ℂ) :
    czBlockY I ⬝ᵥ v = v (finProdFinEquiv (czBlockBond I, czBlockBond I)) := by
  rw [czBlockY, single_one_dotProduct]

/-- The diagonal entries of \(X_{\mathbf i}\) are one. -/
theorem czBlockX_apply_diag (I : Fin (MPSTensor.blockPhysDim 2 2)) (x : Fin 4) :
    czBlockX I (finProdFinEquiv (x, x)) = 1 := by
  rw [czBlockX, Equiv.symm_apply_apply, czBlockVec, czVec_mul_self]

/-- \((\Omega|X_{\mathbf i}) = \|x_{\mathbf i}\|^2 = 4\). -/
theorem czOmega_dotProduct_czBlockX (I : Fin (MPSTensor.blockPhysDim 2 2)) :
    czOmega ⬝ᵥ czBlockX I = 4 := by
  rw [dotProduct, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [czOmega, czBlockX, czBlockVec, czVec_mul_self]

/-- **The simplicity identities of the blocking with the chapter's witnesses** (chapter
Example 4.9 (c)). With \(a = \Omega\) and \(b = \Omega/4\) the double-layer letters `W` of the
blocking of two sites satisfy \((a|W^{\mathbf i\mathbf j}|b) = \delta_{\mathbf i\mathbf j}\)
and \(W^{\mathbf i\mathbf j}W^{\mathbf k\mathbf l}
  = W^{\mathbf i\mathbf j}|b)(a|W^{\mathbf k\mathbf l}\).
The scalar inputs are \((Y_{\mathbf i}|X_{\mathbf k}) = 1\), \((\Omega|X_{\mathbf k}) = 4\) and
\((Y_{\mathbf i}|\Omega) = 1\). `blockTensor_czTensor_two_isMPUSimple` is the existential form. -/
theorem blockTensor_czTensor_two_simple_witnesses :
    (∀ i j : Fin (MPSTensor.blockPhysDim 2 2),
      czOmega ⬝ᵥ (doubleLayerTensor (blockTensor czTensor 2) i j *ᵥ ((1 / 4 : ℂ) • czOmega)) =
        if i = j then 1 else 0) ∧
    (∀ i j k l : Fin (MPSTensor.blockPhysDim 2 2),
      doubleLayerTensor (blockTensor czTensor 2) i j *
          doubleLayerTensor (blockTensor czTensor 2) k l =
        doubleLayerTensor (blockTensor czTensor 2) i j *
          vecMulVec ((1 / 4 : ℂ) • czOmega) czOmega *
            doubleLayerTensor (blockTensor czTensor 2) k l) := by
  have hYb : ∀ I, czBlockY I ⬝ᵥ ((1 / 4 : ℂ) • czOmega) = 1 / 4 := fun I ↦ by
    rw [czBlockY_dotProduct]
    simp [czOmega]
  have hYX : ∀ I K, czBlockY I ⬝ᵥ czBlockX K =
      (czBlockY I ⬝ᵥ ((1 / 4 : ℂ) • czOmega)) * (czOmega ⬝ᵥ czBlockX K) := fun I K ↦ by
    rw [hYb, czOmega_dotProduct_czBlockX, czBlockY_dotProduct, czBlockX_apply_diag]
    norm_num
  have hab : ∀ I, (czOmega ⬝ᵥ czBlockX I) * (czBlockY I ⬝ᵥ ((1 / 4 : ℂ) • czOmega)) = 1 :=
    fun I ↦ by
      rw [hYb, czOmega_dotProduct_czBlockX]
      norm_num
  refine ⟨fun i j ↦ ?_, fun i j k l ↦ ?_⟩
  · rw [doubleLayerTensor_blockTensor_czTensor_two]
    split_ifs with hij
    · subst hij
      rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, mul_comm, hab]
    · simp
  · rw [doubleLayerTensor_blockTensor_czTensor_two i j,
      doubleLayerTensor_blockTensor_czTensor_two k l]
    split_ifs with hij hkl hkl
    · subst hij hkl
      rw [vecMulVec_mul_vecMulVec, Matrix.mul_assoc, vecMulVec_mul_vecMulVec,
        vecMulVec_mul_vecMulVec, hYX, mul_smul]
    all_goals simp

/-- **The blocking of two sites is simple** (chapter Example 4.9 (c)), with boundary vectors
\(a = \Omega\) and \(b = \Omega/4\); the existential form of
`blockTensor_czTensor_two_simple_witnesses`. -/
theorem blockTensor_czTensor_two_isMPUSimple : IsMPUSimple (blockTensor czTensor 2) :=
  ⟨czOmega, (1 / 4 : ℂ) • czOmega, blockTensor_czTensor_two_simple_witnesses⟩

/-! ### The cut ranks -/

/-- A matrix that factors through a `k`-dimensional space and has an identity submatrix of
size `k` has rank `k`. -/
private theorem rank_eq_card_of_factor {m n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq k] (M : Matrix m n ℂ) (A : Matrix m k ℂ) (B : Matrix k n ℂ)
    (hM : M = A * B) (r : k → m) (c : k → n) (hsub : M.submatrix r c = 1) :
    M.rank = Fintype.card k := by
  refine le_antisymm ?_ ?_
  · rw [hM]
    exact (rank_mul_le_left A B).trans (rank_le_card_width A)
  · have h := rank_submatrix_le M r c
    rwa [hsub, rank_one] at h

/-- `rank_eq_card_of_factor` through the pairs `Fin 2 × Fin 2`. -/
private theorem rank_eq_four_of_factor {m n : Type*} [Fintype n]
    (M : Matrix m n ℂ) (A : Matrix m (Fin 2 × Fin 2) ℂ) (B : Matrix (Fin 2 × Fin 2) n ℂ)
    (hM : M = A * B) (r : Fin 2 × Fin 2 → m) (c : Fin 2 × Fin 2 → n)
    (hsub : M.submatrix r c = 1) : M.rank = 4 :=
  rank_eq_card_of_factor M A B hM r c hsub

/-- **The right cut rank of the controlled-\(Z\) tensor is `4`** (chapter Example 4.9 (d), not
printed in the chapter). The first cut factors through the pairs `(i, β₁)`, and the rows
`(i, (b, i))` with the columns `((0, b), i)` form an identity submatrix. -/
theorem rightRank_czTensor : r[czTensor] = 4 := by
  refine rank_eq_four_of_factor _
    (Matrix.of fun iβ ib ↦ if iβ.1 = ib.1 ∧ czBond.symm iβ.2 = (ib.2, ib.1) then 1 else 0)
    (Matrix.of fun ib αj ↦ if ib.1 = αj.2 ∧ (czBond.symm αj.1).2 = ib.2 then
      (-1 : ℂ) ^ (((czBond.symm αj.1).1 : ℕ) * (αj.2 : ℕ)) else 0) ?_
    (fun ib ↦ (ib.1, czBond (ib.2, ib.1))) (fun ib ↦ (czBond (0, ib.2), ib.1)) ?_
  · ext ⟨i, β⟩ ⟨α, j⟩
    obtain ⟨⟨a₁, a₂⟩, rfl⟩ := czBond.surjective α
    obtain ⟨⟨b₁, b₂⟩, rfl⟩ := czBond.surjective β
    fin_cases i <;> fin_cases j <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
      simp [sourceCutM₁, czTensor_apply_czBond, mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two]
  · ext ⟨i, b⟩ ⟨i', b'⟩
    fin_cases i <;> fin_cases i' <;> fin_cases b <;> fin_cases b' <;>
      simp [sourceCutM₁, czTensor_apply_czBond, one_apply, Prod.ext_iff]

/-- **The left cut rank of the controlled-\(Z\) tensor is `4`** (chapter Example 4.9 (d), not
printed in the chapter). The second cut factors through the pairs `(i, α₂)`, and the rows
`((0, b), i)` with the columns `(i, (b, i))` form an identity submatrix. -/
theorem leftRank_czTensor : ℓ[czTensor] = 4 := by
  refine rank_eq_four_of_factor _
    (Matrix.of fun αi ib ↦ if αi.2 = ib.1 ∧ (czBond.symm αi.1).2 = ib.2 then
      (-1 : ℂ) ^ (((czBond.symm αi.1).1 : ℕ) * (αi.2 : ℕ)) else 0)
    (Matrix.of fun ib jβ ↦ if ib.1 = jβ.1 ∧ czBond.symm jβ.2 = (ib.2, ib.1) then 1 else 0) ?_
    (fun ib ↦ (czBond (0, ib.2), ib.1)) (fun ib ↦ (ib.1, czBond (ib.2, ib.1))) ?_
  · ext ⟨α, i⟩ ⟨j, β⟩
    obtain ⟨⟨a₁, a₂⟩, rfl⟩ := czBond.surjective α
    obtain ⟨⟨b₁, b₂⟩, rfl⟩ := czBond.surjective β
    fin_cases i <;> fin_cases j <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
      simp [sourceCutM₂, czTensor_apply_czBond, mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two]
  · ext ⟨i, b⟩ ⟨i', b'⟩
    fin_cases i <;> fin_cases i' <;> fin_cases b <;> fin_cases b' <;>
      simp [sourceCutM₂, czTensor_apply_czBond, one_apply, Prod.ext_iff]

/-- There are four blocked indices of two sites. -/
theorem card_blockPhysDim_two_two : Fintype.card (Fin (MPSTensor.blockPhysDim 2 2)) = 4 := by
  rw [Fintype.card_fin, MPSTensor.blockPhysDim_eq_pow]
  norm_num

/-- **The right cut rank of the blocking of two sites is `4`** (chapter Example 4.9 (d), not
printed in the chapter). The first cut factors through the blocked index, and the rows
\((\mathbf k, y_{\mathbf k})\) with the columns \(((0,0), \mathbf k)\) form an identity
submatrix. -/
theorem rightRank_blockTensor_czTensor_two : r[blockTensor czTensor 2] = 4 := by
  rw [rightRank]
  refine (rank_eq_card_of_factor _
    (Matrix.of fun Iβ K ↦ if Iβ.1 = K ∧ Iβ.2 = czBlockBond K then 1 else 0)
    (Matrix.of fun K αJ ↦ if K = αJ.2 then czBlockVec K αJ.1 else 0) ?_
    (fun K ↦ (K, czBlockBond K)) (fun K ↦ (czBond (0, 0), K)) ?_).trans
    card_blockPhysDim_two_two
  · ext ⟨I, β⟩ ⟨α, J⟩
    simp only [sourceCutM₁, blockTensor_czTensor_two]
    by_cases h : I = J <;> simp [h, mul_apply, vecMulVec_apply, Pi.single_apply, ite_and]
  · ext K L
    simp only [submatrix_apply, sourceCutM₁, blockTensor_czTensor_two]
    by_cases h : K = L <;> simp [h, one_apply, vecMulVec_apply, czBlockVec_apply_zero]

/-- **The left cut rank of the blocking of two sites is `4`** (chapter Example 4.9 (d), not
printed in the chapter). The second cut factors through the blocked index, and the rows
\(((0,0), \mathbf k)\) with the columns \((\mathbf k, y_{\mathbf k})\) form an identity
submatrix. -/
theorem leftRank_blockTensor_czTensor_two : ℓ[blockTensor czTensor 2] = 4 := by
  rw [leftRank]
  refine (rank_eq_card_of_factor _
    (Matrix.of fun αI K ↦ if αI.2 = K then czBlockVec K αI.1 else 0)
    (Matrix.of fun K Jβ ↦ if K = Jβ.1 ∧ Jβ.2 = czBlockBond K then 1 else 0) ?_
    (fun K ↦ (czBond (0, 0), K)) (fun K ↦ (K, czBlockBond K)) ?_).trans
    card_blockPhysDim_two_two
  · ext ⟨α, I⟩ ⟨J, β⟩
    simp only [sourceCutM₂, blockTensor_czTensor_two]
    by_cases h : I = J <;> simp [h, mul_apply, vecMulVec_apply, Pi.single_apply, ite_and]
  · ext K L
    simp only [submatrix_apply, sourceCutM₂, blockTensor_czTensor_two]
    by_cases h : K = L <;> simp [h, one_apply, vecMulVec_apply, czBlockVec_apply_zero]

end MPOTensor
