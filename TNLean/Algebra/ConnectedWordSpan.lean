/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Connected coefficient graphs and two-step word spaces

A connected graph of coefficient vectors bounds their span by a space of
outer products along its edges, up to one dimension. A nonzero diagonal
outer product removes the extra dimension. These are the word-space
comparisons in the cyclic and scalar-loop root-selection arguments for
arXiv:1708.00029, Theorem 4.1; the channel applications remain separate.
-/

open Module

namespace Matrix

private def skewContract {𝕜 n : Type*} [Field 𝕜]
    (f : (n → 𝕜) →ₗ[𝕜] 𝕜) : Matrix n n 𝕜 →ₗ[𝕜] (n → 𝕜) where
  toFun A i := f (fun j => A i j) - f (fun j => A j i)
  map_add' A B := by
    ext i
    change f ((fun j => A i j) + fun j => B i j) -
      f ((fun j => A j i) + fun j => B j i) = _
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' c A := by
    ext i
    change f (c • fun j => A i j) - f (c • fun j => A j i) = _
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_sub]

private theorem skewContract_vecMulVec {𝕜 n : Type*} [Field 𝕜]
    (f : (n → 𝕜) →ₗ[𝕜] 𝕜) (x y : n → 𝕜) :
    skewContract f (vecMulVec x y) = f y • x - f x • y := by
  ext i
  change f (fun j => x i * y j) - f (fun j => x j * y i) = _
  have hCol : (fun j => x j * y i) = y i • x := by ext j; simp [mul_comm]
  rw [hCol]
  change f (x i • y) - f (y i • x) = _
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem connected_span_le_image_sup {𝕜 n ι : Type*} [Field 𝕜]
    (G : SimpleGraph ι) (hG : G.Preconnected) (v : ι → n → 𝕜)
    (i₀ : ι) (f : (n → 𝕜) →ₗ[𝕜] 𝕜) (hf : ∀ i, f (v i) ≠ 0)
    (W : Submodule 𝕜 (Matrix n n 𝕜))
    (hEdge : ∀ i j, G.Adj i j →
      vecMulVec (v i) (v j) ∈ W ∨ vecMulVec (v j) (v i) ∈ W) :
    Submodule.span 𝕜 (Set.range v) ≤
      W.map (skewContract f) ⊔ Submodule.span 𝕜 {v i₀} := by
  let M := W.map (skewContract f) ⊔ Submodule.span 𝕜 {v i₀}
  have hStep (i j : ι) (hij : G.Adj i j) (hi : v i ∈ M) : v j ∈ M := by
    have hDelta : f (v j) • v i - f (v i) • v j ∈ W.map (skewContract f) := by
      rcases hEdge i j hij with h | h
      · exact ⟨vecMulVec (v i) (v j), h, skewContract_vecMulVec f _ _⟩
      · have h' : f (v i) • v j - f (v j) • v i ∈ W.map (skewContract f) :=
          ⟨vecMulVec (v j) (v i), h, skewContract_vecMulVec f _ _⟩
        simpa only [neg_sub] using (W.map (skewContract f)).neg_mem h'
    have hDeltaM : f (v j) • v i - f (v i) • v j ∈ M :=
      (show W.map (skewContract f) ≤ M from le_sup_left) hDelta
    have hSub := M.sub_mem (M.smul_mem (f (v j)) hi) hDeltaM
    have hScaled : f (v i) • v j ∈ M := by
      convert hSub using 1
      abel
    exact (Submodule.smul_mem_iff M (hf i)).mp hScaled
  have hReach (i j : ι) (hij : G.Reachable i j) : v i ∈ M → v j ∈ M := by
    obtain ⟨p⟩ := hij
    induction p with
    | nil => exact id
    | @cons i j k hij p ih => exact fun hi => ih (hStep i j hij hi)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hBase : v i₀ ∈ M :=
    (show Submodule.span 𝕜 {v i₀} ≤ M from le_sup_right)
      (Submodule.subset_span (by simp))
  exact hReach i₀ i (hG i₀ i) hBase

private theorem connected_span_finrank_le_image_add_one {𝕜 n ι : Type*}
    [Field 𝕜] [Finite n]
    (G : SimpleGraph ι) (hG : G.Preconnected) (v : ι → n → 𝕜)
    (i₀ : ι) (f : (n → 𝕜) →ₗ[𝕜] 𝕜) (hf : ∀ i, f (v i) ≠ 0)
    (W : Submodule 𝕜 (Matrix n n 𝕜))
    (hEdge : ∀ i j, G.Adj i j →
      vecMulVec (v i) (v j) ∈ W ∨ vecMulVec (v j) (v i) ∈ W) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range v)) ≤
      finrank 𝕜 (W.map (skewContract f)) + 1 := by
  have hv : v i₀ ≠ 0 := fun h => hf i₀ (by simp [h])
  have h := Submodule.finrank_mono (connected_span_le_image_sup G hG v i₀ f hf W hEdge)
  have hSup := Submodule.finrank_add_le_finrank_add_finrank
    (W.map (skewContract f)) (Submodule.span 𝕜 {v i₀})
  rw [finrank_span_singleton hv] at hSup
  exact h.trans hSup

private theorem range_restrict_skewContract {𝕜 n : Type*} [Field 𝕜]
    (f : (n → 𝕜) →ₗ[𝕜] 𝕜) (W : Submodule 𝕜 (Matrix n n 𝕜)) :
    LinearMap.range ((skewContract f).comp W.subtype) = W.map (skewContract f) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- A connected graph of nonzero coefficient vectors bounds the dimension
of their span by the dimension of its oriented outer-product space plus
one. The functional is explicitly assumed nonzero on every coefficient;
this is the path-space ingredient for arXiv:1708.00029, Theorem 4.1. -/
theorem finrank_span_le_wordSpace_add_one {𝕜 n ι : Type*} [Field 𝕜] [Finite n]
    (G : SimpleGraph ι) (hG : G.Preconnected) (v : ι → n → 𝕜)
    (i₀ : ι) (f : (n → 𝕜) →ₗ[𝕜] 𝕜) (hf : ∀ i, f (v i) ≠ 0)
    (W : Submodule 𝕜 (Matrix n n 𝕜))
    (hEdge : ∀ i j, G.Adj i j →
      vecMulVec (v i) (v j) ∈ W ∨ vecMulVec (v j) (v i) ∈ W) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range v)) ≤ finrank 𝕜 W + 1 := by
  have hSpan := connected_span_finrank_le_image_add_one G hG v i₀ f hf W hEdge
  have hRank := ((skewContract f).comp W.subtype).finrank_range_add_finrank_ker
  rw [range_restrict_skewContract] at hRank
  omega

/-- A diagonal outer product in a connected coefficient graph removes the
extra dimension in the word-space bound. This is the scalar-loop rank
comparison used in the paper argument for arXiv:1708.00029, Theorem 4.1;
the whole-channel root selector is a separate assertion. -/
theorem finrank_span_le_wordSpace_of_diagonal {𝕜 n ι : Type*}
    [Field 𝕜] [Finite n]
    (G : SimpleGraph ι) (hG : G.Preconnected) (v : ι → n → 𝕜)
    (i₀ : ι) (f : (n → 𝕜) →ₗ[𝕜] 𝕜) (hf : ∀ i, f (v i) ≠ 0)
    (W : Submodule 𝕜 (Matrix n n 𝕜))
    (hEdge : ∀ i j, G.Adj i j →
      vecMulVec (v i) (v j) ∈ W ∨ vecMulVec (v j) (v i) ∈ W)
    (hLoop : vecMulVec (v i₀) (v i₀) ∈ W) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range v)) ≤ finrank 𝕜 W := by
  classical
  have hv : v i₀ ≠ 0 := fun h => hf i₀ (by simp [h])
  obtain ⟨j, hj⟩ : ∃ j, v i₀ j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  have hOuter : vecMulVec (v i₀) (v i₀) ≠ 0 := by
    intro h
    have hjj := congrArg (fun A : Matrix n n 𝕜 => A j j) h
    exact mul_ne_zero hj hj (by simpa [vecMulVec_apply] using hjj)
  let r := (skewContract f).comp W.subtype
  let z : W := ⟨vecMulVec (v i₀) (v i₀), hLoop⟩
  have hz : z ≠ 0 := fun h => hOuter (congrArg Subtype.val h)
  have hKer : z ∈ LinearMap.ker r := by
    change skewContract f (vecMulVec (v i₀) (v i₀)) = 0
    rw [skewContract_vecMulVec, sub_self]
  have hKerNe : LinearMap.ker r ≠ ⊥ := by
    intro h
    exact hz (by simpa only [h, Submodule.mem_bot] using hKer)
  have hDim : 1 ≤ finrank 𝕜 (LinearMap.ker r) :=
    Submodule.one_le_finrank_iff.mpr hKerNe
  have hSpan := connected_span_finrank_le_image_add_one G hG v i₀ f hf W hEdge
  have hRank := r.finrank_range_add_finrank_ker
  rw [range_restrict_skewContract] at hRank
  omega

/-- Over an infinite field, nonzero coefficients on a finite connected
graph admit the word-space bound without supplying a functional. This is
the finite coefficient case of the path comparison used for
arXiv:1708.00029, Theorem 4.1. -/
theorem finrank_span_le_wordSpace_add_one_of_nonzero {𝕜 n ι : Type*}
    [Field 𝕜] [Infinite 𝕜] [Finite n] [Finite ι]
    (G : SimpleGraph ι) (hG : G.Preconnected) (v : ι → n → 𝕜)
    (i₀ : ι) (hv : ∀ i, v i ≠ 0) (W : Submodule 𝕜 (Matrix n n 𝕜))
    (hEdge : ∀ i j, G.Adj i j →
      vecMulVec (v i) (v j) ∈ W ∨ vecMulVec (v j) (v i) ∈ W) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range v)) ≤ finrank 𝕜 W + 1 := by
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := 𝕜) v hv
  exact finrank_span_le_wordSpace_add_one G hG v i₀ f hf W hEdge

/-- Over an infinite field, a finite connected coefficient graph with a
diagonal outer product gives the word-space bound without a functional
hypothesis. This is the scalar-loop comparison in the paper argument for
arXiv:1708.00029, Theorem 4.1; it is not a whole-channel selector. -/
theorem finrank_span_le_wordSpace_of_diagonal_of_nonzero {𝕜 n ι : Type*}
    [Field 𝕜] [Infinite 𝕜] [Finite n] [Finite ι]
    (G : SimpleGraph ι) (hG : G.Preconnected) (v : ι → n → 𝕜)
    (i₀ : ι) (hv : ∀ i, v i ≠ 0) (W : Submodule 𝕜 (Matrix n n 𝕜))
    (hEdge : ∀ i j, G.Adj i j →
      vecMulVec (v i) (v j) ∈ W ∨ vecMulVec (v j) (v i) ∈ W)
    (hLoop : vecMulVec (v i₀) (v i₀) ∈ W) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range v)) ≤ finrank 𝕜 W := by
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := 𝕜) v hv
  exact finrank_span_le_wordSpace_of_diagonal G hG v i₀ f hf W hEdge hLoop

end Matrix
