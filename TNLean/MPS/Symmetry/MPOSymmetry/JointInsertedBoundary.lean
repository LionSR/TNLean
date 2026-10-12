/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointIntersection
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceMapContinuity
import TNLean.MPS.MPDO.BiCFDerivation.Core

/-!
# Joint inserted boundary maps

For a family of tensor blocks on a common physical alphabet, the extended
boundary map is
\(\Gamma'_n(X)=\sum_x\operatorname{tr}(A_x^{i_1}W_x\cdots W_xA_x^{i_n}X_x)\).
The final insertion is omitted. Simultaneous one-site spanning and a nonzero
insertion in every block make this map injective at every positive length.
The domain remains the product of the block matrix algebras, with dimension
\(\sum_x D_x^2\), rather than the full matrix algebra on their direct sum.

The induction uses a matrix-valued left inverse for each inserted letter
family. Its base case uses the simultaneous span, which separates all block
labels. No orthogonality of the physical block columns is assumed.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563, Section 5,
lines 1695–1777; the exact separating inverse is equation `leftinv`,
lines 1332–1349. The thermodynamic orthogonality at line 317 is not an exact
finite-site orthogonality hypothesis.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Joint extended coefficient map on the product of virtual block algebras.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def blockInsertedGroundSpaceMap
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) (N : ℕ) :
    ((x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) →ₗ[ℂ] NSiteSpace d N :=
  LinearMap.lsum ℂ (fun x => Matrix (Fin (dim x)) (Fin (dim x)) ℂ) ℂ
    (fun x => insertedGroundSpaceMap (A x) (W x) N)

/-- The joint extended map sums the block trace coefficients.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
@[simp]
theorem blockInsertedGroundSpaceMap_apply
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W X : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) (N : ℕ) :
    blockInsertedGroundSpaceMap A W N X =
      ∑ x, insertedGroundSpaceMap (A x) (W x) N (X x) := by
  simp [blockInsertedGroundSpaceMap, LinearMap.lsum_apply]

/-- At one site the inserted map is the original joint boundary map.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
@[simp]
theorem blockInsertedGroundSpaceMap_one
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) :
    blockInsertedGroundSpaceMap A W 1 = blockGroundSpaceMap A 1 := by
  simp only [blockInsertedGroundSpaceMap, insertedGroundSpaceMap_one, blockGroundSpaceMap]

/-- Fixing the last letter multiplies every boundary on the left.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedGroundSpaceMap_restrictLast
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W X : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    {L : ℕ} (hL : 0 < L) (j : Fin d) :
    restrictLast (blockInsertedGroundSpaceMap A W (L + 1) X) j =
      blockInsertedGroundSpaceMap A W L (fun x => W x * A x j * X x) := by
  ext σ
  simp only [restrictLast_apply, blockInsertedGroundSpaceMap_apply, Finset.sum_apply,
    insertedGroundSpaceMap_snoc _ _ hL]

/-- Fixing the first letter multiplies every boundary on the right.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedGroundSpaceMap_restrictFirst
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W X : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    {L : ℕ} (hL : 0 < L) (i : Fin d) :
    restrictFirst (blockInsertedGroundSpaceMap A W (L + 1) X) i =
      blockInsertedGroundSpaceMap A W L (fun x => X x * A x i * W x) := by
  ext σ
  simp only [restrictFirst_apply, blockInsertedGroundSpaceMap_apply, Finset.sum_apply,
    insertedGroundSpaceMap_cons _ _ hL]

/-- Simultaneous one-site injectivity propagates through arbitrary nonzero
block insertions, including singular or nilpotent ones.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedGroundSpaceMap_injective
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) {N : ℕ} (hN : 0 < N) :
    Function.Injective (blockInsertedGroundSpaceMap A W N) := by
  classical
  suffices h : ∀ n, Function.Injective (blockInsertedGroundSpaceMap A W (n + 1)) by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    exact h n
  intro n
  induction n with
  | zero =>
      rw [blockInsertedGroundSpaceMap_one]
      exact blockGroundSpaceMap_injective_of_wordTupleSpanTop hA
  | succ n ih =>
      refine (injective_iff_map_eq_zero _).mpr fun X hX => ?_
      have hzero (j : Fin d) : (fun x => W x * A x j * X x) = 0 := by
        apply ih
        rw [map_zero, ← blockInsertedGroundSpaceMap_restrictLast A W X (by omega) j,
          hX]
        rfl
      funext x
      obtain ⟨R, hR⟩ := exists_leftInverse_insertedLetters (A x)
        (hA.isInjective_one x) (W x) (hW x)
      calc
        X x = (∑ j, R j * W x * A x j) * X x := by rw [hR, Matrix.one_mul]
        _ = 0 := by
          rw [Finset.sum_mul]
          apply Finset.sum_eq_zero
          intro j _
          simpa only [Matrix.mul_assoc, Pi.zero_apply, Matrix.mul_zero] using
            congrArg (fun M => R j * M) (congrFun (hzero j) x)

/-- Positive-length inserted word tuples span the entire product algebra.
This is simultaneous spanning, rather than separate spanning of each block.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem span_range_blockInsertedEvalWord_eq_top
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) {N : ℕ} (hN : 0 < N) :
    Submodule.span ℂ (Set.range fun σ : Cfg d N =>
      fun x => insertedEvalWord (A x) (W x) (List.ofFn σ)) = ⊤ := by
  apply Matrix.family_submodule_eq_top_of_trace_separating
  intro X hX
  have hz : blockInsertedGroundSpaceMap A W N X = 0 := by
    ext σ
    simp only [blockInsertedGroundSpaceMap_apply, Finset.sum_apply,
      insertedGroundSpaceMap_apply, Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun x _ => Matrix.trace_mul_comm _ (X x))]
    exact hX _ (Submodule.subset_span (Set.mem_range_self σ))
  have := blockInsertedGroundSpaceMap_injective A hA W hW hN
    (hz.trans (map_zero _).symm)
  exact fun x => congrFun this x

/-- Joint extended boundary map in the existing diagonal-block Hilbert coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
noncomputable def blockInsertedBoundaryMap
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) (N : ℕ) :
    EuclideanSpace ℂ ((x : Fin r) × (Fin (dim x) × Fin (dim x))) →L[ℂ]
      EuclideanSpace ℂ (Cfg d N) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap.comp
      ((blockInsertedGroundSpaceMap A W N).comp blockBoundaryEquiv.toLinearMap)

/-- Hilbert and coefficient coordinates describe the same joint extended support.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem mem_range_blockInsertedBoundaryMap_iff
    (A : (x : Fin r) → MPSTensor d (dim x))
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ) (N : ℕ)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    v ∈ (blockInsertedBoundaryMap A W N).range ↔
      WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v ∈
        (blockInsertedGroundSpaceMap A W N).range := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨blockBoundaryEquiv X, rfl⟩
  · rintro ⟨X, hX⟩
    refine ⟨blockBoundaryEquiv.symm X, ?_⟩
    apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).injective
    exact hX

/-- Joint Hilbert boundary injectivity at every positive length.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedBoundaryMap_injective
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) {N : ℕ} (hN : 0 < N) :
    Function.Injective (blockInsertedBoundaryMap A W N) :=
  (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.injective.comp
    ((blockInsertedGroundSpaceMap_injective A hA W hW hN).comp blockBoundaryEquiv.injective)

/-- The joint extended support has dimension equal to the sum of the squared
block dimensions. Source: arXiv:2203.12563, line 319 and Section 5, lines 1695–1777. -/
theorem finrank_range_blockInsertedBoundaryMap
    (A : (x : Fin r) → MPSTensor d (dim x)) (hA : WordTupleSpanTop A 1)
    (W : (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, W x ≠ 0) {N : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (blockInsertedBoundaryMap A W N).range = ∑ x, dim x * dim x := by
  rw [LinearMap.finrank_range_of_inj (blockInsertedBoundaryMap_injective A hA W hW hN)]
  simp [Fintype.card_sigma]

/-- The joint boundary maps vary continuously with their tensor blocks and insertions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem continuous_blockInsertedBoundaryMap_family
    {X : Type*} [TopologicalSpace X]
    (A : X → (x : Fin r) → MPSTensor d (dim x))
    (hA : ∀ x, Continuous fun t => A t x)
    (W : X → (x : Fin r) → Matrix (Fin (dim x)) (Fin (dim x)) ℂ)
    (hW : ∀ x, Continuous fun t => W t x) (N : ℕ) :
    Continuous fun t => blockInsertedBoundaryMap (A t) (W t) N := by
  apply continuous_clm_apply.2
  intro v
  apply (EuclideanSpace.equiv (Cfg d N) ℂ).symm.continuous.comp
  change Continuous fun t => blockInsertedGroundSpaceMap (A t) (W t) N (blockBoundaryEquiv v)
  simp only [blockInsertedGroundSpaceMap_apply]
  apply continuous_finsetSum _ fun x _ => ?_
  exact continuous_pi fun σ =>
    ((continuous_insertedEvalWord_family (fun t => A t x) (hA x)
      (fun t => W t x) (hW x) (List.ofFn σ)).matrix_mul continuous_const).matrix_trace

end MPSTensor.MPOSymmetry
