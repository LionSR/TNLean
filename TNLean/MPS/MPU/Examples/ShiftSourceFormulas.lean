/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.ShiftSourceFactors
import QICLean.Channel.MaximallyEntangled

/-!
# Supplied source formulas for the cyclic-shift examples

This module evaluates the explicit supplied source factors from
`ShiftSourceFactors` for the three shift families of arXiv:1703.09188.  The
coordinate identifications retain the paper's tensor-factor order in equations
`eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` (lines 2009--2034).
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

/-- Explicit supplied source factors for the paper's identity family $U_1$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁SourceFactors (d : ℕ) :
    SourceFactors (shiftExampleU₁ d) (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  SourceFactors.independentTensorProductOfIdentityWeight (identitySourceFactors d)
    (identitySourceFactors d)

/-- Explicit supplied source factors for the paper's counter-shift family $U_2$.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2027). -/
noncomputable def shiftExampleU₂SourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (shiftExampleU₂ d)
      (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :=
  SourceFactors.independentTensorProductOfIdentityWeight (leftShiftSourceFactors d)
    (rightShiftSourceFactors d)

/-- Explicit supplied source factors for the paper's reversed counter-shift
family $U_3$.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3` and `eq:uv2_U3`
(lines 2009--2016 and 2028--2034). -/
noncomputable def shiftExampleU₃SourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (shiftExampleU₃ d)
      (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :=
  SourceFactors.independentTensorProductOfIdentityWeight (rightShiftSourceFactors d)
    (leftShiftSourceFactors d)

/-- Decode the two physical sites of a shift-family source matrix into their
four constituent $d$-dimensional spins, in site order.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3`, `eq:uv2_U2`, and
`eq:uv2_U3` (lines 2009--2034). -/
def shiftTwoSitePhysicalEquiv (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin (d * d) × Fin (d * d)) :=
  Equiv.prodCongr finProdFinEquiv finProdFinEquiv

/-- The matrix $\Id\otimes\Id$ on the two composite physical sites.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def identityTensorIdentityMatrix (d : ℕ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
    (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)

/-- Entry formula for the paper's $\Id\otimes\Id$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
@[simp] theorem identityTensorIdentityMatrix_apply (d : ℕ)
    (a b c e i j k l : Fin d) :
    identityTensorIdentityMatrix d ((a, b), (c, e)) ((i, j), (k, l)) =
      if a = i ∧ b = j ∧ c = k ∧ e = l then 1 else 0 := by
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    by_cases hc : c = k <;> by_cases he : e = l <;>
    simp [identityTensorIdentityMatrix, Matrix.kroneckerMap_apply,
      Prod.ext_iff, ha, hb, hc, he]

/-- The four-spin matrix $\Id\otimes\mathbb S\otimes\Id$, with the two
physical sites grouped as `((1, 2), (3, 4))`.

Source: arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3`
(lines 2018--2034). -/
noncomputable def identitySwapIdentityMatrix (d : ℕ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  fun ((a, b), (c, e)) ((i, j), (k, l)) ↦
    if a = i ∧ b = k ∧ c = j ∧ e = l then 1 else 0

/-- Entry formula for $\Id\otimes\mathbb S\otimes\Id$ in the paper's
four-spin order.

Source: arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3`
(lines 2018--2034). -/
@[simp] theorem identitySwapIdentityMatrix_apply (d : ℕ)
    (a b c e i j k l : Fin d) :
    identitySwapIdentityMatrix d ((a, b), (c, e)) ((i, j), (k, l)) =
      if a = i ∧ b = k ∧ c = j ∧ e = l then 1 else 0 := rfl

/-- The four-spin matrix $\mathbb S\otimes\mathbb S$, with the two swaps
acting on the pairs `(1, 2)` and `(3, 4)`.

Source: arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3`
(lines 2018--2034). -/
noncomputable def swapTensorSwapMatrix (d : ℕ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d))
      ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  Matrix.swapMatrix d ⊗ₖ Matrix.swapMatrix d

/-- Entry formula for $\mathbb S\otimes\mathbb S$ in the paper's four-spin
order.

Source: arXiv:1703.09188, equations `eq:uv2_U2` and `eq:uv2_U3`
(lines 2018--2034). -/
@[simp] theorem swapTensorSwapMatrix_apply (d : ℕ)
    (a b c e i j k l : Fin d) :
    swapTensorSwapMatrix d ((a, b), (c, e)) ((i, j), (k, l)) =
      if a = j ∧ b = i ∧ c = l ∧ e = k then 1 else 0 := by
  by_cases ha : a = j <;> by_cases hb : b = i <;>
    by_cases hc : c = l <;> by_cases he : e = k <;>
    simp [swapTensorSwapMatrix, Matrix.kroneckerMap_apply,
      Matrix.swapMatrix_apply, ha, hb, hc, he]

/-- Entry formula for
$(\mathbb S\otimes\mathbb S)(\Id\otimes\mathbb S\otimes\Id)$.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2021--2026). -/
@[simp] theorem swapTensorSwapMatrix_mul_identitySwapIdentityMatrix_apply
    (d : ℕ) (a b c e i j k l : Fin d) :
    (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
        ((a, b), (c, e)) ((i, j), (k, l)) =
      if a = k ∧ b = i ∧ c = l ∧ e = j then 1 else 0 := by
  classical
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [swapTensorSwapMatrix_apply, identitySwapIdentityMatrix_apply,
    ite_and, eq_comm]

/-- Entry formula for
$(\Id\otimes\mathbb S\otimes\Id)(\mathbb S\otimes\mathbb S)$.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2030--2034). -/
@[simp] theorem identitySwapIdentityMatrix_mul_swapTensorSwapMatrix_apply
    (d : ℕ) (a b c e i j k l : Fin d) :
    (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
        ((a, b), (c, e)) ((i, j), (k, l)) =
      if a = j ∧ b = l ∧ c = i ∧ e = k then 1 else 0 := by
  classical
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [swapTensorSwapMatrix_apply, identitySwapIdentityMatrix_apply,
    ite_and, eq_comm]

/-- The product coordinates are the left source coordinates of $U_1$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁LeftRankEquiv (d : ℕ) :
    Fin d × Fin d ≃ Fin ℓ[shiftExampleU₁ d] :=
  (Equiv.prodCongr (identityLeftRankEquiv d) (identityLeftRankEquiv d)).trans
    (tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d))

/-- The product coordinates are the right source coordinates of $U_1$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁RightRankEquiv (d : ℕ) :
    Fin d × Fin d ≃ Fin r[shiftExampleU₁ d] :=
  (Equiv.prodCongr (identityRightRankEquiv d) (identityRightRankEquiv d)).trans
    (tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d))

/-- The two nontrivial left-shift coordinates are the left source coordinates
of $U_2$; the right-shift left source has its unique value.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2027). -/
noncomputable def shiftExampleU₂LeftRankEquiv (d : ℕ) [NeZero d] :
    Fin d × Fin d ≃ Fin ℓ[shiftExampleU₂ d] :=
  (Equiv.prodUnique (Fin d × Fin d) (Fin 1)).symm |>.trans
    ((Equiv.prodCongr (leftShiftLeftRankEquiv d)
      (rightShiftLeftRankEquiv d)).trans
        (tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)))

/-- The two nontrivial right-shift coordinates are the right source
coordinates of $U_2$; the left-shift right source has its unique value.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2027). -/
noncomputable def shiftExampleU₂RightRankEquiv (d : ℕ) [NeZero d] :
    Fin d × Fin d ≃ Fin r[shiftExampleU₂ d] :=
  (Equiv.uniqueProd (Fin d × Fin d) (Fin 1)).symm |>.trans
    ((Equiv.prodCongr (leftShiftRightRankEquiv d)
      (rightShiftRightRankEquiv d)).trans
        (tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)))

/-- The two nontrivial left-shift coordinates are the left source coordinates
of $U_3$; the right-shift left source has its unique value.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3` and `eq:uv2_U3`
(lines 2009--2016 and 2028--2034). -/
noncomputable def shiftExampleU₃LeftRankEquiv (d : ℕ) [NeZero d] :
    Fin d × Fin d ≃ Fin ℓ[shiftExampleU₃ d] :=
  (Equiv.uniqueProd (Fin d × Fin d) (Fin 1)).symm |>.trans
    ((Equiv.prodCongr (rightShiftLeftRankEquiv d)
      (leftShiftLeftRankEquiv d)).trans
        (tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)))

/-- The two nontrivial right-shift coordinates are the right source
coordinates of $U_3$; the left-shift right source has its unique value.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3` and `eq:uv2_U3`
(lines 2009--2016 and 2028--2034). -/
noncomputable def shiftExampleU₃RightRankEquiv (d : ℕ) [NeZero d] :
    Fin d × Fin d ≃ Fin r[shiftExampleU₃ d] :=
  (Equiv.prodUnique (Fin d × Fin d) (Fin 1)).symm |>.trans
    ((Equiv.prodCongr (rightShiftRightRankEquiv d)
      (leftShiftRightRankEquiv d)).trans
        (tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)))

/-- Evaluation of the left source-rank coordinates of $U_1$.

Formalization coordinate identity for arXiv:1703.09188, equation
`eq:SF_u1_u3` (lines 2009--2016); the paper states the resulting source
matrix, not this intermediate equivalence. -/
@[simp] theorem shiftExampleU₁LeftRankEquiv_apply (d : ℕ) (a b : Fin d) :
    shiftExampleU₁LeftRankEquiv d (a, b) =
      tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d)
        (identityLeftRankEquiv d a, identityLeftRankEquiv d b) := rfl

/-- Evaluation of the right source-rank coordinates of $U_1$.

Formalization coordinate identity for arXiv:1703.09188, equation
`eq:SF_u1_u3` (lines 2009--2016); the paper states the resulting source
matrix, not this intermediate equivalence. -/
@[simp] theorem shiftExampleU₁RightRankEquiv_apply (d : ℕ) (a b : Fin d) :
    shiftExampleU₁RightRankEquiv d (a, b) =
      tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d)
        (identityRightRankEquiv d a, identityRightRankEquiv d b) := rfl

/-- Evaluation of the left source-rank coordinates of $U_2$.

Formalization coordinate identity for arXiv:1703.09188, equation `eq:uv2_U2`
(lines 2018--2027); the paper states the resulting source matrix, not this
intermediate equivalence. -/
@[simp] theorem shiftExampleU₂LeftRankEquiv_apply (d : ℕ) [NeZero d]
    (a b : Fin d) :
    shiftExampleU₂LeftRankEquiv d (a, b) =
      tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)
        (leftShiftLeftRankEquiv d (a, b), rightShiftLeftRankEquiv d 0) := rfl

/-- Evaluation of the right source-rank coordinates of $U_2$.

Formalization coordinate identity for arXiv:1703.09188, equation `eq:uv2_U2`
(lines 2018--2027); the paper states the resulting source matrix, not this
intermediate equivalence. -/
@[simp] theorem shiftExampleU₂RightRankEquiv_apply (d : ℕ) [NeZero d]
    (a b : Fin d) :
    shiftExampleU₂RightRankEquiv d (a, b) =
      tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)
        (leftShiftRightRankEquiv d 0, rightShiftRightRankEquiv d (a, b)) := rfl

/-- Evaluation of the left source-rank coordinates of $U_3$.

Formalization coordinate identity for arXiv:1703.09188, equations
`eq:SF_u1_u3` and `eq:uv2_U3` (lines 2009--2016 and 2028--2034); the paper
states the resulting source matrices, not this intermediate equivalence. -/
@[simp] theorem shiftExampleU₃LeftRankEquiv_apply (d : ℕ) [NeZero d]
    (a b : Fin d) :
    shiftExampleU₃LeftRankEquiv d (a, b) =
      tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)
        (rightShiftLeftRankEquiv d 0, leftShiftLeftRankEquiv d (a, b)) := rfl

/-- Evaluation of the right source-rank coordinates of $U_3$.

Formalization coordinate identity for arXiv:1703.09188, equations
`eq:SF_u1_u3` and `eq:uv2_U3` (lines 2009--2016 and 2028--2034); the paper
states the resulting source matrices, not this intermediate equivalence. -/
@[simp] theorem shiftExampleU₃RightRankEquiv_apply (d : ℕ) [NeZero d]
    (a b : Fin d) :
    shiftExampleU₃RightRankEquiv d (a, b) =
      tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)
        (rightShiftRightRankEquiv d (a, b), leftShiftRightRankEquiv d 0) := rfl

/-- Paper coordinates for the source row of $u_1$: the right-source pair is
followed by the left-source pair.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁SourceURowEquiv (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin ℓ[shiftExampleU₁ d] × Fin r[shiftExampleU₁ d]) :=
  (Equiv.prodComm (Fin d × Fin d) (Fin d × Fin d)).trans
    (Equiv.prodCongr (shiftExampleU₁LeftRankEquiv d)
      (shiftExampleU₁RightRankEquiv d))

/-- Paper coordinates for the source column of $v_1$: the right-source pair
is followed by the left-source pair.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁SourceVColumnEquiv (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin r[shiftExampleU₁ d] × Fin ℓ[shiftExampleU₁ d]) :=
  Equiv.prodCongr (shiftExampleU₁RightRankEquiv d)
    (shiftExampleU₁LeftRankEquiv d)

/-- Paper coordinates for the source row of $u_2^{(2)}$.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2027). -/
noncomputable def shiftExampleU₂SourceURowEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin ℓ[shiftExampleU₂ d] × Fin r[shiftExampleU₂ d]) :=
  Equiv.prodCongr (shiftExampleU₂LeftRankEquiv d)
    (shiftExampleU₂RightRankEquiv d)

/-- Coordinates for the source column of $v_2^{(2)}$.

The outer coordinate has the order $(r,\ell)$ fixed by the diagram defining
$v$ in arXiv:1703.09188, equation `vdagger` (lines 520--543).  Within each
primitive-shift rank, `Equiv.prodComm` changes the tensor-product rank order to
the four-spin order in which equation `eq:uv2_U2` is printed (lines
2018--2026).  This is an explicit formalization reindexing; the paper states
the resulting matrix, not this intermediate equivalence. -/
noncomputable def shiftExampleU₂SourceVColumnEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin r[shiftExampleU₂ d] × Fin ℓ[shiftExampleU₂ d]) :=
  (Equiv.prodCongr (Equiv.prodComm (Fin d) (Fin d))
      (Equiv.prodComm (Fin d) (Fin d))).trans
    (Equiv.prodCongr (shiftExampleU₂RightRankEquiv d)
      (shiftExampleU₂LeftRankEquiv d))

/-- Paper coordinates for the source row of $u_3^{(2)}$.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
noncomputable def shiftExampleU₃SourceURowEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin ℓ[shiftExampleU₃ d] × Fin r[shiftExampleU₃ d]) :=
  Equiv.prodCongr (shiftExampleU₃LeftRankEquiv d)
    (shiftExampleU₃RightRankEquiv d)

/-- Coordinates for the source column of $v_3^{(2)}$.

The outer coordinate has the order $(r,\ell)$ fixed by the diagram defining
$v$ in arXiv:1703.09188, equation `vdagger` (lines 520--543).  Within each
primitive-shift rank, `Equiv.prodComm` changes the tensor-product rank order to
the four-spin order in which equation `eq:uv2_U3` is printed (lines
2028--2034).  This is an explicit formalization reindexing; the paper states
the resulting matrix, not this intermediate equivalence. -/
noncomputable def shiftExampleU₃SourceVColumnEquiv (d : ℕ) [NeZero d] :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      (Fin r[shiftExampleU₃ d] × Fin ℓ[shiftExampleU₃ d]) :=
  (Equiv.prodCongr (Equiv.prodComm (Fin d) (Fin d))
      (Equiv.prodComm (Fin d) (Fin d))).trans
    (Equiv.prodCongr (shiftExampleU₃RightRankEquiv d)
      (shiftExampleU₃LeftRankEquiv d))

/-- Reorder two pairs so that the $u_3$ source coordinates exhibit one swap.

After expanding the product ranks in the outer $(\ell,r)$ order fixed by the
diagram defining $u$ in arXiv:1703.09188, equation `uu` (lines 532--543), this
map sends $((a,b),(c,e))$ to $((e,b),(c,a))$.  It thereby gives the two
composite indices in which equation `eq:SF_u1_u3` prints $u_3=\mathbb S$
(lines 2009--2016).  This shuffle is formalization infrastructure; the paper
states the final swap, not the intermediate reindexing. -/
def shiftExampleU₃SourceUSwapShuffle (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      ((Fin d × Fin d) × (Fin d × Fin d)) where
  toFun x := ((x.2.2, x.1.2), (x.2.1, x.1.1))
  invFun x := ((x.2.2, x.1.2), (x.2.1, x.1.1))
  left_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

/-- Reorder two pairs so that the $v_3$ source coordinates exhibit one swap.

After expanding the product ranks in the outer $(r,\ell)$ order fixed by the
diagram defining $v$ in arXiv:1703.09188, equation `vdagger` (lines 520--543),
this map sends $((a,b),(c,e))$ to $((a,c),(b,e))$.  It thereby gives the two
composite indices in which equation `eq:SF_u1_u3` prints $v_3=\mathbb S$
(lines 2009--2016).  This shuffle is formalization infrastructure; the paper
states the final swap, not the intermediate reindexing. -/
def shiftExampleU₃SourceVSwapShuffle (d : ℕ) :
    ((Fin d × Fin d) × (Fin d × Fin d)) ≃
      ((Fin d × Fin d) × (Fin d × Fin d)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

/-- Composite-site coordinates for the source row of the paper's $u_3$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₃SwapSourceURowEquiv (d : ℕ) [NeZero d] :
    (Fin (d * d) × Fin (d * d)) ≃
      (Fin ℓ[shiftExampleU₃ d] × Fin r[shiftExampleU₃ d]) :=
  ((Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
    (shiftExampleU₃SourceUSwapShuffle d)).trans
      (Equiv.prodCongr (shiftExampleU₃LeftRankEquiv d)
        (shiftExampleU₃RightRankEquiv d))

/-- Composite-site coordinates for the source column of the paper's $v_3$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₃SwapSourceVColumnEquiv (d : ℕ) [NeZero d] :
    (Fin (d * d) × Fin (d * d)) ≃
      (Fin r[shiftExampleU₃ d] × Fin ℓ[shiftExampleU₃ d]) :=
  ((Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
    (shiftExampleU₃SourceVSwapShuffle d)).trans
      (Equiv.prodCongr (shiftExampleU₃RightRankEquiv d)
        (shiftExampleU₃LeftRankEquiv d))

/-- Evaluation of the composite-site source-row coordinates exhibiting
$u_3=\mathbb S$.

Formalization coordinate identity for arXiv:1703.09188, equations `uu` and
`eq:SF_u1_u3` (lines 532--543 and 2009--2016); the paper states the final
swap, not this intermediate equivalence. -/
@[simp] theorem shiftExampleU₃SwapSourceURowEquiv_apply (d : ℕ) [NeZero d]
    (a b c e : Fin d) :
    shiftExampleU₃SwapSourceURowEquiv d
        (finProdFinEquiv (a, b), finProdFinEquiv (c, e)) =
      (shiftExampleU₃LeftRankEquiv d (e, b),
        shiftExampleU₃RightRankEquiv d (c, a)) := by
  simp [shiftExampleU₃SwapSourceURowEquiv,
    shiftExampleU₃SourceUSwapShuffle]

/-- Evaluation of the composite-site source-column coordinates exhibiting
$v_3=\mathbb S$.

Formalization coordinate identity for arXiv:1703.09188, equations `vdagger`
and `eq:SF_u1_u3` (lines 520--543 and 2009--2016); the paper states the final
swap, not this intermediate equivalence. -/
@[simp] theorem shiftExampleU₃SwapSourceVColumnEquiv_apply (d : ℕ) [NeZero d]
    (a b c e : Fin d) :
    shiftExampleU₃SwapSourceVColumnEquiv d
        (finProdFinEquiv (a, b), finProdFinEquiv (c, e)) =
      (shiftExampleU₃RightRankEquiv d (a, c),
        shiftExampleU₃LeftRankEquiv d (b, e)) := by
  simp [shiftExampleU₃SwapSourceVColumnEquiv,
    shiftExampleU₃SourceVSwapShuffle]

private theorem shiftExampleU₂_sourceU_product_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        (tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)
            (leftShiftLeftRankEquiv d (a, b), rightShiftLeftRankEquiv d 0),
          tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)
            (leftShiftRightRankEquiv d 0, rightShiftRightRankEquiv d (c, e)))
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) =
      SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (a, b), leftShiftRightRankEquiv d 0) (i, k) *
        SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (c, e)) (j, l) := by
  simpa only [shiftExampleU₂, shiftExampleU₂SourceFactors] using
    SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply
      (leftShiftSourceFactors d) (rightShiftSourceFactors d)
      (leftShiftLeftRankEquiv d (a, b)) (rightShiftLeftRankEquiv d 0)
      (leftShiftRightRankEquiv d 0) (rightShiftRightRankEquiv d (c, e)) i k j l

/-- Entry formula for the supplied source $u$ of $U_2$ in the four-spin
coordinates used by the paper's two-site standard form.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_sourceU_fourSpin_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        (shiftExampleU₂SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      identitySwapIdentityMatrix d ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [show shiftExampleU₂SourceURowEquiv d ((a, b), (c, e)) =
      (tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftLeftRankEquiv d (a, b), rightShiftLeftRankEquiv d 0),
        tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftRightRankEquiv d 0, rightShiftRightRankEquiv d (c, e))) by rfl,
    show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl]
  calc
    _ = SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (a, b), leftShiftRightRankEquiv d 0) (i, k) *
        SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (c, e))
            (j, l) := shiftExampleU₂_sourceU_product_apply d a b c e i j k l
    _ = _ := by
      rw [sourceU_leftShiftSourceFactors_apply,
        sourceU_rightShiftSourceFactors_apply]
      by_cases ha : a = i <;> by_cases hb : b = k <;>
        by_cases hc : c = j <;> by_cases he : e = l <;>
        simp [identitySwapIdentityMatrix, ha, hb, hc, he,
          shiftSourceScale_cancel d]

/-- In the four-spin coordinates used by the two-site standard form, the
supplied source $u$ of $U_2$ is $\Id\otimes\mathbb S\otimes\Id$.

Its occurrence as the central gate $u_2^{(2)}$ in the actual two-site block is
the content of `shiftExampleU₂_blockTwo_apply_eq_sum_X₁_mul_u₂_two_mul_Y₂`.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_sourceU_reindex_eq_identitySwapIdentity
    (d : ℕ) [NeZero d] :
    Matrix.reindex (shiftExampleU₂SourceURowEquiv d).symm
        (shiftTwoSitePhysicalEquiv d).symm
        (SourceFactors.sourceU (shiftExampleU₂ d)
          (shiftExampleU₂SourceFactors d)) =
      identitySwapIdentityMatrix d := by
  ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm] using
    shiftExampleU₂_sourceU_fourSpin_apply d a b c e i j k l

private theorem shiftExampleU₂_sourceV_product_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceV (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l))
        (tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)
            (leftShiftRightRankEquiv d 0, rightShiftRightRankEquiv d (b, a)),
          tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)
            (leftShiftLeftRankEquiv d (e, c), rightShiftLeftRankEquiv d 0)) =
      SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
          (i, k) (leftShiftRightRankEquiv d 0, leftShiftLeftRankEquiv d (e, c)) *
        SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
          (j, l) (rightShiftRightRankEquiv d (b, a),
            rightShiftLeftRankEquiv d 0) := by
  simpa only [shiftExampleU₂, shiftExampleU₂SourceFactors] using
    SourceFactors.sourceV_independentTensorProductOfIdentityWeight_apply
      (leftShiftSourceFactors d) (rightShiftSourceFactors d) i k j l
      (leftShiftRightRankEquiv d 0) (rightShiftRightRankEquiv d (b, a))
      (leftShiftLeftRankEquiv d (e, c)) (rightShiftLeftRankEquiv d 0)

/-- Entry formula for the supplied source $v$ of $U_2$ in the four-spin
coordinates used by the paper's reflected two-site standard form.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_sourceV_fourSpin_apply (d : ℕ) [NeZero d]
    (i j k l a b c e : Fin d) :
    SourceFactors.sourceV (shiftExampleU₂ d) (shiftExampleU₂SourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₂SourceVColumnEquiv d ((a, b), (c, e))) =
      (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)
        ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl,
    show shiftExampleU₂SourceVColumnEquiv d ((a, b), (c, e)) =
      (tensorProductRightRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftRightRankEquiv d 0, rightShiftRightRankEquiv d (b, a)),
        tensorProductLeftRankEquiv (leftShiftTensor d) (rightShiftTensor d)
          (leftShiftLeftRankEquiv d (e, c), rightShiftLeftRankEquiv d 0)) by rfl]
  calc
    _ = SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
          (i, k) (leftShiftRightRankEquiv d 0, leftShiftLeftRankEquiv d (e, c)) *
        SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
          (j, l) (rightShiftRightRankEquiv d (b, a),
            rightShiftLeftRankEquiv d 0) :=
      shiftExampleU₂_sourceV_product_apply d a b c e i j k l
    _ = _ := by
      rw [sourceV_leftShiftSourceFactors_apply,
        sourceV_rightShiftSourceFactors_apply]
      by_cases ha : j = a <;> by_cases hb : l = b <;>
        by_cases hc : i = c <;> by_cases he : k = e <;>
        simp [ha, hb, hc, he, shiftSourceScale_cancel_rev d] <;> aesop

/-- In the four-spin coordinates used by the reflected two-site standard form,
the supplied source $v$ of $U_2$ is
$(\mathbb S\otimes\mathbb S)(\Id\otimes\mathbb S\otimes\Id)$.

Its occurrence as the central gate $v_2^{(2)}$ in the actual two-site block is
the content of
`shiftExampleU₂_blockTwo_apply_eq_sum_X₂_mul_v₂_two_reflected_mul_Y₁`.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2026). -/
theorem shiftExampleU₂_sourceV_reindex_eq_swapSwap_mul_identitySwapIdentity
    (d : ℕ) [NeZero d] :
    Matrix.reindex (shiftTwoSitePhysicalEquiv d).symm
        (shiftExampleU₂SourceVColumnEquiv d).symm
        (SourceFactors.sourceV (shiftExampleU₂ d)
          (shiftExampleU₂SourceFactors d)) =
      swapTensorSwapMatrix d * identitySwapIdentityMatrix d := by
  ext ⟨⟨i, j⟩, ⟨k, l⟩⟩ ⟨⟨a, b⟩, ⟨c, e⟩⟩
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm] using
    shiftExampleU₂_sourceV_fourSpin_apply d i j k l a b c e

private theorem shiftExampleU₃_sourceU_product_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        (tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)
            (rightShiftLeftRankEquiv d 0, leftShiftLeftRankEquiv d (a, b)),
          tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)
            (rightShiftRightRankEquiv d (c, e), leftShiftRightRankEquiv d 0))
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) =
      SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (c, e)) (i, k) *
        SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (a, b), leftShiftRightRankEquiv d 0) (j, l) := by
  simpa only [shiftExampleU₃, shiftExampleU₃SourceFactors] using
    SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply
      (rightShiftSourceFactors d) (leftShiftSourceFactors d)
      (rightShiftLeftRankEquiv d 0) (leftShiftLeftRankEquiv d (a, b))
      (rightShiftRightRankEquiv d (c, e)) (leftShiftRightRankEquiv d 0) i k j l

/-- Entry formula for the supplied source $u$ of $U_3$ in the four-spin
coordinates used by the paper's two-site standard form.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_sourceU_fourSpin_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        (shiftExampleU₃SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      (identitySwapIdentityMatrix d * swapTensorSwapMatrix d)
        ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [show shiftExampleU₃SourceURowEquiv d ((a, b), (c, e)) =
      (tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftLeftRankEquiv d 0, leftShiftLeftRankEquiv d (a, b)),
        tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftRightRankEquiv d (c, e), leftShiftRightRankEquiv d 0)) by rfl,
    show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl]
  calc
    _ = SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (c, e)) (i, k) *
        SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (a, b), leftShiftRightRankEquiv d 0)
            (j, l) := shiftExampleU₃_sourceU_product_apply d a b c e i j k l
    _ = _ := by
      rw [sourceU_rightShiftSourceFactors_apply,
        sourceU_leftShiftSourceFactors_apply]
      by_cases ha : a = j <;> by_cases hb : b = l <;>
        by_cases hc : c = i <;> by_cases he : e = k <;>
        simp [ha, hb, hc, he, shiftSourceScale_cancel_rev d]

/-- In the four-spin coordinates used by the two-site standard form, the
supplied source $u$ of $U_3$ is
$(\Id\otimes\mathbb S\otimes\Id)(\mathbb S\otimes\mathbb S)$.

Its occurrence as the central gate $u_3^{(2)}$ in the actual two-site block is
the content of `shiftExampleU₃_blockTwo_apply_eq_sum_X₁_mul_u₃_two_mul_Y₂`.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_sourceU_reindex_eq_identitySwapIdentity_mul_swapSwap
    (d : ℕ) [NeZero d] :
    Matrix.reindex (shiftExampleU₃SourceURowEquiv d).symm
        (shiftTwoSitePhysicalEquiv d).symm
        (SourceFactors.sourceU (shiftExampleU₃ d)
          (shiftExampleU₃SourceFactors d)) =
      identitySwapIdentityMatrix d * swapTensorSwapMatrix d := by
  ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm] using
    shiftExampleU₃_sourceU_fourSpin_apply d a b c e i j k l

private theorem shiftExampleU₃_sourceV_product_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceV (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l))
        (tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)
            (rightShiftRightRankEquiv d (b, a), leftShiftRightRankEquiv d 0),
          tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)
            (rightShiftLeftRankEquiv d 0, leftShiftLeftRankEquiv d (e, c))) =
      SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
          (i, k) (rightShiftRightRankEquiv d (b, a),
            rightShiftLeftRankEquiv d 0) *
        SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
          (j, l) (leftShiftRightRankEquiv d 0,
            leftShiftLeftRankEquiv d (e, c)) := by
  simpa only [shiftExampleU₃, shiftExampleU₃SourceFactors] using
    SourceFactors.sourceV_independentTensorProductOfIdentityWeight_apply
      (rightShiftSourceFactors d) (leftShiftSourceFactors d) i k j l
      (rightShiftRightRankEquiv d (b, a)) (leftShiftRightRankEquiv d 0)
      (rightShiftLeftRankEquiv d 0) (leftShiftLeftRankEquiv d (e, c))

/-- Entry formula for the supplied source $v$ of $U_3$ in the four-spin
coordinates used by the paper's reflected two-site standard form.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_sourceV_fourSpin_apply (d : ℕ) [NeZero d]
    (i j k l a b c e : Fin d) :
    SourceFactors.sourceV (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₃SourceVColumnEquiv d ((a, b), (c, e))) =
      identitySwapIdentityMatrix d ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl,
    show shiftExampleU₃SourceVColumnEquiv d ((a, b), (c, e)) =
      (tensorProductRightRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftRightRankEquiv d (b, a), leftShiftRightRankEquiv d 0),
        tensorProductLeftRankEquiv (rightShiftTensor d) (leftShiftTensor d)
          (rightShiftLeftRankEquiv d 0, leftShiftLeftRankEquiv d (e, c))) by rfl]
  calc
    _ = SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
          (i, k) (rightShiftRightRankEquiv d (b, a),
            rightShiftLeftRankEquiv d 0) *
        SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
          (j, l) (leftShiftRightRankEquiv d 0,
            leftShiftLeftRankEquiv d (e, c)) :=
      shiftExampleU₃_sourceV_product_apply d a b c e i j k l
    _ = _ := by
      rw [sourceV_rightShiftSourceFactors_apply,
        sourceV_leftShiftSourceFactors_apply]
      by_cases ha : i = a <;> by_cases hb : k = b <;>
        by_cases hc : j = c <;> by_cases he : l = e <;>
        simp [identitySwapIdentityMatrix, ha, hb, hc, he,
          shiftSourceScale_cancel d] <;> aesop

/-- In the four-spin coordinates used by the reflected two-site standard form,
the supplied source $v$ of $U_3$ is $\Id\otimes\mathbb S\otimes\Id$.

Its occurrence as the central gate $v_3^{(2)}$ in the actual two-site block is
the content of
`shiftExampleU₃_blockTwo_apply_eq_sum_X₂_mul_v₃_two_reflected_mul_Y₁`.

Source: arXiv:1703.09188, equation `eq:uv2_U3` (lines 2028--2034). -/
theorem shiftExampleU₃_sourceV_reindex_eq_identitySwapIdentity
    (d : ℕ) [NeZero d] :
    Matrix.reindex (shiftTwoSitePhysicalEquiv d).symm
        (shiftExampleU₃SourceVColumnEquiv d).symm
        (SourceFactors.sourceV (shiftExampleU₃ d)
          (shiftExampleU₃SourceFactors d)) =
      identitySwapIdentityMatrix d := by
  ext ⟨⟨i, j⟩, ⟨k, l⟩⟩ ⟨⟨a, b⟩, ⟨c, e⟩⟩
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm] using
    shiftExampleU₃_sourceV_fourSpin_apply d i j k l a b c e

private theorem shiftExampleU₁_sourceU_product_apply (d : ℕ)
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₁ d) (shiftExampleU₁SourceFactors d)
        (tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d)
            (identityLeftRankEquiv d c, identityLeftRankEquiv d e),
          tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d)
            (identityRightRankEquiv d a, identityRightRankEquiv d b))
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) =
      SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
          (identityLeftRankEquiv d c, identityRightRankEquiv d a) (i, k) *
        SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
          (identityLeftRankEquiv d e, identityRightRankEquiv d b) (j, l) := by
  simpa only [shiftExampleU₁, shiftExampleU₁SourceFactors] using
    SourceFactors.sourceU_independentTensorProductOfIdentityWeight_apply
      (identitySourceFactors d) (identitySourceFactors d)
      (identityLeftRankEquiv d c) (identityLeftRankEquiv d e)
      (identityRightRankEquiv d a) (identityRightRankEquiv d b) i k j l

/-- Entry formula for the supplied $u_1=\Id\otimes\Id$ in the paper's source
coordinates.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₁_sourceU_apply (d : ℕ)
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₁ d) (shiftExampleU₁SourceFactors d)
        (shiftExampleU₁SourceURowEquiv d ((a, b), (c, e)))
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l))) =
      identityTensorIdentityMatrix d ((a, b), (c, e)) ((i, j), (k, l)) := by
  rw [show shiftExampleU₁SourceURowEquiv d ((a, b), (c, e)) =
      (tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityLeftRankEquiv d c, identityLeftRankEquiv d e),
        tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityRightRankEquiv d a, identityRightRankEquiv d b)) by rfl,
    show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl]
  calc
    _ = SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
          (identityLeftRankEquiv d c, identityRightRankEquiv d a) (i, k) *
        SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
          (identityLeftRankEquiv d e, identityRightRankEquiv d b)
            (j, l) := shiftExampleU₁_sourceU_product_apply d a b c e i j k l
    _ = _ := by
      rw [sourceU_identitySourceFactors_apply,
        sourceU_identitySourceFactors_apply]
      by_cases ha : a = i <;> by_cases hb : b = j <;>
        by_cases hc : c = k <;> by_cases he : e = l <;>
        simp [identityTensorIdentityMatrix_apply, ha, hb, hc, he]

private theorem shiftExampleU₁_sourceV_product_apply (d : ℕ)
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceV (shiftExampleU₁ d) (shiftExampleU₁SourceFactors d)
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l))
        (tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d)
            (identityRightRankEquiv d a, identityRightRankEquiv d b),
          tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d)
            (identityLeftRankEquiv d c, identityLeftRankEquiv d e)) =
      SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
          (i, k) (identityRightRankEquiv d a, identityLeftRankEquiv d c) *
        SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
          (j, l) (identityRightRankEquiv d b, identityLeftRankEquiv d e) := by
  simpa only [shiftExampleU₁, shiftExampleU₁SourceFactors] using
    SourceFactors.sourceV_independentTensorProductOfIdentityWeight_apply
      (identitySourceFactors d) (identitySourceFactors d) i k j l
      (identityRightRankEquiv d a) (identityRightRankEquiv d b)
      (identityLeftRankEquiv d c) (identityLeftRankEquiv d e)

/-- Entry formula for the supplied $v_1=\Id\otimes\Id$ in the paper's source
coordinates.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₁_sourceV_apply (d : ℕ)
    (i j k l a b c e : Fin d) :
    SourceFactors.sourceV (shiftExampleU₁ d) (shiftExampleU₁SourceFactors d)
        (shiftTwoSitePhysicalEquiv d ((i, j), (k, l)))
        (shiftExampleU₁SourceVColumnEquiv d ((a, b), (c, e))) =
      identityTensorIdentityMatrix d ((i, j), (k, l)) ((a, b), (c, e)) := by
  rw [show shiftTwoSitePhysicalEquiv d ((i, j), (k, l)) =
      (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) by rfl,
    show shiftExampleU₁SourceVColumnEquiv d ((a, b), (c, e)) =
      (tensorProductRightRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityRightRankEquiv d a, identityRightRankEquiv d b),
        tensorProductLeftRankEquiv (identityMPUTensor d) (identityMPUTensor d)
          (identityLeftRankEquiv d c, identityLeftRankEquiv d e)) by rfl]
  calc
    _ = SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
          (i, k) (identityRightRankEquiv d a, identityLeftRankEquiv d c) *
        SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
          (j, l) (identityRightRankEquiv d b,
            identityLeftRankEquiv d e) :=
      shiftExampleU₁_sourceV_product_apply d a b c e i j k l
    _ = _ := by
      rw [sourceV_identitySourceFactors_apply,
        sourceV_identitySourceFactors_apply]
      by_cases ha : i = a <;> by_cases hb : j = b <;>
        by_cases hc : k = c <;> by_cases he : l = e <;>
        simp [identityTensorIdentityMatrix_apply, ha, hb, hc, he] <;> aesop

/-- For the supplied factors of $U_1$, both paper source gates are
$u_1=v_1=\Id\otimes\Id$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₁_sourceUV_eq_identityTensorIdentity (d : ℕ) :
    Matrix.reindex (shiftExampleU₁SourceURowEquiv d).symm
        (shiftTwoSitePhysicalEquiv d).symm
        (SourceFactors.sourceU (shiftExampleU₁ d)
          (shiftExampleU₁SourceFactors d)) = identityTensorIdentityMatrix d ∧
      Matrix.reindex (shiftTwoSitePhysicalEquiv d).symm
        (shiftExampleU₁SourceVColumnEquiv d).symm
        (SourceFactors.sourceV (shiftExampleU₁ d)
          (shiftExampleU₁SourceFactors d)) = identityTensorIdentityMatrix d := by
  constructor
  · ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm] using
      shiftExampleU₁_sourceU_apply d a b c e i j k l
  · ext ⟨⟨i, j⟩, ⟨k, l⟩⟩ ⟨⟨a, b⟩, ⟨c, e⟩⟩
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm] using
      shiftExampleU₁_sourceV_apply d i j k l a b c e

/-- Entry formula for the supplied $u_3=\mathbb S$ in the paper's
composite-site source coordinates.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₃_sourceU_eq_swap_apply (d : ℕ) [NeZero d]
    (a b c e i j k l : Fin d) :
    SourceFactors.sourceU (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        (shiftExampleU₃SwapSourceURowEquiv d
          (finProdFinEquiv (a, b), finProdFinEquiv (c, e)))
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) =
      Matrix.swapMatrix (d * d)
        (finProdFinEquiv (a, b), finProdFinEquiv (c, e))
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l)) := by
  rw [shiftExampleU₃SwapSourceURowEquiv_apply,
    shiftExampleU₃LeftRankEquiv_apply,
    shiftExampleU₃RightRankEquiv_apply]
  calc
    _ = SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
          (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (c, a)) (i, k) *
        SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
          (leftShiftLeftRankEquiv d (e, b), leftShiftRightRankEquiv d 0)
            (j, l) := shiftExampleU₃_sourceU_product_apply d e b c a i j k l
    _ = _ := by
      rw [sourceU_rightShiftSourceFactors_apply,
        sourceU_leftShiftSourceFactors_apply, Matrix.swapMatrix_apply]
      by_cases ha : a = k <;> by_cases hb : b = l <;>
        by_cases hc : c = i <;> by_cases he : e = j <;>
        simp [ha, hb, hc, he, shiftSourceScale_cancel_rev d]

/-- Entry formula for the supplied $v_3=\mathbb S$ in the paper's
composite-site source coordinates.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₃_sourceV_eq_swap_apply (d : ℕ) [NeZero d]
    (i j k l a b c e : Fin d) :
    SourceFactors.sourceV (shiftExampleU₃ d) (shiftExampleU₃SourceFactors d)
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l))
        (shiftExampleU₃SwapSourceVColumnEquiv d
          (finProdFinEquiv (a, b), finProdFinEquiv (c, e))) =
      Matrix.swapMatrix (d * d)
        (finProdFinEquiv (i, j), finProdFinEquiv (k, l))
        (finProdFinEquiv (a, b), finProdFinEquiv (c, e)) := by
  rw [shiftExampleU₃SwapSourceVColumnEquiv_apply,
    shiftExampleU₃RightRankEquiv_apply,
    shiftExampleU₃LeftRankEquiv_apply]
  calc
    _ = SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
          (i, k) (rightShiftRightRankEquiv d (a, c),
            rightShiftLeftRankEquiv d 0) *
        SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
          (j, l) (leftShiftRightRankEquiv d 0,
            leftShiftLeftRankEquiv d (b, e)) :=
      shiftExampleU₃_sourceV_product_apply d c a e b i j k l
    _ = _ := by
      rw [sourceV_rightShiftSourceFactors_apply,
        sourceV_leftShiftSourceFactors_apply, Matrix.swapMatrix_apply]
      by_cases ha : k = a <;> by_cases hb : l = b <;>
        by_cases hc : i = c <;> by_cases he : j = e <;>
        simp [ha, hb, hc, he, shiftSourceScale_cancel d] <;> aesop

/-- For the supplied factors of $U_3$, both unblocked paper source gates are
$u_3=v_3=\mathbb S$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem shiftExampleU₃_sourceUV_eq_swap (d : ℕ) [NeZero d] :
    Matrix.reindex (shiftExampleU₃SwapSourceURowEquiv d).symm
        (Equiv.refl _)
        (SourceFactors.sourceU (shiftExampleU₃ d)
          (shiftExampleU₃SourceFactors d)) = Matrix.swapMatrix (d * d) ∧
      Matrix.reindex (Equiv.refl _)
        (shiftExampleU₃SwapSourceVColumnEquiv d).symm
        (SourceFactors.sourceV (shiftExampleU₃ d)
          (shiftExampleU₃SourceFactors d)) = Matrix.swapMatrix (d * d) := by
  constructor
  · ext row col
    obtain ⟨⟨⟨a, b⟩, ⟨c, e⟩⟩, rfl⟩ :=
      (shiftTwoSitePhysicalEquiv d).surjective row
    obtain ⟨⟨⟨i, j⟩, ⟨k, l⟩⟩, rfl⟩ :=
      (shiftTwoSitePhysicalEquiv d).surjective col
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, Equiv.refl_symm, Equiv.refl_apply,
      shiftTwoSitePhysicalEquiv, Equiv.prodCongr_apply, Prod.map_apply'] using
      shiftExampleU₃_sourceU_eq_swap_apply d a b c e i j k l
  · ext row col
    obtain ⟨⟨⟨i, j⟩, ⟨k, l⟩⟩, rfl⟩ :=
      (shiftTwoSitePhysicalEquiv d).surjective row
    obtain ⟨⟨⟨a, b⟩, ⟨c, e⟩⟩, rfl⟩ :=
      (shiftTwoSitePhysicalEquiv d).surjective col
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, Equiv.refl_symm, Equiv.refl_apply,
      shiftTwoSitePhysicalEquiv, Equiv.prodCongr_apply, Prod.map_apply'] using
      shiftExampleU₃_sourceV_eq_swap_apply d i j k l a b c e

end MPOTensor
