/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSumPermutation
import QICLean.Spectral.Eigenvalue.HermitianExtremalEigenvalues
import TNLean.MPS.CanonicalForm.BNT.Basic
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.Operator.PairAlphabet
import TNLean.MPS.Operator.Product.PhysicalAdjoint
import TNLean.MPS.Tensor.DirectSum.BlockAssembly

/-!
# Vertical canonical form for MPO tensors

This file introduces the vertically viewed tensor of an MPO and the vertical
canonical-form structure used in the MPDO analysis of arXiv:1606.00608,
Section 4.4.

The vertical direction is obtained by exchanging the notion of physical and
virtual indices (arXiv:1606.00608, line 943): the vertically viewed tensor has
its letters indexed by the horizontal bond pair $(a, b)$, and each letter is
the operator on the physical space with matrix elements
$(\widetilde M_{ab})_{ij} = M^{ij}_{ab}$. Proposition 4.13 of arXiv:1606.00608
(lines 1863--1870) concludes that, after an isometry $U$ on
the physical space, this tensor is a direct sum
$U \widetilde M U^\dagger = \bigoplus_\alpha \mu_\alpha \otimes M_\alpha$,
where the $\mu_\alpha$ are positive diagonal matrices and the $M_\alpha$ form a basis of
normal tensors (BNT). Since each $\mu_\alpha$ is diagonal, the summand
$\mu_\alpha \otimes M_\alpha$
equals the direct sum $\bigoplus_k \omega_{\alpha,k} M_\alpha$ of its diagonal entries, so the
right-hand side is the block-diagonal tensor over the pairs $(\alpha, k)$ in which
the multiplicities $r_\alpha$ and the diagonal entries $\omega_{\alpha,k}$ stay explicit;
the coefficients $m_\alpha = \operatorname{tr}(\mu_\alpha)$ appearing in the
renormalization fixed-point characterization are recovered from them.
The predicate `IsVerticalCF` states this conclusion after the zero physical
sector has been discarded, as allowed in the source's canonical-form
construction (arXiv:1606.00608, lines 214--225).

## Main definitions

* `verticalTensor`:
  the vertically viewed tensor, with letters indexed by the horizontal bond
  pair and matrices acting on the physical space (arXiv:1606.00608, line 943).
* `diagonalTensor`:
  the MPS tensor `i ↦ M i i` extracted from the diagonal MPO entries; its
  coefficients are the diagonal entries $\langle\sigma|\rho^{(N)}(M)|\sigma\rangle$ of the
  generated operator.
* `IsVerticalCF`:
  the vertical canonical form of arXiv:1606.00608, Proposition 4.13: an
  isometry after restriction to the nonzero physical sectors, represented by
  a coisometry $U$ with
  $U \widetilde M_{ab} U^\dagger = (\bigoplus_\alpha \mu_\alpha \otimes M_\alpha)_{ab}$
  for every bond pair $(a, b)$, with positive diagonal matrices $\mu_\alpha$ and a
  BNT $\{M_\alpha\}$ for the vertically viewed tensor.
* `MPSTensor.diagBlock`:
  the diagonal restriction `B ↦ (i ↦ B (i, i))` of a pair-alphabet block.

## Main results (toward Proposition 4.13)

* `mpv_diagonalTensor`:
  the MPV of `diagonalTensor M` at `σ` equals the MPV of `M` on the pair alphabet at
  the diagonal-paired configuration `k ↦ (σ k, σ k)`.
* `mpv_diagonalTensor_eq_blocks`:
  under a horizontal canonical form, `diagonalTensor M` shares its MPV family with
  the single-spin block-diagonal assembly of the diagonally-restricted blocks.
* `mpv_diagonalTensor_eq_mpo_diag` / `mpv_diagonalTensor_nonneg`:
  the diagonal-tensor MPV equals the density-operator diagonal
  $\langle\sigma|\rho^{(N)}(M)|\sigma\rangle$, hence is nonnegative when `M` generates an MPDO.
* `Matrix.IsHermitian.opposite_corner_eq_zero` / `mpo_opposite_corner_eq_zero`:
  the positivity identity `P H = P H P ⇒ (1 - P) H P = 0` used in the first
  step of Proposition 4.13.
* `mpo_compress_posSemidef` / `mpo_compress_trace_pos`:
  Hermitian compressions of an MPDO density operator are positive
  semidefinite, and nonzero compressions have positive trace; applied to the
  sector projectors $P_{\alpha,k}$ this is the positivity of lines 1899--1903
  of Proposition 4.13.
* `mpv_verticalAssembledTensor_eq_sum`:
  the MPV of the vertical-assembled tensor as a sum over the flattened
  `(block, multiplicity)` index.
* `sameMPV₂_toTensorFromBlocks_verticalAssembledTensor_of_equiv`:
  regrouping an indexed block family along a copy-label equivalence preserves
  its full MPV family.
The results above supply matrix-product-vector identities and elementary
positivity consequences, but do not give the passage from horizontal to
vertical canonical form in arXiv:1606.00608, Proposition 4.13. That theorem
requires an independent canonical-form decomposition of the tensor viewed in
the vertical direction.
Its basis cannot be obtained by diagonally restricting the horizontal blocks:
the finite-dimensional obstruction is proved in
`TNLean.MPS.MPDO.BiCFDerivation.DiagonalRestrictionCounterexample` and documented
in `docs/paper-gaps/cpgsv17_vertical_diagonal_restriction.tex`. A source-faithful
argument must instead follow arXiv:1606.00608, lines 1873--1921, using MPDO
positivity and Lemma L to establish an independent vertical canonical form and
then proving positivity of its weights.  The doubled-index coefficient
identification in the first step is formalized in
`TNLean.MPS.MPDO.PerCopyHorizontalCF`. The one-sided operator identity and its
blockwise consequence are proved in `TNLean.MPS.MPDO.InvariantProjection`.
The periodic sectors are excluded in `TNLean.MPS.MPDO.CyclicProjector`, and
`TNLean.MPS.MPDO.VerticalReduction` constructs a complete orthogonal family of
irreducible reducing vertical corners. The general theorem in
`TNLean.MPS.CanonicalForm.ProjectorClosureSpectral` gives an abstract
positive-length normal-block decomposition, while
`TNLean.MPS.MPDO.VerticalSpectral` removes zero corners and normalizes the
remaining corners without losing their physical isometries or the literal
letterwise reconstruction. `TNLean.MPS.MPDO.VerticalBNT` groups these corners
into representatives while retaining their physical isometries, and
`TNLean.MPS.MPDO.SectorTrace` proves positivity of every grouped coefficient.
The relative Gram algebra is formalized in
`QICLean.Kraus.NormalCommutant`; its application to the grouped
sectors is carried out in `TNLean.MPS.MPDO.GroupedSectorGram` and
`TNLean.MPS.MPDO.GroupedGramNormalization`.  The normalized physical maps and
the vertical basis of normal tensors are constructed in
`TNLean.MPS.MPDO.NormalizedGroupedSectors` and
`TNLean.MPS.MPDO.VerticalBNTConstruction`.  Their final coisometry assembly is
proved in `TNLean.MPS.MPDO.VerticalCanonicalForm`.

## Module location

The MPO/MPDO/LPDO foundations live under `TNLean/MPS/MPDO/` (imported as layer
3b in `TNLean.lean`) rather than as a top-level `TNLean/MPDO/` namespace: they
sit on top of the `MPSTensor` framework from `TNLean/MPS/`, so the MPS-scoped
location matches the existing layering.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 and the auxiliary Lemma L in the appendix
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A "first-site insertion" on a tensor. The resulting local tensor is the
one obtained by contracting the physical index with `Y` at a single site. -/
noncomputable def insertedTensor {α β : Type*} [Fintype α]
    (Y : Matrix α α ℂ) (A : MPTensor α β) : MPTensor α β :=
  fun i => ∑ j : α, Y i j • A j

/-- Coefficient-level formulation of "acting with `Y` on the first spin" of an
MPV. This is the hypothesis used in the paper's Lemma L. -/
def FirstSiteActionAgree {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : MPTensor α β) (Y Z : Matrix α α ℂ) : Prop :=
  ∀ (N : ℕ) (σ : Fin (N + 1) → α),
    ∑ i : α, Y (σ 0) i * MPTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) =
      ∑ i : α, Z (σ 0) i * MPTensor.mpv A (Fin.cons i (σ ∘ Fin.succ))

/-- Equality of all positive-length matrix product vectors transports a
first-site action identity between tensors of possibly different bond dimensions.

Every coefficient in `FirstSiteActionAgree` has length `N + 1`, so no
length-zero coefficient is involved.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858. -/
theorem FirstSiteActionAgree.of_sameMPVPos {α β β' : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [Fintype β'] [DecidableEq β'] {A : MPTensor α β}
    {B : MPTensor α β'} {Y Z : Matrix α α ℂ}
    (hAB : MPTensor.SameMPV₂Pos A B) (h : FirstSiteActionAgree A Y Z) :
    FirstSiteActionAgree B Y Z := by
  intro N σ
  calc
    ∑ i : α, Y (σ 0) i * MPTensor.mpv B (Fin.cons i (σ ∘ Fin.succ)) =
        ∑ i : α, Y (σ 0) i * MPTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hAB (N + 1) (by omega) (Fin.cons i (σ ∘ Fin.succ))]
    _ = ∑ i : α, Z (σ 0) i *
        MPTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) := h N σ
    _ = ∑ i : α, Z (σ 0) i *
        MPTensor.mpv B (Fin.cons i (σ ∘ Fin.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hAB (N + 1) (by omega) (Fin.cons i (σ ∘ Fin.succ))]

/-- Full MPV equality transports a first-site action identity. -/
theorem FirstSiteActionAgree.of_sameMPV {α β β' : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [Fintype β'] [DecidableEq β'] {A : MPTensor α β}
    {B : MPTensor α β'} {Y Z : Matrix α α ℂ}
    (hAB : MPTensor.SameMPV₂ A B) (h : FirstSiteActionAgree A Y Z) :
    FirstSiteActionAgree B Y Z :=
  h.of_sameMPVPos hAB.toSameMPV₂Pos

/-- A first-site action identity transports along a relabelling of the physical alphabet,
the actions being relabelled on both indices. -/
theorem FirstSiteActionAgree.reindexPhysical {α α' β : Type*} [Fintype α] [Fintype α']
    [Fintype β] [DecidableEq β] (e : α' ≃ α) {A : MPTensor α β} {Y Z : Matrix α α ℂ}
    (h : FirstSiteActionAgree A Y Z) :
    FirstSiteActionAgree (Kraus.reindexPhysical e A) (Y.submatrix e e) (Z.submatrix e e) := by
  intro N σ
  have hsum : ∀ W : Matrix α α ℂ,
      ∑ i : α', W.submatrix e e (σ 0) i *
          MPTensor.mpv (Kraus.reindexPhysical e A) (Fin.cons i (σ ∘ Fin.succ)) =
        ∑ i : α, W (e (σ 0)) i *
          MPTensor.mpv A (Fin.cons i ((fun n => e (σ n)) ∘ Fin.succ)) := by
    intro W
    refine Fintype.sum_equiv e _ _ fun i => ?_
    rw [MPTensor.mpv_reindexPhysical, Matrix.submatrix_apply]
    congr 2
    funext n
    refine Fin.cases rfl (fun k => rfl) n
  rw [hsum Y, hsum Z]
  exact h N fun n => e (σ n)

/-- Inserting a relabelled action into a relabelled tensor relabels the insertion. -/
theorem insertedTensor_reindexPhysical {α α' β : Type*} [Fintype α] [Fintype α']
    (e : α' ≃ α) (Y : Matrix α α ℂ) (A : MPTensor α β) :
    insertedTensor (Y.submatrix e e) (Kraus.reindexPhysical e A) =
      Kraus.reindexPhysical e (insertedTensor Y A) := by
  funext i
  exact Fintype.sum_equiv e _ _ fun j => rfl

/-! ### Pair-alphabet form of the three contractions in Proposition 4.13 -/

/-- The pair-alphabet action obtained by multiplying the ket index by `P`.

For the horizontal MPO contraction this is the first-site form of
$PH^{(N)}$.  It is the leftmost contraction in the displayed equation of
the proof of Proposition 4.13 of arXiv:1606.00608, lines 1873--1887. -/
noncomputable def ketLeftAction (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => if p.2 = q.2 then P p.1 q.1 else 0

/-- The pair-alphabet action obtained by multiplying the bra index by `P` on
the right.  For the horizontal MPO contraction this is the first-site form of
$H^{(N)}P$ in the displayed equation of the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1873--1887. -/
noncomputable def braRightAction (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => if p.1 = q.1 then P q.2 p.2 else 0

/-- The pair-alphabet action obtained by multiplying the ket index by `P` and
the bra index by `P` on the right.  For the horizontal MPO contraction this is
the first-site form of $PH^{(N)}P$ in the displayed equation of the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1873--1887. -/
noncomputable def ketLeftBraRightAction (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => P p.1 q.1 * P q.2 p.2

/-- The coefficient of an operator tensor with one pair letter separated from an arbitrary
pair-alphabet tail is a matrix entry of the periodic operator. -/
theorem mpv_cons_pair (M : MPOTensor d D) {N : ℕ}
    (i j : Fin d) (ρ : Fin N → Fin d × Fin d) :
    MPTensor.mpv M (Fin.cons (i, j) ρ) =
      MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ n).1))
        (Fin.cons j (fun n => (ρ n).2)) := by
  rw [MPOTensor.mpv_eq_mpo]
  congr 1 <;> funext n <;> refine Fin.cases rfl (fun k => rfl) n

/-- Coefficient identity identifying the first-site pair-alphabet ket action
with the matrix entries of $PH^{(N)}$. -/
theorem ketLeftAction_mpv (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    {N : ℕ} (ρ : Fin (N + 1) → Fin d × Fin d) :
    ∑ q : Fin d × Fin d, ketLeftAction P (ρ 0) q *
        MPTensor.mpv M (Fin.cons q (ρ ∘ Fin.succ)) =
      ∑ i : Fin d, P (ρ 0).1 i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).1))
          (Fin.cons (ρ 0).2 (fun n => (ρ (Fin.succ n)).2)) := by
  rw [Fintype.sum_prod_type]
  simp only [ketLeftAction]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_eq_single (ρ 0).2]
  · simp only [ite_true]
    rw [mpv_cons_pair]
    rfl
  · intro j hj
    simp only [hj.symm, ite_false, zero_mul]

/-- Coefficient identity identifying the first-site pair-alphabet bra action
with the matrix entries of $H^{(N)}P$. -/
theorem braRightAction_mpv (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    {N : ℕ} (ρ : Fin (N + 1) → Fin d × Fin d) :
    ∑ q : Fin d × Fin d, braRightAction P (ρ 0) q *
        MPTensor.mpv M (Fin.cons q (ρ ∘ Fin.succ)) =
      ∑ j : Fin d,
        MPOTensor.mpo M (N + 1)
          (Fin.cons (ρ 0).1 (fun n => (ρ (Fin.succ n)).1))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).2)) * P j (ρ 0).2 := by
  rw [Fintype.sum_prod_type]
  simp only [braRightAction, ite_mul]
  rw [Fintype.sum_eq_single (ρ 0).1]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [ite_true]
    rw [mpv_cons_pair]
    simp only [Function.comp_apply, mul_comm]
  · intro i hi
    simp only [hi.symm, ite_false, zero_mul, Finset.sum_const_zero]

/-- Coefficient identity identifying the two-sided first-site pair-alphabet
action with the matrix entries of $PH^{(N)}P$. -/
theorem ketLeftBraRightAction_mpv (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (ρ : Fin (N + 1) → Fin d × Fin d) :
    ∑ q : Fin d × Fin d, ketLeftBraRightAction P (ρ 0) q *
        MPTensor.mpv M (Fin.cons q (ρ ∘ Fin.succ)) =
      ∑ i : Fin d, ∑ j : Fin d, P (ρ 0).1 i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).1))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).2)) * P j (ρ 0).2 := by
  rw [Fintype.sum_prod_type]
  simp only [ketLeftBraRightAction]
  apply Finset.sum_congr₂
  intro i _ j _
  rw [mpv_cons_pair]
  simp only [Function.comp_apply]
  ring

/-- Entrywise equality $PH^{(N)} = PH^{(N)}P$ gives the first of
the two pair-alphabet first-site equalities used in Lemma L. -/
theorem firstSiteActionAgree_ketLeft_ketLeftBraRight
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hInv : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin d × Fin d),
      (∑ i : Fin d, P (ρ 0).1 i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).1))
          (Fin.cons (ρ 0).2 (fun n => (ρ (Fin.succ n)).2)) =
      ∑ i : Fin d, ∑ j : Fin d, P (ρ 0).1 i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).1))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).2)) * P j (ρ 0).2)) :
    MPSTensor.FirstSiteActionAgree M
      (ketLeftAction P) (ketLeftBraRightAction P) := by
  intro N ρ
  rw [ketLeftAction_mpv, ketLeftBraRightAction_mpv]
  exact hInv N ρ

/-- Entrywise equality $PH^{(N)} = H^{(N)}P$ gives the second of the
two pair-alphabet first-site equalities used in Lemma L. -/
theorem firstSiteActionAgree_ketLeft_braRight
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hComm : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin d × Fin d),
      (∑ i : Fin d, P (ρ 0).1 i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).1))
          (Fin.cons (ρ 0).2 (fun n => (ρ (Fin.succ n)).2)) =
      ∑ j : Fin d,
        MPOTensor.mpo M (N + 1)
          (Fin.cons (ρ 0).1 (fun n => (ρ (Fin.succ n)).1))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).2)) * P j (ρ 0).2)) :
    MPSTensor.FirstSiteActionAgree M
      (ketLeftAction P) (braRightAction P) := by
  intro N ρ
  rw [ketLeftAction_mpv, braRightAction_mpv]
  exact hComm N ρ

/-- The diagonal restriction of a pair-alphabet block: `diagBlock B i = B (i, i)`. -/
def diagBlock {β : Type*} (B : MPTensor (Fin d × Fin d) β) : MPTensor (Fin d) β :=
  fun i => B (i, i)

/-- Evaluating a block-diagonal assembly of pair-alphabet blocks on a diagonal-paired
configuration equals evaluating the assembly of the diagonally-restricted blocks on the
original configuration. -/
theorem mpv_toTensorFromBlocks_diag {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPTensor (Fin d × Fin d) (Fin (dim k)))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks (α := Fin d × Fin d) (μ := μ) A) (fun k => (σ k, σ k))
      = mpv (toTensorFromBlocks (α := Fin d) (μ := μ) (fun k => diagBlock (A k))) σ :=
  (mpv_reindexPhysical (fun i => (i, i)) (toTensorFromBlocks (μ := μ) A) σ).symm

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-! ### The vertically viewed tensor -/

/-- The **vertically viewed tensor** of an MPO tensor.  The vertical direction
is obtained by exchanging the notion of physical and virtual indices
(arXiv:1606.00608, line 943): the letters of the vertical tensor are indexed
by the horizontal bond pair $(a, b)$, and each letter is the operator on the
physical space with matrix elements $(\widetilde M_{ab})_{ij} = M^{ij}_{ab}$.
Concatenating this tensor vertically generates the matrix product vectors of
the vertical direction, and the vertical canonical form of
arXiv:1606.00608, Proposition 4.13, is a statement about this tensor. -/
def verticalTensor (M : MPOTensor d D) : MPSTensor (D * D) d :=
  fun ab i j => M (i, j) ab.divNat ab.modNat

@[simp] lemma verticalTensor_apply (M : MPOTensor d D) (ab : Fin (D * D))
    (i j : Fin d) : verticalTensor M ab i j = M (i, j) ab.divNat ab.modNat :=
  rfl

/-- The vertical letter at an explicitly paired bond index $(a, b)$. -/
lemma verticalTensor_finProdFinEquiv (M : MPOTensor d D) (a b : Fin D)
    (i j : Fin d) :
    verticalTensor M (finProdFinEquiv (a, b)) i j = M (i, j) a b := by
  simp

/-- The vertical view of the MPO adjoint exchanges the oriented horizontal
bond indices and conjugate-transposes the resulting vertical letter:
$\widetilde{M^\dagger}_{a,b}=(\widetilde M_{b,a})^\dagger$.

This is the indexed adjoint convention in the first displayed diagram of the
proof of Proposition 4.13 of arXiv:1606.00608, lines 1909--1913. -/
@[simp] theorem verticalTensor_adjointTensor (M : MPOTensor d D)
    (ab : Fin (D * D)) :
    verticalTensor (adjointTensor M) ab =
      (verticalTensor M (bondPairSwap ab))ᴴ := by
  ext i j
  simp [verticalTensor_apply, bondPairSwap, Matrix.conjTranspose_apply]

/-- The diagonal MPS tensor extracted from an MPO by restricting to equal ket
and bra indices.  Its matrix product vectors are the diagonal entries
$\langle\sigma|\rho^{(N)}(M)|\sigma\rangle$ of the generated operator
(`mpv_diagonalTensor_eq_mpo_diag`), the positivity input to the vertical
canonical form.  The tensor generating the vertical direction itself is
`verticalTensor`. -/
def diagonalTensor (M : MPOTensor d D) : MPSTensor d D :=
  fun i => M (i, i)

@[simp] lemma diagonalTensor_apply (M : MPOTensor d D) (i : Fin d) :
    diagonalTensor M i = M (i, i) :=
  rfl

/-- **Matrix product vector of the diagonal tensor.** The MPV of the diagonal tensor at
a configuration `σ` equals the MPV of `M` on the pair alphabet at the diagonal-paired
configuration `k ↦ (σ k, σ k)`. This lets the horizontal canonical form of
`M` (which constrains all pair-alphabet configurations) be specialized to the
diagonal configurations seen by `diagonalTensor M`, the first step of Proposition 4.13. -/
theorem mpv_diagonalTensor (M : MPOTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    MPTensor.mpv (diagonalTensor M) σ = MPTensor.mpv M (fun k => (σ k, σ k)) :=
  MPTensor.mpv_reindexPhysical (fun i => (i, i)) M σ

/-- Under a horizontal canonical-form decomposition of `M`, the diagonal
tensor of `M` generates the same MPV family as the block-diagonal assembly, on the
physical index `Fin d`, of the diagonally-restricted blocks.  This is a preliminary
coefficient identity for arXiv:1606.00608, Proposition 4.13, not the vertical
canonical decomposition: diagonal restriction need not preserve normality, and
the horizontal weights need not be positive. -/
theorem mpv_diagonalTensor_eq_blocks (M : MPOTensor d D)
    {r : ℕ} {dim : Fin r → ℕ} (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPTensor (Fin d × Fin d) (Fin (dim k)))
    (hM : MPTensor.SameMPV₂Pos M
      (MPTensor.toTensorFromBlocks (α := Fin d × Fin d) (μ := μ) A))
    {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin d) :
    MPTensor.mpv (diagonalTensor M) σ
      = MPTensor.mpv (MPTensor.toTensorFromBlocks (α := Fin d) (μ := μ)
          (fun k => MPSTensor.diagBlock (A k))) σ := by
  rw [mpv_diagonalTensor, hM N hN, MPSTensor.mpv_toTensorFromBlocks_diag]

/-- Word evaluation of the diagonal MPS tensor equals the MPO word evaluation with equal
ket and bra words. -/
theorem evalWord_diagonalTensor (M : MPOTensor d D) (w : List (Fin d)) :
    Kraus.evalWord (diagonalTensor M) w = evalWord M w w := by
  induction w with
  | nil => rfl
  | cons i t ih =>
    simp only [Kraus.evalWord_cons, evalWord_cons, diagonalTensor_apply, ih]

/-- **The diagonal tensor evaluates the density-operator diagonal.** The matrix product
vector of the diagonal tensor at a configuration `σ` equals the diagonal entry
⟨σ|ρ^{(N)}(M)|σ⟩ of the generated operator. When `M` generates an MPDO this entry is a
nonnegative real, which is the source of the positivity of the vertical weights. -/
theorem mpv_diagonalTensor_eq_mpo_diag (M : MPOTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    MPTensor.mpv (diagonalTensor M) σ = mpo M N σ σ := by
  simp only [MPTensor.mpv, MPTensor.coeff, mpo_apply, mpoMatrixEntry, evalWord_diagonalTensor]

/-- For a tensor generating a positive semidefinite operator, the diagonal-tensor matrix
product vector is a nonnegative real. This is the positivity that the vertical
canonical-form weights inherit from the MPDO. -/
theorem mpv_diagonalTensor_nonneg (M : MPOTensor d D) {N : ℕ}
    (hM : (mpo M N).PosSemidef) (σ : Fin N → Fin d) :
    0 ≤ MPTensor.mpv (diagonalTensor M) σ := by
  rw [mpv_diagonalTensor_eq_mpo_diag]
  exact hM.diag_nonneg

/-! ### Positivity and one-sided invariant projections -/

/-- For an MPDO, a one-sided invariant Hermitian matrix for an `N`-site density
operator has zero opposite corner.

This is the displayed equation in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1873--1887.  The subsequent use of Lemma L transfers
this operator equality back to the tensor blocks. Positivity supplies the
Hermiticity of the density operator; the algebraic corner argument then uses
only that Hermiticity, one-sided invariance, and Hermiticity of `P`. -/
theorem mpo_opposite_corner_eq_zero (M : MPOTensor d D) (hM : IsMPDO M) (N : ℕ)
    (hN : 0 < N)
    (P : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (hP : P.IsHermitian)
    (hInv : P * mpo M N = P * mpo M N * P) :
    (1 - P) * mpo M N * P = 0 :=
  Matrix.IsHermitian.opposite_corner_eq_zero (hM N hN).isHermitian hP hInv

/-- Compressions of an MPDO density operator by a Hermitian matrix are
positive semidefinite.  Applied to the sector projectors $P_{\alpha,k}$ of the
vertical decomposition, this is the operator inequality
$P_{\alpha,k}H^{(N)}P_{\alpha,k} \ge 0$ in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1899--1903. -/
theorem mpo_compress_posSemidef (M : MPOTensor d D) (hM : IsMPDO M) (N : ℕ)
    (hN : 0 < N) (P : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hP : P.IsHermitian) :
    (P * mpo M N * P).PosSemidef := by
  have h := Matrix.PosSemidef.mul_mul_conjTranspose_same (hM N hN) P
  rwa [hP.eq] at h

/-- A nonzero Hermitian compression of an MPDO density operator has positive
trace.  For the sector projectors of the vertical decomposition this is the
positivity $\tr(P_{\alpha,k}H^{(N)}P_{\alpha,k}) > 0$ from which the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1899--1903, deduces
$\mu_{\alpha,k}d_\alpha > 0$; the identification of the trace with
$\mu_{\alpha,k}d_\alpha$ uses the vertical decomposition and is a separate
step. -/
theorem mpo_compress_trace_pos (M : MPOTensor d D) (hM : IsMPDO M) (N : ℕ)
    (hN : 0 < N) (P : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hP : P.IsHermitian)
    (hne : P * mpo M N * P ≠ 0) :
    0 < Matrix.trace (P * mpo M N * P) :=
  Matrix.PosSemidef.trace_pos_of_ne_zero
    (mpo_compress_posSemidef M hM N hN P hP) hne

/-- The multiplicity-expanded block dimensions corresponding to a family of
positive diagonal weights. -/
def verticalCopyDim {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ) :
    Fin (∑ α : Fin g, mult α) → ℕ :=
  fun q => dim ((finSigmaFinEquiv.symm q).1)

/-- The multiplicity-expanded block family obtained by repeating the same BNT
block across all diagonal entries of its positive weight matrix. -/
def verticalCopyBlocks {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (A : (α : Fin g) → MPSTensor d (dim α)) :
    (q : Fin (∑ α : Fin g, mult α)) → MPSTensor d (verticalCopyDim dim mult q) :=
  fun q => A ((finSigmaFinEquiv.symm q).1)

/-- The multiplicity-expanded scalar weights obtained by flattening the
positive diagonal matrices from the paper's vertical decomposition. -/
def verticalCopyWeights {g : ℕ} (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ) :
    Fin (∑ α : Fin g, mult α) → ℂ :=
  fun q =>
    let p := finSigmaFinEquiv.symm q
    ω p.1 p.2

/-- The direct-sum tensor $\bigoplus_\alpha \mu_\alpha \otimes M_\alpha$ with positive diagonal
matrices $\mu_\alpha = \operatorname{diag}(\omega_{\alpha,0}, \dots)$.  Since each $\mu_\alpha$ is
diagonal, the summand $\mu_\alpha \otimes M_\alpha$ is the further direct sum
$\bigoplus_k \omega_{\alpha,k} M_\alpha$ of its diagonal
entries; this constructor lists those blocks in exactly that order, so the
multiplicities `mult α` and the diagonal entries `ω α k` stay explicit. -/
noncomputable def verticalAssembledTensor {g : ℕ}
    (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)) :
    MPSTensor d (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) :=
  MPTensor.toTensorFromBlocks
    (μ := verticalCopyWeights mult ω)
    (A := verticalCopyBlocks dim mult A)

/-- **Vertical canonical form** of an MPO tensor (arXiv:1606.00608,
Proposition 4.13, lines 1863--1870; the vertical direction
is defined at line 943 by exchanging the physical and virtual indices).

There are a basis of normal tensors $\{M_\alpha\}$ for the vertically viewed tensor,
positive diagonal matrices $\mu_\alpha = \operatorname{diag}(\omega_{\alpha,0}, \dots)$, and an
isometry $U$ on the physical space such that, letter by letter over the horizontal bond pairs
$(a, b)$,
$U \widetilde M_{ab} U^\dagger = (\bigoplus_\alpha \mu_\alpha \otimes M_\alpha)_{ab}$.
The reverse identity reconstructs $\widetilde M_{ab}$ from this direct sum and
records that the discarded orthogonal complement is a zero sector.

The right-hand side keeps the multiplicities `mult α` and the diagonal
entries `ω α k` explicit; the trace coefficients
$m_\alpha = \operatorname{tr}\,\mu_\alpha$ of this
decomposition are the ones consumed by the renormalization fixed-point
characterization at arXiv:1606.00608, line 1956.  Every basis tensor appears
with at least one copy: each $\mu_\alpha$ is a positive diagonal matrix of size
`mult α`, at least one, matching arXiv:1606.00608, line 1901, where the sector
$(\alpha, 1)$ exists for every $\alpha$.

The source's general canonical-form construction permits zero sectors and only
requires the sum of the nonzero block dimensions to be at most the original
dimension (arXiv:1606.00608, lines 214--225). In the matrix orientation used
below, $U$ maps the original physical space onto the retained nonzero sector
space. Thus $U U^\dagger = 1$; the matrix $U^\dagger U$ is generally the
support projection on the original physical space. The reverse identity
$\widetilde M = U^\dagger (\bigoplus_\alpha \mu_\alpha \otimes M_\alpha) U$
ensures that every vertical letter is supported on this projection; a bare
compression would not exclude nonzero discarded or off-diagonal corners.

**Local fix (zero-sector complement):** An earlier formulation also required
$U^\dagger U = 1$, which incorrectly excluded the zero sectors allowed at
arXiv:1606.00608, lines 216--219. The correction and a two-dimensional example
are recorded in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
def IsVerticalCF (M : MPOTensor d D) : Prop :=
  ∃ (g : ℕ) (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (U : Matrix (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ),
    (∀ α, 0 < mult α) ∧
      (∀ α k, (0 : ℂ) < ω α k) ∧
      U * Uᴴ = 1 ∧
      MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M) (fun α ↦ ⟨dim α, A α⟩) ∧
      (∀ v : Fin (D * D),
        U * verticalTensor M v * Uᴴ = verticalAssembledTensor dim mult ω A v) ∧
      ∀ v : Fin (D * D),
        verticalTensor M v = Uᴴ * verticalAssembledTensor dim mult ω A v * U

/-- The matrix product vector of the vertical-assembled tensor, as a sum over the
flattened `(block, multiplicity)` index `(α, j)`:
`∑_{α} ∑_{j} (ω_{α j})^N · V^{(N)}(A_α)(σ)`. -/
theorem mpv_verticalAssembledTensor_eq_sum {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ) (A : (α : Fin g) → MPSTensor d (dim α))
    {N : ℕ} (σ : Fin N → Fin d) :
    MPTensor.mpv (verticalAssembledTensor dim mult ω A) σ
      = ∑ p : (α : Fin g) × Fin (mult α), (ω p.1 p.2) ^ N • MPTensor.mpv (A p.1) σ := by
  rw [verticalAssembledTensor, MPSTensor.mpv_toTensorFromBlocks_eq_sum]
  exact Equiv.sum_comp finSigmaFinEquiv.symm
    (fun s : (α : Fin g) × Fin (mult α) => (ω s.1 s.2) ^ N • MPTensor.mpv (A s.1) σ)

/-- Regrouping an indexed block assembly into repeated copies of a family of
representative blocks preserves its positive-length matrix product vector
family.  The equivalence records which representative and which copy correspond to each
original block; the pointwise hypotheses identify the weights and the
positive-length matrix product vector families.

This is the finite-sum reindexing used after the vertical canonical
decomposition in arXiv:1606.00608, Proposition 4.13, lines 1895--1921. Those
lines first produce the vertical sectors and only then group gauge-equivalent
sectors into the repeated copies of each basis tensor. -/
theorem sameMPV₂Pos_toTensorFromBlocks_verticalAssembledTensor_of_equiv
    {r g : ℕ} {dim₀ : Fin r → ℕ} {dim : Fin g → ℕ}
    (μ : Fin r → ℂ) (B : (k : Fin r) → MPSTensor d (dim₀ k))
    (mult : Fin g → ℕ) (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α))
    (e : Fin r ≃ (α : Fin g) × Fin (mult α))
    (hWeight : ∀ k, μ k = ω (e k).1 (e k).2)
    (hBlock : ∀ k, MPTensor.SameMPV₂Pos (B k) (A (e k).1)) :
    MPTensor.SameMPV₂Pos
      (MPTensor.toTensorFromBlocks (α := Fin d) (μ := μ) B)
      (verticalAssembledTensor dim mult ω A) := by
  intro N hN σ
  rw [MPSTensor.mpv_toTensorFromBlocks_eq_sum, mpv_verticalAssembledTensor_eq_sum]
  trans ∑ k : Fin r, (ω (e k).1 (e k).2) ^ N • MPTensor.mpv (A (e k).1) σ
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hWeight k, hBlock k N hN σ]
  · exact Equiv.sum_comp e
      (fun p : (α : Fin g) × Fin (mult α) ↦ (ω p.1 p.2) ^ N • MPTensor.mpv (A p.1) σ)

-- The BNT-refined implication `verticalCF_of_horizontalCF` is proved in
-- `VerticalCanonicalForm.lean`; the literal CPSV implication is proved by
-- `verticalCF_of_cpsvCanonicalForm` in `CPSVVerticalCanonicalForm.lean`.

end MPOTensor
