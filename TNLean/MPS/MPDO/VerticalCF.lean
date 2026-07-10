/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.HermitianHelpers
import TNLean.MPS.BNT.Basic
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Vertical canonical form for MPO tensors

This file introduces a block-decomposed version of the vertical canonical-form
structure used in the MPDO analysis of arXiv:1606.00608, Section 4.4.

Proposition 4.13 of arXiv:1606.00608 writes the tensor, after a local isometry
on the physical indices, as a direct sum
`⊕_α μ_α ⊗ M_α`, where the `μ_α` are positive diagonal matrices and the
`M_α` form a basis of normal tensors (BNT). The current repository formalization
uses canonical-form and BNT data with scalar block weights. We therefore
encode the paper's diagonal matrices by **flattening** each diagonal entry of
`μ_α` into a repeated positive scalar weight attached to the same block `M_α`.

The resulting predicate `IsVerticalCF` should be read as a repository-friendly
surrogate for the paper's vertical canonical form.

## Main definitions

* `diagonalTensor`:
  the MPS tensor `i ↦ M i i` extracted from the diagonal MPO entries.
* `verticalTransferMap`:
  the transfer map of `diagonalTensor`, i.e. `E_vert(X) = Σ_i M^{ii} X (M^{ii})†`.
* `HorizontalCFData` / `IsHorizontalCF`:
  lightweight horizontal canonical-form data for an MPO, expressed via the
  doubled-index MPS tensor `M.toMPSTensor`.
* `IsVerticalCF`:
  a flattened positive-weight BNT decomposition for `diagonalTensor M`.
* `MPSTensor.diagBlock`:
  the diagonal restriction `B ↦ (i ↦ B (i, i))` of a doubled-index block.

## Main results (toward Proposition 4.13)

* `blockwise_insert_eq_of_mpv_agree`:
  Lemma L from the paper's appendix, proved using the block-injective
  canonical-form (biCF) field of `HorizontalCFData`.
* `mpv_diagonalTensor`:
  the MPV of `diagonalTensor M` at `σ` equals the MPV of `M.toMPSTensor` at the
  diagonal-paired configuration `k ↦ (σ k, σ k)`.
* `mpv_diagonalTensor_eq_blocks`:
  under a horizontal canonical form, `diagonalTensor M` shares its MPV family with
  the single-spin block-diagonal assembly of the diagonally-restricted blocks.
* `mpv_diagonalTensor_eq_mpo_diag` / `mpv_diagonalTensor_nonneg`:
  the diagonal-tensor MPV equals the density-operator diagonal `⟨σ|ρ^{(N)}(M)|σ⟩`,
  hence is nonnegative when `M` generates an MPDO.
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
* `sameMPV₂_diagonalTensor_verticalAssembledTensor_of_equiv`:
  the exact diagonal-tensor consequence once the vertical BNT grouping and
  pointwise block identifications are supplied.
* `sameMPV₂Pos_diagonalTensor_verticalAssembledTensor_of_power_sums`:
  a separate positive-length comparison under scalar power-sum identities.
* `blockwise_opposite_insert_eq_of_mpv_agree`:
  if two pairs of first-site matrices satisfy `FirstSiteActionAgree` with a
  common left matrix, then the corresponding inserted tensors agree on every
  horizontal canonical-form block, by two applications of
  `blockwise_insert_eq_of_mpv_agree`.
* `blockwise_opposite_insert_eq_of_rotated_mpo_entries`:
  the preceding abstract matrices are identified explicitly with the
  doubled-index contractions of $PH^{(N)}$, $PH^{(N)}P$, and $H^{(N)}P$.

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
identification in the first step is formalized below.  The one-sided operator
identity and its blockwise consequence are proved in
`TNLean.MPS.MPDO.InvariantProjection`; the periodic-sector construction and
the independent vertical canonical form remain open.

## Module location

The MPO/MPDO/LPDO foundations live under `TNLean/MPS/MPDO/` (imported as layer
3b in `TNLean.lean`) rather than as a top-level `TNLean/MPDO/` namespace: they
sit on top of the `MPSTensor` framework from `TNLean/MPS/`, so the MPS-scoped
location matches the existing layering.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 and the auxiliary Lemma L in the appendix
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A "first-site insertion" on an MPS tensor. The resulting local tensor is the
one obtained by contracting the physical index with `Y` at a single site. -/
noncomputable def insertedTensor
    (Y : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => ∑ j : Fin d, Y i j • A j

/-- Coefficient-level formulation of "acting with `Y` on the first spin" of an
MPV. This is the hypothesis used in the paper's Lemma L. -/
def FirstSiteActionAgree (A : MPSTensor d D)
    (Y Z : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ (N : ℕ) (σ : Fin (N + 1) → Fin d),
    ∑ i : Fin d, Y (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) =
      ∑ i : Fin d, Z (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ))

/-- Equality of all matrix product vectors transports a first-site action
identity between tensors of possibly different bond dimensions. -/
theorem FirstSiteActionAgree.of_sameMPV {D' : ℕ} {A : MPSTensor d D}
    {B : MPSTensor d D'} {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAB : MPSTensor.SameMPV₂ A B) (h : FirstSiteActionAgree A Y Z) :
    FirstSiteActionAgree B Y Z := by
  intro N σ
  calc
    ∑ i : Fin d, Y (σ 0) i * MPSTensor.mpv B (Fin.cons i (σ ∘ Fin.succ)) =
        ∑ i : Fin d, Y (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hAB (N + 1) (Fin.cons i (σ ∘ Fin.succ))]
    _ = ∑ i : Fin d, Z (σ 0) i *
        MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) := h N σ
    _ = ∑ i : Fin d, Z (σ 0) i *
        MPSTensor.mpv B (Fin.cons i (σ ∘ Fin.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hAB (N + 1) (Fin.cons i (σ ∘ Fin.succ))]

/-! ### Doubled-index form of the three contractions in Proposition 4.13 -/

/-- The doubled-index action obtained by multiplying the ket index by `P`.

For the horizontal MPO contraction this is the first-site form of
$PH^{(N)}$.  It is the leftmost contraction in the displayed equation of
the proof of Proposition 4.13 of arXiv:1606.00608, lines 1873--1887. -/
noncomputable def ketLeftAction (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  fun p q => if p.modNat = q.modNat then P p.divNat q.divNat else 0

/-- The doubled-index action obtained by multiplying the bra index by `P` on
the right.  For the horizontal MPO contraction this is the first-site form of
$H^{(N)}P$ in the displayed equation of the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1873--1887. -/
noncomputable def braRightAction (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  fun p q => if p.divNat = q.divNat then P q.modNat p.modNat else 0

/-- The doubled-index action obtained by multiplying the ket index by `P` and
the bra index by `P` on the right.  For the horizontal MPO contraction this is
the first-site form of $PH^{(N)}P$ in the displayed equation of the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1873--1887. -/
noncomputable def ketLeftBraRightAction (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  fun p q => P p.divNat q.divNat * P q.modNat p.modNat

/-- Reading the doubled physical index as a ket--bra pair recovers the
corresponding matrix entry of the horizontal MPO contraction. -/
theorem mpv_toMPSTensor_pairConfig (M : MPOTensor d D) {N : ℕ}
    (σ τ : Fin N → Fin d) :
    MPSTensor.mpv M.toMPSTensor (fun n => finProdFinEquiv (σ n, τ n)) =
      MPOTensor.mpo M N σ τ := by
  simp only [MPSTensor.mpv, MPSTensor.coeff, MPOTensor.mpo_apply,
    MPOTensor.mpoMatrixEntry]
  congr 1
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [List.ofFn_succ, MPSTensor.evalWord_cons, MPOTensor.evalWord_cons,
        MPOTensor.toMPSTensor]
      rw [finProdFinEquiv_divNat, finProdFinEquiv_modNat]
      congr 1
      convert ih (σ ∘ Fin.succ) (τ ∘ Fin.succ) using 1 <;> rfl

/-- The preceding identity with one doubled index separated from an arbitrary
doubled-index tail. -/
theorem mpv_toMPSTensor_cons_pair (M : MPOTensor d D) {N : ℕ}
    (i j : Fin d) (ρ : Fin N → Fin (d * d)) :
    MPSTensor.mpv M.toMPSTensor (Fin.cons (finProdFinEquiv (i, j)) ρ) =
      MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ n).divNat))
        (Fin.cons j (fun n => (ρ n).modNat)) := by
  rw [← mpv_toMPSTensor_pairConfig]
  congr 1
  funext n
  refine Fin.cases ?_ (fun k => ?_) n
  · rfl
  · change ρ k = finProdFinEquiv ((ρ k).divNat, (ρ k).modNat)
    exact (finProdFinEquiv.apply_symm_apply (ρ k)).symm

/-- Coefficient identity identifying the first-site doubled-index ket action
with the matrix entries of $PH^{(N)}$. -/
theorem ketLeftAction_mpv (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    {N : ℕ} (ρ : Fin (N + 1) → Fin (d * d)) :
    ∑ q : Fin (d * d), ketLeftAction P (ρ 0) q *
        MPSTensor.mpv M.toMPSTensor (Fin.cons q (ρ ∘ Fin.succ)) =
      ∑ i : Fin d, P (ρ 0).divNat i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n => (ρ (Fin.succ n)).modNat)) := by
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [ketLeftAction, finProdFinEquiv_divNat, finProdFinEquiv_modNat]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (ρ 0).modNat]
  · simp only [if_true]
    rw [mpv_toMPSTensor_cons_pair]
    rfl
  · intro j _ hj
    simp only [hj.symm, if_false, zero_mul]
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

/-- Coefficient identity identifying the first-site doubled-index bra action
with the matrix entries of $H^{(N)}P$. -/
theorem braRightAction_mpv (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    {N : ℕ} (ρ : Fin (N + 1) → Fin (d * d)) :
    ∑ q : Fin (d * d), braRightAction P (ρ 0) q *
        MPSTensor.mpv M.toMPSTensor (Fin.cons q (ρ ∘ Fin.succ)) =
      ∑ j : Fin d,
        MPOTensor.mpo M (N + 1)
          (Fin.cons (ρ 0).divNat (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat := by
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [braRightAction, finProdFinEquiv_divNat, finProdFinEquiv_modNat,
    ite_mul]
  rw [Finset.sum_eq_single (ρ 0).divNat]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [if_true]
    rw [mpv_toMPSTensor_cons_pair]
    simp only [Function.comp_apply, mul_comm]
  · intro i _ hi
    simp only [hi.symm, if_false, zero_mul, Finset.sum_const_zero]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-- Coefficient identity identifying the two-sided first-site doubled-index
action with the matrix entries of $PH^{(N)}P$. -/
theorem ketLeftBraRightAction_mpv (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (ρ : Fin (N + 1) → Fin (d * d)) :
    ∑ q : Fin (d * d), ketLeftBraRightAction P (ρ 0) q *
        MPSTensor.mpv M.toMPSTensor (Fin.cons q (ρ ∘ Fin.succ)) =
      ∑ i : Fin d, ∑ j : Fin d, P (ρ 0).divNat i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat := by
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [ketLeftBraRightAction, finProdFinEquiv_divNat, finProdFinEquiv_modNat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mpv_toMPSTensor_cons_pair]
  simp only [Function.comp_apply]
  ring

/-- Entrywise equality $PH^{(N)} = PH^{(N)}P$ gives the first of
the two doubled-index first-site equalities used in Lemma L. -/
theorem firstSiteActionAgree_ketLeft_ketLeftBraRight
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hInv : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, P (ρ 0).divNat i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n => (ρ (Fin.succ n)).modNat)) =
      ∑ i : Fin d, ∑ j : Fin d, P (ρ 0).divNat i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat)) :
    MPSTensor.FirstSiteActionAgree M.toMPSTensor
      (ketLeftAction P) (ketLeftBraRightAction P) := by
  intro N ρ
  rw [ketLeftAction_mpv, ketLeftBraRightAction_mpv]
  exact hInv N ρ

/-- Entrywise equality $PH^{(N)} = H^{(N)}P$ gives the second of the
two doubled-index first-site equalities used in Lemma L. -/
theorem firstSiteActionAgree_ketLeft_braRight
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hComm : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, P (ρ 0).divNat i *
        MPOTensor.mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n => (ρ (Fin.succ n)).modNat)) =
      ∑ j : Fin d,
        MPOTensor.mpo M (N + 1)
          (Fin.cons (ρ 0).divNat (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat)) :
    MPSTensor.FirstSiteActionAgree M.toMPSTensor
      (ketLeftAction P) (braRightAction P) := by
  intro N ρ
  rw [ketLeftAction_mpv, braRightAction_mpv]
  exact hComm N ρ

/-- The diagonal restriction of a doubled-index block: `diagBlock B i = B (i, i)`. -/
def diagBlock {dim : ℕ} (B : MPSTensor (d * d) dim) : MPSTensor d dim :=
  fun i => B (finProdFinEquiv (i, i))

/-- Evaluating a block-diagonal assembly of doubled-index blocks on a diagonal-paired
configuration equals evaluating the assembly of the diagonally-restricted blocks on the
original configuration. -/
theorem mpv_toTensorFromBlocks_diag {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor (d * d) (dim k))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks (d := d * d) (μ := μ) A) (fun k => finProdFinEquiv (σ k, σ k))
      = mpv (toTensorFromBlocks (d := d) (μ := μ) (fun k => diagBlock (A k))) σ := by
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact (mpv_reindexPhysical (fun i => finProdFinEquiv (i, i)) (A k) σ).symm

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- The diagonal MPS tensor extracted from an MPO by restricting to equal ket
and bra indices. This is the tensor whose transfer map is the "vertical"
transfer map used in the MPDO vertical-canonical-form discussion. -/
def diagonalTensor (M : MPOTensor d D) : MPSTensor d D :=
  fun i => M i i

@[simp] lemma diagonalTensor_apply (M : MPOTensor d D) (i : Fin d) :
    diagonalTensor M i = M i i :=
  rfl

/-- The diagonal tensor is the doubled-index tensor restricted to the diagonal pair
`(i, i)`: `diagonalTensor M i = M.toMPSTensor (finProdFinEquiv (i, i))`. -/
theorem diagonalTensor_apply_eq (M : MPOTensor d D) (i : Fin d) :
    diagonalTensor M i = M.toMPSTensor (finProdFinEquiv (i, i)) := by
  simp only [diagonalTensor_apply, toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]

/-- **Matrix product vector of the diagonal tensor.** The MPV of the diagonal tensor at
a configuration `σ` equals the MPV of the doubled-index tensor at the diagonal-paired
configuration `k ↦ (σ k, σ k)`. This lets the horizontal canonical form of
`M.toMPSTensor` (which constrains all `Fin (d*d)` configurations) be specialized to the
diagonal configurations seen by `diagonalTensor M`, the first step of Proposition 4.13. -/
theorem mpv_diagonalTensor (M : MPOTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    MPSTensor.mpv (diagonalTensor M) σ
      = MPSTensor.mpv M.toMPSTensor (fun k => finProdFinEquiv (σ k, σ k)) := by
  have htensor : diagonalTensor M =
      MPSTensor.reindexPhysical (fun i => finProdFinEquiv (i, i)) M.toMPSTensor :=
    funext (diagonalTensor_apply_eq M)
  rw [htensor, MPSTensor.mpv_reindexPhysical (fun i => finProdFinEquiv (i, i)) M.toMPSTensor]

/-- Under a horizontal canonical-form decomposition of `M.toMPSTensor`, the diagonal
tensor of `M` generates the same MPV family as the block-diagonal assembly, on the
physical index `Fin d`, of the diagonally-restricted blocks.  This is a preliminary
coefficient identity for arXiv:1606.00608, Proposition 4.13, not the vertical
canonical decomposition: diagonal restriction need not preserve normality, and
the horizontal weights need not be positive. -/
theorem mpv_diagonalTensor_eq_blocks (M : MPOTensor d D)
    {r : ℕ} {dim : Fin r → ℕ} (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor (d * d) (dim k))
    (hM : MPSTensor.SameMPV₂ M.toMPSTensor
      (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) A))
    {N : ℕ} (σ : Fin N → Fin d) :
    MPSTensor.mpv (diagonalTensor M) σ
      = MPSTensor.mpv (MPSTensor.toTensorFromBlocks (d := d) (μ := μ)
          (fun k => MPSTensor.diagBlock (A k))) σ := by
  rw [mpv_diagonalTensor, hM, MPSTensor.mpv_toTensorFromBlocks_diag]

/-- Word evaluation of the diagonal MPS tensor equals the MPO word evaluation with equal
ket and bra words. -/
theorem evalWord_diagonalTensor (M : MPOTensor d D) (w : List (Fin d)) :
    MPSTensor.evalWord (diagonalTensor M) w = evalWord M w w := by
  induction w with
  | nil => rfl
  | cons i t ih =>
    simp only [MPSTensor.evalWord_cons, evalWord_cons, diagonalTensor_apply, ih]

/-- **The diagonal tensor evaluates the density-operator diagonal.** The matrix product
vector of the diagonal tensor at a configuration `σ` equals the diagonal entry
⟨σ|ρ^{(N)}(M)|σ⟩ of the generated operator. When `M` generates an MPDO this entry is a
nonnegative real, which is the source of the positivity of the vertical weights. -/
theorem mpv_diagonalTensor_eq_mpo_diag (M : MPOTensor d D) {N : ℕ} (σ : Fin N → Fin d) :
    MPSTensor.mpv (diagonalTensor M) σ = mpo M N σ σ := by
  simp only [MPSTensor.mpv, MPSTensor.coeff, mpo_apply, mpoMatrixEntry, evalWord_diagonalTensor]

/-- For a tensor generating a positive semidefinite operator, the diagonal-tensor matrix
product vector is a nonnegative real. This is the positivity that the vertical
canonical-form weights inherit from the MPDO. -/
theorem mpv_diagonalTensor_nonneg (M : MPOTensor d D) {N : ℕ}
    (hM : (mpo M N).PosSemidef) (σ : Fin N → Fin d) :
    0 ≤ MPSTensor.mpv (diagonalTensor M) σ := by
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
    (P : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (hP : P.IsHermitian)
    (hInv : P * mpo M N = P * mpo M N * P) :
    (1 - P) * mpo M N * P = 0 :=
  Matrix.IsHermitian.opposite_corner_eq_zero (hM N).isHermitian hP hInv

/-- Compressions of an MPDO density operator by a Hermitian matrix are
positive semidefinite.  Applied to the sector projectors $P_{\alpha,k}$ of the
vertical decomposition, this is the operator inequality
$P_{\alpha,k}H^{(N)}P_{\alpha,k} \ge 0$ in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1899--1903. -/
theorem mpo_compress_posSemidef (M : MPOTensor d D) (hM : IsMPDO M) (N : ℕ)
    (P : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (hP : P.IsHermitian) :
    (P * mpo M N * P).PosSemidef := by
  have h := Matrix.PosSemidef.mul_mul_conjTranspose_same (hM N) P
  rwa [hP.eq] at h

/-- A nonzero Hermitian compression of an MPDO density operator has positive
trace.  For the sector projectors of the vertical decomposition this is the
positivity $\tr(P_{\alpha,k}H^{(N)}P_{\alpha,k}) > 0$ from which the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1899--1903, deduces
$\mu_{\alpha,k}d_\alpha > 0$; the identification of the trace with
$\mu_{\alpha,k}d_\alpha$ uses the vertical decomposition and is a separate
step. -/
theorem mpo_compress_trace_pos (M : MPOTensor d D) (hM : IsMPDO M) (N : ℕ)
    (P : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (hP : P.IsHermitian)
    (hne : P * mpo M N * P ≠ 0) :
    0 < Matrix.trace (P * mpo M N * P) :=
  Matrix.PosSemidef.trace_pos_of_ne_zero (mpo_compress_posSemidef M hM N P hP) hne

/-- The vertical transfer map of an MPO tensor:
`E_vert(X) = Σ_i M^{ii} X (M^{ii})†`. -/
noncomputable def verticalTransferMap (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  MPSTensor.transferMap (diagonalTensor M)

/-- Lightweight horizontal canonical-form data for a family of blocks.

This is the fragment of the full canonical-form data needed for the MPDO
vertical-canonical-form interface in this file: injective blocks, the
left-canonical normalization, nonzero block weights, and block-injective
canonical form (biCF). -/
structure HorizontalCFData {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective. -/
  block_injective : ∀ k, MPSTensor.IsInjective (A k)
  /-- Each block is left-canonical. -/
  left_canonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- No block weight vanishes. -/
  weight_ne_zero : ∀ k, μ k ≠ 0
  /-- **Block-injective canonical form** (biCF): there is a blocking length `L`
  such that the trace pairing against length-`L` block products is faithful
  across all blocks simultaneously. Concretely, if a tuple of block matrices
  `Δ k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ` pairs to zero against every
  length-`L` block-diagonal product, then each `Δ k` vanishes individually.

  This is the block-decomposed surrogate for the block-injectivity proposition
  in Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  lines 340--345: after blocking at most `3 D^5` spins,
  where `D` denotes the bond dimension in the paper (in this block-decomposed
  setting one may take `D` to be a global bound such as `⨆ k, dim k`),
  any tensor in CF is in biCF, which is what the paper's Lemma L invokes to
  separate blockwise contributions.

  *Current repository status.* `TNLean/MPS/MPDO/BiCFDerivation.lean` now provides
  several exact routes to this field: from a full finite-length tuple-span
  witness (`WordTupleSpanTop`), from the abstract selector data
  (`PropBlockInjective`), and from the more concrete linear-independence criterion
  `wordEntryFamily`. What is still open is to derive one of those finite-length
  witnesses from the remaining canonical-form/BNT data alone, i.e. the actual
  block-injectivity proposition in Cirac--Perez-Garcia--Schuch--Verstraete,
  arXiv:1606.00608, lines 340--345. -/
  biCF : ∃ L : ℕ, ∀ (Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
    (∀ w : Fin L → Fin d,
        (∑ k : Fin r, Matrix.trace (Δ k * MPSTensor.evalWord (A k) (List.ofFn w))) = 0) →
    ∀ k, Δ k = 0

/-- Horizontal canonical form for an MPO tensor, expressed via a canonical-form
decomposition of the doubled-index MPS tensor `M.toMPSTensor`. -/
def IsHorizontalCF (M : MPOTensor d D) : Prop :=
  ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor (d * d) (dim k)),
    HorizontalCFData (d := d * d) μ A ∧
      MPSTensor.SameMPV₂ M.toMPSTensor
        (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) A)

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

/-- The flattened repeated tensor corresponding to the paper's
`⊕_α μ_α ⊗ M_α` block structure. -/
noncomputable def verticalAssembledTensor {g : ℕ}
    (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)) :
    MPSTensor d (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) :=
  MPSTensor.toTensorFromBlocks
    (μ := verticalCopyWeights mult ω)
    (A := verticalCopyBlocks dim mult A)

/-- A Lean-friendly version of the paper's vertical canonical form:

there is a basis of normal tensors `A α`, together with positive scalar weights
obtained by flattening the positive diagonal matrices `μ_α`, such that the
diagonal MPO tensor `diagonalTensor M` generates the same MPV family as the
flattened repeated tensor built from those blocks. -/
def IsVerticalCF (M : MPOTensor d D) : Prop :=
  ∃ (g : ℕ) (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)),
    (∀ α q, (0 : ℂ) < ω α q) ∧
      MPSTensor.IsBNT (verticalAssembledTensor dim mult ω A) g dim A ∧
      MPSTensor.SameMPV₂ (diagonalTensor M) (verticalAssembledTensor dim mult ω A)

/-- The matrix product vector of the vertical-assembled tensor, as a sum over the
flattened `(block, multiplicity)` index `(α, j)`:
`∑_{α} ∑_{j} (ω_{α j})^N · V^{(N)}(A_α)(σ)`. -/
theorem mpv_verticalAssembledTensor_eq_sum {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ) (A : (α : Fin g) → MPSTensor d (dim α))
    {N : ℕ} (σ : Fin N → Fin d) :
    MPSTensor.mpv (verticalAssembledTensor dim mult ω A) σ
      = ∑ p : (α : Fin g) × Fin (mult α), (ω p.1 p.2) ^ N • MPSTensor.mpv (A p.1) σ := by
  rw [verticalAssembledTensor, MPSTensor.mpv_toTensorFromBlocks_eq_sum]
  exact Equiv.sum_comp finSigmaFinEquiv.symm
    (fun s : (α : Fin g) × Fin (mult α) => (ω s.1 s.2) ^ N • MPSTensor.mpv (A s.1) σ)

/-- Regrouping an indexed block assembly into repeated copies of a family of
representative blocks preserves its full matrix product vector family.  The
equivalence records which representative and which copy correspond to each
original block; the pointwise hypotheses identify the bond dimensions and
weights and give equality of the positive-length matrix product vector
families.

This is the finite-sum reindexing used after the vertical canonical
decomposition in arXiv:1606.00608, Proposition 4.13, lines 1895--1921. Those
lines first produce the vertical sectors and only then group gauge-equivalent
sectors into the repeated copies of each basis tensor. -/
theorem sameMPV₂_toTensorFromBlocks_verticalAssembledTensor_of_equiv
    {r g : ℕ} {dim₀ : Fin r → ℕ} {dim : Fin g → ℕ}
    (μ : Fin r → ℂ) (B : (k : Fin r) → MPSTensor d (dim₀ k))
    (mult : Fin g → ℕ) (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α))
    (e : Fin r ≃ (α : Fin g) × Fin (mult α))
    (hDim : ∀ k, dim₀ k = dim (e k).1)
    (hWeight : ∀ k, μ k = ω (e k).1 (e k).2)
    (hBlock : ∀ k, MPSTensor.SameMPV₂Pos (B k) (A (e k).1)) :
    MPSTensor.SameMPV₂
      (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) B)
      (verticalAssembledTensor dim mult ω A) := by
  refine MPSTensor.SameMPV₂Pos.toSameMPV₂_of_bondDim_eq ?_ ?_
  · intro N hN σ
    rw [MPSTensor.mpv_toTensorFromBlocks_eq_sum, mpv_verticalAssembledTensor_eq_sum]
    trans ∑ k : Fin r, (ω (e k).1 (e k).2) ^ N • MPSTensor.mpv (A (e k).1) σ
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hWeight k, hBlock k N hN σ]
    · exact Equiv.sum_comp e
        (fun p : (α : Fin g) × Fin (mult α) ↦ (ω p.1 p.2) ^ N • MPSTensor.mpv (A p.1) σ)
  · trans ∑ k : Fin r, dim (e k).1
    · exact Finset.sum_congr rfl fun k _ ↦ hDim k
    · trans ∑ p : (α : Fin g) × Fin (mult α), dim p.1
      · exact Equiv.sum_comp e fun p ↦ dim p.1
      · change (∑ p : (α : Fin g) × Fin (mult α), dim p.1) =
          ∑ q : Fin (∑ α : Fin g, mult α), dim ((finSigmaFinEquiv.symm q).1)
        exact (Equiv.sum_comp finSigmaFinEquiv.symm (fun p ↦ dim p.1)).symm

/-- A horizontal block decomposition yields the full matrix product vector
equality required by the flattened vertical assembly once the vertical
canonical-form grouping has been supplied.  The equivalence lists every
original diagonal restriction as one copy of a representative vertical block;
the remaining hypotheses identify its bond dimension and weight and its
positive-length matrix product vector family.

The grouping hypotheses correspond to the vertical decomposition constructed
in arXiv:1606.00608, Proposition 4.13, lines 1895--1921. They are not a
consequence of reindexing the horizontal blocks alone. -/
theorem sameMPV₂_diagonalTensor_verticalAssembledTensor_of_equiv
    (M : MPOTensor d D) {r g : ℕ} {dim₀ : Fin r → ℕ} (μ : Fin r → ℂ)
    (B : (k : Fin r) → MPSTensor (d * d) (dim₀ k))
    {dim : Fin g → ℕ} (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α))
    (hM : MPSTensor.SameMPV₂ M.toMPSTensor
      (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) B))
    (e : Fin r ≃ (α : Fin g) × Fin (mult α))
    (hDim : ∀ k, dim₀ k = dim (e k).1)
    (hWeight : ∀ k, μ k = ω (e k).1 (e k).2)
    (hBlock : ∀ k,
      MPSTensor.SameMPV₂Pos (MPSTensor.diagBlock (B k)) (A (e k).1)) :
    MPSTensor.SameMPV₂ (diagonalTensor M) (verticalAssembledTensor dim mult ω A) := by
  intro N σ
  trans MPSTensor.mpv
    (MPSTensor.toTensorFromBlocks (d := d) (μ := μ)
      (fun k ↦ MPSTensor.diagBlock (B k))) σ
  · exact mpv_diagonalTensor_eq_blocks M μ B hM σ
  · exact sameMPV₂_toTensorFromBlocks_verticalAssembledTensor_of_equiv
      μ (fun k ↦ MPSTensor.diagBlock (B k)) mult ω A e hDim hWeight hBlock N σ

/-- Positive-length scalar power-sum identities imply that a block assembly
with one scalar weight per block has the same positive-length MPV family as an
assembly that repeats each block with several scalar weights.

This is a conditional comparison lemma. In arXiv:1606.00608, Proposition 4.13,
lines 1895--1921, the repeated weights instead arise by grouping the already
constructed vertical canonical sectors; that source step is expressed by
`sameMPV₂_toTensorFromBlocks_verticalAssembledTensor_of_equiv`. -/
theorem sameMPV₂Pos_toTensorFromBlocks_verticalAssembledTensor_of_power_sums
    {g : ℕ} {dim : Fin g → ℕ} (μ : Fin g → ℂ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α))
    (hPower : ∀ (α : Fin g) (N : ℕ),
      0 < N → (μ α) ^ N = ∑ q : Fin (mult α), (ω α q) ^ N) :
    MPSTensor.SameMPV₂Pos
      (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A)
      (verticalAssembledTensor dim mult ω A) := by
  intro N hN σ
  rw [MPSTensor.mpv_toTensorFromBlocks_eq_sum, mpv_verticalAssembledTensor_eq_sum]
  calc
    ∑ α : Fin g, (μ α) ^ N • MPSTensor.mpv (A α) σ
        = ∑ α : Fin g, (∑ q : Fin (mult α), (ω α q) ^ N) •
            MPSTensor.mpv (A α) σ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hPower α N hN]
    _ = ∑ α : Fin g, ∑ q : Fin (mult α), (ω α q) ^ N • MPSTensor.mpv (A α) σ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_smul]
    _ = ∑ p : (α : Fin g) × Fin (mult α),
          (ω p.1 p.2) ^ N • MPSTensor.mpv (A p.1) σ := by
          exact (Fintype.sum_sigma'
            (fun α q => (ω α q) ^ N • MPSTensor.mpv (A α) σ)).symm

/-- Under a horizontal block decomposition, the diagonal tensor has the same
positive-length MPV family as a repeated-block assembly when their scalar
weights satisfy the stated positive-length power-sum identities.

This conditional result does not construct the vertical grouping in
arXiv:1606.00608, Proposition 4.13, lines 1873--1921. That construction must
first identify the vertical BNT sectors and their positive weights. -/
theorem sameMPV₂Pos_diagonalTensor_verticalAssembledTensor_of_power_sums
    (M : MPOTensor d D) {g : ℕ} {dim : Fin g → ℕ} (μ : Fin g → ℂ)
    (A : (α : Fin g) → MPSTensor (d * d) (dim α))
    (mult : Fin g → ℕ) (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (hM : MPSTensor.SameMPV₂ M.toMPSTensor
      (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) A))
    (hPower : ∀ (α : Fin g) (N : ℕ),
      0 < N → (μ α) ^ N = ∑ q : Fin (mult α), (ω α q) ^ N) :
    MPSTensor.SameMPV₂Pos
      (diagonalTensor M)
      (verticalAssembledTensor dim mult ω (fun α => MPSTensor.diagBlock (A α))) := by
  intro N hN σ
  calc
    MPSTensor.mpv (diagonalTensor M) σ
        = MPSTensor.mpv
            (MPSTensor.toTensorFromBlocks (d := d) (μ := μ)
              (fun α => MPSTensor.diagBlock (A α))) σ := by
          exact mpv_diagonalTensor_eq_blocks M μ A hM σ
    _ = MPSTensor.mpv
          (verticalAssembledTensor dim mult ω (fun α => MPSTensor.diagBlock (A α))) σ :=
        sameMPV₂Pos_toTensorFromBlocks_verticalAssembledTensor_of_power_sums
          μ mult ω (fun α => MPSTensor.diagBlock (A α)) hPower N hN σ

/-- **Lemma L** (arXiv:1606.00608, appendix): if two operators act identically
on the first site of every MPV generated by a canonical-form tensor, then their
insertions agree blockwise.

This is the precise blockwise statement needed in the proof of Proposition
IV.12. The intended proof follows the paper: use block separation for the
canonical-form decomposition together with the nonvanishing of the Newton-Girard
sums of the block weights. -/
theorem blockwise_insert_eq_of_mpv_agree
    {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : HorizontalCFData (d := d) μ A)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct :
      MPSTensor.FirstSiteActionAgree
        (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A) Y Z) :
    ∀ k, MPSTensor.insertedTensor Y (A k) = MPSTensor.insertedTensor Z (A k) := by
  -- Obtain the biCF blocking length `L`.
  obtain ⟨L, hL⟩ := hCF.biCF
  intro k₀
  funext s
  -- Candidate witness for biCF: the blockwise difference weighted by `(μ k)^(L+1)`.
  set Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ := fun k =>
    (μ k) ^ (L + 1) • (MPSTensor.insertedTensor Y (A k) s -
      MPSTensor.insertedTensor Z (A k) s)
  -- Show that `Δ` pairs to zero against every length-`L` block word, so biCF forces `Δ = 0`.
  have hΔzero : ∀ k, Δ k = 0 := by
    refine hL Δ (fun w => ?_)
    -- Specialize `hAct` at `σ := Fin.cons s w` (which has length `L + 1`).
    have hA := hAct L (Fin.cons s w)
    -- Simplify `σ 0 = s` and `Fin.cons i (σ ∘ Fin.succ) = Fin.cons i w`.
    have hsimp : ∀ i : Fin d,
        (Fin.cons i ((Fin.cons s w : Fin (L + 1) → Fin d) ∘ Fin.succ) :
            Fin (L + 1) → Fin d) = Fin.cons i w :=
      fun i => by simp [Function.comp_def, Fin.cons_succ]
    simp only [Fin.cons_zero, hsimp] at hA
    -- Rewriter: for any `W`, expand the MPV pairing on the LHS of `hA` into a
    -- blockwise trace pairing against `insertedTensor W (A k) s`.
    have htrans : ∀ W : Matrix (Fin d) (Fin d) ℂ,
        ∑ i : Fin d, W s i *
            MPSTensor.mpv
              (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A)
              (Fin.cons i w : Fin (L + 1) → Fin d) =
          ∑ k : Fin r, Matrix.trace
            ((μ k) ^ (L + 1) • MPSTensor.insertedTensor W (A k) s *
              MPSTensor.evalWord (A k) (List.ofFn w)) := by
      intro W
      -- Expand the assembled-tensor MPV block-by-block and fold
      -- `mpv (A k) (Fin.cons i w)` into `trace (A k i * evalWord (A k) (List.ofFn w))`.
      have hExp : ∀ i : Fin d,
          MPSTensor.mpv
              (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A)
              (Fin.cons i w : Fin (L + 1) → Fin d) =
            ∑ k : Fin r, (μ k) ^ (L + 1) *
              Matrix.trace (A k i * MPSTensor.evalWord (A k) (List.ofFn w)) := by
        intro i
        rw [MPSTensor.mpv_toTensorFromBlocks_eq_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hof : List.ofFn (Fin.cons i w : Fin (L + 1) → Fin d)
            = i :: List.ofFn w := by
          simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        simp only [smul_eq_mul, MPSTensor.mpv, MPSTensor.coeff, hof,
          MPSTensor.evalWord_cons]
      simp_rw [hExp, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc ∑ i : Fin d, W s i *
                ((μ k) ^ (L + 1) *
                  Matrix.trace (A k i * MPSTensor.evalWord (A k) (List.ofFn w)))
            = (μ k) ^ (L + 1) * ∑ i : Fin d, W s i *
                Matrix.trace (A k i * MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring
        _   = (μ k) ^ (L + 1) * ∑ i : Fin d, Matrix.trace
                ((W s i • A k i) * MPSTensor.evalWord (A k) (List.ofFn w)) := by
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
        _   = (μ k) ^ (L + 1) * Matrix.trace
                (∑ i : Fin d, (W s i • A k i) *
                    MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Matrix.trace_sum]
        _   = (μ k) ^ (L + 1) * Matrix.trace
                ((∑ i : Fin d, W s i • A k i) *
                  MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Finset.sum_mul]
        _   = (μ k) ^ (L + 1) * Matrix.trace
                (MPSTensor.insertedTensor W (A k) s *
                  MPSTensor.evalWord (A k) (List.ofFn w)) := rfl
        _   = Matrix.trace ((μ k) ^ (L + 1) •
                MPSTensor.insertedTensor W (A k) s *
                MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    -- Apply `htrans` to both sides of `hA`.
    rw [htrans Y, htrans Z] at hA
    -- Rewrite each `Δ k * E_k` trace as the difference of the `Y` and `Z` versions.
    have hsubtr : ∀ k : Fin r,
        Matrix.trace (Δ k * MPSTensor.evalWord (A k) (List.ofFn w)) =
          Matrix.trace ((μ k) ^ (L + 1) •
              MPSTensor.insertedTensor Y (A k) s *
              MPSTensor.evalWord (A k) (List.ofFn w)) -
            Matrix.trace ((μ k) ^ (L + 1) •
              MPSTensor.insertedTensor Z (A k) s *
              MPSTensor.evalWord (A k) (List.ofFn w)) := by
      intro k
      change Matrix.trace
          (((μ k) ^ (L + 1) • (MPSTensor.insertedTensor Y (A k) s -
              MPSTensor.insertedTensor Z (A k) s)) *
            MPSTensor.evalWord (A k) (List.ofFn w)) = _
      rw [smul_sub, sub_mul, Matrix.trace_sub]
    simp_rw [hsubtr]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hA
  -- From `Δ k₀ = 0` and `(μ k₀)^(L+1) ≠ 0`, conclude the pointwise equality.
  have hk := hΔzero k₀
  have hμne : (μ k₀) ^ (L + 1) ≠ 0 := pow_ne_zero _ (hCF.weight_ne_zero k₀)
  have hdiff : MPSTensor.insertedTensor Y (A k₀) s -
      MPSTensor.insertedTensor Z (A k₀) s = 0 :=
    (smul_eq_zero.mp hk).resolve_left hμne
  exact sub_eq_zero.mp hdiff

/-- **One-sided invariance becomes reduction, block by block.**

Let `Yleft`, `Ycorner`, and `Yright` encode respectively the first-site
coefficients of $PH^{(N)}$, $PH^{(N)}P$, and $H^{(N)}P$.  If the
one-sided invariance gives agreement of the first two actions, while positivity
gives agreement of the first and third actions, then Lemma L shows that the
opposite corner vanishes on every canonical-form block: the `Yright` insertion
equals the `Ycorner` insertion.

This is the tensor-block conclusion of the displayed equation in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1873--1887.  The two
hypotheses are precisely the coefficient-level equalities displayed in that
equation; they do not posit a vertical canonical decomposition. -/
theorem blockwise_opposite_insert_eq_of_mpv_agree
    {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : HorizontalCFData (d := d) μ A)
    {Yleft Ycorner Yright : Matrix (Fin d) (Fin d) ℂ}
    (hInv : MPSTensor.FirstSiteActionAgree
      (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A) Yleft Ycorner)
    (hPos : MPSTensor.FirstSiteActionAgree
      (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A) Yleft Yright) :
    ∀ k, MPSTensor.insertedTensor Yright (A k) =
      MPSTensor.insertedTensor Ycorner (A k) := by
  intro k
  calc
    MPSTensor.insertedTensor Yright (A k) =
        MPSTensor.insertedTensor Yleft (A k) :=
      (blockwise_insert_eq_of_mpv_agree A hCF hPos k).symm
    _ = MPSTensor.insertedTensor Ycorner (A k) :=
      blockwise_insert_eq_of_mpv_agree A hCF hInv k

/-- **The three contractions in Proposition 4.13, with their indices fixed.**

Suppose the horizontal doubled-index tensor of `M` has the displayed
block-diagonal canonical form.  The entrywise identities
$PH^{(N)} = PH^{(N)}P$ and $PH^{(N)} = H^{(N)}P$ then identify
the three abstract first-site matrices in Lemma L with `ketLeftAction P`,
`ketLeftBraRightAction P`, and `braRightAction P`.  Consequently the last two
insertions agree on every canonical-form block.

This formalizes the doubled-index rotation implicit in the displayed
equation of the proof of Proposition 4.13 of arXiv:1606.00608,
lines 1873--1887.  It does not prove that a one-sided invariant projection
for the vertically viewed tensor supplies the first entrywise identity; that
further identification remains part of the horizontal-to-vertical
canonical-form argument. -/
theorem blockwise_opposite_insert_eq_of_rotated_mpo_entries
    {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (M : MPOTensor d D) (A : (k : Fin r) → MPSTensor (d * d) (dim k))
    (hCF : HorizontalCFData (d := d * d) μ A)
    (hM : MPSTensor.SameMPV₂ M.toMPSTensor
      (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) A))
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hInv : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, P (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n => (ρ (Fin.succ n)).modNat)) =
      ∑ i : Fin d, ∑ j : Fin d, P (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat))
    (hComm : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, P (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n => (ρ (Fin.succ n)).modNat)) =
      ∑ j : Fin d,
        mpo M (N + 1)
          (Fin.cons (ρ 0).divNat (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat)) :
    ∀ k, MPSTensor.insertedTensor (MPSTensor.braRightAction P) (A k) =
      MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction P) (A k) := by
  apply blockwise_opposite_insert_eq_of_mpv_agree A hCF
  · exact MPSTensor.FirstSiteActionAgree.of_sameMPV hM
      (MPSTensor.firstSiteActionAgree_ketLeft_ketLeftBraRight M P hInv)
  · exact MPSTensor.FirstSiteActionAgree.of_sameMPV hM
      (MPSTensor.firstSiteActionAgree_ketLeft_braRight M P hComm)

-- The implication `verticalCF_of_horizontalCF` (arXiv:1606.00608,
-- Proposition 4.13) — every MPDO in horizontal canonical form is in vertical
-- canonical form — is tracked by the blueprint entry
-- `thm:vertical_cf_of_horizontal_cf` (currently `\notready`) and will be added
-- as a theorem together with its proof once the horizontal-to-vertical
-- canonical-form argument has been formalized.

end MPOTensor
