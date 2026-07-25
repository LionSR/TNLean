/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTTripleFusionComparison
import TNLean.MPS.MPDO.BNTFinalSectorFusion
import TNLean.MPS.MPDO.BiCFDerivation.Selectors
import TNLean.MPS.MPDO.SourceBNTBlocking
import TNLean.MPS.Core.CyclicTrace
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Separation of final sectors in the triple-fusion comparison

The full triple-fusion comparison intertwines direct sums over all final labels.
If a common word polynomial selects one final-label tensor and annihilates all
the others, its off-diagonal final-label corners vanish.  This is the finite
word form of the simultaneous inverse used in the fixed-channel extraction in
arXiv:1511.08090.

The selector hypothesis is stated explicitly.  It is not presently derived
from the assumptions on `BNTFusionIsometryFamily`. At a positive selector
length it also makes both iterated fusion maps surjective, and hence makes the
full comparison invertible with adjoint inverse. Its diagonal final-sector
corners can then be studied separately. The fixed-final conclusions remain
conditional on the selector and injectivity hypotheses and require a separate
argument.

## References

* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, lines 237--277, especially the simultaneous inverse at
  line 269; see also lines 427--431 for the blocked direct-sum span input
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 995--1010
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

@[simp] private theorem leftFinalIndexEquiv_symm_apply
    (α β γ ε δ : Λ) (μ : Fin (Fam.chi.dim α β δ))
    (ν : Fin (Fam.chi.dim δ γ ε)) (b : Fin (Fam.bondDim ε)) :
    (Fam.leftFinalIndexEquiv α β γ ε).symm (⟨⟨δ, μ, ν⟩, b⟩) =
      ⟨δ, μ, ν, b⟩ := by
  rfl

@[simp] private theorem rightFinalIndexEquiv_symm_apply
    (α β γ ε δ : Λ) (μ : Fin (Fam.chi.dim β γ δ))
    (ν : Fin (Fam.chi.dim α δ ε)) (b : Fin (Fam.bondDim ε)) :
    (Fam.rightFinalIndexEquiv α β γ ε).symm (⟨⟨δ, μ, ν⟩, b⟩) =
      ⟨δ, μ, ν, b⟩ := by
  rfl

/-- A common finite family of word polynomials separates every final-label
tensor from all the others.  This is the arbitrary-finite-label form of
`MPSTensor.HasBlockSelectorWords`.

For each `ε`, the same coefficients evaluate to the identity on `tensor ε`
and to zero on every `tensor ε'` with `ε' ≠ ε`.

Source: arXiv:1511.08090, simultaneous inverse relation
`B_d^+ B_{d'} = δ_{d,d'} 1` at line 269, after the common blocking described
at lines 427--431. -/
def HasFinalLabelSelectorWords (S : ℕ) : Prop :=
  ∀ ε : Λ, ∃ c : (Fin S → Fin (p * p)) → ℂ,
    (∑ w : Fin S → Fin (p * p),
      c w • MPSTensor.evalWord (Fam.tensor ε).toMPSTensor (List.ofFn w)) = 1 ∧
    ∀ ε' : Λ, ε' ≠ ε →
      (∑ w : Fin S → Fin (p * p),
        c w • MPSTensor.evalWord (Fam.tensor ε').toMPSTensor (List.ofFn w)) = 0

/-- Simultaneous block selectors for the labelled MPO tensors are precisely
final-label selectors for their fusion family. -/
theorem hasFinalLabelSelectorWords_of_hasBlockSelectorWords
    {g : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p) {S : ℕ}
    (hSel : MPSTensor.HasBlockSelectorWords
      (fun ε ↦ (Fam.tensor ε).toMPSTensor) S) :
    Fam.HasFinalLabelSelectorWords S :=
  hSel

/-- Finite scalar sums commute with a dependent block diagonal whose blocks
have a fixed identity Kronecker factor. -/
private theorem sum_sum_smul_blockDiagonal'_one_kronecker
    {ι κ₁ κ₂ : Type*} [DecidableEq ι] [Fintype κ₁] [Fintype κ₂]
    (m n : ι → ℕ) (c : κ₁ → κ₂ → ℂ)
    (A : (i : ι) → κ₁ → κ₂ → Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    (∑ a : κ₁, ∑ b : κ₂, c a b • Matrix.blockDiagonal' (fun i =>
      (1 : Matrix (Fin (m i)) (Fin (m i)) ℂ) ⊗ₖ A i a b)) =
      Matrix.blockDiagonal' (fun i =>
        (1 : Matrix (Fin (m i)) (Fin (m i)) ℂ) ⊗ₖ
          (∑ a : κ₁, ∑ b : κ₂, c a b • A i a b)) := by
  classical
  simp_rw [← Matrix.blockDiagonal'_smul]
  let blockDiagonalHom :=
    Matrix.blockDiagonal'AddMonoidHom
      (fun i => Fin (m i) × Fin (n i)) (fun i => Fin (m i) × Fin (n i)) ℂ
  change (∑ a : κ₁, ∑ b : κ₂, blockDiagonalHom (fun i =>
      c a b • ((1 : Matrix (Fin (m i)) (Fin (m i)) ℂ) ⊗ₖ A i a b))) =
    blockDiagonalHom (fun i =>
      (1 : Matrix (Fin (m i)) (Fin (m i)) ℂ) ⊗ₖ
        (∑ a : κ₁, ∑ b : κ₂, c a b • A i a b))
  simp_rw [← map_sum blockDiagonalHom]
  congr 1
  funext i
  ext x y
  by_cases hxy : x.1 = y.1
  · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  · simp [Matrix.sum_apply, Matrix.smul_apply, hxy]

/-- **Positive-length final-label selectors make every pair fusion map surjective.**

Suppose that the positive trace-power coefficients are independent of the positive chain
length, and that common words of one positive length separate the labelled tensors. Then the
range projection of every fusion isometry is the identity.

The positivity of the selector length is essential: products of conjugated letters telescope
through `U† U = 1` only for nonempty words. The selector hypothesis is the finite-word form of
the simultaneous inverse at line 269 of arXiv:1511.08090. It is not derived here from
individual injectivity.

This is the support-completeness step behind the invertible total fusion matrix discussed in
arXiv:1511.08090, lines 181--191. It concerns the full pair fusion map; it does not construct a
fixed-final $F$-matrix or prove a pentagon identity.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, lines 181--191,
247--252, and 269. -/
theorem fusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β : Λ) :
    Fam.fusionIsometry α β * (Fam.fusionIsometry α β)ᴴ = 1 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, (Nat.succ_pred_eq_of_pos hS).symm⟩
  let U := Fam.fusionIsometry α β
  let A := (mulTensor (Fam.tensor α) (Fam.tensor β)).toMPSTensor
  let D : Fin (p * p) →
      Matrix ((γ : Λ) × (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ)))
        ((γ : Λ) × (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) ℂ :=
    fun ij => Matrix.blockDiagonal' fun γ =>
      (1 : Matrix (Fin (Fam.chi.dim α β γ)) (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
        (Fam.tensor γ).toMPSTensor ij
  have hU : Uᴴ * U = 1 := Fam.isometry α β
  have hletter (ij : Fin (p * p)) : D ij = U * A ij * Uᴴ := by
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ij
    simpa [U, A, D, MPOTensor.toMPSTensor,
      Fam.chi_matrix_eq_one_of_lengthIndependent c hχ hLI] using
      (Fam.fusion α β i k).symm
  have evalWord_ofFn_eq_prod (m : ℕ) (w : Fin m → Fin (p * p)) :
      _root_.evalWord D (List.ofFn w) = (List.ofFn fun l => D (w l)).prod := by
    induction m with
    | zero => simp only [List.ofFn_zero, _root_.evalWord, List.prod_nil]
    | succ m ih =>
        simp only [List.ofFn_succ, _root_.evalWord, List.prod_cons]
        congr 1
        exact ih (w ∘ Fin.succ)
  have hword (w : Fin (n + 1) → Fin (p * p)) :
      _root_.evalWord D (List.ofFn w) =
        U * MPSTensor.evalWord A (List.ofFn w) * Uᴴ := by
    rw [evalWord_ofFn_eq_prod, MPSTensor.evalWord_ofFn_eq_prod]
    have hconj := MPOTensor.listProd_conj_of_conjTranspose_mul_self U hU
      (fun l => A (w l))
    simpa only [hletter] using hconj
  have hDword : ∀ w : List (Fin (p * p)),
      _root_.evalWord D w = Matrix.blockDiagonal' fun γ =>
        (1 : Matrix (Fin (Fam.chi.dim α β γ))
          (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
          MPSTensor.evalWord (Fam.tensor γ).toMPSTensor w := by
    intro w
    induction w with
    | nil =>
        simp only [_root_.evalWord, MPSTensor.evalWord_nil]
        rw [show (fun γ =>
            (1 : Matrix (Fin (Fam.chi.dim α β γ))
              (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
              (1 : Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)) =
            fun _ => 1 by
          funext γ
          exact Matrix.one_kronecker_one]
        exact Matrix.blockDiagonal'_one.symm
    | cons ij w ih =>
        simp only [_root_.evalWord, MPSTensor.evalWord_cons, ih, D]
        rw [← Matrix.blockDiagonal'_mul]
        congr 1
        funext γ
        rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  choose coeff hSelf hOther using hSel
  have hcoeffTotal (γ : Λ) :
      (∑ ε : Λ, ∑ w : Fin (n + 1) → Fin (p * p),
        coeff ε w • MPSTensor.evalWord (Fam.tensor γ).toMPSTensor (List.ofFn w)) = 1 := by
    rw [Finset.sum_eq_single γ]
    · exact hSelf γ
    · intro ε _ hε
      exact hOther ε γ hε.symm
    · simp
  have htotal :
      (∑ ε : Λ, ∑ w : Fin (n + 1) → Fin (p * p),
        coeff ε w • _root_.evalWord D (List.ofFn w)) = 1 := by
    calc
      (∑ ε : Λ, ∑ w : Fin (n + 1) → Fin (p * p),
          coeff ε w • _root_.evalWord D (List.ofFn w)) =
          Matrix.blockDiagonal' fun γ =>
            (1 : Matrix (Fin (Fam.chi.dim α β γ))
              (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
              (∑ ε : Λ, ∑ w : Fin (n + 1) → Fin (p * p),
                coeff ε w •
                  MPSTensor.evalWord (Fam.tensor γ).toMPSTensor (List.ofFn w)) := by
        simp_rw [hDword]
        exact sum_sum_smul_blockDiagonal'_one_kronecker
          (fun γ => Fam.chi.dim α β γ) Fam.bondDim coeff
          (fun γ _ w =>
            MPSTensor.evalWord (Fam.tensor γ).toMPSTensor (List.ofFn w))
      _ = Matrix.blockDiagonal' fun γ =>
          (1 : Matrix (Fin (Fam.chi.dim α β γ))
            (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
            (1 : Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ) := by
        congr 1
        funext γ
        rw [hcoeffTotal]
      _ = 1 := by
        rw [show (fun γ =>
            (1 : Matrix (Fin (Fam.chi.dim α β γ))
              (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ
              (1 : Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)) =
            fun _ => 1 by
          funext γ
          exact Matrix.one_kronecker_one]
        exact Matrix.blockDiagonal'_one
  let P := U * Uᴴ
  have hPword (w : Fin (n + 1) → Fin (p * p)) :
      P * _root_.evalWord D (List.ofFn w) =
        _root_.evalWord D (List.ofFn w) := by
    rw [hword]
    simp only [P, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  calc
    U * Uᴴ = P := rfl
    _ = P * 1 := by rw [Matrix.mul_one]
    _ = P * (∑ ε : Λ, ∑ w : Fin (n + 1) → Fin (p * p),
        coeff ε w • _root_.evalWord D (List.ofFn w)) := by rw [htotal]
    _ = ∑ ε : Λ, ∑ w : Fin (n + 1) → Fin (p * p),
        coeff ε w • _root_.evalWord D (List.ofFn w) := by
      simp_rw [Matrix.mul_sum, Matrix.mul_smul, hPword]
    _ = 1 := htotal

/-- A source basis of normal tensors makes every length-independent pair
fusion isometry a coisometry.

The BNT hypothesis supplies a common positive word span.  Matrix-unit
selectors extracted from that span give the final-label selectors required by
`fusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords`.
Thus neither selectors nor coisometry are additional hypotheses.

This is a derived argument from arXiv:1606.00608, BNT separation at lines
317--345, equation `Ualphabeta` at lines 986--993, and length independence at
lines 995--1010.  The simultaneous-inverse interpretation agrees with
arXiv:1511.08090, lines 269--277 and 427--431. -/
theorem fusionIsometry_mul_conjTranspose_eq_one_of_bnt_of_lengthIndependent
    {g D : ℕ} (Fam : BNTFusionIsometryFamily (Fin g) p)
    {A : MPSTensor (p * p) D}
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors A
      (fun γ : Fin g ↦
        ⟨Fam.bondDim γ, (Fam.tensor γ).toMPSTensor⟩))
    (c : BNTLabelCoefficientFamily (Fin g))
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) (α β : Fin g) :
    Fam.fusionIsometry α β * (Fam.fusionIsometry α β)ᴴ = 1 := by
  obtain ⟨S, hS, hSpan⟩ := hBNT.exists_positive_wordTupleSpanTop
  have hBlockSelectors :=
    MPSTensor.hasBlockSelectorWords_of_wordTupleSpanTop
      (fun γ ↦ (Fam.tensor γ).toMPSTensor) hSpan
  exact Fam.fusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
    c hχ hLI hS
      (Fam.hasFinalLabelSelectorWords_of_hasBlockSelectorWords hBlockSelectors)
      α β

private theorem mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one_of_card_eq
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (U : Matrix m n ℂ) (hcard : Fintype.card m = Fintype.card n)
    (hU : Uᴴ * U = 1) : U * Uᴴ = 1 := by
  let e : m ≃ n := Fintype.equivOfCardEq hcard
  let V : Matrix n n ℂ := U.submatrix e.symm id
  have hV : Vᴴ * V = 1 := by
    unfold V
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ e.symm _, hU, Matrix.submatrix_id_id]
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.mpr hV
  have hreindex : (U * Uᴴ).submatrix e.symm e.symm = 1 := by
    rw [← Matrix.submatrix_mul_equiv U Uᴴ e.symm (Equiv.refl n) e.symm]
    exact hVV
  ext i j
  have hij := congrArg (fun M => M (e i) (e j)) hreindex
  simpa [Matrix.one_apply] using hij

private theorem card_fusionIndex_eq_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β : Λ) :
    Fintype.card ((γ : Λ) ×
        (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) =
      Fintype.card (Fin (Fam.bondDim α * Fam.bondDim β)) := by
  let U := Fam.fusionIsometry α β
  apply Nat.le_antisymm
  · calc
      Fintype.card ((γ : Λ) ×
          (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) =
          (1 : Matrix ((γ : Λ) ×
            (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ)))
            ((γ : Λ) ×
              (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) ℂ).rank :=
            Matrix.rank_one.symm
      _ = (U * Uᴴ).rank := by
        rw [Fam.fusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
          c hχ hLI hS hSel α β]
      _ ≤ U.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin (Fam.bondDim α * Fam.bondDim β)) :=
        Matrix.rank_le_card_width _
  · calc
      Fintype.card (Fin (Fam.bondDim α * Fam.bondDim β)) =
          (1 : Matrix (Fin (Fam.bondDim α * Fam.bondDim β))
            (Fin (Fam.bondDim α * Fam.bondDim β)) ℂ).rank := Matrix.rank_one.symm
      _ = (Uᴴ * U).rank := by rw [Fam.isometry]
      _ ≤ U.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card ((γ : Λ) ×
          (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) :=
        Matrix.rank_le_card_height _

private theorem card_leftTripleFusionIndex_eq_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β γ : Λ) :
    Fintype.card (Fam.LeftTripleFusionIndex α β γ) =
      Fintype.card (Fin (Fam.bondDim α * Fam.bondDim β * Fam.bondDim γ)) := by
  have hpair (a b : Λ) :
      ∑ δ, Fam.chi.dim a b δ * Fam.bondDim δ = Fam.bondDim a * Fam.bondDim b := by
    simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] using
      Fam.card_fusionIndex_eq_of_lengthIndependent_of_selectorWords
        c hχ hLI hS hSel a b
  simp only [LeftTripleFusionIndex, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin]
  calc
    ∑ δ, ∑ ε, Fam.chi.dim α β δ *
        (Fam.chi.dim δ γ ε * Fam.bondDim ε) =
        ∑ δ, Fam.chi.dim α β δ *
          (∑ ε, Fam.chi.dim δ γ ε * Fam.bondDim ε) := by
      apply Finset.sum_congr rfl
      intro δ _
      rw [Finset.mul_sum]
    _ = ∑ δ, Fam.chi.dim α β δ * (Fam.bondDim δ * Fam.bondDim γ) := by
      simp_rw [hpair]
    _ = (∑ δ, Fam.chi.dim α β δ * Fam.bondDim δ) * Fam.bondDim γ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro δ _
      simp [Nat.mul_assoc]
    _ = Fam.bondDim α * Fam.bondDim β * Fam.bondDim γ := by rw [hpair]

private theorem card_rightTripleFusionIndex_eq_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β γ : Λ) :
    Fintype.card (Fam.RightTripleFusionIndex α β γ) =
      Fintype.card (Fin (Fam.bondDim α * (Fam.bondDim β * Fam.bondDim γ))) := by
  have hpair (a b : Λ) :
      ∑ δ, Fam.chi.dim a b δ * Fam.bondDim δ = Fam.bondDim a * Fam.bondDim b := by
    simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] using
      Fam.card_fusionIndex_eq_of_lengthIndependent_of_selectorWords
        c hχ hLI hS hSel a b
  simp only [RightTripleFusionIndex, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin]
  calc
    ∑ δ, ∑ ε, Fam.chi.dim β γ δ *
        (Fam.chi.dim α δ ε * Fam.bondDim ε) =
        ∑ δ, Fam.chi.dim β γ δ *
          (∑ ε, Fam.chi.dim α δ ε * Fam.bondDim ε) := by
      apply Finset.sum_congr rfl
      intro δ _
      rw [Finset.mul_sum]
    _ = ∑ δ, Fam.chi.dim β γ δ * (Fam.bondDim α * Fam.bondDim δ) := by
      simp_rw [hpair]
    _ = Fam.bondDim α *
        (∑ δ, Fam.chi.dim β γ δ * Fam.bondDim δ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro δ _
      simp [Nat.mul_assoc, Nat.mul_comm]
    _ = Fam.bondDim α * (Fam.bondDim β * Fam.bondDim γ) := by rw [hpair]

/-- **Positive-length final-label selectors make the left iterated fusion map surjective.**

The pair fusion maps are surjective by the selector argument above. Their source and target
dimensions therefore agree, and the same cardinal calculation for the two fusion stages shows
that the left iterated fusion isometry is square. Its isometry identity then gives the stated
range identity.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, lines 181--191,
247--252, and 269. -/
theorem leftFusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β γ : Λ) :
    Fam.leftFusionIsometry α β γ * (Fam.leftFusionIsometry α β γ)ᴴ = 1 := by
  exact mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one_of_card_eq
    (Fam.leftFusionIsometry α β γ)
    (Fam.card_leftTripleFusionIndex_eq_of_lengthIndependent_of_selectorWords
      c hχ hLI hS hSel α β γ)
    (Fam.leftFusionIsometry_isometry α β γ)

/-- **Positive-length final-label selectors make the right iterated fusion map surjective.**

This is the right-associated counterpart of
`leftFusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords`.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, lines 181--191,
247--252, and 269. -/
theorem rightFusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β γ : Λ) :
    Fam.rightFusionIsometry α β γ * (Fam.rightFusionIsometry α β γ)ᴴ = 1 := by
  exact mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one_of_card_eq
    (Fam.rightFusionIsometry α β γ)
    (Fam.card_rightTripleFusionIndex_eq_of_lengthIndependent_of_selectorWords
      c hχ hLI hS hSel α β γ)
    (Fam.rightFusionIsometry_isometry α β γ)

/-- **The full triple-fusion comparison has a right adjoint inverse under positive-length
final-label separation.**

The comparison times its adjoint is the left iterated fusion range projection, which is the
identity by selector completeness. This is a full-direct-sum statement; no fixed-final
$F$-matrix is asserted.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, lines 181--191,
247--252, and 269. -/
theorem tripleFusionComparison_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β γ : Λ) :
    Fam.tripleFusionComparison α β γ * (Fam.tripleFusionComparison α β γ)ᴴ = 1 := by
  rw [Fam.tripleFusionComparison_mul_conjTranspose,
    Fam.leftFusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
      c hχ hLI hS hSel]

/-- **The adjoint of the full triple-fusion comparison is also a left inverse under
positive-length final-label separation.**

This is the opposite product of
`tripleFusionComparison_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords`.
It proves two-sided invertibility only on the full direct sums; extracting an invertible
fixed-final multiplicity matrix also requires off-diagonal separation,
injectivity of the selected tensor, and positive bond dimension.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, lines 181--191,
247--252, and 269. -/
theorem conjTranspose_mul_tripleFusionComparison_eq_one_of_lengthIndependent_of_selectorWords
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ} (hS : 0 < S)
    (hSel : Fam.HasFinalLabelSelectorWords S) (α β γ : Λ) :
    (Fam.tripleFusionComparison α β γ)ᴴ * Fam.tripleFusionComparison α β γ = 1 := by
  rw [Fam.conjTranspose_mul_tripleFusionComparison,
    Fam.rightFusionIsometry_mul_conjTranspose_eq_one_of_lengthIndependent_of_selectorWords
      c hχ hLI hS hSel]

/-- The fixed-final matrix entries of the triple-fusion comparison intertwine
the corresponding final-label tensor entries.

Source: arXiv:1511.08090, equations `zippercondition2` and `Fmove`, lines
237--277; arXiv:1606.00608, lines 995--1010. -/
private theorem tripleFusionComparison_final_entry_intertwines_of_lengthIndependent
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) (α β γ ε ε' δL δR : Λ)
    (μL : Fin (Fam.chi.dim α β δL)) (νL : Fin (Fam.chi.dim δL γ ε))
    (μR : Fin (Fam.chi.dim β γ δR)) (νR : Fin (Fam.chi.dim α δR ε'))
    (bL : Fin (Fam.bondDim ε)) (bR : Fin (Fam.bondDim ε'))
    (ij : Fin (p * p)) :
    (∑ b, (Fam.tensor ε).toMPSTensor ij bL b *
        Fam.tripleFusionComparison α β γ
          (Fam.leftFinalRow α β γ ε ⟨δL, μL, νL, b⟩)
          (Fam.rightFinalRow α β γ ε' ⟨δR, μR, νR, bR⟩)) =
      ∑ b, Fam.tripleFusionComparison α β γ
          (Fam.leftFinalRow α β γ ε ⟨δL, μL, νL, bL⟩)
          (Fam.rightFinalRow α β γ ε' ⟨δR, μR, νR, b⟩) *
        (Fam.tensor ε').toMPSTensor ij b bR := by
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ij
  have hFull := Fam.tripleFusionComparison_intertwines_of_lengthIndependent
    c hχ hLI α β γ i k
  have hEntry := congrArg
    (fun X => X (Fam.leftFinalRow α β γ ε ⟨δL, μL, νL, bL⟩)
      (Fam.rightFinalRow α β γ ε' ⟨δR, μR, νR, bR⟩)) hFull
  simpa [Matrix.mul_apply, Matrix.blockDiagonal'_apply,
    leftFinalRow, rightFinalRow, Fintype.sum_sigma,
    Fintype.sum_prod_type, Matrix.one_apply, MPOTensor.toMPSTensor]
    using hEntry

private theorem rectangularIntertwiner_eq_zero_of_selectorWords
    {d D₁ D₂ S : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (C : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hC : ∀ i : Fin d, A i * C = C * B i)
    (c : (Fin S → Fin d) → ℂ)
    (hA : (∑ w : Fin S → Fin d,
      c w • MPSTensor.evalWord A (List.ofFn w)) = 1)
    (hB : (∑ w : Fin S → Fin d,
      c w • MPSTensor.evalWord B (List.ofFn w)) = 0) :
    C = 0 := by
  have hWord : ∀ w : List (Fin d),
      MPSTensor.evalWord A w * C = C * MPSTensor.evalWord B w := by
    intro w
    induction w with
    | nil => simp
    | cons i w ih =>
        simp only [MPSTensor.evalWord_cons]
        calc
          (A i * MPSTensor.evalWord A w) * C =
              A i * (MPSTensor.evalWord A w * C) := Matrix.mul_assoc _ _ _
          _ =
              A i * (C * MPSTensor.evalWord B w) := by rw [ih]
          _ = (A i * C) * MPSTensor.evalWord B w := by rw [Matrix.mul_assoc]
          _ = (C * B i) * MPSTensor.evalWord B w := by rw [hC i]
          _ = C * (B i * MPSTensor.evalWord B w) := by rw [Matrix.mul_assoc]
  have hSum :
      (∑ w : Fin S → Fin d,
        (c w • MPSTensor.evalWord A (List.ofFn w)) * C) =
      ∑ w : Fin S → Fin d,
        C * (c w • MPSTensor.evalWord B (List.ofFn w)) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hWord]
  rw [← Matrix.sum_mul, hA, Matrix.one_mul, ← Matrix.mul_sum, hB,
    Matrix.mul_zero] at hSum
  exact hSum

/-- **Conditional off-diagonal final-sector vanishing.** Suppose the positive
trace-power coefficients are independent of the positive chain length and a
common finite word family separates the final-label tensors.  Then the full
triple-fusion comparison has no corner from a right final sector `ε'` to a
distinct left final sector `ε`.

**Scope restriction (simultaneous final-label separation):** the selector
hypothesis is the finite-word form of the simultaneous inverse at line 269 of
arXiv:1511.08090.  It is not derived from the current assumptions on
`BNTFusionIsometryFamily`; this remaining implication is documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

This theorem asserts only off-diagonal vanishing.  It does not assert that a
diagonal corner is invertible, identify such a corner with an $F$-matrix, or
prove a pentagon identity.

Source: arXiv:1511.08090, equations `zippercondition2` and `Fmove`, lines
237--277, especially line 269; arXiv:1606.00608, lines 995--1010. -/
theorem tripleFusionComparison_finalSector_submatrix_eq_zero
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ}
    (hSel : Fam.HasFinalLabelSelectorWords S)
    (α β γ ε ε' : Λ) (hε : ε' ≠ ε) :
    (Fam.tripleFusionComparison α β γ).submatrix
        (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε') = 0 := by
  let C := Fam.tripleFusionComparison α β γ
  ext x y
  rcases x with ⟨δL, μL, νL, bL⟩
  rcases y with ⟨δR, μR, νR, bR⟩
  let Cblock : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε')) ℂ :=
    fun b b' => C (Fam.leftFinalRow α β γ ε ⟨δL, μL, νL, b⟩)
      (Fam.rightFinalRow α β γ ε' ⟨δR, μR, νR, b'⟩)
  have hLetter : ∀ ij : Fin (p * p),
      (Fam.tensor ε).toMPSTensor ij * Cblock =
        Cblock * (Fam.tensor ε').toMPSTensor ij := by
    intro ij
    ext b b'
    simpa [Cblock, C, Matrix.mul_apply] using
      Fam.tripleFusionComparison_final_entry_intertwines_of_lengthIndependent
        c hχ hLI α β γ ε ε' δL δR μL νL μR νR b b' ij
  obtain ⟨coeff, hSelf, hOther⟩ := hSel ε
  have hZero := rectangularIntertwiner_eq_zero_of_selectorWords
    (Fam.tensor ε).toMPSTensor (Fam.tensor ε').toMPSTensor Cblock hLetter
    coeff hSelf (hOther ε' hε)
  exact congrArg (fun X => X bL bR) hZero

/-- **Conditional fixed-final Kronecker form.** Suppose the positive
trace-power coefficients are independent of the positive chain length, common
finite word selectors separate the final-label tensors, and the selected final
tensor is injective at the present blocking. Then the diagonal fixed-final corner of the full
triple-fusion comparison has the form \(F_\varepsilon \otimes 1\), while every
corner from a distinct right final sector into the selected left sector
vanishes.

**Scope restriction (injectivity and simultaneous final-label separation):**
neither injectivity at the present blocking nor the selector hypothesis is derived
from the current assumptions on `BNTFusionIsometryFamily`. The missing
implications are documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

The matrix `F` is rectangular in general. This theorem does not assert that it
or the diagonal comparison corner is invertible, identify it with the printed
$F$-matrix, or prove a pentagon identity.

Source: arXiv:1511.08090, equations `Fmove` and `zippercondition2`, lines
237--277, especially the simultaneous inverse at line 269, the injectivity
argument following equation `pentagon3`, and the tensor-product conclusion at
line 277; arXiv:1606.00608, lines 995--1010. -/
theorem exists_tripleFusionComparison_finalSector_eq_kronecker_one_of_separation
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ}
    (hSel : Fam.HasFinalLabelSelectorWords S)
    (α β γ ε : Λ)
    (hε : MPSTensor.IsInjective (Fam.tensor ε).toMPSTensor) :
    ∃ F : Matrix (Fam.LeftFinalMultiplicity α β γ ε)
        (Fam.RightFinalMultiplicity α β γ ε) ℂ,
      ((Fam.tripleFusionComparison α β γ).submatrix
          (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε)).submatrix
            (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm =
          F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ) ∧
        ∀ ε' : Λ, ε' ≠ ε →
          (Fam.tripleFusionComparison α β γ).submatrix
            (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε') = 0 := by
  let C := (Fam.tripleFusionComparison α β γ).submatrix
    (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε)
  have hC : ∀ ij : Fin (p * p),
      ((1 : Matrix (Fam.LeftFinalMultiplicity α β γ ε)
          (Fam.LeftFinalMultiplicity α β γ ε) ℂ) ⊗ₖ
          (Fam.tensor ε).toMPSTensor ij) *
          C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm =
        C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm *
          ((1 : Matrix (Fam.RightFinalMultiplicity α β γ ε)
            (Fam.RightFinalMultiplicity α β γ ε) ℂ) ⊗ₖ
            (Fam.tensor ε).toMPSTensor ij) := by
    intro ij
    ext ⟨⟨δL, μL, νL⟩, bL⟩ ⟨⟨δR, μR, νR⟩, bR⟩
    simpa [C, Matrix.mul_apply,
      leftFinalIndexEquiv_symm_apply, rightFinalIndexEquiv_symm_apply,
      Fintype.sum_prod_type, Matrix.one_apply] using
      Fam.tripleFusionComparison_final_entry_intertwines_of_lengthIndependent
        c hχ hLI α β γ ε ε δL δR μL νL μR νR bL bR ij
  obtain ⟨F, hF⟩ :=
    Fam.exists_reindexed_intertwiner_eq_kronecker_one_of_isInjective
      α β γ ε hε C hC
  refine ⟨F, ?_, ?_⟩
  · exact hF
  · intro ε' hε'
    exact Fam.tripleFusionComparison_finalSector_submatrix_eq_zero
      c hχ hLI hSel α β γ ε ε' hε'

end MPOTensor.BNTFusionIsometryFamily
