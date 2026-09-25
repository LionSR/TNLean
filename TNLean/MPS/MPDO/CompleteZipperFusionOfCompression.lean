/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock
import TNLean.MPS.FundamentalTheorem.Reduction.Splitting
import TNLean.MPS.MPDO.CompleteZipperFusionDefs

/-!
# Complete zipper fusion families from split compressions

The multi-block compression theorem decomposes the product `O_a O_b` of two matrix product
operators: after a change of coordinates, every letter of the product tensor is block upper
triangular, with the fusion channels `c` repeated `N_{ab}^c` times on the diagonal and zero
diagonal blocks otherwise.  When the product has no nonzero blocks above the diagonal, the
remainder of the compression vanishes.  This file shows that the compression pairs are then
complete zipper fusion tensors: they are biorthogonal, reconstruct every letter of the product,
and satisfy both zipper identities.

The hypothesis that the remainder vanishes is the condition of arXiv:1511.08090,
`AnyonsPEPS.tex`, lines 181--191: the absence of nonzero blocks above the diagonal, which is
what makes equation `inversegaugeone` hold.  The source states that this condition fails in
general (lines 181--183) and assumes it, in the form of the zipper condition, for the
associativity analysis (lines 193--200 and 247).  The star-closed case supplies it
(`MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_star`).

## Main definitions

* `MPOTensor.CompleteZipperFusionFamily.ofCompression`: the complete zipper fusion family whose
  fusion tensors and left inverses are the pairs of split multi-block compressions of the
  pairwise products.
* `MPOTensor.CompleteZipperFusionFamily.ofStar`: the complete zipper fusion family in the
  star-closed case, built from the split compressions of
  `exists_pairCompression_remainder_eq_zero_of_star`.

## Main statements

* `MPOTensor.CompleteZipperFusionFamily.exists_pairCompression_remainder_eq_zero_of_star`: under
  the fusion rules on word traces and the star closure of the product tensor, the product `O_a O_b`
  has a multi-block compression with vanishing remainder.
* `MPOTensor.CompleteZipperFusionFamily.exists_ofStar_fusionTensor_eq`: the fusion tensors of
  `ofStar` are the compression maps of split compressions of the pairwise products.

* `MPOTensor.CompleteZipperFusionFamily.ofCompression_fusionTensor`,
  `MPOTensor.CompleteZipperFusionFamily.ofCompression_fusionTensorLeftInverse`: the fusion
  tensors of this family are the compression pairs.

## References

* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--200.
* arXiv:2203.12563, `REsubmission.tex`, lines 361--391 (fusion tensors and their orthogonality).
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor.CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}

section Compression

variable {D : Λ → ℕ} (T : ∀ a, MPOTensor p (D a)) (N : Λ → Λ → Λ → ℕ)

/-- The multi-block compression of the product `O_a O_b` whose target slots are the pairs
`(c, μ)` with `μ < N_{ab}^c`, the slot `(c, μ)` carrying the block `O_c`. -/
abbrev PairCompression (a b : Λ) : Type u :=
  MPSTensor.MultiBlockCompression (D := fun s : (c : Λ) × Fin (N a b c) => D s.1)
    (mulTensor (T a) (T b)).toMPSTensor Finset.univ
    fun s : (c : Λ) × Fin (N a b c) => (T s.1).toMPSTensor

variable {T N}

/-- The slot `(c, μ)` of a pair compression. -/
abbrev pairSlot {a b : Λ} (c : Λ) (μ : Fin (N a b c)) :
    {s : (c : Λ) × Fin (N a b c) // s ∈ (Finset.univ : Finset _)} :=
  ⟨⟨c, μ⟩, Finset.mem_univ _⟩

/-- The synthesis matrix collecting the compression maps `V_{(c,μ)}` of a pair compression as
columns, on the product bond space `Fin (D a) × Fin (D b)`. -/
noncomputable def compressionSynthesis {a b : Λ} (P : PairCompression T N a b) :
    Matrix (Fin (D a) × Fin (D b)) ((c : Λ) × (Fin (N a b c) × Fin (D c))) ℂ :=
  fun x y => P.right (pairSlot y.1 y.2.1) (finProdFinEquiv x) y.2.2

/-- The analysis matrix collecting the compression maps `W_{(c,μ)}` of a pair compression as
rows. -/
noncomputable def compressionAnalysis {a b : Λ} (P : PairCompression T N a b) :
    Matrix ((c : Λ) × (Fin (N a b c) × Fin (D c))) (Fin (D a) × Fin (D b)) ℂ :=
  fun y x => P.left (pairSlot y.1 y.2.1) y.2.2 (finProdFinEquiv x)

theorem compressionAnalysis_mul_compressionSynthesis {a b : Λ} (P : PairCompression T N a b) :
    compressionAnalysis P * compressionSynthesis P = 1 := by
  funext ⟨c, μ, y⟩ ⟨c', μ', y'⟩
  have hsum : (compressionAnalysis P * compressionSynthesis P) ⟨c, μ, y⟩ ⟨c', μ', y'⟩ =
      (P.left (pairSlot c μ) * P.right (pairSlot c' μ')) y y' := by
    simp only [Matrix.mul_apply]
    exact Fintype.sum_equiv finProdFinEquiv _ _ fun x => rfl
  rw [hsum]
  by_cases h : (⟨c, μ⟩ : (c : Λ) × Fin (N a b c)) = ⟨c', μ'⟩
  · obtain ⟨rfl, hμ⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl := eq_of_heq hμ
    rw [P.left_mul_right_self]
    change (1 : Matrix (Fin (D c)) (Fin (D c)) ℂ) y y' = _
    simp [Matrix.one_apply]
  · rw [P.left_mul_right_of_ne (fun hst => h (congrArg Subtype.val hst)),
      Matrix.one_apply_ne (fun hst => h (by cases hst; rfl))]
    rfl

/-- An entry of `S (⊕_c 1 ⊗ B_c) A` is the sum of the matching entries of the blocks. -/
private theorem mul_blockDiagonal_one_kronecker_mul_apply {m : Type*}
    {M : Λ → ℕ} {n : Λ → ℕ}
    (S : Matrix m ((c : Λ) × (Fin (M c) × Fin (n c))) ℂ)
    (B : ∀ c, Matrix (Fin (n c)) (Fin (n c)) ℂ)
    (A : Matrix ((c : Λ) × (Fin (M c) × Fin (n c))) m ℂ) (x x' : m) :
    (S * Matrix.blockDiagonal' (fun c => (1 : Matrix (Fin (M c)) (Fin (M c)) ℂ) ⊗ₖ B c) * A)
        x x' =
      ∑ c, ∑ μ, ∑ y, ∑ y', S x ⟨c, μ, y⟩ * B c y y' * A ⟨c, μ, y'⟩ x' := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single c
    (fun c' _ hc' => Finset.sum_eq_zero fun q _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc', mul_zero])
    (fun h => absurd (Finset.mem_univ c) h)]
  simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_mul]
  rw [Finset.sum_eq_single μ (fun μ' _ hμ' => Finset.sum_eq_zero fun _ _ => by simp [hμ'])
    (fun h => absurd (Finset.mem_univ μ) h)]
  simp

omit [Fintype Λ] [DecidableEq Λ] in
/-- The pair letter of the product is the corresponding letter of the product tensor, read on
the product bond space. -/
private theorem pairLetter_apply (a b : Λ) (i k : Fin p) (x x' : Fin (D a) × Fin (D b)) :
    (∑ j : Fin p, T a i j ⊗ₖ T b j k) x x' =
      (mulTensor (T a) (T b)).toMPSTensor (finProdFinEquiv (i, k))
        (finProdFinEquiv x) (finProdFinEquiv x') := by
  simp [MPOTensor.toMPSTensor, mulTensor_apply, Matrix.submatrix_apply]

/-- **Reconstruction from a split compression.** If the remainder vanishes, every letter of
the product is the sum of its compressed blocks, equation `inversegaugeone`.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 181--191. -/
theorem pairLetter_eq_compressionSynthesis_mul {a b : Λ} (P : PairCompression T N a b)
    (hP : P.remainder = 0) (i k : Fin p) :
    (∑ j : Fin p, T a i j ⊗ₖ T b j k) =
      compressionSynthesis P * Matrix.blockDiagonal' (fun c =>
        (1 : Matrix (Fin (N a b c)) (Fin (N a b c)) ℂ) ⊗ₖ T c i k) *
        compressionAnalysis P := by
  have hrec := congrFun hP (finProdFinEquiv (i, k))
  simp only [MPSTensor.MultiBlockCompression.remainder, Pi.zero_apply, sub_eq_zero] at hrec
  funext x x'
  rw [pairLetter_apply, hrec, Matrix.sum_apply, mul_blockDiagonal_one_kronecker_mul_apply]
  refine (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _) _
    (fun t : (c : Λ) × Fin (N a b c) =>
      (P.right (pairSlot t.1 t.2) * (T t.1).toMPSTensor (finProdFinEquiv (i, k)) *
        P.left (pairSlot t.1 t.2)) (finProdFinEquiv x) (finProdFinEquiv x')) fun _ => rfl).trans ?_
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun μ _ => ?_
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  simp [compressionSynthesis, compressionAnalysis, MPOTensor.toMPSTensor]

/-- **Complete zipper fusion family from split compressions.** Let `O_a` be injective MPO blocks
of positive bond dimension, with a simultaneous left inverse of their labelled letters, and for
every pair `(a, b)` let `P a b` be a multi-block compression of the product `O_a O_b` onto
`N_{ab}^c` copies of each `O_c`, with vanishing remainder.  Then the compression pairs are the
fusion tensors and left inverses of a complete zipper fusion family.

The vanishing remainder is the absence of nonzero blocks above the diagonal in
arXiv:1511.08090, `AnyonsPEPS.tex`, lines 181--191; the injectivity, multiplicities and
simultaneous left inverse are the remaining data of that source at lines 156--163 and
269--277.

**Local fix (arXiv:1511.08090, line 269):** the source derives the simultaneous left inverse
`K` from injectivity of each block, which does not suffice when there are several blocks: two
injective, non-equivalent blocks at physical dimension two can have no simultaneous left
inverse.  `K` is therefore an input here, recording joint linear independence of the blocks at
one site.  After a common positive blocking it is derived for normal blocks that are pairwise
inequivalent up to a nonzero scalar (`ofCompressionBlocked`).  Documented in
`docs/paper-gaps/bmwshv17_joint_block_left_inverse.tex`. -/
noncomputable def ofCompression (hD : ∀ a, 0 < D a)
    (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor)
    (P : ∀ a b, PairCompression T N a b) (hP : ∀ a b, (P a b).remainder = 0)
    (K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c))) (Fin p × Fin p) ℂ)
    (hK : ∀ (c d : Λ) (x y : Fin (D c)) (x' y' : Fin (D d)),
      (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
        if h : c = d then
          if _ : h ▸ x = x' then if _ : h ▸ y = y' then 1 else 0 else 0
        else 0) :
    CompleteZipperFusionFamily Λ p where
  bondDim := D
  bondDim_pos := hD
  tensor := T
  tensor_injective := hT
  fusionMultiplicity := N
  fusionSynthesis a b := compressionSynthesis (P a b)
  fusionAnalysis a b := compressionAnalysis (P a b)
  analysis_mul_synthesis a b := compressionAnalysis_mul_compressionSynthesis (P a b)
  pairLetter_mul_synthesis a b i k := by
    rw [pairLetter_eq_compressionSynthesis_mul (P a b) (hP a b), Matrix.mul_assoc,
      compressionAnalysis_mul_compressionSynthesis, Matrix.mul_one]
  analysis_mul_pairLetter a b i k := by
    rw [pairLetter_eq_compressionSynthesis_mul (P a b) (hP a b), ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, compressionAnalysis_mul_compressionSynthesis, Matrix.one_mul]
  pairLetter_eq_synthesis_mul_directSum_mul_analysis a b i k :=
    pairLetter_eq_compressionSynthesis_mul (P a b) (hP a b) i k
  blockLeftInverse := K
  blockLeftInverse_apply := hK


/-- The fusion tensor `X^c_{ab,μ}` of `ofCompression` is the compression map `V_{(c,μ)}` of the
compression of `O_a O_b`. -/
theorem ofCompression_fusionTensor (hD : ∀ a, 0 < D a)
    (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor)
    (P : ∀ a b, PairCompression T N a b) (hP : ∀ a b, (P a b).remainder = 0)
    (K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c))) (Fin p × Fin p) ℂ) (hK)
    (a b c : Λ) (μ : Fin (N a b c)) (x : Fin (D a) × Fin (D b)) (z : Fin (D c)) :
    (ofCompression hD hT P hP K hK).fusionTensor a b c μ x z =
      (P a b).right (pairSlot c μ) (finProdFinEquiv x) z := rfl

/-- The left inverse `X^{c+}_{ab,μ}` of `ofCompression` is the compression map `W_{(c,μ)}` of
the compression of `O_a O_b`. -/
theorem ofCompression_fusionTensorLeftInverse (hD : ∀ a, 0 < D a)
    (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor)
    (P : ∀ a b, PairCompression T N a b) (hP : ∀ a b, (P a b).remainder = 0)
    (K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c))) (Fin p × Fin p) ℂ) (hK)
    (a b c : Λ) (μ : Fin (N a b c)) (z : Fin (D c)) (x : Fin (D a) × Fin (D b)) :
    (ofCompression hD hT P hP K hK).fusionTensorLeftInverse a b c μ z x =
      (P a b).left (pairSlot c μ) z (finProdFinEquiv x) := rfl

/-- **Split compressions of the pairwise products in the star-closed case.** If the word traces
of the product `O_a O_b` are the sums of the word traces of `N_{ab}^c` copies of each `O_c`, and
the letters of the product tensor lie, with their conjugate transposes, in the algebra they
generate, then the product has a multi-block compression with vanishing remainder
(`MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_star`). -/
theorem exists_pairCompression_remainder_eq_zero_of_star (hD : ∀ a, 0 < D a)
    (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor) (a b : Λ)
    (htr : ∀ w : List (Fin (p * p)), w ≠ [] →
      Matrix.trace (Kraus.evalWord (mulTensor (T a) (T b)).toMPSTensor w) =
        ∑ s : (c : Λ) × Fin (N a b c), Matrix.trace (Kraus.evalWord (T s.1).toMPSTensor w))
    (hstar : ∀ i, ((mulTensor (T a) (T b)).toMPSTensor i)ᴴ ∈
      Algebra.adjoin ℂ (Set.range (mulTensor (T a) (T b)).toMPSTensor)) :
    ∃ P : PairCompression T N a b, P.remainder = 0 :=
  MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_star
    (D := fun s : (c : Λ) × Fin (N a b c) => D s.1) Finset.univ
    (fun s : (c : Λ) × Fin (N a b c) => (T s.1).toMPSTensor)
    (fun s _ => (hT s.1).isNormal) (fun s _ => hD s.1) _ htr hstar

/-- **Complete zipper fusion family in the star-closed case.** Under the fusion rules on word
traces and the star closure of every product tensor, the split compressions of
`exists_pairCompression_remainder_eq_zero_of_star` give a complete zipper fusion family.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--200 (fusion rules and fusion tensors);
arXiv:2203.12563, `REsubmission.tex`, lines 361--362 (the fusion rules). The star closure is the
sufficient condition for a vanishing remainder in
`Notes/OpenProblemsTN/strategies/final_resolution/p5_local_zipper_hypotheses.tex`,
`thm:p5-local-adjoint-closure`; the simultaneous left inverse `K` remains an input, as in
`ofCompression`. -/
noncomputable def ofStar (hD : ∀ a, 0 < D a)
    (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor)
    (htr : ∀ a b, ∀ w : List (Fin (p * p)), w ≠ [] →
      Matrix.trace (Kraus.evalWord (mulTensor (T a) (T b)).toMPSTensor w) =
        ∑ s : (c : Λ) × Fin (N a b c), Matrix.trace (Kraus.evalWord (T s.1).toMPSTensor w))
    (hstar : ∀ a b, ∀ i, ((mulTensor (T a) (T b)).toMPSTensor i)ᴴ ∈
      Algebra.adjoin ℂ (Set.range (mulTensor (T a) (T b)).toMPSTensor))
    (K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c))) (Fin p × Fin p) ℂ)
    (hK : ∀ (c d : Λ) (x y : Fin (D c)) (x' y' : Fin (D d)),
      (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
        if h : c = d then
          if _ : h ▸ x = x' then if _ : h ▸ y = y' then 1 else 0 else 0
        else 0) :
    CompleteZipperFusionFamily Λ p :=
  ofCompression hD hT
    (fun a b => (exists_pairCompression_remainder_eq_zero_of_star hD hT a b
      (htr a b) (hstar a b)).choose)
    (fun a b => (exists_pairCompression_remainder_eq_zero_of_star hD hT a b
      (htr a b) (hstar a b)).choose_spec) K hK

/-- The fusion tensors of `ofStar` are the compression maps of split compressions of the
pairwise products. -/
theorem exists_ofStar_fusionTensor_eq (hD : ∀ a, 0 < D a)
    (hT : ∀ a, Kraus.IsInjective (T a).toMPSTensor) (htr) (hstar)
    (K : Matrix ((c : Λ) × (Fin (D c) × Fin (D c))) (Fin p × Fin p) ℂ) (hK) (a b : Λ) :
    ∃ P : PairCompression T N a b, P.remainder = 0 ∧
      ∀ (c : Λ) (μ : Fin (N a b c)) (x : Fin (D a) × Fin (D b)) (z : Fin (D c)),
        (ofStar hD hT htr hstar K hK).fusionTensor a b c μ x z =
          P.right (pairSlot c μ) (finProdFinEquiv x) z :=
  ⟨_, (exists_pairCompression_remainder_eq_zero_of_star hD hT a b (htr a b)
    (hstar a b)).choose_spec, fun _ _ _ _ => rfl⟩

end Compression

end MPOTensor.CompleteZipperFusionFamily
