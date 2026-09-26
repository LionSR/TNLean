/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionCoproduct

/-!
# Coassociativity of the fusion coproduct

The fusion coproduct of a complete zipper fusion family is coassociative:
$(\Delta\otimes\mathrm{id})\circ\Delta=(\mathrm{id}\otimes\Delta)\circ\Delta$.  This is the
coassociativity axiom of a coalgebra (arXiv:2204.05940, `mpo.tex`, lines 866--875).  The source
starts from a coassociative coproduct and derives the associativity of the fusion trees
(`mpo.tex`, lines 1732--1787, equation `eq:associative`).  Here the direction is reversed.  The
coproduct is built from the fusion tensors and its coassociativity is proved.

The two iterated maps are written in Kronecker coordinates on the triple bond space
$(\mathbb C^{\chi_a}\otimes\mathbb C^{\chi_b})\otimes\mathbb C^{\chi_c}$:
\[
  (\Delta\otimes\mathrm{id})(Y)_{abc}
    =\sum_{e,\mu}(X^e_{ab,\mu}\otimes1)\,Y_{ec}\,(X^{e+}_{ab,\mu}\otimes1),\qquad
  (\mathrm{id}\otimes\Delta)(Y)_{abc}
    =\sum_{f,\lambda}(1\otimes X^f_{bc,\lambda})\,Y_{af}\,(1\otimes X^{f+}_{bc,\lambda}),
\]
where the second is reassociated to the same triple bond space.

The proof does not use the $F$-move.  Both iterated coproducts are linear, and on a letter both
equal the letter of the triple product $T_aT_bT_c$.  The letters span the boundary space.  This
is the argument of `mpo.tex`, lines 940--945 and 2001--2003, run backwards.

## Main definitions

* `CompleteZipperFusionFamily.coproductLeft`: the map $\Delta\otimes\mathrm{id}$.
* `CompleteZipperFusionFamily.coproductRight`: the map $\mathrm{id}\otimes\Delta$.

## Main statements

* `coproduct_coassoc`: coassociativity of the fusion coproduct.

## References

* arXiv:2204.05940, `mpo.tex`, lines 866--875, 1655, 1732--1787, and 2003--2006.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

namespace CompleteZipperFusionFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

/-- The map $\Delta\otimes\mathrm{id}$ on pairs of blocks, with values on the triple bond space
of `(a, b, c)`.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875 and 1655. -/
noncomputable def coproductLeft (Y : Fus.PairSpace) (a b c : Λ) :
    Matrix (Fus.TripleBond a b c) (Fus.TripleBond a b c) ℂ :=
  ∑ e, ∑ μ, (Fus.fusionTensor a b e μ ⊗ₖ
      (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ)) * Y e c *
    (Fus.fusionTensorLeftInverse a b e μ ⊗ₖ
      (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ))

/-- The map $\mathrm{id}\otimes\Delta$ on pairs of blocks, reassociated to the triple bond space
of `(a, b, c)`.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875 and 1655. -/
noncomputable def coproductRight (Y : Fus.PairSpace) (a b c : Λ) :
    Matrix (Fus.TripleBond a b c) (Fus.TripleBond a b c) ℂ :=
  (∑ f, ∑ μ, ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
      Fus.fusionTensor b c f μ) * Y a f *
    ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
      Fus.fusionTensorLeftInverse b c f μ)).submatrix
    (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)

private theorem sum_kronecker {ι l m n q : Type*} (s : Finset ι) (A : ι → Matrix l m ℂ)
    (B : Matrix n q ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext x y
  simp [Matrix.sum_apply, Finset.sum_mul]

private theorem kronecker_sum {ι l m n q : Type*} (s : Finset ι) (A : Matrix l m ℂ)
    (B : ι → Matrix n q ℂ) : A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ B i := by
  ext x y
  simp [Matrix.sum_apply, Finset.mul_sum]

private theorem kronecker_one_conj {l m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (V : Matrix l m ℂ) (A : Matrix m m ℂ) (W : Matrix m l ℂ) (B : Matrix n n ℂ) :
    (V ⊗ₖ (1 : Matrix n n ℂ)) * (A ⊗ₖ B) * (W ⊗ₖ (1 : Matrix n n ℂ)) = (V * A * W) ⊗ₖ B := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

private theorem one_kronecker_conj {l m n : Type*} [Fintype l] [Fintype m] [DecidableEq l]
    (A : Matrix l l ℂ) (V : Matrix n m ℂ) (B : Matrix m m ℂ) (W : Matrix m n ℂ) :
    ((1 : Matrix l l ℂ) ⊗ₖ V) * (A ⊗ₖ B) * ((1 : Matrix l l ℂ) ⊗ₖ W) = A ⊗ₖ (V * B * W) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- The sum over fusion channels of a conjugated letter is the letter of the stacked tensor. -/
private theorem sum_fusion_conj_letter (a b : Λ) (i k : Fin p) :
    ∑ e, ∑ μ, Fus.fusionTensor a b e μ * Fus.tensor e i k *
        Fus.fusionTensorLeftInverse a b e μ =
      ∑ j, Fus.tensor a i j ⊗ₖ Fus.tensor b j k := by
  rw [← Fus.coproduct_letter i k a b, Fus.coproduct_apply_eq_sum]
  rfl

omit [DecidableEq Λ] in
private theorem sum_sum_sum_comm {β : Type*} [AddCommMonoid β] {κ : Λ → Type*}
    [∀ e, Fintype (κ e)] (F : ∀ e, κ e → Fin p → β) :
    ∑ e, ∑ μ, ∑ j, F e μ j = ∑ j, ∑ e, ∑ μ, F e μ j :=
  calc _ = ∑ e, ∑ j, ∑ μ, F e μ j := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- $(\Delta\otimes\mathrm{id})\Delta(T^{il})$ is the letter of the triple product. -/
theorem coproductLeft_coproduct_letter (i l : Fin p) (a b c : Λ) :
    Fus.coproductLeft (Fus.coproduct (Fus.letter i l)) a b c =
      Fus.tripleProductLetter a b c i l := by
  simp only [coproductLeft, coproduct_letter, Matrix.mul_sum, Matrix.sum_mul,
    kronecker_one_conj]
  rw [sum_sum_sum_comm]
  simp only [← sum_kronecker, Fus.sum_fusion_conj_letter]
  rw [tripleProductLetter]
  simp only [sum_kronecker]
  exact Finset.sum_comm

/-- $(\mathrm{id}\otimes\Delta)\Delta(T^{il})$ is the letter of the triple product. -/
theorem coproductRight_coproduct_letter (i l : Fin p) (a b c : Λ) :
    Fus.coproductRight (Fus.coproduct (Fus.letter i l)) a b c =
      Fus.tripleProductLetter a b c i l := by
  simp only [coproductRight, coproduct_letter, Matrix.mul_sum, Matrix.sum_mul,
    one_kronecker_conj]
  rw [sum_sum_sum_comm]
  simp only [← kronecker_sum, Fus.sum_fusion_conj_letter]
  ext ⟨⟨xa, xb⟩, xc⟩ ⟨⟨ya, yb⟩, yc⟩
  simp [tripleProductLetter, Matrix.sum_apply, Finset.mul_sum, mul_assoc]

theorem coproductLeft_add (Y Y' : Fus.PairSpace) (a b c : Λ) :
    Fus.coproductLeft (Y + Y') a b c = Fus.coproductLeft Y a b c + Fus.coproductLeft Y' a b c := by
  simp [coproductLeft, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem coproductLeft_smul (r : ℂ) (Y : Fus.PairSpace) (a b c : Λ) :
    Fus.coproductLeft (r • Y) a b c = r • Fus.coproductLeft Y a b c := by
  simp [coproductLeft, Finset.smul_sum]

theorem coproductRight_add (Y Y' : Fus.PairSpace) (a b c : Λ) :
    Fus.coproductRight (Y + Y') a b c =
      Fus.coproductRight Y a b c + Fus.coproductRight Y' a b c := by
  simp only [coproductRight, Pi.add_apply, Matrix.mul_add, Matrix.add_mul,
    Finset.sum_add_distrib]
  rfl

theorem coproductRight_smul (r : ℂ) (Y : Fus.PairSpace) (a b c : Λ) :
    Fus.coproductRight (r • Y) a b c = r • Fus.coproductRight Y a b c := by
  simp only [coproductRight, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.smul_sum]
  rfl

/-- **Coassociativity of the fusion coproduct.**
$(\Delta\otimes\mathrm{id})\circ\Delta=(\mathrm{id}\otimes\Delta)\circ\Delta$ on the boundary
space of a complete zipper fusion family.

Source: arXiv:2204.05940, `mpo.tex`, lines 866--875 (coassociativity of a coalgebra), with the
coproduct of line 1655 and the letter identity of lines 2003--2006. -/
theorem coproduct_coassoc (Z : Fus.BoundarySpace) (a b c : Λ) :
    Fus.coproductLeft (Fus.coproduct Z) a b c = Fus.coproductRight (Fus.coproduct Z) a b c := by
  have hZ : Z ∈ Submodule.span ℂ (Set.range fun ik : Fin p × Fin p => Fus.letter ik.1 ik.2) := by
    rw [Fus.span_letter_eq_top]
    exact Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, l⟩, rfl⟩ := hx
    rw [coproductLeft_coproduct_letter, coproductRight_coproduct_letter]
  | zero =>
    have hL := Fus.coproductLeft_smul 0 0 a b c
    have hR := Fus.coproductRight_smul 0 0 a b c
    simp only [zero_smul, map_zero] at hL hR ⊢
    rw [hL, hR]
  | add x y _ _ hx hy =>
    rw [map_add, coproductLeft_add, coproductRight_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smul, coproductLeft_smul, coproductRight_smul, hx]

end CompleteZipperFusionFamily

end MPOTensor
