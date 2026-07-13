/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarCommutant
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Complete zipper fusion and the printed F-move

A complete zipper fusion family consists of injective MPO blocks, integer fusion
multiplicities, fusion tensors, and independently specified left inverses.  The
left inverses are biorthogonal to the fusion tensors.  The sum of the opposite
products is the projector onto the product-MPO support, which need not be the
identity on the ambient product bond space.  They satisfy the two zipper
identities.  A common left inverse for the labelled MPO letters separates the
final block.

The two ways of fusing three blocks give coordinate systems for the same
triple-product support.  The coordinate change from the left tree to the right
tree is oriented as in equation `Fmove` of arXiv:1511.08090: its rows are
indexed by the right tree and its columns by the left tree.  The resulting
matrix carries the right-associated fusion tensors to the left-associated
fusion tensors.  Its inverse has the opposite orientation.

No construction of complete zipper fusion tensors from the positive diagonal
matrices of arXiv:1606.00608 is asserted here.

## Main definitions

* `CompleteZipperFusionFamily`: complete fusion tensors and their left inverses.
* `printedFMatrix`: the source-oriented fixed-final change of fusion basis.

## Main statements

* `rightTripleSynthesis_mul_printedFMatrix`: equation `Fmove`.
* `printedFMatrix_mul_inversePrintedFMatrix`: the first inverse identity.
* `inversePrintedFMatrix_mul_printedFMatrix`: the second inverse identity.

## References

* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 161, 181--200, 237--283.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

universe u

/-- Complete zipper fusion tensors for a finite family of injective MPO blocks.

The synthesis matrix collects the tensors $X^c_{ab,\mu}$ as its columns, while
the analysis matrix collects the independently chosen left inverses
$X^{c+}_{ab,\mu}$ as its rows.  Their product in the coordinate space encodes
$X^{d+}_{ab,\nu}X^c_{ab,\mu}=\delta_{cd}\delta_{\mu\nu}1$.  Their product in the
ambient product space is only a support projector.  Equation `inversegaugeone`
states that inserting this projector reconstructs every product-MPO letter.
The two zipper identities are recorded in the orientations printed in the
source.  The last two fields give the simultaneous left inverse of the family
of block letters used to distinguish the final label.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, line 161, equation
`inversegaugeone` at lines 181--191, the zipper equations at lines 193--200,
and the simultaneous inverse at lines 269--277. -/
structure CompleteZipperFusionFamily (Λ : Type u) [Fintype Λ] [DecidableEq Λ]
    (p : ℕ) where
  /-- Bond dimension of the MPO block with label `a`.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, line 161. -/
  bondDim : Λ → ℕ
  /-- Every MPO block has a nonzero bond space.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, line 161. -/
  bondDim_pos : ∀ a : Λ, 0 < bondDim a
  /-- The injective MPO blocks $B_a^{ij}$.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--163. -/
  tensor : ∀ a : Λ, MPOTensor p (bondDim a)
  /-- Each labelled MPO block is injective.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--163 and the
  injectivity argument at lines 269--277. -/
  tensor_injective : ∀ a : Λ, MPSTensor.IsInjective (tensor a).toMPSTensor
  /-- The fusion multiplicity $N_{ab}^c$.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, line 161. -/
  fusionMultiplicity : Λ → Λ → Λ → ℕ
  /-- The matrix whose columns are the fusion tensors $X^c_{ab,\mu}$.

  **Local fix (arXiv:1511.08090, line 161):** The displayed arrow for $X$ in
  the prose is reversed.  Equations `inversegaugeone`, `zippercondition`, and
  `Fmove` fix the orientation used here.  This is documented in
  `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 161--163 and 248--251. -/
  fusionSynthesis : ∀ a b : Λ,
    Matrix (Fin (bondDim a) × Fin (bondDim b))
      ((c : Λ) × (Fin (fusionMultiplicity a b c) × Fin (bondDim c))) ℂ
  /-- The matrix whose rows are the left inverses $X^{c+}_{ab,\mu}$.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 161--163. -/
  fusionAnalysis : ∀ a b : Λ,
    Matrix ((c : Λ) × (Fin (fusionMultiplicity a b c) × Fin (bondDim c)))
      (Fin (bondDim a) × Fin (bondDim b)) ℂ
  /-- The fusion left inverses are biorthogonal to the fusion tensors.

  **Local fix (arXiv:1511.08090, line 161):** The displayed Kronecker factor
  is written as $\delta_{de}$ although no label $e$ occurs in the relation.
  The typed relation is $\delta_{dc}$ (equivalently $\delta_{cd}$), as used
  here.  This is documented in
  `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, line 161. -/
  analysis_mul_synthesis : ∀ a b : Λ,
    fusionAnalysis a b * fusionSynthesis a b = 1
  /-- The first zipper identity, $B_{ab}X=X(1_N\otimes B)$.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 193--196. -/
  pairLetter_mul_synthesis : ∀ (a b : Λ) (i k : Fin p),
    (∑ j : Fin p, tensor a i j ⊗ₖ tensor b j k) * fusionSynthesis a b =
      fusionSynthesis a b * Matrix.blockDiagonal' (fun c =>
        (1 : Matrix (Fin (fusionMultiplicity a b c))
          (Fin (fusionMultiplicity a b c)) ℂ) ⊗ₖ tensor c i k)
  /-- The second zipper identity, $X^+B_{ab}=(1_N\otimes B)X^+$.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 198--200. -/
  analysis_mul_pairLetter : ∀ (a b : Λ) (i k : Fin p),
    fusionAnalysis a b * (∑ j : Fin p, tensor a i j ⊗ₖ tensor b j k) =
      Matrix.blockDiagonal' (fun c =>
        (1 : Matrix (Fin (fusionMultiplicity a b c))
          (Fin (fusionMultiplicity a b c)) ℂ) ⊗ₖ tensor c i k) *
        fusionAnalysis a b
  /-- Every product-MPO letter is reconstructed through the fusion support.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, equation `inversegaugeone` at
  lines 184--186. -/
  pairLetter_eq_synthesis_mul_directSum_mul_analysis : ∀
      (a b : Λ) (i k : Fin p),
    (∑ j : Fin p, tensor a i j ⊗ₖ tensor b j k) =
      fusionSynthesis a b * Matrix.blockDiagonal' (fun c =>
        (1 : Matrix (Fin (fusionMultiplicity a b c))
          (Fin (fusionMultiplicity a b c)) ℂ) ⊗ₖ tensor c i k) *
        fusionAnalysis a b
  /-- A simultaneous left inverse of the labelled block-letter matrix.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 269--277. -/
  blockLeftInverse : Matrix
    ((c : Λ) × (Fin (bondDim c) × Fin (bondDim c))) (Fin p × Fin p) ℂ
  /-- The simultaneous inverse distinguishes the final label and both bond indices.

  Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 269--277. -/
  blockLeftInverse_apply : ∀ (c d : Λ) (x y : Fin (bondDim c))
      (x' y' : Fin (bondDim d)),
    (∑ i : Fin p, ∑ k : Fin p,
      blockLeftInverse ⟨c, x, y⟩ (i, k) * tensor d i k x' y') =
      if h : c = d then
        if _ : h ▸ x = x' then if _ : h ▸ y = y' then 1 else 0 else 0
      else 0

namespace CompleteZipperFusionFamily

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

/-- The bond space of the left-associated triple product. -/
abbrev TripleBond (a b c : Λ) : Type :=
  (Fin (Fus.bondDim a) × Fin (Fus.bondDim b)) × Fin (Fus.bondDim c)

/-- The left-tree multiplicity space with fixed final label `d`.

Its coordinates are $(e,\mu,\nu)$ with
$\mu=1,\ldots,N_{ab}^e$ and $\nu=1,\ldots,N_{ec}^d$.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251. -/
abbrev LeftTripleMultiplicity (a b c d : Λ) : Type u :=
  (e : Λ) × (Fin (Fus.fusionMultiplicity a b e) ×
    Fin (Fus.fusionMultiplicity e c d))

/-- The right-tree multiplicity space with fixed final label `d`.

Its coordinates are $(f,\lambda,\sigma)$ with
$\lambda=1,\ldots,N_{bc}^f$ and $\sigma=1,\ldots,N_{af}^d$.

Source: arXiv:1511.08090, equation `Fmove`, lines 248--251. -/
abbrev RightTripleMultiplicity (a b c d : Λ) : Type u :=
  (f : Λ) × (Fin (Fus.fusionMultiplicity b c f) ×
    Fin (Fus.fusionMultiplicity a f d))

/-- The fusion tensor $X^c_{ab,\mu}$ extracted from the total synthesis matrix.

**Local fix (arXiv:1511.08090, line 161):** The displayed arrow for $X$ in
the prose is reversed.  Equations `inversegaugeone`, `zippercondition`, and
`Fmove` fix the orientation used here.  This is documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 161--163 and 248--251. -/
def fusionTensor (a b c : Λ) (μ : Fin (Fus.fusionMultiplicity a b c)) :
    Matrix (Fin (Fus.bondDim a) × Fin (Fus.bondDim b))
      (Fin (Fus.bondDim c)) ℂ :=
  fun x y => Fus.fusionSynthesis a b x ⟨c, μ, y⟩

/-- The left inverse $X^{c+}_{ab,\mu}$ extracted from the total analysis matrix.

It is an independent matrix, not the adjoint of `fusionTensor`.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, line 161. -/
def fusionTensorLeftInverse (a b c : Λ)
    (μ : Fin (Fus.fusionMultiplicity a b c)) :
    Matrix (Fin (Fus.bondDim c))
      (Fin (Fus.bondDim a) × Fin (Fus.bondDim b)) ℂ :=
  fun x y => Fus.fusionAnalysis a b ⟨c, μ, x⟩ y

/-- The left-associated fixed-final synthesis map.  Its column
$(e,\mu,\nu,z)$ is the composite
$(X^e_{ab,\mu}\otimes1)X^d_{ec,\nu}$.

Source: arXiv:1511.08090, equations preceding `Fmove` and `Fmove`, lines
242--251. -/
noncomputable def leftTripleSynthesis (a b c d : Λ) :
    Matrix (Fus.TripleBond a b c)
      (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ :=
  fun ⟨⟨xa, xb⟩, xc⟩ ⟨⟨e, μ, ν⟩, z⟩ =>
    ∑ y : Fin (Fus.bondDim e),
      Fus.fusionTensor a b e μ (xa, xb) y *
        Fus.fusionTensor e c d ν (y, xc) z

/-- The left-associated fixed-final analysis map.  Its row
$(e,\mu,\nu,z)$ is the composite of the two fusion left inverses in reverse
order.

Source: arXiv:1511.08090, lines 161 and 242--251. -/
noncomputable def leftTripleAnalysis (a b c d : Λ) :
    Matrix (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (Fus.TripleBond a b c) ℂ :=
  fun ⟨⟨e, μ, ν⟩, z⟩ ⟨⟨xa, xb⟩, xc⟩ =>
    ∑ y : Fin (Fus.bondDim e),
      Fus.fusionTensorLeftInverse e c d ν z (y, xc) *
        Fus.fusionTensorLeftInverse a b e μ y (xa, xb)

/-- The right-associated fixed-final synthesis map.  Its column
$(f,\lambda,\sigma,z)$ is the composite
$(1\otimes X^f_{bc,\lambda})X^d_{af,\sigma}$, reindexed on the common
left-associated triple-bond space.

Source: arXiv:1511.08090, equations preceding `Fmove` and `Fmove`, lines
242--251. -/
noncomputable def rightTripleSynthesis (a b c d : Λ) :
    Matrix (Fus.TripleBond a b c)
      (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d)) ℂ :=
  fun ⟨⟨xa, xb⟩, xc⟩ ⟨⟨f, l, s⟩, z⟩ =>
    ∑ y : Fin (Fus.bondDim f),
      Fus.fusionTensor b c f l (xb, xc) y *
        Fus.fusionTensor a f d s (xa, y) z

/-- The right-associated fixed-final analysis map, in the reverse order from
the right-associated synthesis composite.

Source: arXiv:1511.08090, lines 161 and 242--251. -/
noncomputable def rightTripleAnalysis (a b c d : Λ) :
    Matrix (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d))
      (Fus.TripleBond a b c) ℂ :=
  fun ⟨⟨f, l, s⟩, z⟩ ⟨⟨xa, xb⟩, xc⟩ =>
    ∑ y : Fin (Fus.bondDim f),
      Fus.fusionTensorLeftInverse a f d s z (xa, y) *
        Fus.fusionTensorLeftInverse b c f l y (xb, xc)

/-- The full left-associated triple-fusion index, including the final label and
its bond coordinate. -/
abbrev LeftTripleIndex (a b c : Λ) : Type u :=
  (d : Λ) × (Fus.LeftTripleMultiplicity a b c d × Fin (Fus.bondDim d))

/-- The full right-associated triple-fusion index, including the final label
and its bond coordinate. -/
abbrev RightTripleIndex (a b c : Λ) : Type u :=
  (d : Λ) × (Fus.RightTripleMultiplicity a b c d × Fin (Fus.bondDim d))

/-- The direct sum of all left-associated fixed-final synthesis maps. -/
noncomputable def leftTripleSynthesisFull (a b c : Λ) :
    Matrix (Fus.TripleBond a b c) (Fus.LeftTripleIndex a b c) ℂ :=
  fun x y => Fus.leftTripleSynthesis a b c y.1 x y.2

/-- The direct sum of all left-associated fixed-final analysis maps. -/
noncomputable def leftTripleAnalysisFull (a b c : Λ) :
    Matrix (Fus.LeftTripleIndex a b c) (Fus.TripleBond a b c) ℂ :=
  fun x y => Fus.leftTripleAnalysis a b c x.1 x.2 y

/-- The direct sum of all right-associated fixed-final synthesis maps. -/
noncomputable def rightTripleSynthesisFull (a b c : Λ) :
    Matrix (Fus.TripleBond a b c) (Fus.RightTripleIndex a b c) ℂ :=
  fun x y => Fus.rightTripleSynthesis a b c y.1 x y.2

/-- The direct sum of all right-associated fixed-final analysis maps. -/
noncomputable def rightTripleAnalysisFull (a b c : Λ) :
    Matrix (Fus.RightTripleIndex a b c) (Fus.TripleBond a b c) ℂ :=
  fun x y => Fus.rightTripleAnalysis a b c x.1 x.2 y

/-- A letter of the left-associated triple product on the common triple-bond
space. -/
noncomputable def tripleProductLetter (a b c : Λ) (i l : Fin p) :
    Matrix (Fus.TripleBond a b c) (Fus.TripleBond a b c) ℂ :=
  ∑ j : Fin p, ∑ k : Fin p,
    (Fus.tensor a i j ⊗ₖ Fus.tensor b j k) ⊗ₖ Fus.tensor c k l

/-- The direct sum of final-block letters in the left-tree coordinates. -/
noncomputable def leftTripleDirectSumLetter (a b c : Λ) (i l : Fin p) :
    Matrix (Fus.LeftTripleIndex a b c) (Fus.LeftTripleIndex a b c) ℂ :=
  Matrix.blockDiagonal' fun d =>
    (1 : Matrix (Fus.LeftTripleMultiplicity a b c d)
      (Fus.LeftTripleMultiplicity a b c d) ℂ) ⊗ₖ Fus.tensor d i l

/-- The direct sum of final-block letters in the right-tree coordinates. -/
noncomputable def rightTripleDirectSumLetter (a b c : Λ) (i l : Fin p) :
    Matrix (Fus.RightTripleIndex a b c) (Fus.RightTripleIndex a b c) ℂ :=
  Matrix.blockDiagonal' fun d =>
    (1 : Matrix (Fus.RightTripleMultiplicity a b c d)
      (Fus.RightTripleMultiplicity a b c d) ℂ) ⊗ₖ Fus.tensor d i l

end CompleteZipperFusionFamily

end MPOTensor
