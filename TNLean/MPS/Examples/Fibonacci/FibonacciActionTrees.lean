/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciFSymbol
import TNLean.MPS.MPDO.MPOAction.RingTreeData

/-!
# Exact fusion and action trees of the two-block Fibonacci realization

**Source.** Garre-Rubio, Lootens and Molnár 2023 (arXiv:2203.12563),
`Papers/2203.12563/REsubmission.tex`: closedness with arbitrary boundary conditions gives
exact fusion tensors `O_a O_b = ∑_c W_{ab}^c O_c V_{ab}^c` (`fusiontensors`, lines 361–391)
and exact action tensors `O_a · A_x = ∑_y W_{ax}^y A_y V_{ax}^y` (`fusiontensors2`,
lines 459–490), with the biorthogonality relations `eq:orthoW` and `eq:orthoV`; lines
1991–1993: the Fibonacci algebra acts on two blocks by `τ · x_1 = x_τ` and
`τ · x_τ = x_1 + x_τ`.

**Formalized here.** For the Fibonacci operator blocks `O_1`, `O_τ` of
`Examples/Fibonacci.lean` and the pair of normal states `A = A_{x_1}`, `C = A_{x_τ}` of
`Examples/FibonacciAction.lean`, explicit analysis and synthesis maps over the golden integers
`ℤ[σ]` for all four products `O_a O_b` and all four actions `O_a · A_x`, and the proof that
each is an exact biorthogonal decomposition, with multiplicities the Fibonacci structure
constants `N_{ab}^c = M_{a,x}^y`. Exactness is the statement that every letter of the product
or action tensor is the sum of its blocks, with no remainder; it holds for this realization in
exact arithmetic, including the unit action `1 · C`, which earlier files do not compress.

**Local fix (provenance):** the operator blocks and the two states are those of
`Examples/Fibonacci.lean` and `Examples/FibonacciAction.lean`, whose entries the source does
not print; documented in `docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`.

## Main definitions

* `FibonacciCompression.fibBlockGolden`: the two operator blocks over `ℤ[σ]`.
* `FibonacciCompression.fibFusionAnalysis`, `FibonacciCompression.fibFusionSynthesis`,
  `FibonacciCompression.fibActAnalysis`, `FibonacciCompression.fibActSynthesis`: the complex
  fusion and action trees.

## Main statements

* `FibonacciCompression.isBiorthogonalDecomposition_fibFusion`: the exact fusion trees.
* `FibonacciCompression.isBiorthogonalDecomposition_fibAct`: the exact action trees.
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor MPOTensor

/-- The Fibonacci operator blocks over the golden integers: the admissibility projector at the
trivial label and the `τ` block at `τ`. -/
def fibBlockGolden : (a : Fin 2) → Fin 2 × Fin 2 →
    Matrix (Fin (fibBlockDim a)) (Fin (fibBlockDim a)) GoldenInt
  | 0 => fibOneGolden
  | 1 => fibTauGolden

/-- The Fibonacci structure constants `N_{ab}^c`, which are also the action multiplicities
`M_{a,x}^y` of the regular module, as a function of three labels. -/
def fibMult (a b c : Fin 2) : ℕ := fibNim a b c

/-- Every Fibonacci multiplicity is zero or one, so each multiplicity space has at most one
element and the trees below need one map per admissible triple. -/
theorem fibMult_le_one (a b c : Fin 2) : fibMult a b c ≤ 1 := by
  revert a b c
  decide

instance (a b c : Fin 2) : Subsingleton (Fin (fibMult a b c)) :=
  Fin.subsingleton_iff_le_one.mpr (fibMult_le_one a b c)

theorem fibBlock_eq_complexOfGolden (a : Fin 2) :
    fibBlock a = fun ij ↦ complexOfGolden (fibBlockGolden a ij) := by
  fin_cases a <;> rfl

theorem fibNimTargets_eq_complexOfGolden (x : Fin 2) :
    fibNimTargets x = fun i ↦ complexOfGolden (fibNimTargetsGolden x i) :=
  funext (fibNimTargets_eq x)

/-- The synthesis maps `W_{a,x}^y` of the action trees `O_a · A_x → A_y`, the action tensors
of arXiv:2203.12563, `fusiontensors2`, lines 459–490. They vanish where `M_{a,x}^y = 0`. -/
def fibActSynthesisGolden : (a x y : Fin 2) →
    Matrix (Fin (fibBlockDim a * fibNimDim x)) (Fin (fibNimDim y)) GoldenInt
  | 0, 0, 0 =>
    !![⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩]
  | 0, 1, 1 =>
    !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1, 0, 1 =>
    !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1, 1, 0 =>
    !![⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩;
       ⟨0, 1, 0, 0⟩;
       ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩]
  | 1, 1, 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | _, _, _ => 0

/-- The analysis maps `V_{a,x}^y` of the action trees, left inverses of the synthesis maps
(arXiv:2203.12563, `eq:orthoV`, lines 459–490). -/
def fibActAnalysisGolden : (a x y : Fin 2) →
    Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibNimDim x)) GoldenInt
  | 0, 0, 0 =>
    !![⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 0, 1, 1 =>
    !![⟨1, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1, 0, 1 =>
    !![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 1⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1, 1, 0 =>
    !![⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, -1, 0, 1⟩, ⟨-1, 0, 1, 0⟩,
       ⟨0, 0, 1, 0⟩]
  | 1, 1, 1 =>
    !![⟨1, 0, -1, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩,
       ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨0, 1, 0, -1⟩, ⟨0, 0, -1, 0⟩,
       ⟨1, 0, -1, 0⟩]
  | _, _, _ => 0

/-- The synthesis maps `W_{a,b}^c` of the fusion trees `O_a O_b → O_c`, the fusion tensors of
arXiv:2203.12563, `fusiontensors`, lines 361–391. They vanish where `N_{ab}^c = 0`. -/
def fibFusionSynthesisGolden : (a b c : Fin 2) →
    Matrix (Fin (fibBlockDim a * fibBlockDim b)) (Fin (fibBlockDim c)) GoldenInt
  | 0, 0, 0 =>
    !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 0, 1, 1 =>
    !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1, 0, 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1, 1, 0 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 1, 0, 1⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 1, 1, 1 =>
    !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨-1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | _, _, _ => 0

/-- The analysis maps `V_{a,b}^c` of the fusion trees, left inverses of the synthesis maps
(arXiv:2203.12563, `eq:orthoW`, lines 361–391). -/
def fibFusionAnalysisGolden : (a b c : Fin 2) →
    Matrix (Fin (fibBlockDim c)) (Fin (fibBlockDim a * fibBlockDim b)) GoldenInt
  | 0, 0, 0 =>
    !![⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]
  | 0, 1, 1 =>
    !![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, -1⟩, ⟨1, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩,
       ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 1⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
       ⟨1, 0, 0, 0⟩]
  | 1, 0, 1 =>
    !![⟨1, 0, -1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩,
       ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩,
       ⟨0, 0, 0, 0⟩;
       ⟨-1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩,
       ⟨1, 0, 0, 0⟩]
  | 1, 1, 0 =>
    !![⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩,
       ⟨0, -1, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩,
       ⟨0, 0, 0, 1⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩]
  | 1, 1, 1 =>
    !![⟨1, 0, -2, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 2, 0⟩,
       ⟨0, 0, 0, -1⟩, ⟨1, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, -2⟩,
       ⟨1, 0, -1, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩;
       ⟨-1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨1, 0, -2, 0⟩,
       ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩]
  | _, _, _ => 0

/-- The complex analysis maps of the fusion trees. The multiplicity index is not used: each
multiplicity space has at most one element (`fibMult_le_one`). -/
def fibFusionAnalysis (a b c : Fin 2) (_ : Fin (fibMult a b c)) :
    Matrix (Fin (fibBlockDim c)) (Fin (fibBlockDim a * fibBlockDim b)) ℂ :=
  complexOfGolden (fibFusionAnalysisGolden a b c)

/-- The complex synthesis maps of the fusion trees. -/
def fibFusionSynthesis (a b c : Fin 2) (_ : Fin (fibMult a b c)) :
    Matrix (Fin (fibBlockDim a * fibBlockDim b)) (Fin (fibBlockDim c)) ℂ :=
  complexOfGolden (fibFusionSynthesisGolden a b c)

/-- The complex analysis maps of the action trees. The multiplicity index is not used: each
multiplicity space has at most one element (`fibMult_le_one`). -/
def fibActAnalysis (a x y : Fin 2) (_ : Fin (fibMult a x y)) :
    Matrix (Fin (fibNimDim y)) (Fin (fibBlockDim a * fibNimDim x)) ℂ :=
  complexOfGolden (fibActAnalysisGolden a x y)

/-- The complex synthesis maps of the action trees. -/
def fibActSynthesis (a x y : Fin 2) (_ : Fin (fibMult a x y)) :
    Matrix (Fin (fibBlockDim a * fibNimDim x)) (Fin (fibNimDim y)) ℂ :=
  complexOfGolden (fibActSynthesisGolden a x y)

set_option maxRecDepth 8000 in
/-- **Exact fusion trees.** For every pair of labels, the product `O_a O_b` of Fibonacci
operator blocks is the exact sum of its blocks `O_c`, with multiplicity `N_{ab}^c`.
Source: arXiv:2203.12563, `fusiontensors`, `eq:orthoW`, lines 361–391. -/
theorem isBiorthogonalDecomposition_fibFusion (a b : Fin 2) :
    IsBiorthogonalDecomposition (mulTensor (fibBlock a) (fibBlock b))
      (fun q : (c : Fin 2) × Fin (fibMult a b c) ↦ fibBlock q.1)
      (fun q ↦ fibFusionAnalysis a b q.1 q.2) (fun q ↦ fibFusionSynthesis a b q.1 q.2) := by
  have hB : mulTensor (fibBlock a) (fibBlock b) = fun p ↦
      complexOfGolden (mulGoldenTensor (fibBlockGolden a) (fibBlockGolden b) p) := by
    funext p
    rw [fibBlock_eq_complexOfGolden a, fibBlock_eq_complexOfGolden b]
    exact mulTensor_complexOfGolden _ _ _
  have hA : (fun q : (c : Fin 2) × Fin (fibMult a b c) ↦ fibBlock q.1) =
      fun (q : (c : Fin 2) × Fin (fibMult a b c)) (p : Fin 2 × Fin 2) ↦
        complexOfGolden (fibBlockGolden q.1 p) := by
    funext q p
    rw [fibBlock_eq_complexOfGolden q.1]
  rw [hB, hA]
  refine isBiorthogonalDecomposition_complexOfRing goldenToComplex _ _
    (fun q : (c : Fin 2) × Fin (fibMult a b c) ↦ fibFusionAnalysisGolden a b q.1)
    (fun q : (c : Fin 2) × Fin (fibMult a b c) ↦ fibFusionSynthesisGolden a b q.1)
    ?_ ?_ ?_ <;> fin_cases a <;> fin_cases b <;> decide +kernel

set_option maxRecDepth 8000 in
/-- **Exact action trees.** For every label `a` and every block `x`, the action `O_a · A_x`
is the exact sum of the blocks `A_y`, with multiplicity `M_{a,x}^y = N_{ax}^y`: `1 · x = x`,
`τ · x_1 = x_τ` and `τ · x_τ = x_1 + x_τ`. Source: arXiv:2203.12563, `fusiontensors2`,
`eq:orthoV`, lines 459–490, and lines 1991–1993. -/
theorem isBiorthogonalDecomposition_fibAct (a x : Fin 2) :
    IsBiorthogonalDecomposition (actTensor (fibBlock a) (fibNimTargets x))
      (fun q : (y : Fin 2) × Fin (fibMult a x y) ↦ fibNimTargets q.1)
      (fun q ↦ fibActAnalysis a x q.1 q.2) (fun q ↦ fibActSynthesis a x q.1 q.2) := by
  have hB : actTensor (fibBlock a) (fibNimTargets x) = fun i ↦
      complexOfGolden (actTensorR (fibBlockGolden a) (fibNimTargetsGolden x) i) := by
    funext i
    rw [fibBlock_eq_complexOfGolden a, fibNimTargets_eq_complexOfGolden x]
    exact actTensor_complexOfRing goldenToComplex _ _ i
  have hA : (fun q : (y : Fin 2) × Fin (fibMult a x y) ↦ fibNimTargets q.1) =
      fun (q : (y : Fin 2) × Fin (fibMult a x y)) (i : Fin 2) ↦
        complexOfGolden (fibNimTargetsGolden q.1 i) := by
    funext q i
    exact fibNimTargets_eq _ _
  rw [hB, hA]
  refine isBiorthogonalDecomposition_complexOfRing goldenToComplex _ _
    (fun q : (y : Fin 2) × Fin (fibMult a x y) ↦ fibActAnalysisGolden a x q.1)
    (fun q : (y : Fin 2) × Fin (fibMult a x y) ↦ fibActSynthesisGolden a x q.1)
    ?_ ?_ ?_ <;> fin_cases a <;> fin_cases x <;> decide +kernel

end FibonacciCompression
