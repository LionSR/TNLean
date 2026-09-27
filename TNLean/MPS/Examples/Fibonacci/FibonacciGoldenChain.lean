/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciGSymbol
import TNLean.MPS.MPDO.OperatorCyclicSum
import TNLean.MPS.MPDO.SiteOperatorKernel

/-!
# Fibonacci: the golden chain commutes with the topological symmetry

**Source.** Feiguin, Trebst, Ludwig, Troyer, Kitaev, Wang, Freedman 2007
(arXiv:cond-mat/0612341), `References/cond-mat_0612341/source/fibonacci.tex` lines 136–175:
the golden chain `H = ∑_i H_i` on the fusion paths `x_0, …, x_{L−1}` of Fibonacci anyons, with
the three-site term `(H_i)_{x_i}^{x'_i} = −(F^{x_{i+1}}_{x_{i−1} τ τ})^1_{x_i}
(F^{x_{i+1}}_{x_{i−1} τ τ})^1_{x'_i}` (lines 148–153), which is `diag(−1, 0, 0)` on
`|1τ1⟩, |1ττ⟩, |ττ1⟩` and `−[[φ^{−2}, φ^{−3/2}], [φ^{−3/2}, φ^{−1}]]` between two `τ`
neighbours (lines 154–175); lines 510–516: the topological symmetry `Y` with
`⟨x'|Y|x⟩ = ∏_i (F^{x'_{i+1}}_{τ x_i τ})^{x'_i}_{x_{i+1}}` on the periodic chain. These formulas
are quoted in Feiguin's notation `F^d_{abc}`; in the notation `[F^{abc}_d]_e^f` of
`fibFSymbolGolden` the three-site term is `−[F^{x_{i−1} τ τ}_{x_{i+1}}]_{x_i}^1
[F^{x_{i−1} τ τ}_{x_{i+1}}]_{x'_i}^1` and the factor of `Y` is
`[F^{τ x_i τ}_{x'_{i+1}}]_{x'_i}^{x_{i+1}}`.
Review: arXiv:2011.12127, Section 4 "MPO symmetries" and Appendix A, "The MPO for the Fibonacci
model", `Papers/2011.12127/TN-Review-main.tex` lines 1388–1393 and 2613–2627: the anyonic spin
chains built from the pulling-through tensors commute with the whole matrix product operator
algebra, with the Fibonacci F-symbols.

**Formalized here.** With the local projector `Π^{(1)} = −H_i` onto the trivial fusion channel
of two neighbouring anyons, written with the F-symbols of `FibonacciFSymbol`, the golden-chain
Hamiltonian `H_N = −∑_i Π^{(1)}_{i−1,i,i+1}` on the configurations `Fin N → Fin 2` commutes, for
every `N ≥ 2`, with the periodic operator `O_N(B_τ)` of the `τ` block, with the periodic
operator `O_N(B_1)` of the vacuum block, and with the projector `P_N = w_1 O_N(B_1) +
w_τ O_N(B_τ)`. The periodic operator of `B_τ` is Feiguin's `Y`
(`mpo_fibTau_eq_neighbourKernel`). Each commutation follows from one three-site identity of
golden integers (`goldenChainTerm_local_tau`, `goldenChainTerm_local_one`), the local
pulling-through relation of the review, closed around the ring by
`MPOTensor.siteOperator_mul_neighbourKernel`.

The blocks `B_1`, `B_τ` carry the entries fixed by the Local fix (provenance) of
`Fibonacci.lean` (`docs/paper-gaps/bmwshv17_fibonacci_block_entries_provenance.tex`); the
statements here are about those blocks.

## Main definitions

* `FibonacciCompression.goldenChainTermGolden`: the entries of the local projector `Π^{(1)}`.
* `FibonacciCompression.fibYGolden`: the factor of Feiguin's topological symmetry `Y`.
* `FibonacciCompression.goldenChainHamiltonian`: the golden-chain Hamiltonian `H_N`.

## Main results

* `FibonacciCompression.goldenChainTermGolden_tau_tau`: the printed `2 × 2` block of `Π^{(1)}`.
* `FibonacciCompression.mpo_fibTau_eq_neighbourKernel`,
  `FibonacciCompression.mpo_fibOne_eq_neighbourKernel`: the periodic operators of the two blocks
  as nearest-neighbour product kernels.
* `FibonacciCompression.goldenChainHamiltonian_commute_mpo_fibTau`,
  `FibonacciCompression.goldenChainHamiltonian_commute_mpo_fibOne`,
  `FibonacciCompression.goldenChainHamiltonian_commute_fibProjector`: the three commutations.
* `FibonacciCompression.goldenChainHamiltonian_commute_mpo_fibStringNetEdgeTau`: the same for
  the periodic operators of the source's G-symbol tensor on edge label `τ`.

## References
- [arXiv:cond-mat/0612341](https://arxiv.org/abs/cond-mat/0612341) -- A. Feiguin, S. Trebst,
  A. W. W. Ludwig, M. Troyer, A. Kitaev, Z. Wang, M. H. Freedman, *Interacting anyons in
  topological quantum liquids: The golden chain*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor MPOTensor

/-! ### The local projector and the golden chain -/

/-- Source: arXiv:cond-mat/0612341, `fibonacci.tex` lines 148–153. The entry of the local
projector `Π^{(1)} = −H_i` onto the trivial fusion channel of the anyons at links `i`, `i + 1`,
between the neighbours `x_{i−1} = a`, `x_{i+1} = c`, the output `x'_i = b'` and the input
`x_i = b`: `(F^{a τ τ}_c)_{b'}^1 (F^{a τ τ}_c)_b^1`. The label `0` is the trivial anyon and `1`
is `τ`. -/
def goldenChainTermGolden (a c b' b : Fin 2) : GoldenInt :=
  fibFSymbolGolden a 1 1 c b' 0 * fibFSymbolGolden a 1 1 c b 0

/-- Source: arXiv:cond-mat/0612341, `fibonacci.tex` lines 154–175. Between two `τ` neighbours
the local projector is `[[φ^{−2}, φ^{−3/2}], [φ^{−3/2}, φ^{−1}]] = [[σ⁴, σ³], [σ³, σ²]]`. -/
theorem goldenChainTermGolden_tau_tau :
    Matrix.of (goldenChainTermGolden 1 1) = !![sigma ^ 4, sigma ^ 3; sigma ^ 3, sigma ^ 2] := by
  decide

/-- Source: arXiv:cond-mat/0612341, `fibonacci.tex` lines 154–157. Between two trivial
neighbours the local projector is `1` on `|1τ1⟩`, and it vanishes between a trivial and a `τ`
neighbour. -/
theorem goldenChainTermGolden_of_ne_tau_tau :
    goldenChainTermGolden 0 0 = (fun b' b => if b' = 1 ∧ b = 1 then 1 else 0) ∧
      goldenChainTermGolden 0 1 = 0 ∧ goldenChainTermGolden 1 0 = 0 := by
  decide

/-- The complex entries of the local projector `Π^{(1)}`. -/
def goldenChainTerm (a c b' b : Fin 2) : ℂ := goldenToComplex (goldenChainTermGolden a c b' b)

/-- Source: arXiv:cond-mat/0612341, `fibonacci.tex` lines 136–153. The golden-chain Hamiltonian
`H_N = ∑_i H_i = −∑_i Π^{(1)}_{i−1,i,i+1}` on the configurations of a periodic chain of `N`
links. It vanishes on the configurations with two neighbouring trivial labels at a changed
link, which lie outside the constrained space of the source. -/
def goldenChainHamiltonian (N : ℕ) [NeZero N] : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  -∑ i, siteOperator goldenChainTerm i

/-! ### The two blocks as nearest-neighbour kernels -/

/-- Source: arXiv:cond-mat/0612341, `fibonacci.tex` lines 512–516. The factor
`[F^{τ x_i τ}_{x'_{i+1}}]_{x'_i}^{x_{i+1}}` (Feiguin's `(F^{x'_{i+1}}_{τ x_i τ})^{x'_i}_{x_{i+1}}`)
of Feiguin's topological symmetry `Y` at the outputs
`x'_i = a'`, `x'_{i+1} = b'` and the inputs `x_i = a`, `x_{i+1} = b`. -/
def fibYGolden (a' b' a b : Fin 2) : GoldenInt := fibFSymbolGolden 1 a 1 b' a' b

/-- The row of the `τ` block carrying the letter `(x', x)`. -/
private def fibTauRow : Fin 2 → Fin 2 → Fin 3 := ![![0, 0], ![1, 2]]

/-- The vacuum block's kernel factor: the letter `(x', x)` is diagonal and carries the
admissibility of the pair `(x_i, x_{i+1})`. -/
def fibOneKernelGolden (a' b' a b : Fin 2) : GoldenInt :=
  if a' = a ∧ b' = b ∧ ¬(a = 0 ∧ b = 0) then 1 else 0

private theorem fibTauGolden_row_eq_zero :
    ∀ a' a l r, l ≠ fibTauRow a' a → fibTauGolden a' a l r = 0 := by
  have h : ∀ a' a l r, l ≠ fibTauRow a' a → Matrix.of.symm (fibTauGolden a' a) l r = 0 := by
    decide
  exact h

private theorem fibTauGolden_row_eq_fibY :
    ∀ a' a b' b, ¬(b' = 0 ∧ b = 0) →
      fibTauGolden a' a (fibTauRow a' a) (fibTauRow b' b) = fibYGolden a' b' a b := by
  decide

private theorem fibTauGolden_zero_zero : ∀ l r, fibTauGolden 0 0 l r = 0 := by
  have h : ∀ l r, Matrix.of.symm (fibTauGolden 0 0) l r = 0 := by decide
  exact h

private theorem fibYGolden_zero_zero : ∀ b' b, fibYGolden 0 b' 0 b = 0 := by decide

private theorem fibOneGolden_row_eq_zero :
    ∀ a' a l r, l ≠ a → fibOneGolden a' a l r = 0 := by
  have h : ∀ a' a l r, l ≠ a → Matrix.of.symm (fibOneGolden a' a) l r = 0 := by decide
  exact h

private theorem fibOneGolden_eq_kernel :
    ∀ a b, fibOneGolden a a a b = fibOneKernelGolden a b a b := by
  decide

private theorem fibOneGolden_of_ne : ∀ a' a l r, a' ≠ a → fibOneGolden a' a l r = 0 := by
  have h : ∀ a' a l r, a' ≠ a → Matrix.of.symm (fibOneGolden a' a) l r = 0 := by decide
  exact h

/-- Two products around the ring agree when their factors agree at every site whose two ends
are both good, and both factors vanish at every bad site. -/
private theorem prod_eq_prod_of_bad {N : ℕ} [NeZero N] {L R : Fin N → ℂ} (bad : Fin N → Prop)
    (hgood : ∀ n, ¬bad n → ¬bad (n + 1) → L n = R n)
    (hbad : ∀ n, bad n → L n = 0 ∧ R n = 0) :
    ∏ n, L n = ∏ n, R n := by
  by_cases h : ∃ n, bad n
  · obtain ⟨n, hn⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ n) (hbad n hn).1,
      Finset.prod_eq_zero (Finset.mem_univ n) (hbad n hn).2]
  · simp only [not_exists] at h
    exact Finset.prod_congr rfl fun n _ ↦ hgood n (h n) (h (n + 1))

/-- **The periodic operator of the `τ` block is Feiguin's topological symmetry.** Bridge: at
every positive length, `O_N(B_τ)` is the nearest-neighbour product kernel with the factors
`[F^{τ x_i τ}_{x'_{i+1}}]_{x'_i}^{x_{i+1}}` of arXiv:cond-mat/0612341, `fibonacci.tex`
lines 512–516, written there as `(F^{x'_{i+1}}_{τ x_i τ})^{x'_i}_{x_{i+1}}`. -/
theorem mpo_fibTau_eq_neighbourKernel (N : ℕ) [NeZero N] :
    mpo fibTau N = neighbourKernel (fun a' b' a b ↦ goldenToComplex (fibYGolden a' b' a b)) N := by
  ext s t
  rw [mpo_apply_eq_prod_of_forced_bond fibTau s t (fun n ↦ fibTauRow (s n) (t n)) fun g hg ↦ ?_]
  · refine prod_eq_prod_of_bad (fun n ↦ s n = 0 ∧ t n = 0) (fun n h₀ h₁ ↦ ?_) fun n h₀ ↦ ?_
    · simp only [fibTau, complexOfGolden_apply,
        fibTauGolden_row_eq_fibY _ _ _ _ h₁]
    · simp only [fibTau, complexOfGolden_apply, h₀.1, h₀.2, fibTauGolden_zero_zero,
        fibYGolden_zero_zero, map_zero, and_self]
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    exact ⟨n, by simp only [fibTau, complexOfGolden_apply,
      fibTauGolden_row_eq_zero _ _ _ _ hn, map_zero]⟩

/-- **The periodic operator of the vacuum block.** Bridge: at every positive length, `O_N(B_1)`
is the nearest-neighbour product kernel that is diagonal and records whether the configuration
has no two neighbouring trivial labels. -/
theorem mpo_fibOne_eq_neighbourKernel (N : ℕ) [NeZero N] :
    mpo fibOne N =
      neighbourKernel (fun a' b' a b ↦ goldenToComplex (fibOneKernelGolden a' b' a b)) N := by
  ext s t
  rw [mpo_apply_eq_prod_of_forced_bond fibOne s t t fun g hg ↦ ?_]
  · refine prod_eq_prod_of_bad (fun n ↦ s n ≠ t n) (fun n h₀ h₁ ↦ ?_) fun n h₀ ↦ ?_
    · rw [not_not] at h₀ h₁
      simp only [fibOne, complexOfGolden_apply, h₀, h₁, fibOneGolden_eq_kernel]
    · refine ⟨by simp only [fibOne, complexOfGolden_apply,
        fibOneGolden_of_ne _ _ _ _ h₀, map_zero], ?_⟩
      simp [fibOneKernelGolden, h₀]
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    exact ⟨n, by simp only [fibOne, complexOfGolden_apply,
      fibOneGolden_row_eq_zero _ _ _ _ hn, map_zero]⟩

/-! ### The local pulling-through relations -/

/-- **The local relation with the `τ` block.** Project result: the three-site identity
`∑_y Π(a',c')_{b'y} Y(a',y;a,b) Y(y,c';b,c) = ∑_y Y(a',b';a,y) Y(b',c';y,c) Π(a,c)_{yb}`
over the golden integers, the local form of the pulling-through relation of
arXiv:2011.12127, lines 1388–1393. -/
theorem goldenChainTerm_local_tau : ∀ a' b' c' a b c : Fin 2,
    ∑ y, goldenChainTermGolden a' c' b' y * fibYGolden a' y a b * fibYGolden y c' b c =
      ∑ y, fibYGolden a' b' a y * fibYGolden b' c' y c * goldenChainTermGolden a c y b := by
  decide +kernel

/-- **The local relation with the vacuum block.** Project result: the same three-site identity
for the kernel of `O_N(B_1)`. -/
theorem goldenChainTerm_local_one : ∀ a' b' c' a b c : Fin 2,
    ∑ y, goldenChainTermGolden a' c' b' y * fibOneKernelGolden a' y a b *
        fibOneKernelGolden y c' b c =
      ∑ y, fibOneKernelGolden a' b' a y * fibOneKernelGolden b' c' y c *
        goldenChainTermGolden a c y b := by
  decide +kernel

/-- The golden-chain Hamiltonian commutes with every nearest-neighbour kernel of golden
integers that satisfies the local relation. -/
private theorem goldenChainHamiltonian_commute_of_local {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (f : Fin 2 → Fin 2 → Fin 2 → Fin 2 → GoldenInt)
    (hloc : ∀ a' b' c' a b c : Fin 2,
      ∑ y, goldenChainTermGolden a' c' b' y * f a' y a b * f y c' b c =
        ∑ y, f a' b' a y * f b' c' y c * goldenChainTermGolden a c y b) :
    Commute (goldenChainHamiltonian N)
      (neighbourKernel (fun a' b' a b ↦ goldenToComplex (f a' b' a b)) N) := by
  refine (Commute.sum_left _ _ _ fun i _ ↦ ?_).neg_left
  refine siteOperator_mul_neighbourKernel hN (fun a' b' c' a b c ↦ ?_) i
  simpa only [goldenChainTerm, map_sum, map_mul] using
    congrArg goldenToComplex (hloc a' b' c' a b c)

/-- **The golden chain commutes with the `τ` operator.** Source: arXiv:2011.12127, lines 1388–1393,
and arXiv:cond-mat/0612341, `fibonacci.tex` lines 510–516: `[H_N, O_N(B_τ)] = 0` on every
periodic chain of `N ≥ 2` links. -/
theorem goldenChainHamiltonian_commute_mpo_fibTau {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    Commute (goldenChainHamiltonian N) (mpo fibTau N) := by
  rw [mpo_fibTau_eq_neighbourKernel]
  exact goldenChainHamiltonian_commute_of_local hN fibYGolden goldenChainTerm_local_tau

/-- **The golden chain commutes with the vacuum operator.** Source: arXiv:2011.12127,
lines 1388–1393: `[H_N, O_N(B_1)] = 0` on every periodic chain of `N ≥ 2` links. -/
theorem goldenChainHamiltonian_commute_mpo_fibOne {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    Commute (goldenChainHamiltonian N) (mpo fibOne N) := by
  rw [mpo_fibOne_eq_neighbourKernel]
  exact goldenChainHamiltonian_commute_of_local hN fibOneKernelGolden goldenChainTerm_local_one

/-- **The golden chain commutes with the projector.** Source: arXiv:2011.12127, lines 1388–1393:
`[H_N, P_N] = 0` for the projector `P_N = w_1 O_N(B_1) + w_τ O_N(B_τ)` on every periodic chain
of `N ≥ 2` links. -/
theorem goldenChainHamiltonian_commute_fibProjector {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    Commute (goldenChainHamiltonian N) (fibProjector N) :=
  ((goldenChainHamiltonian_commute_mpo_fibOne hN).smul_right _).add_right
    ((goldenChainHamiltonian_commute_mpo_fibTau hN).smul_right _)

/-- **The golden chain commutes with the G-symbol operators.** Source: arXiv:2011.12127,
lines 1388–1393: for each label `f`, `H_N` commutes with the periodic operator of the G-symbol tensor
of arXiv:1511.08090 (lines 1257–1268) restricted to edge label `τ`, which equals `O_N(B_f)` by
`mpo_fibStringNetEdgeTau`. -/
theorem goldenChainHamiltonian_commute_mpo_fibStringNetEdgeTau {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (f : Fin 2) : Commute (goldenChainHamiltonian N) (mpo (fibStringNetEdgeTau f) N) := by
  rw [mpo_fibStringNetEdgeTau]
  fin_cases f
  · exact goldenChainHamiltonian_commute_mpo_fibOne hN
  · exact goldenChainHamiltonian_commute_mpo_fibTau hN

end FibonacciCompression
