/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.VerticalCF
import TNLean.PiAlgebra.Construction

/-!
# Finite-length sufficient conditions and obstructions for MPDO biCF

The `HorizontalCFData` structure in `VerticalCF.lean` packages the block-injective
canonical-form property `biCF` as a hypothesis.  This file records two complementary
facts about that field.

1. A clean **abstract sufficient condition**: if, after blocking to some fixed
   length `L`, the word-evaluation tuples
   `w ↦ (k ↦ evalWord (A k) (List.ofFn w))`
   span the full product algebra `∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ`,
   then the `biCF` conclusion follows from nondegeneracy of the product trace
   pairing.

2. A concrete **counterexample**: blockwise injectivity, left-canonical
   normalization, nonzero weights, and even pairwise distinct weights do **not**
   imply `biCF`.  Thus the current `HorizontalCFData` fields other than `biCF`
   are insufficient for deriving that property.

This isolates the missing ingredient precisely: one still needs a genuine
finite-length block-separation hypothesis, i.e. the content of Proposition IV.3
(`propblockinj`) from arXiv:1606.00608.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- The tuple of length-`L` word evaluations across all blocks. -/
def wordTuple
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) (w : Fin L → Fin d) :
    (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
  fun k => evalWord (A k) (List.ofFn w)

/-- Finite-length span condition on the product algebra of block matrices. -/
def WordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (wordTuple A L)) = ⊤

/-- The block-injective canonical-form property used by `HorizontalCFData`. -/
def HasBiCF
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop :=
  ∃ L : ℕ, ∀ (Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
    (∀ w : Fin L → Fin d,
        (∑ k : Fin r, Matrix.trace (Δ k * evalWord (A k) (List.ofFn w))) = 0) →
    ∀ k, Δ k = 0

/-- A finite-length spanning hypothesis implies `HasBiCF`. -/
theorem hasBiCF_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hSpan : WordTupleSpanTop A L) :
    HasBiCF A := by
  refine ⟨L, ?_⟩
  intro Δ hΔ
  have hΔzero : Δ = 0 := by
    apply piTrace_mul_right_eq_zero
    intro N
    have hZeroOnSpan :
        ∀ M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
          M ∈ Submodule.span ℂ (Set.range (wordTuple A L)) →
          (∑ k : Fin r, Matrix.trace (Δ k * M k)) = 0 := by
      intro M hM
      exact Submodule.span_induction (p := fun x _ =>
          (∑ k : Fin r, Matrix.trace (Δ k * x k)) = 0)
        (fun x hx => by
          rcases hx with ⟨w, rfl⟩
          simpa [wordTuple] using hΔ w)
        (by simp)
        (fun x y hx hy hxzero hyzero => by
          simp [Matrix.mul_add, Matrix.trace_add, hxzero, hyzero, Finset.sum_add_distrib])
        (fun a x hx hxzero => by
          simpa [Pi.smul_apply, Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum] using
            congrArg (fun z : ℂ => a * z) hxzero)
        hM
    exact hZeroOnSpan N (by rw [hSpan]; exact Submodule.mem_top)
  intro k
  simpa using congrArg (fun f => f k) hΔzero

end MPSTensor

namespace MPOTensor

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}

/-- Forgetting the structure fields of `HorizontalCFData` leaves the bare `HasBiCF`
property on the block family. -/
theorem HorizontalCFData.toHasBiCF
    {A : (k : Fin r) → MPSTensor d (dim k)}
    (hCF : HorizontalCFData (d := d) μ A) :
    MPSTensor.HasBiCF A :=
  hCF.biCF

/-- A finite-length block-separation hypothesis packages directly into
`HorizontalCFData`. -/
theorem horizontalCFData_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, MPSTensor.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * A k i = 1)
    (hμne : ∀ k, μ k ≠ 0)
    (hSpan : ∃ L : ℕ, MPSTensor.WordTupleSpanTop A L) :
    HorizontalCFData (d := d) μ A := by
  rcases hSpan with ⟨L, hL⟩
  refine {
    block_injective := hInj
    left_canonical := hLeft
    weight_ne_zero := hμne
    biCF := ?_
  }
  exact MPSTensor.hasBiCF_of_wordTupleSpanTop A hL


/-!
## Why the remaining `HorizontalCFData` fields are still insufficient

The strengthened hypothesis used above is genuinely extra data.  A simple obstruction
shows that one cannot derive `biCF` from blockwise injectivity, left-canonicality,
and nonzero (even pairwise distinct) weights alone.

Take `r = 2`, `d = 1`, `dim k = 1`, and let both blocks be the same scalar tensor
`A_k(0) = 1`, while the weights are `μ 0 = 1` and `μ 1 = 2`.  Then each block is
injective and left-canonical, and the weights are distinct and nonzero.  However for
any blocking length `L` there is only one word `w : Fin L → Fin 1`, and
`evalWord (A k) (List.ofFn w) = 1` for both blocks.  Choosing `Δ 0 = 1` and
`Δ 1 = -1` makes

`∑ k, Matrix.trace (Δ k * MPSTensor.evalWord (A k) (List.ofFn w)) = 0`

for that unique word, while `Δ ≠ 0`.  Therefore `HasBiCF A` fails.

This is exactly the additional information encoded by Proposition IV.3 of
arXiv:1606.00608: one needs a genuine finite-length block-separation theorem, not
just pointwise injectivity of the individual blocks.
-/

end MPOTensor
