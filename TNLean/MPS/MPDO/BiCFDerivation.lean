/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.VerticalCF
import TNLean.PiAlgebra.Construction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite-length sufficient conditions and obstructions for MPDO biCF

The `HorizontalCFData` structure in `VerticalCF.lean` packages the block-injective
canonical-form property `biCF` as a hypothesis. This file records four complementary
facts about that field.

1. A clean **abstract sufficient condition**: if, after blocking to some fixed
   length `L`, the word-evaluation tuples
   `w ↦ (k ↦ evalWord (A k) (List.ofFn w))`
   span the full product algebra `∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ`,
   then the `biCF` conclusion follows from nondegeneracy of the product trace
   pairing.

2. A finite-dimensional **linear-independence endpoint**: if the scalar word-entry
   family obtained by reading off every block matrix entry is linearly
   independent, then those tuple-valued word evaluations already span the full
   product algebra. This reduces biCF to a concrete linear-algebra target.

3. An abstract **Proposition IV.3-style selector package**: if each block is
   block-injective at some common length and a second finite family of words
   isolates the individual blocks (identity on one block, zero on the others),
   then concatenating the two families yields the preceding span condition.
   This captures the finite-length block-separation content of
   [CPGSV17], Proposition IV.3.

4. A concrete **counterexample**: blockwise injectivity, left-canonical
   normalization, nonzero weights, and even pairwise distinct weights do **not**
   imply `biCF`. Thus the current `HorizontalCFData` fields other than `biCF`
   are insufficient for deriving that property.

This isolates the missing ingredient more precisely: one still needs a genuine
finite-length block-separation theorem producing either the selector package of
item (3), or equivalently the word-entry linear independence of item (2), from
canonical-form/BNT data.
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

/-- Index type for a matrix entry inside a block family. -/
abbrev BlockEntryIndex (dim : Fin r → ℕ) :=
  Σ k : Fin r, Fin (dim k) × Fin (dim k)

/-- The value of a tuple of block matrices at a chosen block entry. -/
def blockEntryValue
    (M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (x : BlockEntryIndex dim) : ℂ :=
  M x.1 x.2.1 x.2.2

/-- The scalar word family obtained by reading off one chosen matrix entry of the
block-word tuple. -/
def wordEntryFamily
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) : BlockEntryIndex dim → (Fin L → Fin d) → ℂ :=
  fun x w => blockEntryValue (wordTuple A L w) x

/-- The delta function at a chosen index in a finite function space. -/
private def deltaFun {ι : Type*} [DecidableEq ι] (i : ι) : ι → ℂ :=
  fun j => if j = i then 1 else 0

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

/-- A finite family of words which isolates each block: for every `k`, one can
form a linear combination of those word evaluations that equals the identity on
block `k` and vanishes on all other blocks. -/
def HasBlockSelectorWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    (S : ℕ) : Prop :=
  ∀ k : Fin r, ∃ c : (Fin S → Fin d) → ℂ,
    (∑ w : Fin S → Fin d, c w • evalWord (A k) (List.ofFn w)) = 1 ∧
    ∀ j : Fin r, j ≠ k →
      (∑ w : Fin S → Fin d, c w • evalWord (A j) (List.ofFn w)) = 0

/-- Any finite-length product-algebra spanning witness already contains block
selectors as a special case. -/
theorem hasBlockSelectorWords_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    {S : ℕ} (hSpan : WordTupleSpanTop A S) :
    HasBlockSelectorWords A S := by
  classical
  intro k
  let target : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j => if h : j = k then 1 else 0
  have htarget : target ∈ Submodule.span ℂ (Set.range (wordTuple A S)) := by
    rw [hSpan]
    exact Submodule.mem_top
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp htarget with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · simpa [target] using congrArg (fun M => M k) hc
  · intro j hj
    simpa [target, hj] using congrArg (fun M => M j) hc

private theorem exists_dualCoeffs_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    ∃ coeff : BlockEntryIndex dim → (Fin L → Fin d) → ℂ,
      ∀ x y : BlockEntryIndex dim,
        ∑ w : Fin L → Fin d, coeff x w * wordEntryFamily A L y w =
          if x = y then 1 else 0 := by
  classical
  let lc := Fintype.linearCombination ℂ (wordEntryFamily A L)
  have hlcKer : lc.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact funext (Fintype.linearIndependent_iff.mp hLI c (by simpa [lc] using hc))
  obtain ⟨Ψ, hΨ⟩ := lc.exists_leftInverse_of_injective hlcKer
  let coeff : BlockEntryIndex dim → (Fin L → Fin d) → ℂ :=
    fun x w => Ψ (deltaFun w) x
  have hΨ_apply :
      ∀ (f : (Fin L → Fin d) → ℂ) (x : BlockEntryIndex dim),
        Ψ f x = ∑ w : Fin L → Fin d, f w * coeff x w := by
    intro f x
    have hdecomp : f = ∑ w : Fin L → Fin d, f w • deltaFun w := by
      ext w
      simp [deltaFun]
    rw [hdecomp, map_sum]
    simp [coeff, deltaFun]
  refine ⟨coeff, ?_⟩
  intro x y
  have hsingle : lc (deltaFun y) = wordEntryFamily A L y := by
    ext w
    rw [Fintype.linearCombination_apply, Finset.sum_eq_single y]
    · simp [deltaFun]
    · intro z _ hzy
      simp [deltaFun, hzy]
    · intro hy
      exact False.elim (hy (Finset.mem_univ y))
  have hy : Ψ (wordEntryFamily A L y) x = if x = y then 1 else 0 := by
    have hleft : Ψ (lc (deltaFun y)) = deltaFun y := by
      simpa using congrArg (fun f => f (deltaFun y)) hΨ
    simpa [hsingle, deltaFun] using congrFun hleft x
  simpa [hΨ_apply (wordEntryFamily A L y) x, mul_comm] using hy

/-- Linear independence of the scalar word-entry family forces the tuple-valued
length-`L` word evaluations to span the full product algebra. -/
theorem wordTupleSpanTop_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    WordTupleSpanTop A L := by
  classical
  rcases exists_dualCoeffs_of_wordEntryFamily_linearIndependent A hLI with
    ⟨coeff, hcoeff⟩
  rw [WordTupleSpanTop, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  intro M
  let c : (Fin L → Fin d) → ℂ :=
    fun w => ∑ x : BlockEntryIndex dim, blockEntryValue M x * coeff x w
  refine ⟨c, ?_⟩
  ext j a b
  calc
    (Fintype.linearCombination ℂ (wordTuple A L) c) j a b
        = (∑ w : Fin L → Fin d, c w • evalWord (A j) (List.ofFn w)) a b := by
            simp [Fintype.linearCombination_apply, wordTuple, Pi.smul_apply]
    _ = ∑ w : Fin L → Fin d, c w * wordEntryFamily A L ⟨j, (a, b)⟩ w := by
          simp_rw [Matrix.sum_apply, Matrix.smul_apply]
          simp [wordEntryFamily, blockEntryValue, wordTuple]
    _ = ∑ w : Fin L → Fin d,
          ∑ x : BlockEntryIndex dim,
            blockEntryValue M x * (coeff x w * wordEntryFamily A L ⟨j, (a, b)⟩ w) := by
          unfold c
          refine Finset.sum_congr rfl ?_
          intro w _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = ∑ x : BlockEntryIndex dim,
          blockEntryValue M x *
            (∑ w : Fin L → Fin d, coeff x w * wordEntryFamily A L ⟨j, (a, b)⟩ w) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [← Finset.mul_sum]
    _ = ∑ x : BlockEntryIndex dim,
          blockEntryValue M x * (if x = ⟨j, (a, b)⟩ then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [hcoeff x ⟨j, (a, b)⟩]
    _ = blockEntryValue M ⟨j, (a, b)⟩ := by
          rw [Finset.sum_eq_single ⟨j, (a, b)⟩]
          · simp
          · intro x _ hx
            simp [hx]
          · intro hmem
            exact False.elim (hmem (Finset.mem_univ _))
    _ = M j a b := rfl

/-- The linear-independence endpoint above gives the abstract Proposition-IV.3
selector package as a corollary. -/
theorem hasBlockSelectorWords_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    HasBlockSelectorWords A L :=
  hasBlockSelectorWords_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_wordEntryFamily_linearIndependent A hLI)

/-- The linear-independence endpoint above also yields the `HasBiCF` witness
used by `HorizontalCFData`. -/
theorem hasBiCF_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hLI : LinearIndependent ℂ (wordEntryFamily A L)) :
    HasBiCF A :=
  hasBiCF_of_wordTupleSpanTop A
    (wordTupleSpanTop_of_wordEntryFamily_linearIndependent A hLI)

/-- Abstract finite-length data isolating the content of Proposition IV.3
(`propblockinj`) from arXiv:1606.00608.

A family is `PropBlockInjective` if there is a common blocking length making
all blocks injective, together with a second finite family of words selecting
individual blocks. Concatenating an injective prefix with a selector suffix then
spans the full product algebra. -/
def PropBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop :=
  ∃ L S : ℕ, (∀ k, IsNBlkInjective (A k) L) ∧ HasBlockSelectorWords A S

/-- Common block injectivity plus finite-length block selectors yield the full
word-tuple span condition. -/
theorem wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    (hInj : ∀ k, IsNBlkInjective (A k) L)
    (hSel : HasBlockSelectorWords A S) :
    WordTupleSpanTop A (L + S) := by
  classical
  unfold WordTupleSpanTop
  apply top_unique
  intro M _
  have hMk_mem :
      ∀ k : Fin r,
        M k ∈ Submodule.span ℂ
          (Set.range fun u : Fin L → Fin d => evalWord (A k) (List.ofFn u)) := by
    intro k
    rw [hInj k]
    exact Submodule.mem_top
  choose prefixCoeffs hprefix using
    fun k =>
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hMk_mem k)
  choose selectorCoeffs hselector_self hselector_off using hSel
  let assembled : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
    ∑ k : Fin r, ∑ u : Fin L → Fin d, ∑ v : Fin S → Fin d,
      (prefixCoeffs k u * selectorCoeffs k v) •
        wordTuple A (L + S) (Fin.append u v)
  have hassembled_mem :
      assembled ∈ Submodule.span ℂ (Set.range (wordTuple A (L + S))) := by
    unfold assembled
    refine Submodule.sum_mem _ ?_
    intro k _
    refine Submodule.sum_mem _ ?_
    intro u _
    refine Submodule.sum_mem _ ?_
    intro v _
    refine Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨Fin.append u v, rfl⟩
  have hassembled : assembled = M := by
    funext j
    unfold assembled
    calc
      (∑ k : Fin r, ∑ u : Fin L → Fin d, ∑ v : Fin S → Fin d,
            (prefixCoeffs k u * selectorCoeffs k v) •
              wordTuple A (L + S) (Fin.append u v)) j
          = ∑ k : Fin r, ∑ u : Fin L → Fin d, ∑ v : Fin S → Fin d,
              (prefixCoeffs k u * selectorCoeffs k v) •
                (evalWord (A j) (List.ofFn u) *
                  evalWord (A j) (List.ofFn v)) := by
              simp [wordTuple, List.ofFn_fin_append, evalWord_append]
      _ = ∑ k : Fin r, ∑ u : Fin L → Fin d,
            prefixCoeffs k u •
              (evalWord (A j) (List.ofFn u) *
                ∑ v : Fin S → Fin d,
                  selectorCoeffs k v • evalWord (A j) (List.ofFn v)) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            refine Finset.sum_congr rfl ?_
            intro u _
            calc
              ∑ v : Fin S → Fin d,
                  (prefixCoeffs k u * selectorCoeffs k v) •
                    (evalWord (A j) (List.ofFn u) *
                      evalWord (A j) (List.ofFn v))
                = ∑ v : Fin S → Fin d,
                    prefixCoeffs k u •
                      (evalWord (A j) (List.ofFn u) *
                        (selectorCoeffs k v • evalWord (A j) (List.ofFn v))) := by
                    refine Finset.sum_congr rfl ?_
                    intro v _
                    rw [Matrix.mul_smul]
                    simp [smul_smul]
              _ = prefixCoeffs k u •
                    (evalWord (A j) (List.ofFn u) *
                      ∑ v : Fin S → Fin d,
                        selectorCoeffs k v • evalWord (A j) (List.ofFn v)) := by
                    rw [Matrix.mul_sum, Finset.smul_sum]
      _ = ∑ k : Fin r, ∑ u : Fin L → Fin d,
            if h : k = j then
              prefixCoeffs k u • evalWord (A j) (List.ofFn u)
            else 0 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            refine Finset.sum_congr rfl ?_
            intro u _
            by_cases hkj : k = j
            · subst hkj
              simp [hselector_self]
            · have hjk : j ≠ k := by
                intro hjk
                exact hkj hjk.symm
              have hzero :
                  ∑ v : Fin S → Fin d,
                    selectorCoeffs k v • evalWord (A j) (List.ofFn v) = 0 :=
                hselector_off k j hjk
              simp [hkj, hzero]
      _ = ∑ u : Fin L → Fin d,
            prefixCoeffs j u • evalWord (A j) (List.ofFn u) := by
            simp
      _ = M j := hprefix j
  rw [← hassembled]
  exact hassembled_mem

/-- The abstract Proposition-IV.3 selector package implies the finite-length
word-tuple span condition. -/
theorem wordTupleSpanTop_of_propBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hProp : PropBlockInjective A) :
    ∃ N : ℕ, WordTupleSpanTop A N := by
  rcases hProp with ⟨L, S, hInj, hSel⟩
  exact ⟨L + S,
    wordTupleSpanTop_of_common_blockInjective_of_blockSelectorWords A hInj hSel⟩

/-- The abstract Proposition-IV.3 selector package implies `HasBiCF`. -/
theorem hasBiCF_of_propBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hProp : PropBlockInjective A) :
    HasBiCF A := by
  rcases wordTupleSpanTop_of_propBlockInjective A hProp with ⟨N, hN⟩
  exact hasBiCF_of_wordTupleSpanTop A hN

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

/-- Linear independence of the scalar word-entry family is another concrete
route into `HorizontalCFData`: it already implies the finite-length product
algebra span condition. -/
theorem horizontalCFData_of_wordEntryFamily_linearIndependent
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, MPSTensor.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * A k i = 1)
    (hμne : ∀ k, μ k ≠ 0)
    {L : ℕ}
    (hLI : LinearIndependent ℂ (MPSTensor.wordEntryFamily A L)) :
    HorizontalCFData (d := d) μ A :=
  horizontalCFData_of_wordTupleSpanTop A hInj hLeft hμne
    ⟨L, MPSTensor.wordTupleSpanTop_of_wordEntryFamily_linearIndependent A hLI⟩

/-- Proposition-IV.3-style selector data packages directly into
`HorizontalCFData` through the finite-length span criterion. -/
theorem horizontalCFData_of_propBlockInjective
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hInj : ∀ k, MPSTensor.IsInjective (A k))
    (hLeft : ∀ k, ∑ i : Fin d, (A k i)ᴴ * A k i = 1)
    (hμne : ∀ k, μ k ≠ 0)
    (hProp : MPSTensor.PropBlockInjective A) :
    HorizontalCFData (d := d) μ A := by
  refine {
    block_injective := hInj
    left_canonical := hLeft
    weight_ne_zero := hμne
    biCF := MPSTensor.hasBiCF_of_propBlockInjective A hProp
  }


/-!
## Why the remaining `HorizontalCFData` fields are still insufficient

The strengthened hypotheses used above are genuinely extra data. A simple
obstruction shows that one cannot derive `biCF` from blockwise injectivity,
left-canonicality, and nonzero (even pairwise distinct) weights alone.

Take `r = 2`, `d = 1`, `dim k = 1`, and let both blocks be the same scalar tensor
`A_k(0) = 1`, while the weights are `μ 0 = 1` and `μ 1 = 2`. Then each block is
injective and left-canonical, and the weights are distinct and nonzero. However for
any blocking length `L` there is only one word `w : Fin L → Fin 1`, and
`evalWord (A k) (List.ofFn w) = 1` for both blocks. Choosing `Δ 0 = 1` and
`Δ 1 = -1` makes

`∑ k, Matrix.trace (Δ k * MPSTensor.evalWord (A k) (List.ofFn w)) = 0`

for that unique word, while `Δ ≠ 0`. Therefore `HasBiCF A` fails.

The new predicate `PropBlockInjective` packages one abstract finite-length route,
while `wordEntryFamily` packages a second, equivalent linear-algebra endpoint.
What remains open is to derive either of those finite-length witnesses from the
repository's current BNT / canonical-form hypotheses, i.e. to formalize the full
content of Proposition IV.3 of arXiv:1606.00608.
-/

end MPOTensor
