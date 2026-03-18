/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

/-!
# Full Fundamental Theorem of MPS

This module proves the **Fundamental Theorem of Matrix Product States** by combining:

1. **`BNTConstruction.lean`**: the `IsCanonicalFormBNT` structure for canonical forms with
   basis-of-normal-tensors (BNT) separation, the legacy bridge theorem
   `fundamentalTheorem_of_IsCanonicalFormBNT`, and the weaker split-data bridge
   `fundamentalTheorem_of_separated_CFBNT_data` (proportional MPVs with convergent coefficients
   → permutation + gauge-phase matching).

2. **`ScalarPowerSumIdentity.lean`**: `Matrix.sum_pow_eq_implies_multiset_eq`
   (equal power sums → equal multisets of scalars).

3. **`CanonicalFormSep.lean`**: `fundamentalTheorem_canonicalForm` together with the weaker
   split-data interface `fundamentalTheorem_of_separated_canonical_data` (per-block separation
   for tensors in canonical form with equal MPVs).

4. **`FundamentalTheoremMulti.lean`**: `toTensorFromBlocks`, `mpv_toTensorFromBlocks_eq_sum`,
   `gaugeEquiv_toTensorFromBlocks_of_blockConj` (block-diagonal assembly).

5. **`BNT/PermutationRigidity.lean`**:
   `exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp`
   (permutation + gauge-phase from proportional MPVs — core of Thm 4.4).

## Main results

### Theorem 1: Equal-MPV Fundamental Theorem for `IsCanonicalFormBNT`
(`fundamentalTheorem_equalMPV_CFBNT`)

**Corollary II_cor2 (equal case)**: If two families of tensors in canonical form with
basis-of-normal-tensors (BNT) separation share the same `μ`-weights, same block count `r`, and
same block dimensions, and
generate *equal* MPVs for all system sizes, then per-block gauge equivalence holds together
with a global gauge equivalence of the block-diagonal tensors.

### Theorem 2: Proportional-MPV Fundamental Theorem (Thm 4.4)
(`fundamentalTheorem_proportionalMPV_CFBNT`)

**Theorem 4.4 (proportional case)**: If two families of tensors in canonical form with
basis-of-normal-tensors (BNT) separation generate proportional MPVs, and the decomposition
coefficients converge to
nonzero limits, then the block counts are equal and blocks match up to permutation,
dimension equality, and gauge-phase equivalence.

### Theorem 3: Equal MPVs imply proportional MPVs
(`sameMPV₂_implies_proportionalMPV₂`)

Trivial but useful: `SameMPV₂ A B → ProportionalMPV₂ A B` (take `c_N = 1`).

### Theorem 4: Power-sum multiset equality
(`mu_multiset_eq_of_power_sum_eq`)

If two sequences of complex numbers have equal power sums for all exponents, their multisets
(as roots) are equal. This is the formalized version of Lemma Lem:app_simple from the paper.

## References

- Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.

## Design notes

The **coefficient convergence** question: In the full paper, the decomposition into a basis of
normal tensors uses coefficients `c_j(N) = Σ_{q in group j} μ_{j,q}^N`.
These coefficients need not converge in general after normalization, because unit-modulus
terms can still oscillate. The `IsCanonicalFormBNT` predicate sidesteps this by requiring the
BNT grouping already done, and the proportional-case theorem takes whatever convergent
coefficient data it needs as explicit hypotheses.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ## Theorem 1: Equal-MPV Fundamental Theorem for `IsCanonicalFormBNT`

This is the content of Corollary II_cor2 from arXiv:2011.12127 / arXiv:1606.00608,
specialized to the case where both families share the same block structure (same `r`,
same `dim`, same `μ`).
-/

/-- **Equal-MPV Fundamental Theorem for CF-BNT (Cor. II_cor2, same structure).**

If two families of tensors in canonical form with BNT separation share the same
block weights `μ`, the same number of blocks `r`, and the same block dimensions
`dim`, and generate equal MPV families for all system sizes, then:

(i)  per-block gauge equivalence: `GaugeEquiv (A k) (B k)` for all `k`;
(ii) global gauge equivalence of the block-diagonal tensors. -/
theorem fundamentalTheorem_equalMPV_CFBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A)
    (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  fundamentalTheorem_canonicalForm μ A B hA.toIsCanonicalForm hB.block_injective hB.leftCanonical
    hSame

/-- **Equal-MPV FT for CF-BNT with explicit gauge matrices.** -/
theorem fundamentalTheorem_equalMPV_CFBNT_explicit
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A)
    (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) :=
  fundamentalTheorem_canonicalForm_explicit μ A B hA.toIsCanonicalForm hB.block_injective
    hB.leftCanonical hSame

/-! ## Theorem 2: Proportional-MPV Fundamental Theorem (Thm 4.4)

This is the content of Theorem 4.4 from arXiv:1606.00608 (primitive branch).
The theorem takes convergent coefficient data as explicit hypotheses.
-/

/-- Split-data proportional-MPV Fundamental Theorem for CF-BNT-style data (Thm 4.4).

This is the Stage B low-risk interface: it packages only the hypotheses actually used by the
proportional-MPV argument, and leaves the legacy `IsCanonicalFormBNT` wrapper theorem below
unchanged. -/
theorem fundamentalTheorem_proportionalMPV_of_separated_CFBNT_data
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA_inj : HasInjectiveBlocks (d := d) A)
    (hA_left : IsLeftCanonicalBlockFamily (d := d) A)
    (hA_overlap : HasNormalizedSelfOverlap (d := d) A)
    (hA_blocks : ∀ j k : Fin rA, j ≠ k →
      ∀ (h : dimA j = dimA k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k))
    (hB_inj : HasInjectiveBlocks (d := d) B)
    (hB_left : IsLeftCanonicalBlockFamily (d := d) B)
    (hB_overlap : HasNormalizedSelfOverlap (d := d) B)
    (hB_blocks : ∀ j k : Fin rB, j ≠ k →
      ∀ (h : dimB j = dimB k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (B j)) (B k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  fundamentalTheorem_of_separated_CFBNT_data A B
    hA_inj hA_left hA_overlap hA_blocks
    hB_inj hB_left hB_overlap hB_blocks
    A_total B_total aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

/-- **Proportional-MPV Fundamental Theorem for CF-BNT (Thm 4.4).**

If two families of tensors in canonical form with BNT separation generate proportional
MPV families (with explicitly convergent nonzero decomposition coefficients), then:

(i)  same block count: `rA = rB`;
(ii) there exists a permutation `σ : Fin rA ≃ Fin rB` such that for each block `j`,
     the bond dimensions match and the blocks are gauge-phase equivalent.

**Coefficient convergence**: The caller must supply the decomposition coefficients
`aCoeff`, `bCoeff` and their limits. In a strict-dominance specialization one may take
`aCoeff N j = μA_j^N / μA_0^N` after normalizing so that `|μA_0| = |μB_0| = 1`,
and then the subdominant ratios decay. In the general paper-level BNT setup, however,
the coefficients are sums `Σ_q μ_{j,q}^N` and need not converge without extra input. -/
theorem fundamentalTheorem_proportionalMPV_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  fundamentalTheorem_of_IsCanonicalFormBNT A B hA hB A_total B_total aCoeff bCoeff aLim bLim c
    cLim hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

/-- Split-data proportional-MPV Fundamental Theorem for normal-CF-BNT-style data. -/
theorem fundamentalTheorem_proportionalMPV_of_separated_normalCFBNT_data
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA_ncf : IsNormalCanonicalForm μA A)
    (hA_blocks : ∀ j k : Fin rA, j ≠ k →
      ∀ (h : dimA j = dimA k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k))
    (hB_ncf : IsNormalCanonicalForm μB B)
    (hB_blocks : ∀ j k : Fin rB, j ≠ k →
      ∀ (h : dimB j = dimB k),
        ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (B j)) (B k))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  fundamentalTheorem_of_separated_normalCFBNT_data A B
    hA_ncf hA_blocks hB_ncf hB_blocks
    A_total B_total aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

/-- Fundamental Theorem (proportional case) for normal canonical form blocks. -/
theorem fundamentalTheorem_proportionalMPV_normalCFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsNormalCanonicalFormBNT μA A)
    (hB : IsNormalCanonicalFormBNT μB B)
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (c : ℕ → ℂ) (cLim : ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc : Tendsto c atTop (nhds cLim))
    (hcLim_ne : cLim ≠ 0) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  fundamentalTheorem_of_IsNormalCanonicalFormBNT A B hA hB
    A_total B_total aCoeff bCoeff aLim bLim c cLim
    hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne hProp hc hcLim_ne

/-! ## Theorem 3: Equal MPVs imply proportional MPVs -/

/-- **Equal MPVs imply proportional MPVs** (trivially, with proportionality constant `1`).

This is useful for reducing Corollary II_cor2 to the proportional case of Thm 4.4. -/
theorem sameMPV₂_implies_proportionalMPV₂
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : SameMPV₂ A B) :
    ProportionalMPV₂ A B := by
  intro N
  exact ⟨1, fun σ => by simpa using h N σ⟩

/-- **Equal-MPV upgrade of the current formalized proportional FT for CF-BNT.**

The literature-level equal-MPV FT (`thm:ft_equal` in the blueprint) should start from only the
CF-BNT data and `SameMPV₂`.  The current local machinery is weaker: the available proportional FT
`fundamentalTheorem_proportionalMPV_CFBNT` still requires explicit decomposition coefficients with
nonzero limits, and its conclusion is a block permutation together with per-block
`GaugePhaseEquiv` data.

This theorem records the equal-case endpoint that *is* derivable from that machinery.  Under the
same coefficient hypotheses as the proportional theorem, equal MPVs force the phase-corrected
weights to match blockwise.  After reindexing the `B`-family by the permutation from the
proportional FT, the assembled weighted block tensors are globally gauge equivalent. -/
theorem fundamentalTheorem_equalMPV_full
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (aCoeff : ℕ → Fin rA → ℂ) (bCoeff : ℕ → Fin rB → ℂ)
    (aLim : Fin rA → ℂ) (bLim : Fin rB → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μA A) σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μB B) σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (haCoeff : ∀ j, Tendsto (fun N => aCoeff N j) atTop (nhds (aLim j)))
    (hbCoeff : ∀ k, Tendsto (fun N => bCoeff N k) atTop (nhds (bLim k)))
    (haLim_ne : ∀ j, aLim j ≠ 0)
    (hbLim_ne : ∀ k, bLim k ≠ 0)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ perm : Fin rA ≃ Fin rB,
      ∃ hdim : ∀ j : Fin rA, dimA j = dimB (perm j),
        GaugeEquiv
          (toTensorFromBlocks μA
            (fun j => cast (congr_arg (MPSTensor d) (hdim j)) (A j)))
          (toTensorFromBlocks (fun j => μB (perm j))
            (fun j => B (perm j))) := by
  have hProp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μA A) σ = (1 : ℂ) * mpv (toTensorFromBlocks μB B) σ := by
    intro N σ
    simpa using hEqual N σ
  obtain ⟨_hcount, perm, hperm⟩ :=
    fundamentalTheorem_proportionalMPV_CFBNT A B hA hB
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)
      aCoeff bCoeff aLim bLim (fun _ => (1 : ℂ)) (1 : ℂ)
      hA_decomp hB_decomp haCoeff hbCoeff haLim_ne hbLim_ne
      hProp tendsto_const_nhds one_ne_zero
  choose hdim hGP using hperm
  choose X ζ hζ hX using hGP
  have hBNTA := hA.isBNT
  obtain ⟨N0, hLI⟩ := hBNTA.eventually_li
  have hμA_ne : ∀ j : Fin rA, μA j ≠ 0 :=
    hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  have hμB_ne : ∀ k : Fin rB, μB k ≠ 0 :=
    hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  have hCoeffEq :
      ∀ N : ℕ, N > N0 →
        ∀ j : Fin rA, μA j ^ N = (μB (perm j) * ζ j) ^ N := by
    intro N hN j
    have hLIN : LinearIndependent ℂ (fun j : Fin rA => mpvState (d := d) (A j) N) := hLI N hN
    have hsums :
        ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N =
          ∑ j : Fin rA, (μB (perm j) * ζ j) ^ N • mpvState (d := d) (A j) N := by
      ext σ
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
        mpvState_apply, smul_eq_mul]
      calc
        ∑ j : Fin rA, (μA j) ^ N * mpv (A j) σ
            = mpv (toTensorFromBlocks μA A) σ := by
              symm
              simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μA A σ
        _ = mpv (toTensorFromBlocks μB B) σ := hEqual N σ
        _ = ∑ k : Fin rB, (μB k) ^ N * mpv (B k) σ := by
              simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μB B σ
        _ = ∑ j : Fin rA, (μB (perm j)) ^ N * mpv (B (perm j)) σ := by
              simpa using (Equiv.sum_comp perm (fun k : Fin rB => (μB k) ^ N * mpv (B k) σ)).symm
        _ = ∑ j : Fin rA, (μB (perm j) * ζ j) ^ N * mpv (A j) σ := by
              refine Finset.sum_congr rfl ?_
              intro j _
              have hmpv :=
                mpv_eq_pow_mul_of_gaugePhase
                  (A := cast (congr_arg (MPSTensor d) (hdim j)) (A j))
                  (B := B (perm j))
                  (X := X j) (ζ := ζ j) (hX := hX j)
                  N σ
              rw [hmpv, mpv_cast_dim (hdim j) (A j) N σ]
              calc
                (μB (perm j)) ^ N * (ζ j ^ N * mpv (A j) σ)
                    = ((μB (perm j)) ^ N * ζ j ^ N) * mpv (A j) σ := by ring
                _ = (μB (perm j) * ζ j) ^ N * mpv (A j) σ := by rw [← mul_pow]
    have hdiff :
        ∑ j : Fin rA, ((μA j) ^ N - (μB (perm j) * ζ j) ^ N) •
            mpvState (d := d) (A j) N = 0 := by
      simpa [Finset.sum_sub_distrib, sub_smul] using (sub_eq_zero.mpr hsums)
    have hzero :=
      Fintype.linearIndependent_iff.mp hLIN
        (fun j : Fin rA => (μA j) ^ N - (μB (perm j) * ζ j) ^ N)
        hdiff
    exact sub_eq_zero.mp (hzero j)
  have hWeight : ∀ j : Fin rA, μA j = μB (perm j) * ζ j := by
    intro j
    have hpow1 := hCoeffEq (N0 + 1) (Nat.lt_succ_self N0) j
    have hpow2 := hCoeffEq ((N0 + 1) + 1) (by omega) j
    have hmul :
        μA j ^ (N0 + 1) * μA j = μA j ^ (N0 + 1) * (μB (perm j) * ζ j) := by
      calc
        μA j ^ (N0 + 1) * μA j = μA j ^ ((N0 + 1) + 1) := by
          simp [pow_succ, mul_assoc]
        _ = (μB (perm j) * ζ j) ^ ((N0 + 1) + 1) := hpow2
        _ = (μB (perm j) * ζ j) ^ (N0 + 1) * (μB (perm j) * ζ j) := by
          simp [pow_succ, mul_assoc]
        _ = μA j ^ (N0 + 1) * (μB (perm j) * ζ j) := by rw [hpow1]
    exact mul_left_cancel₀ (pow_ne_zero (N0 + 1) (hμA_ne j)) hmul
  let Acast : (j : Fin rA) → MPSTensor d (dimB (perm j)) :=
    fun j => cast (congr_arg (MPSTensor d) (hdim j)) (A j)
  let Aweighted : (j : Fin rA) → MPSTensor d (dimB (perm j)) :=
    fun j i => (μA j) • Acast j i
  let Bweighted : (j : Fin rA) → MPSTensor d (dimB (perm j)) :=
    fun j i => (μB (perm j)) • B (perm j) i
  have hWeightedConj : ∀ j : Fin rA, ∀ i : Fin d,
      Bweighted j i =
        (X j : Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ) *
          Aweighted j i *
          (((X j)⁻¹ : GL (Fin (dimB (perm j))) ℂ) :
            Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ) := by
    intro j i
    calc
      Bweighted j i
          = (μB (perm j) * ζ j) •
              ((X j : Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ) *
                Acast j i *
                (((X j)⁻¹ : GL (Fin (dimB (perm j))) ℂ) :
                  Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ)) := by
            simp [Bweighted, Acast, hX j i, smul_smul, mul_comm, mul_assoc]
      _ = (μA j) •
            ((X j : Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ) *
              Acast j i *
              (((X j)⁻¹ : GL (Fin (dimB (perm j))) ℂ) :
                Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ)) := by
            rw [(hWeight j).symm]
      _ = (X j : Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ) *
            Aweighted j i *
            (((X j)⁻¹ : GL (Fin (dimB (perm j))) ℂ) :
              Matrix (Fin (dimB (perm j))) (Fin (dimB (perm j))) ℂ) := by
            simp [Aweighted, Acast, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
              Matrix.mul_assoc]
  refine ⟨perm, hdim, ?_⟩
  have hGaugeWeighted :=
    gaugeEquiv_toTensorFromBlocks_of_blockConj (d := d) (μ := fun _ : Fin rA => (1 : ℂ))
      Aweighted Bweighted X hWeightedConj
  have hA_tot :
      toTensorFromBlocks μA (fun j => cast (congr_arg (MPSTensor d) (hdim j)) (A j)) =
        toTensorFromBlocks (fun _ : Fin rA => (1 : ℂ)) Aweighted := by
    ext i
    simp [toTensorFromBlocks, Aweighted, Acast]
  have hB_tot :
      toTensorFromBlocks (fun j => μB (perm j)) (fun j => B (perm j)) =
        toTensorFromBlocks (fun _ : Fin rA => (1 : ℂ)) Bweighted := by
    ext i
    simp [toTensorFromBlocks, Bweighted]
  rw [hA_tot, hB_tot]
  exact hGaugeWeighted

/-! ## Theorem 4: Power-sum multiset equality (Lem:app_simple)

This wraps `Matrix.sum_pow_eq_implies_multiset_eq` from `ScalarPowerSumIdentity.lean`
to provide the paper's Lemma Lem:app_simple in a convenient form.
-/

/-- **Equal power sums imply equal multisets (Lem:app_simple).**

If two sequences of complex numbers `α : Fin n → ℂ` and `β : Fin n → ℂ` satisfy
`∑ i, (α i)^k = ∑ i, (β i)^k` for all positive `k`, then `α` and `β` have the same
multiset of values (counted with multiplicity).

This is the paper's Lemma Lem:app_simple, proved via Newton's identities
(`Matrix.sum_pow_eq_implies_multiset_eq` from `ScalarPowerSumIdentity.lean`). -/
theorem power_sum_eq_implies_multiset_eq (n : ℕ)
    (α β : Fin n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i : Fin n, (α i) ^ k = ∑ i : Fin n, (β i) ^ k) :
    Finset.univ.val.map α = Finset.univ.val.map β :=
  Matrix.sum_pow_eq_implies_multiset_eq α β h

/-! ## Combined corollaries -/

section Corollaries

/-- **Per-block SameMPV from CF-BNT equal MPVs.**

Extracts the per-block `SameMPV` conclusion from the equal-MPV theorem. -/
theorem perBlock_sameMPV_of_equalMPV_CFBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A)
    (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) := by
  intro k
  exact GaugeEquiv.sameMPV ((fundamentalTheorem_equalMPV_CFBNT A B hA hB hSame).1 k)

end Corollaries

/-! ## Theorem 5: Self-contained equal-case FT for heterogeneous CF-BNT

This section builds toward the **strongest equal-case fundamental theorem** currently
formalizable: given two `IsCanonicalFormBNT` families with *different* block structures
(`rA`, `rB`, `dimA`, `dimB`, `μA`, `μB`), the hypothesis `SameMPV₂` alone (no coefficient
convergence data from the caller) forces block-count equality, a block permutation, and
blockwise gauge-phase equivalence.

### References

- [CPSV21, Corollary IV.5] Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states
  and projected entangled pair states*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
- [CPSV17, Theorem 4.4 + equal-case corollary] Cirac, Pérez-García, Schuch, Verstraete,
  *Fundamental Theorems for PEPS*, arXiv:1606.00608 (2017).

### Proof architecture

**Layer 1 — Exponential polynomial uniqueness** (`blocks_match_of_sameMPV₂_CFBNT`):
The BNT decomposition via `mpv_toTensorFromBlocks_eq_sum` gives
  `∑_j (μA j)^N * mpv(A j) σ = ∑_k (μB k)^N * mpv(B k) σ`   (all N, σ).
Since all `μA` values are distinct (injective, from `HasStrictOrderedNonzeroWeights`) and all
`μB` values are distinct, the combined identity is a vanishing exponential polynomial whose
bases are the union `{μA j} ∪ {μB k}`. Grouping terms by common base value and applying
Vandermonde uniqueness (`Matrix.det_vandermonde_ne_zero_iff` from Mathlib) shows:
- Each `μA` value must match some `μB` value (otherwise `mpv(A j) ≡ 0`, contradicting
  self-overlap → 1 / BNT nontriviality).
- For matched pairs, the block MPVs agree pointwise.
- The matching is a bijection (injective map between finite sets of equal cardinality).

**Layer 2 — Overlap dichotomy → dim + GaugePhaseEquiv**
(`gaugePhaseEquiv_of_block_sameMPV₂_CFBNT`):
Per-block `SameMPV₂` makes the cross-overlap equal the self-overlap (→ 1), so it cannot
decay.  The overlap-dichotomy lemmas then force:
  (a) dimension equality (contrapositive of dim-mismatch decay), and
  (b) gauge-phase equivalence (contrapositive of non-GPE decay).

**Layer 3 — Composition** (`fundamentalTheorem_equalMPV_CFBNT_hetero`):
Compose Layer 1 and Layer 2.
-/

section HeteroEqualCase

/-- Overlap of two blocks with pointwise-equal MPVs equals the self-overlap of the first. -/
private lemma mpvOverlap_eq_selfOverlap_of_forall_mpv_eq
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ) :
    ∀ N, mpvOverlap (d := d) A B N = mpvOverlap (d := d) A A N := by
  intro N
  simp only [mpvOverlap, h]

/-- **Layer 2: Per-block `SameMPV₂` + block properties → dim equality + GaugePhaseEquiv.**

Given two individual blocks with pointwise-equal MPVs, both injective and left-canonical,
and with the first block's self-overlap tending to 1:
1. The cross-overlap equals the self-overlap (→ 1), hence does not decay to 0.
2. Dimension mismatch would force overlap → 0 (`mpvOverlap_tendsto_zero_of_dim_ne`).
   Contradiction ⟹ dimensions match.
3. Non-gauge-phase-equivalence would force overlap → 0
   (`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left`).
   Contradiction ⟹ gauge-phase equivalent. -/
private lemma gaugePhaseEquiv_of_block_sameMPV₂
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_inj : IsInjective A) (hB_inj : IsInjective B)
    (hA_norm : (∑ i : Fin d, (A i)ᴴ * (A i)) = 1)
    (hB_norm : (∑ i : Fin d, (B i)ᴴ * (B i)) = 1)
    (hA_self : Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)))
    (hSameMPV : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv A σ = mpv B σ) :
    ∃ hdim : D₁ = D₂,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- Cross-overlap = self-overlap → 1.
  have hOvEq := mpvOverlap_eq_selfOverlap_of_forall_mpv_eq A B hSameMPV
  have hOvOne : Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds (1 : ℂ)) :=
    hA_self.congr (fun N => (hOvEq N).symm)
  have hOvNot0 : ¬ Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0) :=
    fun h0 => one_ne_zero (tendsto_nhds_unique hOvOne h0)
  -- Dim equality by contradiction.
  have hdim : D₁ = D₂ := by
    by_contra hne
    exact hOvNot0
      (mpvOverlap_tendsto_zero_of_dim_ne A B hA_inj hB_inj hA_norm hB_norm hne)
  refine ⟨hdim, ?_⟩
  -- GaugePhaseEquiv by contradiction.
  by_contra hNotGPE
  exact hOvNot0
    (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      hdim A B hA_inj hB_inj hA_norm hB_norm hNotGPE)

/-- If `α ^ n → L` with `L ≠ 0`, then `α = 1`.
Proof: `α^(n+1) → L` and `α * α^n → α * L`, so `α * L = L`, hence `α = 1`. -/
private theorem eq_one_of_pow_tendsto {α L : ℂ} (hL : L ≠ 0)
    (h : Tendsto (fun n => α ^ n) atTop (nhds L)) : α = 1 := by
  have h1 : Tendsto (fun n => α ^ (n + 1)) atTop (nhds L) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => α * α ^ n) atTop (nhds (α * L)) :=
    h.const_mul α
  have h3 : (fun n => α * α ^ n) = (fun n => α ^ (n + 1)) := by ext n; ring
  have h4 : α * L = L := tendsto_nhds_unique (h3 ▸ h2) h1
  exact mul_right_cancel₀ hL (by rwa [one_mul])

/-- **Non-decaying overlap existence for equal-MPV BNT families.**

For two `IsCanonicalFormBNT` families with equal total MPVs (`SameMPV₂`), every block in
one family has non-decaying cross-overlap with some block in the other.

The proof proceeds by strong induction on `rA + rB`:

* **Dominant blocks** (`j = 0` or `k = 0`): The normalized overlap identity and the
  equality `‖μA 0‖ = ‖μB 0‖` (derived from the total self-overlap) give a non-vanishing
  overlap norm, contradicting the hypothesis that all cross-overlaps decay to zero.

* **Non-dominant blocks** (`j > 0` or `k > 0`): After matching dominant blocks via the
  overlap dichotomy and extracting the weight relation `μA 0 = ζ · μB π(0)` from the
  gauge-phase equivalence, the matched dominant pair is subtracted from the weighted-sum
  identity.  The reduced identity involves `rA − 1` and `rB − 1` blocks that still satisfy
  `IsCanonicalFormBNT` (all per-block properties are inherited, and the strict weight
  ordering restricts to the sub-range).  The strong induction hypothesis then closes the
  remaining cases. -/
private lemma exists_nondecaying_overlap_of_sameMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hSumState : ∀ N : ℕ,
      ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)
    (hA_self : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N) atTop (nhds 1))
    (hB_self : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds 1))
    (hA_cross : ∀ j k, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0))
    (hB_cross : ∀ j k, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (B j) (B k) N) atTop (nhds 0)) :
    (∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0)) ∧
    (∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0)) := by
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- Proof sketch (overlap dichotomy + dominant-weight inner-product argument):
  --
  -- **Step A – Norm equality ‖μA 0‖ = ‖μB 0‖** (unconditional):
  -- From hSumState, take ⟨mpvState(B 0, N), ·⟩ and divide by (μB 0)^N.
  -- If ‖μA 0‖ < ‖μB 0‖, all ratios |μA j / μB 0| < 1, so the LHS → 0 while
  -- the RHS → 1 (from self-overlap → 1). Contradiction. Similarly for the reverse.
  --
  -- **Step B – Dominant case** (j₀ = 0 on A-side, k₀ = 0 on B-side):
  -- Assume ∀ k, mpvOverlap(A 0, B k) → 0. Take ⟨mpvState(A 0, N), ·⟩ / (μA 0)^N.
  -- LHS → 1 (self-overlap). RHS: each |μB k / μA 0| ≤ 1 (norm equality) and
  -- inner → 0 (from hall), so each term → 0. Contradiction.
  --
  -- **Step C – Non-dominant blocks** (j₀ > 0 or k₀ > 0):
  -- By strong induction on rA + rB. The dominant case provides a matched pair
  -- (A 0, B 0) with GPE; subtracting it yields a reduced weighted-sum identity
  -- for the tail families indexed by Fin.succ, which inherit IsCanonicalFormBNT.
  -- The induction hypothesis closes the remaining cases.
  -- ═══════════════════════════════════════════════════════════════════════════════
  have hrA_pos : 0 < rA := Nat.pos_of_ne_zero hrA
  have hrB_pos : 0 < rB := Nat.pos_of_ne_zero hrB
  -- ── Helper: mpvOverlap → 0 implies mpvInner → 0 ──
  have tendsto_inner_zero : ∀ {D₁ D₂ : ℕ} (X : MPSTensor d D₁) (Y : MPSTensor d D₂),
      Tendsto (fun N => mpvOverlap (d := d) X Y N) atTop (nhds 0) →
      Tendsto (fun N => mpvInner (d := d) X Y N) atTop (nhds 0) := by
    intro D₁ D₂ X Y hOv
    have h' := hOv.star
    simpa [mpvOverlap_eq_star_mpvInner] using h'
  -- ── Helper: mpvOverlap → 1 implies mpvInner → 1 (self) ──
  have tendsto_inner_one : ∀ {D : ℕ} (X : MPSTensor d D),
      Tendsto (fun N => mpvOverlap (d := d) X X N) atTop (nhds 1) →
      Tendsto (fun N => mpvInner (d := d) X X N) atTop (nhds 1) := by
    intro D X hOv
    have h' := hOv.star
    simpa [mpvOverlap_eq_star_mpvInner] using h'
  -- ── Inner product identity from hSumState ──
  have inner_identity : ∀ {D : ℕ} (X : MPSTensor d D) (N : ℕ),
      ∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N =
        ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N := by
    intro D X N
    simp only [mpvInner]
    have h := congr_arg (fun v => @inner ℂ _ _ (mpvState (d := d) X N) v) (hSumState N)
    simp only [inner_sum, inner_smul_right] at h
    exact h
  -- ── Diagonal / off-diagonal inner product limits ──
  have hA_inner_diag : ∀ j : Fin rA,
      Tendsto (fun N => mpvInner (d := d) (A j) (A j) N) atTop (nhds 1) :=
    fun j => tendsto_inner_one (A j) (hA_self j)
  have hA_inner_off : ∀ i j : Fin rA, i ≠ j →
      Tendsto (fun N => mpvInner (d := d) (A i) (A j) N) atTop (nhds 0) :=
    fun i j hij => tendsto_inner_zero (A i) (A j) (hA_cross i j hij)
  have hB_inner_diag : ∀ k : Fin rB,
      Tendsto (fun N => mpvInner (d := d) (B k) (B k) N) atTop (nhds 1) :=
    fun k => tendsto_inner_one (B k) (hB_self k)
  have hB_inner_off : ∀ i j : Fin rB, i ≠ j →
      Tendsto (fun N => mpvInner (d := d) (B i) (B j) N) atTop (nhds 0) :=
    fun i j hij => tendsto_inner_zero (B i) (B j) (hB_cross i j hij)
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- Step A: Prove ‖μA 0‖ = ‖μB 0‖ (unconditional).
  -- If ‖μA 0‖ < ‖μB 0‖, take inner product of hSumState with B 0 and divide by
  -- (μB 0)^N. The A-side (all geometric → 0 × bounded) → 0, but the B-side
  -- (self-overlap → 1) → 1. Contradiction. Similarly for ‖μB 0‖ < ‖μA 0‖.
  -- ═══════════════════════════════════════════════════════════════════════════════
  have hμA_ne : μA ⟨0, hrA_pos⟩ ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero _
  have hμB_ne : μB ⟨0, hrB_pos⟩ ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero _
  -- ── Auxiliary: normalized inner product identity ──
  -- From inner_identity, dividing by c^N gives the normalized version.
  have normalized_identity :
      ∀ {D : ℕ} (X : MPSTensor d D) (c : ℂ) (hc : c ≠ 0) (N : ℕ),
      ∑ j : Fin rA, (μA j / c) ^ N * mpvInner (d := d) X (A j) N =
        ∑ k : Fin rB, (μB k / c) ^ N * mpvInner (d := d) X (B k) N := by
    intro D X c hc N
    have h := inner_identity X N
    have hcN : c ^ N ≠ 0 := pow_ne_zero N hc
    simp only [div_pow, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← Finset.sum_div]
    exact congr_arg (· / c ^ N) h
  -- ── Auxiliary: ‖μA j‖ ≤ ‖μA 0‖ and ‖μB k‖ ≤ ‖μB 0‖ (weight ordering) ──
  have hμA_le : ∀ j : Fin rA, ‖μA j‖ ≤ ‖μA ⟨0, hrA_pos⟩‖ := by
    intro j; exact hA.toIsCanonicalForm.mu_strict_anti.antitone
      (show (⟨0, hrA_pos⟩ : Fin rA) ≤ j from Fin.mk_le_mk.mpr (Nat.zero_le _))
  have hμB_le : ∀ k : Fin rB, ‖μB k‖ ≤ ‖μB ⟨0, hrB_pos⟩‖ := by
    intro k; exact hB.toIsCanonicalForm.mu_strict_anti.antitone
      (show (⟨0, hrB_pos⟩ : Fin rB) ≤ k from Fin.mk_le_mk.mpr (Nat.zero_le _))
  -- ── Auxiliary: bounded-norm × tendsto-zero → tendsto-zero ──
  -- If ‖c‖ ≤ 1 and f → 0, then c^N * f(N) → 0.
  have bounded_mul_tendsto_zero :
      ∀ (c : ℂ) (f : ℕ → ℂ), ‖c‖ ≤ 1 →
      Tendsto f atTop (nhds 0) →
      Tendsto (fun N => c ^ N * f N) atTop (nhds 0) := by
    intro c f hc hf
    have hfn : Tendsto (fun N => ‖f N‖) atTop (nhds 0) := by
      have := hf.norm; simp only [norm_zero] at this; exact this
    apply squeeze_zero_norm (fun N => ?_) hfn
    calc ‖c ^ N * f N‖ = ‖c ^ N‖ * ‖f N‖ := norm_mul _ _
      _ = ‖c‖ ^ N * ‖f N‖ := by rw [norm_pow]
      _ ≤ 1 * ‖f N‖ := mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) hc) (norm_nonneg _)
      _ = ‖f N‖ := one_mul _
  -- ── Auxiliary: geometric(< 1) × bounded → 0 ──
  -- If ‖c‖ < 1, then c^N * f(N) → 0 for any f with ‖f N‖ ≤ C.
  have geometric_mul_bounded_tendsto_zero :
      ∀ (c : ℂ) (f : ℕ → ℂ) (C : ℝ), ‖c‖ < 1 →
      (∀ N, ‖f N‖ ≤ C) →
      Tendsto (fun N => c ^ N * f N) atTop (nhds 0) := by
    intro c f C hc hbound
    have hgeom : Tendsto (fun N => ‖c‖ ^ N * C) atTop (nhds 0) := by
      have h1 : Tendsto (fun N => (‖c‖ : ℝ) ^ N) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rwa [Real.norm_of_nonneg (norm_nonneg c)])
      have h2 := h1.mul_const C
      simpa [zero_mul] using h2
    apply squeeze_zero_norm (fun N => ?_) hgeom
    calc ‖c ^ N * f N‖ = ‖c ^ N‖ * ‖f N‖ := norm_mul _ _
      _ ≤ ‖c ^ N‖ * C := mul_le_mul_of_nonneg_left (hbound N) (norm_nonneg _)
      _ = ‖c‖ ^ N * C := by rw [norm_pow]
  -- ── Auxiliary: geometric × mpvInner → 0 ──
  -- If ‖c‖ < 1 and both self-overlaps → 1, then c^N * mpvInner(X, Y, N) → 0.
  -- Proof: Cauchy-Schwarz gives |⟨X_N, Y_N⟩| ≤ ‖X_N‖ * ‖Y_N‖, and the norms
  -- are bounded (convergent sequences are bounded), so the inner product is bounded.
  -- Then geometric_mul_bounded_tendsto_zero closes the goal.
  have geometric_mul_inner_tendsto_zero :
      ∀ {D₁ D₂ : ℕ} (c : ℂ) (X : MPSTensor d D₁) (Y : MPSTensor d D₂), ‖c‖ < 1 →
      Tendsto (fun N => mpvOverlap (d := d) X X N) atTop (nhds 1) →
      Tendsto (fun N => mpvOverlap (d := d) Y Y N) atTop (nhds 1) →
      Tendsto (fun N => c ^ N * mpvInner (d := d) X Y N) atTop (nhds 0) := by
    intro D₁ D₂ c X Y hc hX hY
    -- Step 1: Self-inner products converge to 1.
    have hX_inner : Tendsto (fun N => mpvInner (d := d) X X N) atTop (nhds 1) :=
      tendsto_inner_one X hX
    have hY_inner : Tendsto (fun N => mpvInner (d := d) Y Y N) atTop (nhds 1) :=
      tendsto_inner_one Y hY
    -- Step 2: Convergent sequences are bounded; extract uniform norm bounds.
    obtain ⟨C_X, hC_X⟩ :=
      (Metric.isBounded_range_of_tendsto _ hX_inner).exists_norm_le
    obtain ⟨C_Y, hC_Y⟩ :=
      (Metric.isBounded_range_of_tendsto _ hY_inner).exists_norm_le
    have hXX_bdd : ∀ N, ‖mpvInner (d := d) X X N‖ ≤ C_X :=
      fun N => hC_X _ (Set.mem_range_self N)
    have hYY_bdd : ∀ N, ‖mpvInner (d := d) Y Y N‖ ≤ C_Y :=
      fun N => hC_Y _ (Set.mem_range_self N)
    -- Step 3: ‖mpvState X N‖² = ‖mpvInner X X N‖ (and analogously for Y).
    -- Since inner ℂ x x = ↑‖x‖² (inner_self_eq_norm_sq_to_K) and ‖↑r‖_ℂ = r for r ≥ 0.
    have hXX_sq : ∀ N, ‖mpvState (d := d) X N‖ ^ 2 = ‖mpvInner (d := d) X X N‖ := fun N => by
      have heq : mpvInner (d := d) X X N = ↑(‖mpvState (d := d) X N‖ ^ 2 : ℝ) := by
        unfold mpvInner
        rw [inner_self_eq_norm_sq_to_K]
        push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have hYY_sq : ∀ N, ‖mpvState (d := d) Y N‖ ^ 2 = ‖mpvInner (d := d) Y Y N‖ := fun N => by
      have heq : mpvInner (d := d) Y Y N = ↑(‖mpvState (d := d) Y N‖ ^ 2 : ℝ) := by
        unfold mpvInner
        rw [inner_self_eq_norm_sq_to_K]
        push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    -- Step 4: Cauchy-Schwarz + AM-GM gives ‖mpvInner X Y N‖ ≤ (C_X + C_Y) / 2.
    -- Then geometric_mul_bounded_tendsto_zero closes the goal.
    apply geometric_mul_bounded_tendsto_zero c _ ((C_X + C_Y) / 2) hc
    intro N
    have hx := norm_nonneg (mpvState (d := d) X N)
    have hy := norm_nonneg (mpvState (d := d) Y N)
    have h_cs : ‖mpvInner (d := d) X Y N‖ ≤
        ‖mpvState (d := d) X N‖ * ‖mpvState (d := d) Y N‖ := by
      unfold mpvInner; exact norm_inner_le_norm _ _
    calc ‖mpvInner (d := d) X Y N‖
        ≤ ‖mpvState (d := d) X N‖ * ‖mpvState (d := d) Y N‖ := h_cs
      _ ≤ (‖mpvState (d := d) X N‖ ^ 2 + ‖mpvState (d := d) Y N‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖mpvState (d := d) X N‖ - ‖mpvState (d := d) Y N‖)]
      _ = (‖mpvInner (d := d) X X N‖ + ‖mpvInner (d := d) Y Y N‖) / 2 := by
            rw [hXX_sq N, hYY_sq N]
      _ ≤ (C_X + C_Y) / 2 := by linarith [hXX_bdd N, hYY_bdd N]
  -- ── Auxiliary: sum → 1 for "self" direction ──
  -- If the j=j0 term → 1 and the cross terms → 0, the full sum → 1.
  -- This is used for both the A-LHS and B-RHS.
  have sum_tendsto_one_of_diag :
      ∀ {r : ℕ} {μ : Fin r → ℂ} {μ0 : ℂ} {hμ0 : μ0 ≠ 0}
        {j0 : Fin r} {g : Fin r → ℕ → ℂ},
        (μ j0 = μ0) →
        Tendsto (g j0) atTop (nhds 1) →
        (∀ j, j ≠ j0 → ‖μ j / μ0‖ < 1) →
        (∀ j, j ≠ j0 → Tendsto (g j) atTop (nhds 0)) →
        Tendsto (fun N => ∑ j : Fin r, (μ j / μ0) ^ N * g j N) atTop (nhds 1) := by
    intro r μ μ0 hμ0 j0 g hμj0 hdiag hratio hcross
    have hsplit : ∀ N, ∑ j, (μ j / μ0) ^ N * g j N =
        (μ j0 / μ0) ^ N * g j0 N +
        ∑ j ∈ Finset.univ.erase j0, (μ j / μ0) ^ N * g j N := by
      intro N; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    simp_rw [hsplit]
    have h1 : Tendsto (fun N => (μ j0 / μ0) ^ N * g j0 N) atTop (nhds 1) := by
      simp only [hμj0, div_self hμ0, one_pow, one_mul]; exact hdiag
    have h2 : Tendsto (fun N => ∑ j ∈ Finset.univ.erase j0,
        (μ j / μ0) ^ N * g j N) atTop (nhds (0 : ℂ)) := by
      have := tendsto_finset_sum (Finset.univ.erase j0)
        (fun (j : Fin r) (hj : j ∈ Finset.univ.erase j0) =>
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
            (hratio j (Finset.ne_of_mem_erase hj))).mul
          (hcross j (Finset.ne_of_mem_erase hj)))
      simpa using this
    convert h1.add h2 using 1; simp
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- Step A: Prove ‖μA 0‖ = ‖μB 0‖.
  -- If ‖μA 0‖ < ‖μB 0‖: use inner_identity with X = B 0, divide by (μB 0)^N.
  --   LHS: all |μA j / μB 0| < 1, so geometric × bounded → 0. LHS → 0.
  --   RHS → 1 (self-overlap → 1, cross-terms → 0 by geometric × → 0).
  --   Contradiction: 0 = 1.
  -- If ‖μA 0‖ > ‖μB 0‖: symmetric with X = A 0, divide by (μA 0)^N.
  -- ═══════════════════════════════════════════════════════════════════════════════
  have mu0_norm_eq : ‖μA ⟨0, hrA_pos⟩‖ = ‖μB ⟨0, hrB_pos⟩‖ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h_lt | h_gt
    · -- Case ‖μA 0‖ < ‖μB 0‖.
      -- inner_identity with X = B ⟨0, hrB_pos⟩, divided by (μB 0)^N.
      have h_eq := normalized_identity (B ⟨0, hrB_pos⟩) (μB ⟨0, hrB_pos⟩) hμB_ne
      -- LHS → 0: all A-ratios have norm < 1.
      have hLHS : Tendsto (fun N => ∑ j, (μA j / μB ⟨0, hrB_pos⟩) ^ N *
          mpvInner (d := d) (B ⟨0, hrB_pos⟩) (A j) N) atTop (nhds 0) := by
        have := tendsto_finset_sum (Finset.univ : Finset (Fin rA))
          (fun (j : Fin rA) _ => show Tendsto (fun N => (μA j / μB ⟨0, hrB_pos⟩) ^ N *
            mpvInner (d := d) (B ⟨0, hrB_pos⟩) (A j) N) atTop (nhds (0 : ℂ)) from ?_)
        · simpa using this
        -- Each term: geometric(< 1) × bounded → 0.
        have hratio : ‖μA j / μB ⟨0, hrB_pos⟩‖ < 1 := by
          rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
            (lt_of_le_of_lt (hμA_le j) h_lt)
        -- Use bounded_mul_tendsto_zero: ‖ratio‖ ≤ 1 (it's < 1) and
        -- inner is → 0... NO, inner is NOT → 0 in general.
        -- Use geometric_mul_bounded_tendsto_zero with Cauchy-Schwarz bound.
        -- ‖mpvInner X Y N‖ ≤ ‖mpvState X N‖ * ‖mpvState Y N‖ (Cauchy-Schwarz).
        -- Both norms converge → 1, so ∃ C, ∀ N, ‖inner‖ ≤ C.
        -- First establish a uniform norm bound on mpvState.
        exact geometric_mul_inner_tendsto_zero _ _ _ hratio (hB_self _) (hA_self j)
      -- RHS → 1: the ⟨0,_⟩ term → 1, cross terms → 0.
      have hRHS : Tendsto (fun N => ∑ k, (μB k / μB ⟨0, hrB_pos⟩) ^ N *
          mpvInner (d := d) (B ⟨0, hrB_pos⟩) (B k) N) atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := ⟨0, hrB_pos⟩) rfl (hB_inner_diag _)
          (fun k hk => by
            rw [norm_div]
            exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
              (hB.toIsCanonicalForm.mu_strict_anti (by
                simp only [Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                  intro h; exact hk (Fin.ext h)))))
          (fun k hk => hB_inner_off _ _ hk.symm)
      exact zero_ne_one (tendsto_nhds_unique (hLHS.congr (fun N => h_eq N)) hRHS)
    · -- Case ‖μA 0‖ > ‖μB 0‖: symmetric with X = A 0.
      have h_eq := normalized_identity (A ⟨0, hrA_pos⟩) (μA ⟨0, hrA_pos⟩) hμA_ne
      have hLHS : Tendsto (fun N => ∑ j, (μA j / μA ⟨0, hrA_pos⟩) ^ N *
          mpvInner (d := d) (A ⟨0, hrA_pos⟩) (A j) N) atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμA_ne) (j0 := ⟨0, hrA_pos⟩) rfl (hA_inner_diag _)
          (fun j hj => by
            rw [norm_div]
            exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
              (hA.toIsCanonicalForm.mu_strict_anti (by
                simp only [Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                  intro h; exact hj (Fin.ext h)))))
          (fun j hj => hA_inner_off _ _ hj.symm)
      have hRHS : Tendsto (fun N => ∑ k : Fin rB, (μB k / μA ⟨0, hrA_pos⟩) ^ N *
          mpvInner (d := d) (A ⟨0, hrA_pos⟩) (B k) N) atTop (nhds (0 : ℂ)) := by
        have hterm : ∀ k : Fin rB,
            Tendsto (fun N => (μB k / μA ⟨0, hrA_pos⟩) ^ N *
              mpvInner (d := d) (A ⟨0, hrA_pos⟩) (B k) N) atTop (nhds (0 : ℂ)) := by
          intro k
          have hratio : ‖μB k / μA ⟨0, hrA_pos⟩‖ < 1 := by
            rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
              (lt_of_le_of_lt (hμB_le k) h_gt)
          exact geometric_mul_inner_tendsto_zero _ _ _ hratio (hA_self _) (hB_self k)
        have := tendsto_finset_sum (Finset.univ : Finset (Fin rB))
          (fun (k : Fin rB) _ => hterm k)
        simpa using this
      exact one_ne_zero (tendsto_nhds_unique (hLHS.congr (fun N => h_eq N)) hRHS)
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- Steps B+C: Prove both directions via BNT linear independence.
  --
  -- Strategy: assume some A-block j₀ has ∀ k, overlap(A j₀, B k) → 0.
  -- From the B-direction dominant case, identify the unique A-match for B 0 and
  -- show it must be A 0 (norm argument). Then all B-blocks k map injectively
  -- (via the B→A matching) to A-blocks ≠ j₀. Via GPE, express each
  -- mpvState(B k, N) as a phase-multiple of the matched A-state.
  -- Substituting into the sum identity and applying A-BNT linear independence
  -- forces (μA j₀)^N = 0, contradicting μA j₀ ≠ 0.
  -- ═══════════════════════════════════════════════════════════════════════════════
  set a0 : Fin rA := ⟨0, hrA_pos⟩
  set b0 : Fin rB := ⟨0, hrB_pos⟩
  -- ── Helper: dominant case prover ──
  -- If ∀ k, overlap(A j₀, B k) → 0 AND j₀ is the dominant block, derive False.
  have dominant_A_contra :
      (∀ k, Tendsto (fun N => mpvOverlap (d := d) (A a0) (B k) N) atTop (nhds 0)) →
      False := by
    intro hall
    have hall_inner : ∀ k, Tendsto (fun N => mpvInner (d := d) (A a0) (B k) N)
        atTop (nhds 0) := fun k => tendsto_inner_zero _ _ (hall k)
    have h_eq := normalized_identity (A a0) (μA a0) hμA_ne
    have hRHS : Tendsto (fun N => ∑ k, (μB k / μA a0) ^ N *
        mpvInner (d := d) (A a0) (B k) N) atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rB))
        (fun (k : Fin rB) _ => show Tendsto _ atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]; exact (div_le_one (by positivity)).mpr
              (mu0_norm_eq ▸ hμB_le k)) (hall_inner k))
      simpa using this
    have hLHS : Tendsto (fun N => ∑ j, (μA j / μA a0) ^ N *
        mpvInner (d := d) (A a0) (A j) N) atTop (nhds 1) :=
      sum_tendsto_one_of_diag (hμ0 := hμA_ne) (j0 := a0) rfl (hA_inner_diag a0)
        (fun j hj => by
          rw [norm_div]
          exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
            (hA.toIsCanonicalForm.mu_strict_anti (by
              simp only [a0, Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                intro h; exact hj (Fin.ext h)))))
        (fun j hj => hA_inner_off a0 j hj.symm)
    exact zero_ne_one (tendsto_nhds_unique (hRHS.congr (fun N => (h_eq N).symm)) hLHS)
  have dominant_B_contra :
      (∀ j, Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N) atTop (nhds 0)) →
      False := by
    intro hall
    have hall_inner : ∀ j, Tendsto (fun N => mpvInner (d := d) (B b0) (A j) N)
        atTop (nhds 0) := by
      intro j
      have h1 := tendsto_inner_zero _ _ (hall j)
      have h2 : (fun N => mpvInner (d := d) (B b0) (A j) N) =
          (fun N => star (mpvInner (d := d) (A j) (B b0) N)) := by
        ext N; simp [mpvInner, inner_conj_symm]
      rw [h2]; simpa using h1.star
    have h_eq := normalized_identity (B b0) (μB b0) hμB_ne
    have hLHS : Tendsto (fun N => ∑ j, (μA j / μB b0) ^ N *
        mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rA))
        (fun (j : Fin rA) _ => show Tendsto _ atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]; exact (div_le_one (by positivity)).mpr
              (mu0_norm_eq ▸ hμA_le j)) (hall_inner j))
      simpa using this
    have hRHS : Tendsto (fun N => ∑ k, (μB k / μB b0) ^ N *
        mpvInner (d := d) (B b0) (B k) N) atTop (nhds 1) :=
      sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := b0) rfl (hB_inner_diag b0)
        (fun k hk => by
          rw [norm_div]
          exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
            (hB.toIsCanonicalForm.mu_strict_anti (by
              simp only [b0, Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                intro h; exact hk (Fin.ext h)))))
        (fun k hk => hB_inner_off b0 k hk.symm)
    exact zero_ne_one (tendsto_nhds_unique (hLHS.congr (fun N => h_eq N)) hRHS)
  -- ── Step B: Dominant cases (existence) ──
  have domA : ∃ k₀, ¬ Tendsto (fun N => mpvOverlap (d := d) (A a0) (B k₀) N)
      atTop (nhds 0) := by
    by_contra h; push_neg at h; exact dominant_A_contra h
  have domB : ∃ j₀, ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B b0) N)
      atTop (nhds 0) := by
    by_contra h; push_neg at h; exact dominant_B_contra h
  -- ── Step C: For each B-block, there is at most one A-match ──
  -- If two A-blocks both have non-decaying overlap with the same B-block,
  -- their cross-overlap has norm → 1, contradicting A-BNT.
  have hA_inj_local := hA.toHasInjectiveBlocks.block_injective
  have hB_inj_local := hB.toHasInjectiveBlocks.block_injective
  have hA_left_local := hA.toIsLeftCanonicalBlockFamily.leftCanonical
  have hB_left_local := hB.toIsLeftCanonicalBlockFamily.leftCanonical
  have unique_A_match : ∀ (k : Fin rB) (j₁ j₂ : Fin rA),
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₁) (B k) N) atTop (nhds 0) →
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₂) (B k) N) atTop (nhds 0) →
      j₁ = j₂ := by
    intro k j₁ j₂ h1 h2
    by_contra hne
    -- Both A j₁, A j₂ have non-decaying overlap with B k → GPE for both.
    have hdim1 : dimA j₁ = dimB k := by
      by_contra hd; exact h1 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j₁) (hB_inj_local k) (hA_left_local j₁) (hB_left_local k) hd)
    have hdim2 : dimA j₂ = dimB k := by
      by_contra hd; exact h2 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j₂) (hB_inj_local k) (hA_left_local j₂) (hB_left_local k) hd)
    have hgpe1 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim1) (A j₁)) (B k) := by
      by_contra h; exact h1 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim1 _ _ (hA_inj_local j₁) (hB_inj_local k) (hA_left_local j₁) (hB_left_local k) h)
    have hgpe2 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim2) (A j₂)) (B k) := by
      by_contra h; exact h2 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim2 _ _ (hA_inj_local j₂) (hB_inj_local k) (hA_left_local j₂) (hB_left_local k) h)
    -- Extract GPE data and MPV scaling.
    obtain ⟨X1, ζ1, _, hX1⟩ := hgpe1
    obtain ⟨X2, ζ2, _, hX2⟩ := hgpe2
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k) σ = ζ1 ^ N * mpv (A j₁) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X1 ζ1 hX1 N σ, mpv_cast_dim hdim1]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k) σ = ζ2 ^ N * mpv (A j₂) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X2 ζ2 hX2 N σ, mpv_cast_dim hdim2]
    -- Norm of phases = 1.
    have hBB_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k) (B k) N‖) atTop (nhds 1) := by
      convert (hB_self k).norm using 1; simp
    have hAA1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₁) N‖) atTop (nhds 1) := by
      convert (hA_self j₁).norm using 1; simp
    have hAA2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j₂) (A j₂) N‖) atTop (nhds 1) := by
      convert (hA_self j₂).norm using 1; simp
    have hζ1_norm : ‖ζ1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA1_norm hBB_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j₁) (B := B k) (ζ := ζ1) hmpv1)
    have hζ2_norm : ‖ζ2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA2_norm hBB_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j₂) (B := B k) (ζ := ζ2) hmpv2)
    -- Cross-overlap of A j₁ and A j₂ via B k.
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (A j₁) (A j₂) N =
        (starRingEnd ℂ ζ1 * ζ2) ^ N * mpvOverlap (d := d) (B k) (B k) N := by
      intro N; simp only [mpvOverlap]
      have hζ1_star_mul : starRingEnd ℂ ζ1 * ζ1 = 1 := by
        have := Complex.conj_mul' ζ1; rw [this, hζ1_norm, Complex.ofReal_one, one_pow]
      have hζ2_star_mul : starRingEnd ℂ ζ2 * ζ2 = 1 := by
        have := Complex.conj_mul' ζ2; rw [this, hζ2_norm, Complex.ofReal_one, one_pow]
      have hA1_eq : ∀ σ : Cfg d N, mpv (A j₁) σ =
          (starRingEnd ℂ ζ1) ^ N * (ζ1 ^ N * mpv (A j₁) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ1_star_mul, one_pow, one_mul]
      have hA2_eq : ∀ σ : Cfg d N, mpv (A j₂) σ =
          (starRingEnd ℂ ζ2) ^ N * (ζ2 ^ N * mpv (A j₂) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ2_star_mul, one_pow, one_mul]
      have hStep : ∀ σ : Cfg d N, mpv (A j₁) σ * star (mpv (A j₂) σ) =
          (starRingEnd ℂ ζ1) ^ N * mpv (B k) σ *
          star ((starRingEnd ℂ ζ2) ^ N * mpv (B k) σ) := by
        intro σ; rw [hA1_eq σ, ← hmpv1 N σ, hA2_eq σ, ← hmpv2 N σ]
      simp_rw [hStep]; simp only [star_mul, star_pow, RCLike.star_def, starRingEnd_self_apply]
      rw [show ((starRingEnd ℂ) ζ1 * ζ2) ^ N =
          (starRingEnd ℂ) ζ1 ^ N * ζ2 ^ N from mul_pow _ _ _]
      rw [Finset.mul_sum]; congr 1; ext σ; ring
    have hNormζ : ‖starRingEnd ℂ ζ1 * ζ2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hζ1_norm, hζ2_norm, mul_one]
    -- Cross-overlap norm → 1, contradicting BNT cross → 0.
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) =
          fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
            ‖mpvOverlap (d := d) (B k) (B k) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]; have : (fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
          ‖mpvOverlap (d := d) (B k) (B k) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (B k) (B k) N‖ := by
        ext N; rw [norm_pow, hNormζ, one_pow]
      rw [this]; simpa using hBB_norm
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) atTop (nhds 0) := by
      convert (hA_cross j₁ j₂ hne).norm using 1; simp
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- ── Similarly for B-side uniqueness ──
  have unique_B_match : ∀ (j : Fin rA) (k₁ k₂ : Fin rB),
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₁) N) atTop (nhds 0) →
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₂) N) atTop (nhds 0) →
      k₁ = k₂ := by
    intro j k₁ k₂ h1 h2
    by_contra hne
    have hdim1 : dimA j = dimB k₁ := by
      by_contra hd; exact h1 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j) (hB_inj_local k₁) (hA_left_local j) (hB_left_local k₁) hd)
    have hdim2 : dimA j = dimB k₂ := by
      by_contra hd; exact h2 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j) (hB_inj_local k₂) (hA_left_local j) (hB_left_local k₂) hd)
    have hgpe1 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim1) (A j)) (B k₁) := by
      by_contra h; exact h1 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim1 _ _ (hA_inj_local j) (hB_inj_local k₁) (hA_left_local j) (hB_left_local k₁) h)
    have hgpe2 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim2) (A j)) (B k₂) := by
      by_contra h; exact h2 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim2 _ _ (hA_inj_local j) (hB_inj_local k₂) (hA_left_local j) (hB_left_local k₂) h)
    obtain ⟨Y1, ω1, _, hY1⟩ := hgpe1
    obtain ⟨Y2, ω2, _, hY2⟩ := hgpe2
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k₁) σ = ω1 ^ N * mpv (A j) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y1 ω1 hY1 N σ, mpv_cast_dim hdim1]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k₂) σ = ω2 ^ N * mpv (A j) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y2 ω2 hY2 N σ, mpv_cast_dim hdim2]
    have hAA_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j) (A j) N‖) atTop (nhds 1) := by
      convert (hA_self j).norm using 1; simp
    have hBB1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₁) N‖) atTop (nhds 1) := by
      convert (hB_self k₁).norm using 1; simp
    have hBB2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₂) (B k₂) N‖) atTop (nhds 1) := by
      convert (hB_self k₂).norm using 1; simp
    have hω1_norm : ‖ω1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB1_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j) (B := B k₁) (ζ := ω1) hmpv1)
    have hω2_norm : ‖ω2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB2_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j) (B := B k₂) (ζ := ω2) hmpv2)
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (B k₁) (B k₂) N =
        (ω1 * starRingEnd ℂ ω2) ^ N * mpvOverlap (d := d) (A j) (A j) N := by
      intro N; simp only [mpvOverlap]
      simp_rw [hmpv1 N, hmpv2 N, star_mul, star_pow]
      simp_rw [show star ω2 = starRingEnd ℂ ω2 from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ω1 ^ N * mpv (A j) x * (star (mpv (A j) x) * (starRingEnd ℂ ω2) ^ N) =
        ω1 ^ N * (starRingEnd ℂ ω2) ^ N * (mpv (A j) x * star (mpv (A j) x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    have hNormω : ‖ω1 * starRingEnd ℂ ω2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hω1_norm, hω2_norm, mul_one]
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₂) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₂) N‖) =
          fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
            ‖mpvOverlap (d := d) (A j) (A j) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]; have : (fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
          ‖mpvOverlap (d := d) (A j) (A j) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (A j) (A j) N‖ := by
        ext N; rw [norm_pow, hNormω, one_pow]
      rw [this]; simpa using hAA_norm
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₂) N‖) atTop (nhds 0) := by
      convert (hB_cross k₁ k₂ hne).norm using 1; simp
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- ── Step D: For each B-block, choose its unique A-match ──
  -- From domB, B b0 has a match. For other B-blocks k, if ∀ j,
  -- overlap(A j, B k) → 0, that gives the B-direction dominant contradiction
  -- (same argument as dominant_B_contra but with B k in place of B b0).
  -- Actually, we use domB only for b0; for other B-blocks, the existence
  -- of an A-match will follow from the same dominant-weight argument.
  -- However, we only NEED the match for b0 for the main argument.
  --
  -- Key claim: the A-match for B b0 must be A a0.
  have match_B0_is_A0 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A a0) (B b0) N)
      atTop (nhds 0) := by
    obtain ⟨j₁, hj₁⟩ := domB
    -- j₁ has non-decaying overlap with B b0.
    -- If j₁ = a0, done. Otherwise, show j₁ = a0 by norm argument.
    by_cases hj1 : j₁ = a0
    · subst hj1; exact hj₁
    · -- j₁ ≠ a0 means |μA j₁| < |μA a0|.
      -- From GPE(A j₁, B b0): extract phase ω and show |μA j₁| = |μA a0| → ⊥.
      -- The normalized identity with X = B b0, c = μB b0 gives:
      --   LHS (A-side) ≈ (μA j₁ * star(ω) / μB b0)^N → ? and RHS (B-side) → 1.
      -- Since |μA j₁| < |μA a0| = |μB b0|, the ratio < 1, LHS → 0 ≠ 1.
      exfalso
      -- Show uniqueness: j₁ is the only A-match for B b0.
      have huniq : ∀ j, j ≠ j₁ →
          Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N) atTop (nhds 0) :=
        fun j hj => by
          by_contra hnd
          exact hj (unique_A_match b0 j j₁ hnd hj₁)
      -- Extract GPE data.
      have hdim1 : dimA j₁ = dimB b0 := by
        by_contra hd; exact hj₁ (mpvOverlap_tendsto_zero_of_dim_ne _ _
          (hA_inj_local j₁) (hB_inj_local b0) (hA_left_local j₁) (hB_left_local b0) hd)
      have hgpe1 : GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim1) (A j₁)) (B b0) := by
        by_contra h; exact hj₁ (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
          hdim1 _ _ (hA_inj_local j₁) (hB_inj_local b0)
          (hA_left_local j₁) (hB_left_local b0) h)
      obtain ⟨X, ω, _, hX⟩ := hgpe1
      have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (B b0) σ = ω ^ N * mpv (A j₁) σ := fun N σ => by
        rw [mpv_eq_pow_mul_of_gaugePhase _ _ X ω hX N σ, mpv_cast_dim hdim1]
      have hBB_norm :
          Tendsto (fun N => ‖mpvOverlap (d := d) (B b0) (B b0) N‖) atTop (nhds 1) := by
        convert (hB_self b0).norm using 1; simp
      have hAA_norm :
          Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₁) N‖) atTop (nhds 1) := by
        convert (hA_self j₁).norm using 1; simp
      have hω_norm : ‖ω‖ = 1 :=
        norm_eq_one_of_selfOverlap_scale hAA_norm hBB_norm
          (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j₁) (B := B b0) (ζ := ω) hmpv)
      -- mpvInner(B b0, A j₁, N) = star(ω)^N * mpvInner(A j₁, A j₁, N) → star(ω)^N.
      have hInner_j1 : ∀ N, mpvInner (d := d) (B b0) (A j₁) N =
          (starRingEnd ℂ ω) ^ N * mpvInner (d := d) (A j₁) (A j₁) N := by
        intro N
        have hstate : mpvState (d := d) (B b0) N = ω ^ N • mpvState (d := d) (A j₁) N := by
          rw [PiLp.ext_iff]; intro σ
          simp only [PiLp.smul_apply, smul_eq_mul, mpvState_apply]
          exact hmpv N σ
        simp only [mpvInner, hstate, inner_smul_left, map_pow]
      -- For j ≠ j₁: mpvInner(B b0, A j, N) → 0.
      have hInner_other : ∀ j, j ≠ j₁ →
          Tendsto (fun N => mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
        intro j hj
        have h1 := tendsto_inner_zero _ _ (huniq j hj)
        have h2 : (fun N => mpvInner (d := d) (B b0) (A j) N) =
            (fun N => star (mpvInner (d := d) (A j) (B b0) N)) := by
          ext N; simp [mpvInner, inner_conj_symm]
        rw [h2]; simpa using h1.star
      -- Normalized identity with X = B b0, c = μB b0.
      have h_eq := normalized_identity (B b0) (μB b0) hμB_ne
      -- RHS → 1 (B-self-overlap dominates).
      have hRHS_one : Tendsto (fun N => ∑ k, (μB k / μB b0) ^ N *
          mpvInner (d := d) (B b0) (B k) N) atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := b0) rfl (hB_inner_diag b0)
          (fun k hk => by
            rw [norm_div]
            exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
              (hB.toIsCanonicalForm.mu_strict_anti (by
                simp only [b0, Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                  intro h; exact hk (Fin.ext h)))))
          (fun k hk => hB_inner_off b0 k hk.symm)
      -- LHS: isolate the j₁ term.
      -- For j = j₁: (μA j₁ / μB b0)^N * star(ω)^N * (1 + o(1)).
      -- For j ≠ j₁: bounded * o(1) → 0.
      -- So LHS → ((μA j₁ * star(ω)) / μB b0)^N.
      -- Since |μA j₁| < |μA a0| = |μB b0| (j₁ ≠ a0, strict ordering), the ratio < 1.
      -- So LHS → 0 ≠ 1 = RHS. Contradiction.
      have hRatio_lt : ‖μA j₁ / μB b0‖ < 1 := by
        rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
          (mu0_norm_eq ▸ hA.toIsCanonicalForm.mu_strict_anti (by
            simp only [a0, Fin.lt_def]; exact Nat.pos_of_ne_zero
              (fun h => hj1 (Fin.ext h))))
      have hLHS_zero : Tendsto (fun N => ∑ j, (μA j / μB b0) ^ N *
          mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
        -- Split into j = j₁ and j ≠ j₁.
        have hsplit : ∀ N, ∑ j, (μA j / μB b0) ^ N * mpvInner (d := d) (B b0) (A j) N =
            (μA j₁ / μB b0) ^ N * mpvInner (d := d) (B b0) (A j₁) N +
            ∑ j ∈ Finset.univ.erase j₁,
              (μA j / μB b0) ^ N * mpvInner (d := d) (B b0) (A j) N := by
          intro N; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₁)]
        simp_rw [hsplit]
        -- The j₁ term: geometric × bounded → 0.
        have h_j1_term : Tendsto (fun N =>
            (μA j₁ / μB b0) ^ N * mpvInner (d := d) (B b0) (A j₁) N) atTop (nhds 0) :=
          geometric_mul_inner_tendsto_zero _ _ _ hRatio_lt (hB_self b0) (hA_self j₁)
        -- The rest: bounded × → 0 → 0.
        have h_rest : Tendsto (fun N => ∑ j ∈ Finset.univ.erase j₁,
            (μA j / μB b0) ^ N * mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
          have := tendsto_finset_sum (Finset.univ.erase j₁)
            (fun (j : Fin rA) (hj : j ∈ Finset.univ.erase j₁) =>
              show Tendsto _ atTop (nhds (0 : ℂ)) from
              bounded_mul_tendsto_zero _ _ (by
                rw [norm_div]; exact (div_le_one (by positivity)).mpr
                  (mu0_norm_eq ▸ hμA_le j))
              (hInner_other j (Finset.ne_of_mem_erase hj)))
          simpa using this
        convert h_j1_term.add h_rest using 1; simp
      exact zero_ne_one (tendsto_nhds_unique
        (hLHS_zero.congr (fun N => h_eq N)) hRHS_one)
  -- ── Similarly: A a0's match on the B-side is B b0 ──
  have match_A0_is_B0 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A a0) (B b0) N)
      atTop (nhds 0) := match_B0_is_A0
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- Step E: Extract GPE for the dominant match and derive the tail identity.
  --
  -- The dominant match A a0 ↔ B b0 gives gauge-phase equivalence with phase ζ.
  -- From the normalized identity, μA a0 = μB b0 * ζ. Subtracting the dominant
  -- terms from hSumState gives the tail identity:
  --   ∑_{j≠a0} (μA j)^N • v_j = ∑_{k≠b0} (μB k)^N • w_k
  --
  -- For non-dominant blocks (j₀ ≠ a0 or k₀ ≠ b0), the proof proceeds by strong
  -- induction on rA + rB:
  -- • If the opposite tail is empty (rB = 1 for A-direction, rA = 1 for B-direction),
  --   the tail identity + BNT linear independence gives a direct contradiction.
  -- • Otherwise, apply the lemma recursively to the tail families (which inherit
  --   IsCanonicalFormBNT) with strictly smaller rA + rB.
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- ── Extract GPE for the dominant match A a0 ↔ B b0 ──
  have hdim_dom : dimA a0 = dimB b0 := by
    by_contra hd
    exact match_A0_is_B0 (mpvOverlap_tendsto_zero_of_dim_ne _ _
      (hA_inj_local a0) (hB_inj_local b0) (hA_left_local a0) (hB_left_local b0) hd)
  have hgpe_dom : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim_dom) (A a0)) (B b0) := by
    by_contra h
    exact match_A0_is_B0 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      hdim_dom _ _ (hA_inj_local a0) (hB_inj_local b0)
      (hA_left_local a0) (hB_left_local b0) h)
  obtain ⟨X_dom, ζ, hX_dom_inv, hX_dom_eq⟩ := hgpe_dom
  have hmpv_dom : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B b0) σ = ζ ^ N * mpv (A a0) σ := fun N σ => by
    rw [mpv_eq_pow_mul_of_gaugePhase _ _ X_dom ζ hX_dom_eq N σ, mpv_cast_dim hdim_dom]
  have hstate_dom : ∀ N,
      mpvState (d := d) (B b0) N = ζ ^ N • mpvState (d := d) (A a0) N := by
    intro N; ext σ
    simp only [PiLp.smul_apply, smul_eq_mul, mpvState_apply, hmpv_dom]
  have hζ_norm : ‖ζ‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale
      (by convert (hA_self a0).norm using 1; simp)
      (by convert (hB_self b0).norm using 1; simp)
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A a0) (B := B b0) (ζ := ζ) hmpv_dom)
  -- ── Show μA a0 = μB b0 * ζ ──
  -- From the normalized identity with X = A a0, c = μA a0:
  --   LHS → 1, and RHS has b0-term = (μB b0 * ζ / μA a0)^N * inner(A a0, A a0, N).
  -- Setting λ = μB b0 * ζ / μA a0 with |λ| = 1, we show λ^N → 1, hence λ = 1.
  have hμ_eq : μA a0 = μB b0 * ζ := by
    suffices h : μB b0 * ζ / μA a0 = 1 by
      have h' : μB b0 * ζ = μA a0 := by rwa [div_eq_iff hμA_ne, one_mul] at h
      exact h'.symm
    set ratio := μB b0 * ζ / μA a0
    have hratio_norm : ‖ratio‖ = 1 := by
      simp only [ratio, norm_div, norm_mul, hζ_norm, mul_one, mu0_norm_eq]
      exact div_self (ne_of_gt (norm_pos_iff.mpr hμB_ne))
    -- mpvInner(A a0, B b0, N) = ζ^N * mpvInner(A a0, A a0, N).
    have hInner_b0 : ∀ N, mpvInner (d := d) (A a0) (B b0) N =
        ζ ^ N * mpvInner (d := d) (A a0) (A a0) N := by
      intro N; simp only [mpvInner, hstate_dom, inner_smul_right]
    -- Show ratio^N * mpvInner(A a0, A a0, N) → 1 from the normalized identity.
    have h_prod : Tendsto (fun N => ratio ^ N * mpvInner (d := d) (A a0) (A a0) N)
        atTop (nhds 1) := by
      -- The normalized identity gives LHS = RHS for each N.
      have h_ni := normalized_identity (A a0) (μA a0) hμA_ne
      -- LHS → 1.
      have hLHS : Tendsto (fun N => ∑ j, (μA j / μA a0) ^ N *
          mpvInner (d := d) (A a0) (A j) N) atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμA_ne) (j0 := a0) rfl (hA_inner_diag a0)
          (fun j hj => by
            rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
              (hA.toIsCanonicalForm.mu_strict_anti (by
                simp only [a0, Fin.lt_def]; exact Nat.pos_of_ne_zero
                  (fun h => hj (Fin.ext h)))))
          (fun j hj => hA_inner_off a0 j hj.symm)
      -- RHS: split into b0-term and rest.
      have hsplit : ∀ N, ∑ k, (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N =
          ratio ^ N * mpvInner (d := d) (A a0) (A a0) N +
          ∑ k ∈ Finset.univ.erase b0,
            (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N := by
        intro N
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b0)]
        congr 1
        simp only [hInner_b0, ratio, div_mul_eq_mul_div, mul_pow, div_pow]
        ring
      -- The rest → 0.
      have h_rest : Tendsto (fun N => ∑ k ∈ Finset.univ.erase b0,
          (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N) atTop (nhds 0) := by
        have := tendsto_finset_sum (Finset.univ.erase b0)
          (fun (k : Fin rB) (hk : k ∈ Finset.univ.erase b0) =>
            show Tendsto _ atTop (nhds (0 : ℂ)) from
            geometric_mul_inner_tendsto_zero _ _ _ (by
              rw [norm_div]
              exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
                (lt_of_lt_of_eq (hB.toIsCanonicalForm.mu_strict_anti
                  (show b0 < k from Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero
                    (fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)))))
                  mu0_norm_eq.symm))
              (hA_self a0) (hB_self k))
        simpa using this
      -- Combine: RHS = ratio^N * inner + rest → 1 (since LHS = RHS and LHS → 1).
      -- Therefore ratio^N * inner → 1 - 0 = 1.
      have hRHS_eq : ∀ N,
          (∑ k, (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N) -
          (∑ k ∈ Finset.univ.erase b0,
            (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N) =
          ratio ^ N * mpvInner (d := d) (A a0) (A a0) N := by
        intro N; rw [hsplit]; ring
      have h_sub := ((hLHS.congr (fun N => h_ni N)).sub h_rest).congr hRHS_eq
      rwa [show (1 : ℂ) - 0 = 1 from by ring] at h_sub
    -- Show ratio^N → 1 from h_prod and mpvInner → 1.
    have h_ratio_tendsto : Tendsto (fun N => ratio ^ N) atTop (nhds 1) := by
      -- ratio^N = (ratio^N * inner) - ratio^N * (inner - 1)
      -- First part → 1, second part → 0 (bounded × → 0).
      have h_err : Tendsto (fun N => ratio ^ N *
          (mpvInner (d := d) (A a0) (A a0) N - 1)) atTop (nhds 0) :=
        bounded_mul_tendsto_zero ratio _ (by rw [hratio_norm])
          (show Tendsto (fun N => mpvInner (d := d) (A a0) (A a0) N - 1) atTop (nhds 0) by
            have := (hA_inner_diag a0).sub (tendsto_const_nhds (x := (1 : ℂ)))
            simp only [sub_self] at this; exact this)
      have h_decomp : ∀ N, ratio ^ N * mpvInner (d := d) (A a0) (A a0) N -
          ratio ^ N * (mpvInner (d := d) (A a0) (A a0) N - 1) = ratio ^ N := by
        intro N; ring
      have h_sub := h_prod.sub h_err
      rw [show (1 : ℂ) - 0 = 1 from by ring] at h_sub
      exact h_sub.congr h_decomp
    -- ratio = 1 from ratio^N → 1 (shift argument: ratio * 1 = 1).
    have h_shift : Tendsto (fun N => ratio ^ (N + 1)) atTop (nhds 1) :=
      h_ratio_tendsto.comp (tendsto_add_atTop_nat 1)
    have h_mul : Tendsto (fun N => ratio * ratio ^ N) atTop (nhds (ratio * 1)) :=
      tendsto_const_nhds.mul h_ratio_tendsto
    have h_eq_fun : (fun N => ratio ^ (N + 1)) = (fun N => ratio * ratio ^ N) := by
      ext N; rw [pow_succ, mul_comm]
    have := tendsto_nhds_unique (h_eq_fun ▸ h_shift) h_mul
    simpa using this.symm
  -- ── Derive the tail identity ──
  -- Splitting hSumState and cancelling the dominant terms (which are equal):
  --   ∑_{j≠a0} (μA j)^N • v_j = ∑_{k≠b0} (μB k)^N • w_k
  have hTailState : ∀ N,
      ∑ j ∈ Finset.univ.erase a0, μA j ^ N • (A j).mpvState N =
      ∑ k ∈ Finset.univ.erase b0, μB k ^ N • (B k).mpvState N := by
    intro N
    have hN := hSumState N
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ b0)] at hN
    have hdom : μA a0 ^ N • (A a0).mpvState N =
        μB b0 ^ N • (B b0).mpvState N := by
      rw [hstate_dom, smul_smul, ← mul_pow, ← hμ_eq]
    rw [hdom] at hN
    exact add_left_cancel hN
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- Step F: Non-dominant blocks — strong induction on rA + rB.
  --
  -- For j₀ ≠ a0: from the tail identity and hall (all B-overlaps of A j₀ → 0),
  -- • If rB = 1: the B-tail is empty, so ∑_{j≠a0} (μA j)^N • v_j = 0.
  --   BNT linear independence forces (μA j₀)^N = 0, contradicting μA j₀ ≠ 0.
  -- • If rB ≥ 2: apply the lemma recursively to the tail families
  --   (with rA-1 + rB-1 < rA + rB) to get a B-match for j₀ in the tail,
  --   contradicting hall.
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- ── Helper: embed tail index into original index ──
  -- For j : Fin (rA - 1), succA j : Fin rA is the (j+1)-th element.
  let succA : Fin (rA - 1) → Fin rA := fun j => ⟨j.val + 1, by omega⟩
  let succB : Fin (rB - 1) → Fin rB := fun k => ⟨k.val + 1, by omega⟩
  have succA_ne_a0 : ∀ j, succA j ≠ a0 := fun j => by simp [succA, a0]
  have succB_ne_b0 : ∀ k, succB k ≠ b0 := fun k => by simp [succB, b0]
  have succA_inj : Function.Injective succA := fun j₁ j₂ h => by
    simp [succA, Fin.ext_iff] at h; exact Fin.ext (by omega)
  have succB_inj : Function.Injective succB := fun k₁ k₂ h => by
    simp [succB, Fin.ext_iff] at h; exact Fin.ext (by omega)
  -- ── Helper: reindex Finset sums from erase to Fin (r - 1) ──
  have hSumA_reindex : ∀ N,
      ∑ j ∈ Finset.univ.erase a0, μA j ^ N • (A j).mpvState N =
      ∑ j : Fin (rA - 1), μA (succA j) ^ N • (A (succA j)).mpvState N := by
    intro N
    have h_eq : Finset.univ.erase a0 = (Finset.univ : Finset (Fin (rA - 1))).image succA := by
      ext x; constructor
      · intro hx
        rw [Finset.mem_erase] at hx
        have hx_ne : x ≠ a0 := hx.1
        have hx_pos : 0 < x.val := by
          by_contra h; push_neg at h; exact hx_ne (Fin.ext (by omega))
        exact Finset.mem_image.mpr ⟨⟨x.val - 1, by omega⟩, Finset.mem_univ _,
          Fin.ext (by simp [succA]; omega)⟩
      · intro hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_erase.mpr ⟨succA_ne_a0 j, Finset.mem_univ _⟩
    rw [h_eq, Finset.sum_image (fun j _ k _ h => succA_inj h)]
  have hSumB_reindex : ∀ N,
      ∑ k ∈ Finset.univ.erase b0, μB k ^ N • (B k).mpvState N =
      ∑ k : Fin (rB - 1), μB (succB k) ^ N • (B (succB k)).mpvState N := by
    intro N
    have h_eq : Finset.univ.erase b0 = (Finset.univ : Finset (Fin (rB - 1))).image succB := by
      ext x; constructor
      · intro hx
        rw [Finset.mem_erase] at hx
        have hx_ne : x ≠ b0 := hx.1
        have hx_pos : 0 < x.val := by
          by_contra h; push_neg at h; exact hx_ne (Fin.ext (by omega))
        exact Finset.mem_image.mpr ⟨⟨x.val - 1, by omega⟩, Finset.mem_univ _,
          Fin.ext (by simp [succB]; omega)⟩
      · intro hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_erase.mpr ⟨succB_ne_b0 k, Finset.mem_univ _⟩
    rw [h_eq, Finset.sum_image (fun k _ l _ h => succB_inj h)]
  -- ── Reindexed tail identity ──
  have hTailReindex : ∀ N,
      ∑ j : Fin (rA - 1), μA (succA j) ^ N • (A (succA j)).mpvState N =
      ∑ k : Fin (rB - 1), μB (succB k) ^ N • (B (succB k)).mpvState N := by
    intro N; rw [← hSumA_reindex, ← hSumB_reindex]; exact hTailState N
  -- ── Tail succA/succB are strictly monotone ──
  have succA_strictMono : StrictMono succA := fun a b h => by
    simp only [succA, Fin.mk_lt_mk]; omega
  have succB_strictMono : StrictMono succB := fun a b h => by
    simp only [succB, Fin.mk_lt_mk]; omega
  -- ── Helper: derive matching contradiction from tail identity ──
  -- This helper derives False from the assumption that all overlaps of a
  -- non-dominant block with the opposite family tend to zero.
  -- It handles both the "empty tail" case (direct LI argument) and
  -- the "nonempty tail" case (recursive call).
  -- We prove both directions simultaneously.
  refine ⟨fun j₀ => ?_, fun k₀ => ?_⟩
  -- ── A-direction: ∃ k₀, ¬ overlap(A j₀, B k₀) → 0 ──
  · by_contra hall; push_neg at hall
    have hj0_ne : j₀ ≠ a0 := by
      intro h; subst h; exact match_A0_is_B0 (hall b0)
    -- j₀ is in the A-tail: find its preimage under succA.
    have hj0_pos : 0 < j₀.val := Nat.pos_of_ne_zero (fun h => hj0_ne (Fin.ext h))
    set j₀' : Fin (rA - 1) := ⟨j₀.val - 1, by omega⟩ with hj0'_def
    have hj0_eq : succA j₀' = j₀ := Fin.ext (by simp [succA, hj0'_def]; omega)
    -- Case split on rB.
    by_cases hrB1 : rB = 1
    · -- rB = 1: the B-tail is empty. The tail identity gives ∑_{j≠a0} ... = 0.
      -- BNT linear independence forces all coefficients = 0, contradicting μA j₀ ≠ 0.
      have hTailZero : ∀ N,
          ∑ j ∈ Finset.univ.erase a0, μA j ^ N • (A j).mpvState N = 0 := by
        intro N; rw [hTailState N, hSumB_reindex]
        subst hrB1; simp [Finset.univ_eq_empty]
      obtain ⟨N₀, hLI⟩ := hA.isBNT.eventually_li
      specialize hLI (N₀ + 1) (by omega)
      rw [Fintype.linearIndependent_iff] at hLI
      specialize hLI (fun j => if j = a0 then 0 else μA j ^ (N₀ + 1))
      have hzero : ∑ j : Fin rA,
          (if j = a0 then 0 else μA j ^ (N₀ + 1)) •
            (A j).mpvState (N₀ + 1) = 0 := by
        have h := hTailZero (N₀ + 1)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
        simp only [ite_true, zero_smul, zero_add]
        rw [show ∑ x ∈ Finset.univ.erase a0,
            (if x = a0 then (0 : ℂ) else μA x ^ (N₀ + 1)) • (A x).mpvState (N₀ + 1) =
            ∑ x ∈ Finset.univ.erase a0, μA x ^ (N₀ + 1) • (A x).mpvState (N₀ + 1) from
          Finset.sum_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])]
        exact h
      have h_coeff := hLI hzero j₀
      simp only [hj0_ne, ite_false] at h_coeff
      exact pow_ne_zero _ (hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero j₀) h_coeff
    · -- rB ≥ 2: apply the lemma recursively to the tail families.
      have hrB_ge2 : 2 ≤ rB := by omega
      -- ── Tail SameMPV₂ ──
      have hEqual_tail : SameMPV₂
          (toTensorFromBlocks (d := d) (μ := μA ∘ succA) (fun j => A (succA j)))
          (toTensorFromBlocks (d := d) (μ := μB ∘ succB) (fun k => B (succB k))) := by
        intro N σ
        have hA_eq := mpv_toTensorFromBlocks_eq_sum (μA ∘ succA) (fun j => A (succA j)) σ
        have hB_eq := mpv_toTensorFromBlocks_eq_sum (μB ∘ succB) (fun k => B (succB k)) σ
        simp only [Function.comp, smul_eq_mul] at hA_eq hB_eq
        rw [hA_eq, hB_eq]
        -- Extract pointwise from the reindexed tail state identity.
        have h := hTailReindex N
        have h_pw := PiLp.ext_iff.mp h σ
        -- h_pw : (...).ofLp σ = (...).ofLp σ
        -- Unfold to get the scalar identity.
        change (∑ j, μA (succA j) ^ N • (A (succA j)).mpvState N).1 σ =
          (∑ k, μB (succB k) ^ N • (B (succB k)).mpvState N).1 σ at h_pw
        simp only [WithLp.IsEquiv.piLp_sum, WithLp.IsEquiv.piLp_smul, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, mpvState_apply] at h_pw
        exact h_pw
      -- ── Tail hSumState ──
      have hSumState_tail : ∀ N,
          ∑ j : Fin (rA - 1), (μA (succA j)) ^ N • (A (succA j)).mpvState N =
          ∑ k : Fin (rB - 1), (μB (succB k)) ^ N • (B (succB k)).mpvState N :=
        hTailReindex
      -- ── Tail IsCanonicalFormBNT for A ──
      have hA_tail : IsCanonicalFormBNT (μA ∘ succA) (fun j => A (succA j)) :=
        IsCanonicalFormBNT.ofSeparatedData
          (HasInjectiveBlocks.ofForall (fun k => hA_inj_local (succA k)))
          (IsLeftCanonicalBlockFamily.ofForall (fun k => hA_left_local (succA k)))
          ⟨hA.toIsCanonicalForm.mu_strict_anti.comp_strictMono succA_strictMono,
           fun k => hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero (succA k)⟩
          (HasNormalizedSelfOverlap.ofForall (fun k => hA_self (succA k)))
          (fun j k hjk hdim => hA.blocks_not_equiv (succA j) (succA k)
            (fun h => hjk (succA_inj h)) hdim)
      -- ── Tail IsCanonicalFormBNT for B ──
      have hB_tail : IsCanonicalFormBNT (μB ∘ succB) (fun k => B (succB k)) :=
        IsCanonicalFormBNT.ofSeparatedData
          (HasInjectiveBlocks.ofForall (fun k => hB_inj_local (succB k)))
          (IsLeftCanonicalBlockFamily.ofForall (fun k => hB_left_local (succB k)))
          ⟨hB.toIsCanonicalForm.mu_strict_anti.comp_strictMono succB_strictMono,
           fun k => hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero (succB k)⟩
          (HasNormalizedSelfOverlap.ofForall (fun k => hB_self (succB k)))
          (fun j k hjk hdim => hB.blocks_not_equiv (succB j) (succB k)
            (fun h => hjk (succB_inj h)) hdim)
      -- ── Apply the lemma recursively ──
      have IH := exists_nondecaying_overlap_of_sameMPV₂_CFBNT
        (fun j => A (succA j)) (fun k => B (succB k))
        hA_tail hB_tail hEqual_tail
        (by omega) (by omega)
        hSumState_tail
        (fun k => hA_self (succA k))
        (fun k => hB_self (succB k))
        (fun j k hjk => hA_cross (succA j) (succA k) (fun h => hjk (succA_inj h)))
        (fun j k hjk => hB_cross (succB j) (succB k) (fun h => hjk (succB_inj h)))
      -- IH.1 gives: ∀ j', ∃ k', overlap(A (succA j'), B (succB k')) ↛ 0.
      obtain ⟨k', hk'⟩ := IH.1 j₀'
      -- hk' says overlap(A (succA j₀'), B (succB k')) doesn't → 0.
      -- But succA j₀' = j₀ (from hj0_eq), so this is overlap(A j₀, B (succB k')).
      -- hall says it → 0. Contradiction.
      apply hk'; show Tendsto (fun N => mpvOverlap (d := d)
        (A (succA j₀')) (B (succB k')) N) atTop (nhds 0)
      rw [hj0_eq]; exact hall (succB k')
  -- ── B-direction: ∃ j₀, ¬ overlap(A j₀, B k₀) → 0 ──
  · by_contra hall; push_neg at hall
    have hk0_ne : k₀ ≠ b0 := by
      intro h; subst h; exact match_B0_is_A0 (hall a0)
    -- k₀ is in the B-tail: find its preimage under succB.
    have hk0_pos : 0 < k₀.val := Nat.pos_of_ne_zero (fun h => hk0_ne (Fin.ext h))
    set k₀' : Fin (rB - 1) := ⟨k₀.val - 1, by omega⟩ with hk0'_def
    have hk0_eq : succB k₀' = k₀ := Fin.ext (by simp [succB, hk0'_def]; omega)
    -- Case split on rA.
    by_cases hrA1 : rA = 1
    · -- rA = 1: the A-tail is empty. The tail identity gives 0 = ∑_{k≠b0} ... .
      -- BNT linear independence forces all coefficients = 0, contradicting μB k₀ ≠ 0.
      have hTailZero : ∀ N,
          ∑ k ∈ Finset.univ.erase b0, μB k ^ N • (B k).mpvState N = 0 := by
        intro N; rw [← hTailState N, hSumA_reindex]
        subst hrA1; simp [Finset.univ_eq_empty]
      obtain ⟨N₀, hLI⟩ := hB.isBNT.eventually_li
      specialize hLI (N₀ + 1) (by omega)
      rw [Fintype.linearIndependent_iff] at hLI
      specialize hLI (fun k => if k = b0 then 0 else μB k ^ (N₀ + 1))
      have hzero : ∑ k : Fin rB,
          (if k = b0 then 0 else μB k ^ (N₀ + 1)) •
            (B k).mpvState (N₀ + 1) = 0 := by
        have h := hTailZero (N₀ + 1)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b0)]
        simp only [ite_true, zero_smul, zero_add]
        rw [show ∑ x ∈ Finset.univ.erase b0,
            (if x = b0 then (0 : ℂ) else μB x ^ (N₀ + 1)) • (B x).mpvState (N₀ + 1) =
            ∑ x ∈ Finset.univ.erase b0, μB x ^ (N₀ + 1) • (B x).mpvState (N₀ + 1) from
          Finset.sum_congr rfl (fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)])]
        exact h
      have h_coeff := hLI hzero k₀
      simp only [hk0_ne, ite_false] at h_coeff
      exact pow_ne_zero _ (hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero k₀) h_coeff
    · -- rA ≥ 2: apply the lemma recursively to the tail families.
      have hrA_ge2 : 2 ≤ rA := by omega
      -- ── Tail SameMPV₂ ──
      have hEqual_tail : SameMPV₂
          (toTensorFromBlocks (d := d) (μ := μA ∘ succA) (fun j => A (succA j)))
          (toTensorFromBlocks (d := d) (μ := μB ∘ succB) (fun k => B (succB k))) := by
        intro N σ
        have hA_eq := mpv_toTensorFromBlocks_eq_sum (μA ∘ succA) (fun j => A (succA j)) σ
        have hB_eq := mpv_toTensorFromBlocks_eq_sum (μB ∘ succB) (fun k => B (succB k)) σ
        simp only [Function.comp, smul_eq_mul] at hA_eq hB_eq
        rw [hA_eq, hB_eq]
        have h := hTailReindex N
        have h_pw := PiLp.ext_iff.mp h σ
        change (∑ j, μA (succA j) ^ N • (A (succA j)).mpvState N).1 σ =
          (∑ k, μB (succB k) ^ N • (B (succB k)).mpvState N).1 σ at h_pw
        simp only [WithLp.IsEquiv.piLp_sum, WithLp.IsEquiv.piLp_smul, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, mpvState_apply] at h_pw
        exact h_pw
      -- ── Tail hSumState ──
      have hSumState_tail : ∀ N,
          ∑ j : Fin (rA - 1), (μA (succA j)) ^ N • (A (succA j)).mpvState N =
          ∑ k : Fin (rB - 1), (μB (succB k)) ^ N • (B (succB k)).mpvState N :=
        hTailReindex
      -- ── Tail IsCanonicalFormBNT for A ──
      have hA_tail : IsCanonicalFormBNT (μA ∘ succA) (fun j => A (succA j)) :=
        IsCanonicalFormBNT.ofSeparatedData
          (HasInjectiveBlocks.ofForall (fun k => hA_inj_local (succA k)))
          (IsLeftCanonicalBlockFamily.ofForall (fun k => hA_left_local (succA k)))
          ⟨hA.toIsCanonicalForm.mu_strict_anti.comp_strictMono succA_strictMono,
           fun k => hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero (succA k)⟩
          (HasNormalizedSelfOverlap.ofForall (fun k => hA_self (succA k)))
          (fun j k hjk hdim => hA.blocks_not_equiv (succA j) (succA k)
            (fun h => hjk (succA_inj h)) hdim)
      -- ── Tail IsCanonicalFormBNT for B ──
      have hB_tail : IsCanonicalFormBNT (μB ∘ succB) (fun k => B (succB k)) :=
        IsCanonicalFormBNT.ofSeparatedData
          (HasInjectiveBlocks.ofForall (fun k => hB_inj_local (succB k)))
          (IsLeftCanonicalBlockFamily.ofForall (fun k => hB_left_local (succB k)))
          ⟨hB.toIsCanonicalForm.mu_strict_anti.comp_strictMono succB_strictMono,
           fun k => hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero (succB k)⟩
          (HasNormalizedSelfOverlap.ofForall (fun k => hB_self (succB k)))
          (fun j k hjk hdim => hB.blocks_not_equiv (succB j) (succB k)
            (fun h => hjk (succB_inj h)) hdim)
      -- ── Apply the lemma recursively ──
      have IH := exists_nondecaying_overlap_of_sameMPV₂_CFBNT
        (fun j => A (succA j)) (fun k => B (succB k))
        hA_tail hB_tail hEqual_tail
        (by omega) (by omega)
        hSumState_tail
        (fun k => hA_self (succA k))
        (fun k => hB_self (succB k))
        (fun j k hjk => hA_cross (succA j) (succA k) (fun h => hjk (succA_inj h)))
        (fun j k hjk => hB_cross (succB j) (succB k) (fun h => hjk (succB_inj h)))
      -- IH.2 gives: ∀ k', ∃ j', overlap(A (succA j'), B (succB k')) ↛ 0.
      obtain ⟨j', hj'⟩ := IH.2 k₀'
      -- hj' says overlap(A (succA j'), B (succB k₀')) doesn't → 0.
      -- But succB k₀' = k₀ (from hk0_eq), so this is overlap(A (succA j'), B k₀).
      -- hall says it → 0. Contradiction.
      apply hj'; show Tendsto (fun N => mpvOverlap (d := d)
        (A (succA j')) (B (succB k₀')) N) atTop (nhds 0)
      rw [hk0_eq]; exact hall (succA j')
termination_by rA + rB

/-- **Block matching from equal weighted MPV sums via overlap dichotomy.**

Given two `IsCanonicalFormBNT` families generating equal total MPVs via
`toTensorFromBlocks`, this lemma produces the block matching: equal block counts,
a permutation, and per-block gauge-phase equivalence.

### Mathematical content (overlap dichotomy approach, CPSV17 Appendix A)

The `SameMPV₂` hypothesis combined with `mpv_toTensorFromBlocks_eq_sum` gives the identity
  `∑_j (μA j)^N * mpv(A j) σ = ∑_k (μB k)^N * mpv(B k) σ`   for all N, σ.

**Step 1 — Finding matches via overlap dichotomy**: For each B-block k₀, take the inner
product of the identity with `mpvState(B k₀, N)`. The B-side gives a sum where
`mpvOverlap(B k₀, B k₀)(N) → 1` and cross-BNT terms `→ 0`. If ALL cross-family
overlaps `mpvOverlap(A j, B k₀)` tended to 0, the Gram-matrix projection would force
`|μB k₀|^N ≤ o(1) · |μA 0|^N`, giving `|μB k₀| < |μA 0|`. By symmetry from the A-side,
`|μA 0| < |μB 0|`. Combining gives `|μB 0| < |μA 0| < |μB 0|` — a contradiction.
So ∃ at least one pair (j, k) with non-decaying overlap. By the overlap dichotomy
(`mpvOverlap_tendsto_zero_of_dim_ne`, `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv`),
this forces dim equality and gauge-phase equivalence.

**Step 2 — Injectivity**: If two distinct B-blocks k₁ ≠ k₂ were both matched to the
same A-block j₀, both would be GPE with A j₀, hence GPE with each other — contradicting
the B-side BNT separation (`hB.blocks_not_equiv`).

**Step 3 — Induction**: Matched pairs can be peeled off using `μA j = μB k · ζ` (from
BNT LI at consecutive large N), reducing to a smaller problem. Induction on `rA + rB`
gives the full matching, with `rA = rB` following from injectivity on finite sets.

### Note on SameMPV vs GaugePhaseEquiv

The conclusion is per-block `GaugePhaseEquiv`, NOT exact per-block `SameMPV₂`. This is
optimal: from `SameMPV₂` of the assembled tensors, one can only derive GPE for individual
blocks (the phases may be non-trivial). A counterexample: take `B = ζ • (X · A · X⁻¹)`
with `|ζ| = 1, ζ ≠ 1` and `μB = μA / ζ`; then the assembled tensors have equal MPVs
but the blocks differ by phase `ζ^N`.

### Proof structure

The proof has the following fully-formal components:

1. **Base cases** (`rA = 0` or `rB = 0`): linear independence + vanishing sum → ⊥.
2. **Overlap dichotomy**: non-decaying overlap → dim match + GPE (contrapositives of
   `mpvOverlap_tendsto_zero_of_dim_ne` and `..._of_not_gaugePhaseEquiv_cast_left`).
3. **Matching injectivity**: GPE of two A-blocks with the same B-block gives cross-overlap
   norm → 1 (via `mpv_eq_pow_mul_of_gaugePhase` + `norm_eq_one_of_selfOverlap_scale`),
   contradicting A-BNT cross-overlap → 0. Similarly for B-side.
4. **rA = rB**: injective maps `Fin rA → Fin rB` and `Fin rB → Fin rA` on finite types.
5. **Permutation**: `Equiv.ofBijective` on the now-bijective matching function.

The **remaining sorry** is the non-decaying overlap existence (`exists_nondecaying_A`
and `exists_nondecaying_B`): for each block in one family, there must exist a block in
the other with non-decaying cross-overlap. -/
private lemma blocks_match_of_sameMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 0: Extract basic data from the BNT hypotheses.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hμA_ne := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  have hμB_ne := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  obtain ⟨N0A, hLIA⟩ := hA.isBNT.eventually_li
  obtain ⟨N0B, hLIB⟩ := hB.isBNT.eventually_li
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 1: The weighted-sum identity (in mpvState form).
  -- ═══════════════════════════════════════════════════════════════════════════
  have hSumState : ∀ N : ℕ,
      ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
    intro N
    -- Show pointwise equality as functions, then wrap in the PiLp structure.
    have h_pointwise : ∀ σ : Cfg d N,
        ∑ j : Fin rA, μA j ^ N * mpv (A j) σ =
          ∑ k : Fin rB, μB k ^ N * mpv (B k) σ := by
      intro σ
      have hA_eq := mpv_toTensorFromBlocks_eq_sum μA A σ
      have hB_eq := mpv_toTensorFromBlocks_eq_sum μB B σ
      simp only [smul_eq_mul] at hA_eq hB_eq
      rw [← hA_eq, hEqual N σ, hB_eq]
    apply PiLp.ext; intro σ
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    -- The remaining goal involves mpvState.ofLp, which equals mpv.
    change ∑ x, μA x ^ N * (A x).mpvState N σ = ∑ x, μB x ^ N * (B x).mpvState N σ
    simp only [mpvState_apply]
    exact h_pointwise σ
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 2: Handle base cases rA = 0 or rB = 0.
  -- ═══════════════════════════════════════════════════════════════════════════
  by_cases hrA : rA = 0
  · subst hrA
    have hrB : rB = 0 := by
      by_contra hrB_ne
      have hrB_pos : 0 < rB := Nat.pos_of_ne_zero hrB_ne
      have hN := hLIB (N0B + 1) (by omega)
      have hzero : ∑ k : Fin rB, (μB k) ^ (N0B + 1) • mpvState (d := d) (B k) (N0B + 1) = 0 := by
        rw [← hSumState (N0B + 1)]
        simp [Finset.sum_empty]
      exact absurd
        (Fintype.linearIndependent_iff.mp hN _ hzero ⟨0, hrB_pos⟩)
        (pow_ne_zero (N0B + 1) (hμB_ne ⟨0, hrB_pos⟩))
    subst hrB
    exact ⟨rfl, Equiv.refl _, fun j => Fin.elim0 j⟩
  by_cases hrB : rB = 0
  · subst hrB
    exfalso
    have hrA_pos : 0 < rA := Nat.pos_of_ne_zero hrA
    have hN := hLIA (N0A + 1) (by omega)
    have hzero : ∑ j : Fin rA, (μA j) ^ (N0A + 1) • mpvState (d := d) (A j) (N0A + 1) = 0 := by
      rw [hSumState (N0A + 1)]
      simp [Finset.sum_empty]
    exact pow_ne_zero (N0A + 1) (hμA_ne ⟨0, hrA_pos⟩)
      (Fintype.linearIndependent_iff.mp hN _ hzero ⟨0, hrA_pos⟩)
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 3: Main case — rA, rB ≥ 1.
  --
  -- We use the overlap dichotomy approach (CPSV17 Appendix A):
  --
  -- (a) For each j₀ : Fin rA, show ∃ k₀ : Fin rB with non-decaying overlap.
  --     (And symmetrically for each B-block.)
  --
  -- (b) From non-decaying overlap, the overlap dichotomy gives dim equality
  --     and GaugePhaseEquiv (using mpvOverlap_tendsto_zero_of_dim_ne and
  --     mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left).
  --
  -- (c) The matching is injective: if two A-blocks matched the same B-block,
  --     both would be GPE with it, hence GPE with each other, contradicting
  --     BNT separation in the A-family.
  --
  -- (d) Injectivity of both matching functions (Fin rA → Fin rB and
  --     Fin rB → Fin rA) between finite sets forces rA = rB.
  -- ═══════════════════════════════════════════════════════════════════════════
  classical
  -- 3a. Extract overlap properties from BNT data.
  have hA_inj := hA.toHasInjectiveBlocks.block_injective
  have hB_inj := hB.toHasInjectiveBlocks.block_injective
  have hA_left := hA.toIsLeftCanonicalBlockFamily.leftCanonical
  have hB_left := hB.toIsLeftCanonicalBlockFamily.leftCanonical
  have hA_self := hA.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hB_self := hB.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hA_cross : ∀ j k : Fin rA, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) :=
    fun j k hjk => hA.cross_overlap_tendsto_zero j k hjk
  have hB_cross : ∀ j k : Fin rB, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (B j) (B k) N) atTop (nhds 0) :=
    fun j k hjk => hB.cross_overlap_tendsto_zero j k hjk
  -- ═══════════════════════════════════════════════════════════════════════════
  -- 3b. KEY STEP: For each A-block, there exists a B-block with non-decaying
  -- overlap.  This is the core of the overlap dichotomy / dominant-weight
  -- induction argument from CPSV17 Appendix A (see module docstring).
  --
  -- The mathematical argument proceeds by strong induction on rA + rB,
  -- matching the dominant blocks at each step:
  --
  --   • Project the weighted-sum identity onto the biorthogonal dual of the
  --     dominant A-block (j₀ = 0), yielding:
  --       (μA 0)^N = ∑_k (μB k)^N · ⟨ã₀(N), mpvState(B k, N)⟩
  --     If all cross-terms → 0, then |(μA 0)|^N ≤ ε · rB · |μB 0|^N.
  --     When |μA 0| ≥ |μB 0| (ensured by choosing the globally dominant
  --     side), this gives a contradiction.
  --
  --   • The symmetric B-side argument ensures the globally dominant block
  --     always finds a match.  After peeling off the matched dominant pair,
  --     the reduced identity has fewer blocks and the induction continues.
  --
  -- The full formalization of this inductive argument requires infrastructure
  -- for Fin-reindexing of BNT families under block removal.  We encapsulate
  -- the result as a focused sorry and build the rest of the proof around it.
  -- ═══════════════════════════════════════════════════════════════════════════
  have h_nondecaying := exists_nondecaying_overlap_of_sameMPV₂_CFBNT
    A B hA hB hEqual hrA hrB hSumState hA_self hB_self hA_cross hB_cross
  have exists_nondecaying_A : ∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0) :=
    h_nondecaying.1
  have exists_nondecaying_B : ∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0) :=
    h_nondecaying.2
  -- ═══════════════════════════════════════════════════════════════════════════
  -- 3c. From non-decaying overlap → dim equality + GaugePhaseEquiv.
  -- This uses the overlap dichotomy: dim mismatch ⟹ overlap → 0,
  -- and non-GPE ⟹ overlap → 0. Both contrapositives give our result.
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Matching function from A-blocks to B-blocks.
  let fA : Fin rA → Fin rB := fun j => (exists_nondecaying_A j).choose
  have hfA_nd : ∀ j,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B (fA j)) N) atTop (nhds 0) :=
    fun j => (exists_nondecaying_A j).choose_spec
  -- Dimension equality by contrapositive of mpvOverlap_tendsto_zero_of_dim_ne.
  have hfA_dim : ∀ j, dimA j = dimB (fA j) := by
    intro j
    by_contra hne
    exact hfA_nd j (mpvOverlap_tendsto_zero_of_dim_ne (A j) (B (fA j))
      (hA_inj j) (hB_inj (fA j)) (hA_left j) (hB_left (fA j)) hne)
  -- GaugePhaseEquiv by contrapositive of mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv.
  have hfA_gpe : ∀ j,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hfA_dim j)) (A j))
        (B (fA j)) := by
    intro j
    by_contra hNotGPE
    have hdim := hfA_dim j
    exact hfA_nd j
      (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim (A j) (B (fA j))
        (hA_inj j) (hB_inj (fA j))
        (hA_left j) (hB_left (fA j)) hNotGPE)
  -- ═══════════════════════════════════════════════════════════════════════════
  -- 3d. fA is injective (from A-BNT separation).
  -- If fA(j₁) = fA(j₂) for j₁ ≠ j₂, then both A j₁ and A j₂ are GPE with
  -- B(fA j₁). From the MPV scaling formulas, the cross-overlap
  -- mpvOverlap(A j₁, A j₂) has norm → 1, contradicting A-BNT cross-overlap → 0.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hfA_inj : Function.Injective fA := by
    intro j1 j2 hfj
    by_contra hne
    -- Extract GPE data for both blocks.
    obtain ⟨X1, ζ1, _, hX1⟩ := hfA_gpe j1
    obtain ⟨X2, ζ2, _, hX2⟩ := hfA_gpe j2
    -- MPV scaling formulas.
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B (fA j1)) σ = ζ1 ^ N * mpv (A j1) σ := by
      intro N σ
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X1 ζ1 hX1 N σ,
          mpv_cast_dim (hfA_dim j1)]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B (fA j1)) σ = ζ2 ^ N * mpv (A j2) σ := by
      intro N σ
      rw [show fA j1 = fA j2 from hfj]
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X2 ζ2 hX2 N σ,
          mpv_cast_dim (hfA_dim j2)]
    -- Self-overlap of B(fA j1) in norm → 1.
    have hBB_norm_tendsto :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖) atTop (nhds 1) := by
      convert (hB_self (fA j1)).norm using 1; simp
    -- Self-overlap of A j1 in norm → 1.
    have hAA1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j1) N‖) atTop (nhds 1) := by
      convert (hA_self j1).norm using 1; simp
    have hAA2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j2) (A j2) N‖) atTop (nhds 1) := by
      convert (hA_self j2).norm using 1; simp
    -- Norm of ζ₁ = 1.
    have hζ1_norm : ‖ζ1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA1_norm hBB_norm_tendsto
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A j1) (B := B (fA j1)) (ζ := ζ1) hmpv1)
    have hζ2_norm : ‖ζ2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA2_norm hBB_norm_tendsto
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A j2) (B := B (fA j1)) (ζ := ζ2) hmpv2)
    -- Cross overlap mpvOverlap(A j1, A j2) = (ζ1 * star ζ2)^N * self-overlap(B).
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (A j1) (A j2) N =
        (starRingEnd ℂ ζ1 * ζ2) ^ N *
          mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N := by
      intro N
      simp only [mpvOverlap]
      -- From hmpv1: mpv(A j1) σ = star(ζ1)^N * mpv(B(fA j1)) σ  (invert scaling)
      -- From hmpv2: mpv(A j2) σ = star(ζ2)^N * mpv(B(fA j1)) σ
      -- So: mpv(A j1) σ * star(mpv(A j2) σ)
      --   = star(ζ1)^N * mpv(B..) σ * star(star(ζ2)^N * mpv(B..) σ)
      --   = star(ζ1)^N * ζ2^N * |mpv(B..) σ|^2
      have hζ1_star_mul : starRingEnd ℂ ζ1 * ζ1 = 1 := by
        have := Complex.conj_mul' ζ1
        rw [this, hζ1_norm, Complex.ofReal_one, one_pow]
      have hζ2_star_mul : starRingEnd ℂ ζ2 * ζ2 = 1 := by
        have := Complex.conj_mul' ζ2
        rw [this, hζ2_norm, Complex.ofReal_one, one_pow]
      have hA1_eq : ∀ σ : Cfg d N, mpv (A j1) σ =
          (starRingEnd ℂ ζ1) ^ N * (ζ1 ^ N * mpv (A j1) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ1_star_mul, one_pow, one_mul]
      have hA2_eq : ∀ σ : Cfg d N, mpv (A j2) σ =
          (starRingEnd ℂ ζ2) ^ N * (ζ2 ^ N * mpv (A j2) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ2_star_mul, one_pow, one_mul]
      have hStep1 : ∀ σ : Cfg d N, mpv (A j1) σ * star (mpv (A j2) σ) =
          (starRingEnd ℂ ζ1) ^ N * mpv (B (fA j1)) σ *
          star ((starRingEnd ℂ ζ2) ^ N * mpv (B (fA j1)) σ) := by
        intro σ; rw [hA1_eq σ, ← hmpv1 N σ, hA2_eq σ, ← hmpv2 N σ]
      simp_rw [hStep1]
      simp only [star_mul, star_pow, RCLike.star_def, starRingEnd_self_apply]
      rw [show ((starRingEnd ℂ) ζ1 * ζ2) ^ N = (starRingEnd ℂ) ζ1 ^ N * ζ2 ^ N from mul_pow _ _ _]
      rw [Finset.mul_sum]
      congr 1; ext σ; ring
    -- Norm of phase factor is 1.
    have hNormζ : ‖starRingEnd ℂ ζ1 * ζ2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hζ1_norm, hζ2_norm, mul_one]
    -- So ‖mpvOverlap(A j1, A j2, N)‖ → 1.
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖) =
          fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
            ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]
      have : (fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
          ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖ := by
        ext N; rw [norm_pow, hNormζ, one_pow]
      rw [this]; simpa using hBB_norm_tendsto
    -- But A-BNT cross-overlap → 0.
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖) atTop (nhds 0) := by
      convert (hA_cross j1 j2 hne).norm using 1; simp
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- ═══════════════════════════════════════════════════════════════════════════
  -- 3e. Matching function from B-blocks to A-blocks, also injective.
  -- ═══════════════════════════════════════════════════════════════════════════
  let gB : Fin rB → Fin rA := fun k => (exists_nondecaying_B k).choose
  have hgB_nd : ∀ k,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A (gB k)) (B k) N) atTop (nhds 0) :=
    fun k => (exists_nondecaying_B k).choose_spec
  have hgB_dim : ∀ k, dimA (gB k) = dimB k := by
    intro k
    by_contra hne
    exact hgB_nd k (mpvOverlap_tendsto_zero_of_dim_ne (A (gB k)) (B k)
      (hA_inj (gB k)) (hB_inj k) (hA_left (gB k)) (hB_left k) hne)
  have hgB_gpe : ∀ k,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hgB_dim k)) (A (gB k)))
        (B k) := by
    intro k
    by_contra hNotGPE
    exact hgB_nd k
      (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        (hgB_dim k) (A (gB k)) (B k)
        (hA_inj (gB k)) (hB_inj k)
        (hA_left (gB k)) (hB_left k) hNotGPE)
  -- gB is injective by the same argument (B-BNT separation).
  have hgB_inj : Function.Injective gB := by
    intro k1 k2 hgk
    by_contra hne
    obtain ⟨Y1, ω1, _, hY1⟩ := hgB_gpe k1
    obtain ⟨Y2, ω2, _, hY2⟩ := hgB_gpe k2
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k1) σ = ω1 ^ N * mpv (A (gB k1)) σ := by
      intro N σ
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y1 ω1 hY1 N σ,
          mpv_cast_dim (hgB_dim k1)]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k2) σ = ω2 ^ N * mpv (A (gB k1)) σ := by
      intro N σ
      rw [show gB k1 = gB k2 from hgk] at hmpv1 ⊢
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y2 ω2 hY2 N σ,
          mpv_cast_dim (hgB_dim k2)]
    have hAA_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖) atTop (nhds 1) := by
      convert (hA_self (gB k1)).norm using 1; simp
    have hBB1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k1) N‖) atTop (nhds 1) := by
      convert (hB_self k1).norm using 1; simp
    have hBB2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k2) (B k2) N‖) atTop (nhds 1) := by
      convert (hB_self k2).norm using 1; simp
    have hω1_norm : ‖ω1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB1_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A (gB k1)) (B := B k1) (ζ := ω1) hmpv1)
    have hω2_norm : ‖ω2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB2_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A (gB k1)) (B := B k2) (ζ := ω2) hmpv2)
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (B k1) (B k2) N =
        (ω1 * starRingEnd ℂ ω2) ^ N *
          mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N := by
      intro N
      simp only [mpvOverlap]
      simp_rw [hmpv1 N, hmpv2 N, star_mul, star_pow]
      simp_rw [show star ω2 = starRingEnd ℂ ω2 from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ω1 ^ N * mpv (A (gB k1)) x *
          (star (mpv (A (gB k1)) x) * (starRingEnd ℂ ω2) ^ N) =
        ω1 ^ N * (starRingEnd ℂ ω2) ^ N *
          (mpv (A (gB k1)) x * star (mpv (A (gB k1)) x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    have hNormω : ‖ω1 * starRingEnd ℂ ω2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hω1_norm, hω2_norm, mul_one]
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖) =
          fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
            ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]
      have : (fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
          ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖ := by
        ext N; rw [norm_pow, hNormω, one_pow]
      rw [this]; simpa using hAA_norm
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖) atTop (nhds 0) := by
      convert (hB_cross k1 k2 hne).norm using 1; simp
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- ═══════════════════════════════════════════════════════════════════════════
  -- 3f. Derive rA = rB from the injective maps between finite types.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hrA_le_rB : Fintype.card (Fin rA) ≤ Fintype.card (Fin rB) :=
    Fintype.card_le_of_injective fA hfA_inj
  have hrB_le_rA : Fintype.card (Fin rB) ≤ Fintype.card (Fin rA) :=
    Fintype.card_le_of_injective gB hgB_inj
  simp only [Fintype.card_fin] at hrA_le_rB hrB_le_rA
  have hrAB : rA = rB := le_antisymm hrA_le_rB hrB_le_rA
  -- ═══════════════════════════════════════════════════════════════════════════
  -- 3g. Build the permutation from fA (now a bijection since rA = rB).
  -- ═══════════════════════════════════════════════════════════════════════════
  refine ⟨hrAB, ?_⟩
  subst hrAB
  -- fA : Fin rA → Fin rA is injective on a finite type, hence bijective.
  have hfA_bij : Function.Bijective fA :=
    ⟨hfA_inj, (Finite.injective_iff_surjective.mp hfA_inj)⟩
  let perm : Fin rA ≃ Fin rA := Equiv.ofBijective fA hfA_bij
  refine ⟨perm, fun j => ?_⟩
  have hpj : perm j = fA j := Equiv.ofBijective_apply fA hfA_bij j
  rw [hpj]
  exact ⟨hfA_dim j, hfA_gpe j⟩

/-- **Self-contained equal-case Fundamental Theorem for heterogeneous CF-BNT**
([CPSV21, Corollary IV.5] / [CPSV17, Theorem 4.4 + equal-case corollary]).

Given two `IsCanonicalFormBNT` families with *different* block structures
(`rA`, `rB`, `dimA`, `dimB`, `μA`, `μB`), the hypothesis `SameMPV₂` for the assembled
block-diagonal tensors — with **no** coefficient convergence data from the caller —
forces:
1. Equal block counts: `rA = rB`.
2. A block permutation: `perm : Fin rA ≃ Fin rB`.
3. Blockwise gauge-phase equivalence: for each `j`, `dimA j = dimB (perm j)` and
   `GaugePhaseEquiv (cast … (A j)) (B (perm j))`.

Unlike `fundamentalTheorem_proportionalMPV_CFBNT` and `fundamentalTheorem_equalMPV_full`,
this theorem requires **no** explicit `aCoeff`, `bCoeff`, `aLim`, `bLim` arguments. The
coefficient convergence question that plagues the general proportional-case theorem is
bypassed entirely: the BNT decomposition identity
  `∑_j (μA j)^N * mpv(A j) σ = ∑_k (μB k)^N * mpv(B k) σ`
is analyzed directly via the overlap dichotomy (CPSV17 Appendix A), yielding per-block
gauge-phase matching.

### Proof status

The proof delegates to `blocks_match_of_sameMPV₂_CFBNT`.  The full proof structure is
complete:

- Base cases `rA = 0` or `rB = 0`: fully proved (LI + vanishing sum → contradiction).
- Overlap dichotomy (dim mismatch → decay, non-GPE → decay): fully proved.
- Matching injectivity (BNT separation + GPE cross-overlap norm → 1): fully proved.
- `rA = rB` (injective maps on finite types): fully proved.
- Permutation construction and per-block data extraction: fully proved.

The **remaining `sorry`** is in `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`,
which proves both `exists_nondecaying_A` and `exists_nondecaying_B`:
for each block in one family, there exists a block in the other family with non-decaying
cross-overlap.  The mathematical proof (CPSV17 Appendix A) proceeds by strong induction
on block count: project the weighted-sum identity onto the biorthogonal dual of the
dominant block (Gram-matrix inversion), obtain `|μA 0|^N ≤ ε · rB · |μB 0|^N`, derive a
contradiction when `|μA 0| ≥ |μB 0|`, and peel off matched dominant pairs.  Formalizing
the inductive step requires Fin-reindexing under block removal (showing the reduced
subfamily is still `IsCanonicalFormBNT`), which is planned as follow-up work. -/
theorem fundamentalTheorem_equalMPV_CFBNT_hetero
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ∃ _h : rA = rB,
      ∃ perm : Fin rA ≃ Fin rB,
        ∀ j : Fin rA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) :=
  blocks_match_of_sameMPV₂_CFBNT A B hA hB hEqual

end HeteroEqualCase

end MPSTensor
