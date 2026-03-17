/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

/-!
# Full Fundamental Theorem of MPS (Assembly)

This module assembles the **Fundamental Theorem of Matrix Product States** by combining:

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

5. **`BNT/PermutationRigidity.lean`**: `exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp`
   (permutation + gauge-phase from proportional MPVs — the core of Thm 4.4).

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
      simp [mpvState_apply, smul_eq_mul]
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

**Layer 3 — Assembly** (`fundamentalTheorem_equalMPV_CFBNT_hetero`):
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

/-- **Layer 1: Block matching from equal weighted MPV sums**
(exponential polynomial uniqueness).

Given two `IsCanonicalFormBNT` families generating equal total MPVs via
`toTensorFromBlocks`, this lemma produces the block matching: equal block counts,
a permutation, and per-block MPV agreement.

### Mathematical content

The `SameMPV₂` hypothesis combined with `mpv_toTensorFromBlocks_eq_sum` gives the identity
  `∑_j (μA j)^N * mpv(A j) σ = ∑_k (μB k)^N * mpv(B k) σ`   for all N, σ.
This is a **vanishing exponential polynomial** (linear combination of distinct geometric
sequences indexed by the combined weight set `{μA j} ∪ {μB k}`).

The `HasStrictOrderedNonzeroWeights` condition (from `IsCanonicalFormBNT`) ensures that
`μA` and `μB` are each injective (distinct norms → distinct values) and nonzero. Grouping
terms by their common base value (at most one from each family per group, since each is
injective) and applying Vandermonde uniqueness gives:

(a) Every `μA j` must equal some `μB k` — otherwise the "unmatched" coefficient
    `mpv(A j)(σ) = 0` for all σ, contradicting `hA.toHasNormalizedSelfOverlap` which
    gives `∑_σ |mpv(A j)(σ)|² → 1 > 0`.
(b) Symmetrically, every `μB k` matches some `μA j`.
(c) The matching is a bijection `rA = rB` + permutation.
(d) For each matched pair: `mpv(A j)(σ) = mpv(B (perm j))(σ)` for all N, σ.

### Formalization status

The Vandermonde determinant (`Matrix.det_vandermonde_ne_zero_iff`) and the linear-algebra
conclusion (`Matrix.eq_zero_of_mulVec_eq_zero`) are available in Mathlib. The remaining
gap is the **grouping step** — merging terms with equal bases in the combined exponential
polynomial — which requires moderate combinatorial bookkeeping (partitioning
`Fin (rA + rB)` by weight value and reindexing the Vandermonde argument over the quotient).
This is mathematically elementary but not yet formalized; the proof is left as `sorry`.

An alternative path uses the `geom_sum_eventually_zero` telescoping induction (already
proved in `SectorDecomposition.lean`, though currently `private`) to establish the full
power-sum vanishing, then derives individual coefficient vanishing via Vandermonde. -/
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
          ∀ (N : ℕ) (σ : Fin N → Fin d), mpv (A j) σ = mpv (B (perm j)) σ := by
  /- The proof uses the BNT linear independence from both sides together with
     `geom_sum_eventually_zero` (from SectorDecomposition.lean) to reduce the
     exponential-polynomial identity to a multiset equality of weights via
     `Matrix.sum_pow_eq_implies_multiset_eq`.

     Step 1: Derive the weighted sum identity from SameMPV₂.
     Step 2: Use BNT LI for A (eventually) + BNT LI for B (eventually) to
             extract per-component coefficient equations for large N.
     Step 3: Use `geom_sum_eventually_zero` to extend to all N ≥ 1.
     Step 4: Use `Matrix.sum_pow_eq_implies_multiset_eq` to get weight multiset equality.
     Step 5: From weight injectivity, derive rA = rB and a weight-matching permutation.
     Step 6: From the permutation + BNT LI, derive per-block MPV equality. -/
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 0: Extract basic data from the BNT hypotheses.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hμA_ne := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  have hμB_ne := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  have hμA_inj := hA.toHasStrictOrderedNonzeroWeights.mu_injective
  have hμB_inj := hB.toHasStrictOrderedNonzeroWeights.mu_injective
  obtain ⟨N0A, hLIA⟩ := hA.isBNT.eventually_li
  obtain ⟨N0B, hLIB⟩ := hB.isBNT.eventually_li
  set N0 := max N0A N0B with hN0_def
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 1: The weighted-sum identity (in mpvState form).
  -- ═══════════════════════════════════════════════════════════════════════════
  have hSum : ∀ (N : ℕ) (σ : Fin N → Fin d),
      ∑ j : Fin rA, (μA j) ^ N * mpv (A j) σ =
        ∑ k : Fin rB, (μB k) ^ N * mpv (B k) σ := by
    intro N σ
    have hA_eq := mpv_toTensorFromBlocks_eq_sum μA A σ
    have hB_eq := mpv_toTensorFromBlocks_eq_sum μB B σ
    simp only [smul_eq_mul] at hA_eq hB_eq
    rw [← hA_eq, hEqual N σ, hB_eq]
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 2: BNT LI from both sides — coefficient extraction for large N.
  -- For N > N0, both {mpvState(A j, N)} and {mpvState(B k, N)} are LI.
  -- From the vector identity, subtracting gives a vanishing linear combination
  -- of the combined family. Applying LI on each side gives coefficient equations.
  -- ═══════════════════════════════════════════════════════════════════════════
  -- For large N, the identity in mpvState form:
  have hSumState : ∀ N : ℕ,
      ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
    intro N; ext σ; simp [mpvState_apply, smul_eq_mul]; exact hSum N σ
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 3: For each j, using LI of {mpvState(A j, N)} at large N:
  -- The B-sum ∑_k (μB k)^N • g_k = ∑_j (μA j)^N • f_j lies in span{f_j}.
  -- Since both sides are the same vector, the A-side decomposition is unique.
  --
  -- Now consider two consecutive large N values. From the identity at N and N+1,
  -- together with LI, we extract: for each j, (μA j)^N = ∑_k (μB k)^N * α_{jk}
  -- where α_{jk} are the "B-to-A expansion coefficients" (via the Gram matrix).
  --
  -- Instead, we use a more direct route via `sum_pow_eq_implies_multiset_eq`:
  -- The identity ∑_j (μA j)^N * mpv(A j)(σ) = ∑_k (μB k)^N * mpv(B k)(σ)
  -- combined with BNT LI gives weight multiset equality.
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Key step: show the weight multisets are equal.
  -- We use `geom_sum_eventually_zero` for the extension argument, then
  -- `Matrix.sum_pow_eq_implies_multiset_eq` for the multiset conclusion.
  --
  -- From LI of A at N > N0A: The identity says ∑_j (μA j)^N • f_j = ∑_k (μB k)^N • g_k.
  -- Since f_j are LI and the LHS uniquely determines the coefficients w.r.t. f_j,
  -- the B-side must have the SAME expansion w.r.t. f_j.
  -- For this, each g_k must lie in span{f_j}. The sum ∑_k (μB k)^N • g_k ∈ span{f_j}.
  --
  -- CRUCIAL: g_k ∈ span{f_j} for large N follows from the identity holding for ALL N.
  -- (At each N, the specific linear combination is in span{f_j}. Since the coefficients
  -- vary with N in a Vandermonde-like way, the individual g_k must be in span{f_j}.)
  --
  -- This requires the following intermediate result:
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Intermediate: show that for large N, each mpvState(B k, N) ∈ span{mpvState(A j, N)}.
  -- Then extract: mpvState(B k, N) = ∑_j β_{jk}(N) • mpvState(A j, N)
  -- and use LI of A to get: (μA j)^N = ∑_k (μB k)^N * β_{jk}(N) for each j.
  -- The β coefficients converge (via the Gram matrix convergence), and
  -- `geom_sum_eventually_zero` extends the relation to all N.
  --
  -- For now, we proceed via a direct argument using the BNT structure.
  -- ═══════════════════════════════════════════════════════════════════════════
  -- We use the approach from the existing `fundamentalTheorem_equalMPV_full` proof:
  -- Given that both families generate the same mpvState sums (weighted by powers),
  -- and the BNT LI holds, we derive the block matching directly.
  --
  -- The key insight: if rB > 0, then for each B-block there must be a matching A-block,
  -- using the overlap dichotomy + the weighted identity.
  -- If no A-block matches, the overlap analysis leads to a contradiction with BNT
  -- (the B-block would have self-overlap → 0, contradicting → 1).
  --
  -- This argument parallels the PermutationRigidityPrimitive but without needing
  -- convergent coefficients; instead, we use the exponential-polynomial identity
  -- directly.
  --
  -- For the formal proof, we delegate to an auxiliary lemma that performs
  -- the induction on (rA + rB), using:
  -- 1. The weighted sum identity (hSum)
  -- 2. BNT LI from both sides
  -- 3. The overlap dichotomy (dim mismatch → 0, not GPE → 0)
  -- 4. `geom_sum_eventually_zero` for extrapolation
  -- 5. `Matrix.sum_pow_eq_implies_multiset_eq` for multiset matching
  --
  -- The detailed argument proceeds as follows:
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step A: Handle rA = 0 or rB = 0.
  -- ═══════════════════════════════════════════════════════════════════════════
  by_cases hrA : rA = 0
  · -- rA = 0: LHS is an empty sum = 0 for all N, σ.
    subst hrA
    -- If rB > 0, take large N where B-states are LI. The identity gives
    -- ∑_k (μB k)^N • mpvState(B k, N) = 0 with LI family and nonzero coefficients.
    -- Contradiction.
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
  · -- rB = 0: symmetric argument.
    subst hrB
    exfalso
    have hrA_pos : 0 < rA := Nat.pos_of_ne_zero hrA
    have hN := hLIA (N0A + 1) (by omega)
    have hzero : ∑ j : Fin rA, (μA j) ^ (N0A + 1) • mpvState (d := d) (A j) (N0A + 1) = 0 := by
      rw [hSumState (N0A + 1)]
      simp [Finset.sum_empty]
    exact pow_ne_zero (N0A + 1) (hμA_ne ⟨0, hrA_pos⟩)
      (Fintype.linearIndependent_iff.mp hN _ hzero ⟨0, hrA_pos⟩)
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step B: Main case — rA, rB ≥ 1.
  --
  -- The full proof requires establishing that the exponential-polynomial identity
  --   ∑_j (μA j)^N * mpv(A j)(σ) = ∑_k (μB k)^N * mpv(B k)(σ)
  -- forces a weight-matching bijection between {μA j} and {μB k}, and that
  -- matched blocks have pointwise-equal MPVs.
  --
  -- This is mathematically elementary but formally requires one of:
  --   (a) Eigenvalue decomposition of cross-transfer matrices to convert the
  --       overlap scalar identity into a power-sum identity suitable for
  --       `Matrix.sum_pow_eq_implies_multiset_eq`, or
  --   (b) A Gram-matrix inversion argument + `geom_sum_eventually_zero` to
  --       extract per-component coefficient equations from the BNT LI, or
  --   (c) A dominant-norm induction argument using overlap convergence rates.
  --
  -- The infrastructure for approach (a) requires Tr(M^N) = ∑ eigenvalue^N
  -- (not yet available). Approach (b) requires continuous inverse convergence
  -- of the Gram matrix (available in principle via Mathlib but not yet wired).
  -- Approach (c) requires quantitative spectral-gap bounds on transfer matrices.
  --
  -- All three approaches are planned developments. The `geom_sum_eventually_zero`
  -- lemma (now public in SectorDecomposition.lean) provides the key extrapolation
  -- step once the per-component equations are established.
  --
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Known consequences that are fully proved elsewhere:
  --   • The base cases (rA = 0 or rB = 0) are handled above.
  --   • Given a permutation with per-block GPE, the weight identity and
  --     per-block MPV equality follow (see `fundamentalTheorem_equalMPV_full`).
  --   • The overlap dichotomy (dim mismatch → 0, not GPE → 0) is available.
  --   • `geom_sum_eventually_zero` extends eventual coefficient equations to
  --     all N.
  -- ═══════════════════════════════════════════════════════════════════════════
  sorry

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
is analyzed directly via exponential-polynomial uniqueness (Vandermonde + grouping),
yielding per-block MPV agreement, from which the overlap dichotomy gives the full
gauge-phase matching.

### Proof status

The **Layer 2** step (overlap dichotomy → dim + GaugePhaseEquiv from per-block SameMPV₂)
is fully proved. The **Layer 1** step (exponential polynomial uniqueness → block matching)
is stated with a `sorry` — see `blocks_match_of_sameMPV₂_CFBNT` for the precise gap
description and proof strategy. -/
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
              (B (perm j)) := by
  -- Layer 1: block matching from exponential polynomial uniqueness.
  obtain ⟨hcount, perm, hBlockSameMPV⟩ :=
    blocks_match_of_sameMPV₂_CFBNT A B hA hB hEqual
  refine ⟨hcount, perm, fun j => ?_⟩
  -- Layer 2: per-block SameMPV₂ → dim equality + GaugePhaseEquiv.
  exact gaugePhaseEquiv_of_block_sameMPV₂ (A j) (B (perm j))
    (hA.toHasInjectiveBlocks.block_injective j)
    (hB.toHasInjectiveBlocks.block_injective (perm j))
    (hA.toIsLeftCanonicalBlockFamily.leftCanonical j)
    (hB.toIsLeftCanonicalBlockFamily.leftCanonical (perm j))
    (hA.toHasNormalizedSelfOverlap.overlap_tendsto_one j)
    (hBlockSameMPV j)

end HeteroEqualCase

end MPSTensor
