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
  remaining cases.

The full formalization of the inductive block-removal step requires Fin-reindexing
infrastructure for BNT families.  We encapsulate the complete mathematical argument
and mark the proof with `sorry` pending this infrastructure. -/
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
  -- The proof uses the normalized total tensor approach combined with strong induction
  -- on rA + rB. The key steps are:
  --
  -- 1. From the self-overlap of the total tensor, derive |μA 0| = |μB 0|.
  -- 2. For the dominant blocks (j₀ = 0, k₀ = 0): the normalized overlap
  --    overlap(A_norm, B 0) has two expressions:
  --    - From the A-decomposition + all overlaps → 0: overlap(A_norm, B 0) → 0.
  --    - From equal MPV + B-decomposition: |overlap(A_norm, B 0)| → 1 (using |μB 0/μA 0| = 1).
  --    Contradiction.
  -- 3. For non-dominant blocks: after matching the dominant pair via the overlap
  --    dichotomy and extracting the weight relation μA 0 = ζ · μB 0, the matched pair
  --    is subtracted from the weighted-sum identity. The reduced families of rA-1 and
  --    rB-1 blocks inherit IsCanonicalFormBNT, and the strong induction hypothesis
  --    closes the remaining cases.
  --
  -- The full formalization requires Fin-reindexing infrastructure for block removal
  -- under IsCanonicalFormBNT. The mathematical argument is complete; the formal
  -- implementation is pending this infrastructure.
  -- We prove the result by strong induction on rA + rB.
  -- The key tool is the normalized overlap expansion:
  --   overlap(A_norm, C) = ∑_j (μA j / μA 0)^N · overlap(A j, C)
  -- where the normalized coefficients (μA j / μA 0)^N converge (to δ_{j,0}).
  --
  -- Base case intuition (rA = rB = 1): the normalized identity gives
  -- overlap(A_norm, B 0) = overlap(A 0, B 0) directly, and the B-side gives
  -- overlap(A_norm, B 0) = c(N) · overlap(B 0, B 0) → c(N) · 1. Since
  -- |c(N)| = |μB 0 / μA 0|^N = 1 (from |μA 0| = |μB 0|), the overlap has
  -- norm → 1, contradicting → 0.
  --
  -- Inductive step: match dominant blocks, extract μA 0 = ζ · μB 0, subtract,
  -- apply IH to reduced family of rA-1 + rB-1 blocks.
  --
  -- The induction is formalized as Nat.strongRecOn on rA + rB.
  -- The block-removal sub-step (showing reduced families are still CF-BNT with
  -- equal total MPVs) requires Fin-reindexing infrastructure that is planned
  -- as follow-up work.
  exact ⟨fun j₀ => by
    -- For each A-block j₀, find a B-block with non-decaying overlap.
    -- The proof is by contradiction.
    by_contra hall; push_neg at hall
    -- hall : ∀ k, overlap(A j₀, B k) → 0
    --
    -- Step 1: From the weighted-sum identity, take overlap with A j₀.
    -- Using the A-side Gram matrix inverse (which → I), the biorthogonal
    -- projection gives (μA j₀)^N = ∑_k (μB k)^N · α_k(N) with α_k → 0.
    --
    -- Step 2: Dividing by (μA 0)^N, the ratio (μA j₀/μA 0)^N = ∑_k (μB k/μA 0)^N · α_k.
    -- For j₀ = 0: LHS = 1, RHS → 0 (each ‖μB k/μA 0‖ ≤ 1 from |μA 0| = |μB 0|).
    --   Contradiction.
    -- For j₀ > 0: use the induction hypothesis on the reduced family after
    --   matching dominant blocks.
    sorry,
  fun k₀ => by
    -- Symmetric argument (swap A ↔ B roles in the overlap identity).
    by_contra hall; push_neg at hall
    sorry⟩

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
    intro N; ext σ; simp [mpvState_apply, smul_eq_mul]
    have hA_eq := mpv_toTensorFromBlocks_eq_sum μA A σ
    have hB_eq := mpv_toTensorFromBlocks_eq_sum μB B σ
    simp only [smul_eq_mul] at hA_eq hB_eq
    rw [← hA_eq, hEqual N σ, hB_eq]
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
      ((mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim (A j) (B (fA j))
        (hA_inj j) (hB_inj (fA j))
        (hA_left j) (hB_left (fA j)) hNotGPE).congr
        fun N => mpvOverlap_cast_dim_left hdim (A j) (B (fA j)) N)
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
      norm_eq_one_of_selfOverlap_scale hBB_norm_tendsto hAA1_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := B (fA j1)) (B := A j1) (ζ := ζ1) hmpv1)
    have hζ2_norm : ‖ζ2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hBB_norm_tendsto hAA2_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := B (fA j1)) (B := A j2) (ζ := ζ2) (by rwa [hfj] at hmpv2))
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
      simp_rw [show ∀ σ : Cfg d N, mpv (A j1) σ =
        (starRingEnd ℂ ζ1) ^ N * (ζ1 ^ N * mpv (A j1) σ) from fun σ => by
          rw [← mul_assoc]; simp [star_pow, mul_comm (star ζ1) ζ1,
            show star ζ1 * ζ1 = ↑‖ζ1‖ ^ 2 from by
              rw [Complex.sq_abs]; ring_nf,
            hζ1_norm]]
      simp_rw [← hmpv1]
      simp_rw [show ∀ σ : Cfg d N, mpv (A j2) σ =
        (starRingEnd ℂ ζ2) ^ N * (ζ2 ^ N * mpv (A j2) σ) from fun σ => by
          rw [← mul_assoc]; simp [star_pow, mul_comm (star ζ2) ζ2,
            show star ζ2 * ζ2 = ↑‖ζ2‖ ^ 2 from by
              rw [Complex.sq_abs]; ring_nf,
            hζ2_norm]]
      simp_rw [← hmpv2]
      simp_rw [star_mul, star_pow, RCLike.star_def, map_pow, starRingEnd_self_apply]
      rw [← Finset.mul_sum]
      ring_nf
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
      ((mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        (hgB_dim k) (A (gB k)) (B k)
        (hA_inj (gB k)) (hB_inj k)
        (hA_left (gB k)) (hB_left k) hNotGPE).congr
        fun N => mpvOverlap_cast_dim_left (hgB_dim k) (A (gB k)) (B k) N)
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
          (A := A (gB k1)) (B := B k2) (ζ := ω2) (by rwa [hgk] at hmpv2))
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

The **remaining `sorry`** is in `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`, which proves both `exists_nondecaying_A` and `exists_nondecaying_B`:
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
