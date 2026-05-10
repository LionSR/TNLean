/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

/-!
# Equal and Proportional MPV Fundamental Theorems

This module collects the **equal-case** and **proportional-case** fundamental theorems for
matrix product states in canonical form with basis-of-normal-tensors (BNT) separation,
together with supporting corollaries.

## Main results

### Theorem 1: Equal-MPV Fundamental Theorem for `IsCanonicalFormBNT`
(`fundamentalTheorem_equalMPV_CFBNT`)

**Corollary II_cor2 (equal case)**: If two families of tensors in canonical form with
basis-of-normal-tensors (BNT) separation share the same `μ`-weights, same block count `r`, and
same block dimensions, and
generate *equal* MPVs for all system sizes, then per-block gauge equivalence holds together
with a global gauge equivalence of the block-diagonal tensors.

### Theorem 2: Proportional-MPV Fundamental Theorem (Theorem 4.4)
(`fundamentalTheorem_proportionalMPV_CFBNT`)

**Theorem 4.4 (proportional case)**: If two families of tensors in canonical form with
basis-of-normal-tensors (BNT) separation generate proportional MPVs, and the decomposition
coefficients converge to
nonzero limits, then the block counts are equal and blocks match up to permutation,
dimension equality, and gauge-phase equivalence.

### Theorem 3: Equal MPVs imply proportional MPVs
(`sameMPV₂_implies_proportionalMPV₂`)

Trivial but useful: `SameMPV₂ A B → ProportionalMPV₂ A B` (take `c_N = 1`).

### Theorem 4: Power-sum multiset equality (Lem:app_simple support lemma)

If two same-cardinality sequences of complex numbers have equal power sums for all positive
exponents, their multisets are equal.  For different cardinalities, the positive-power
theorem needs nonzero entries; otherwise positive powers determine only the multiset after
zero entries are deleted.  See `TNLean.Algebra.ScalarPowerSumIdentity`.

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

/-- **Equal-MPV Fundamental Theorem for CF-BNT (Corollary II_cor2, same structure).**

If two families of tensors in canonical form with BNT separation share the same
block weights `μ`, the same number of blocks `r`, and the same block dimensions
`dim`, and generate equal MPV families for all system sizes, then:

(i)  per-block gauge equivalence: `GaugeEquiv (A k) (B k)` for all `k`;
(ii) global gauge equivalence of the block-diagonal tensors.

**Scope restriction (one-copy-per-sector)**: Both families must share the same block
structure `(r, dim, μ)`.  This is the multiplicity-free special case of Cor II.2; the
paper's general theorem does not assume identical block structures as a hypothesis —
it derives them.  The multiplicity recovery (`Lem:app_simple` on `∑_q μ_{j,q}^N`) is
absent.  See `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
-- SCOPE(one-copy-per-sector): requires same (r, dim, μ); paper derives this from BNT.
theorem fundamentalTheorem_equalMPV_CFBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A)
    (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  fundamentalTheorem_canonicalForm μ A B hA.toIsCanonicalForm hA.mu_strict_anti
    hB.block_injective hB.leftCanonical hSame

/-- **Equal-MPV FT for CF-BNT with explicit gauge matrices.**

**Scope restriction (one-copy-per-sector)**: same-structure restriction as
`fundamentalTheorem_equalMPV_CFBNT`; see that theorem's note. -/
-- SCOPE(one-copy-per-sector): same-structure restriction.
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
  fundamentalTheorem_canonicalForm_explicit μ A B hA.toIsCanonicalForm hA.mu_strict_anti
    hB.block_injective hB.leftCanonical hSame

/-! ## Theorem 2: Proportional-MPV Fundamental Theorem (Theorem 4.4)

This is the content of Theorem 4.4 from arXiv:1606.00608 (primitive branch).
The theorem takes convergent coefficient data as explicit hypotheses.
-/

/-- Split-data proportional-MPV Fundamental Theorem for CF-BNT-style data (Theorem 4.4).

This formulation exposes exactly the hypotheses used by the proportional-MPV argument,
separating the BNT matching data from the bundled `IsCanonicalFormBNT` interface. -/
abbrev BlockPermutationGaugeWitness
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k)) : Prop :=
  ∃ _h : rA = rB,
    ∃ perm : Fin rA ≃ Fin rB,
      ∀ j : Fin rA,
        ∃ hdim : dimA j = dimB (perm j),
          GaugePhaseEquiv (d := d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B (perm j))

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
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (a_top_norm_one : ∀ N (h : 0 < rA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (b_top_norm_one : ∀ N (h : 0 < rB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (a_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (b_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1) :
    BlockPermutationGaugeWitness (d := d) A B :=
  fundamentalTheorem_of_separated_CFBNT_data A B
    hA_inj hA_left hA_overlap hA_blocks
    hB_inj hB_left hB_overlap hB_blocks
    ⟨A_total, B_total, aCoeff, bCoeff, c, hA_decomp, hB_decomp, hProp,
      hc_ne, a_top_norm_one, b_top_norm_one, a_norm_le_one, b_norm_le_one⟩

/-- **Proportional-MPV Fundamental Theorem for CF-BNT (Theorem 4.4).**

If two families of tensors in canonical form with BNT separation generate proportional
MPV families (with explicitly supplied decomposition coefficients), then:

(i)  same block count: `rA = rB`;
(ii) there exists a permutation `σ : Fin rA ≃ Fin rB` such that for each block `j`,
     the bond dimensions match and the blocks are gauge-phase equivalent.

**Scope restriction (one-copy-per-sector)**: The caller must supply coefficient arrays
`aCoeff`, `bCoeff` explicitly.  In the paper (arXiv:1606.00608 Thm II.1 / Cor II.2) no
such arrays are supplied as hypotheses — they are derived from the BNT decomposition
(the sum `∑_q μ_{j,q}^N` over copies in each sector).  Additionally, `IsCanonicalFormBNT`
forces `r_j = 1`, so the Newton–Girard multiplicity recovery (`Lem:app_simple`) is never
invoked.  This theorem has two `sorry`s in its proof chain at `NonzeroOverlap.lean` from
the paper-realignment PR.  See `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
-- SCOPE(one-copy-per-sector): explicit coefficient arrays are extra hypotheses not in paper;
-- r_j = 1 forced by IsCanonicalFormBNT; sorry'd chain at NonzeroOverlap.lean.
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
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (a_top_norm_one : ∀ N (h : 0 < rA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (b_top_norm_one : ∀ N (h : 0 < rB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (a_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (b_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1) :
    BlockPermutationGaugeWitness (d := d) A B :=
  fundamentalTheorem_of_IsCanonicalFormBNT A B hA hB A_total B_total aCoeff bCoeff c
    hA_decomp hB_decomp hProp hc_ne a_top_norm_one b_top_norm_one a_norm_le_one b_norm_le_one

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
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (a_top_norm_one : ∀ N (h : 0 < rA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (b_top_norm_one : ∀ N (h : 0 < rB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (a_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (b_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1) :
    BlockPermutationGaugeWitness (d := d) A B :=
  fundamentalTheorem_of_separated_normalCFBNT_data A B
    hA_ncf hA_blocks hB_ncf hB_blocks
    ⟨A_total, B_total, aCoeff, bCoeff, c, hA_decomp, hB_decomp, hProp,
      hc_ne, a_top_norm_one, b_top_norm_one, a_norm_le_one, b_norm_le_one⟩

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
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (hc_ne : ∀ N, c N ≠ 0)
    (a_top_norm_one : ∀ N (h : 0 < rA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (b_top_norm_one : ∀ N (h : 0 < rB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (a_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (b_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1) :
    BlockPermutationGaugeWitness (d := d) A B :=
  fundamentalTheorem_of_IsNormalCanonicalFormBNT A B hA hB
    A_total B_total aCoeff bCoeff c
    hA_decomp hB_decomp hProp hc_ne a_top_norm_one b_top_norm_one a_norm_le_one b_norm_le_one

/-! ## Theorem 3: Equal MPVs imply proportional MPVs -/

/-- **Equal MPVs imply proportional MPVs** (trivially, with proportionality constant `1`).

This is useful for reducing Corollary II_cor2 to the proportional case of Theorem 4.4. -/
theorem sameMPV₂_implies_proportionalMPV₂
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : SameMPV₂ A B) :
    ProportionalMPV₂ A B := by
  intro N
  exact ⟨1, fun σ => by simpa using h N σ⟩

/-- **Equal-MPV upgrade of the current formalized proportional FT for CF-BNT.**

The literature-level equal-MPV FT (`thm:ft_equal` in the blueprint) should start from only the
CF-BNT data and `SameMPV₂`.  The current local results are weaker: the available proportional FT
`fundamentalTheorem_proportionalMPV_CFBNT` still requires explicit decomposition coefficients,
and its conclusion is a block permutation together with per-block `GaugePhaseEquiv` data.

This theorem states the equal-case conclusion derivable from those results.  Under the same
coefficient hypotheses, equal MPVs force the phase-corrected weights to match blockwise.  After
reindexing the `B`-family by the permutation, the assembled tensors are globally gauge equivalent.

**Scope restriction (one-copy-per-sector)**: Inherits all restrictions of
`fundamentalTheorem_proportionalMPV_CFBNT`: `IsCanonicalFormBNT` forces `r_j = 1`, explicit
coefficient arrays are extra hypotheses, and the sorry'd chain from `NonzeroOverlap.lean`
propagates here.  Not the paper's Cor II.2.  See `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
-- SCOPE(one-copy-per-sector): inherits sorry'd chain and r_j=1 restriction from proportional FT.
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
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μA A) σ = ∑ j : Fin rA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv (toTensorFromBlocks μB B) σ = ∑ k : Fin rB, (bCoeff N k) * mpv (B k) σ)
    (a_top_norm_one : ∀ N (h : 0 < rA), ‖aCoeff N ⟨0, h⟩‖ = 1)
    (b_top_norm_one : ∀ N (h : 0 < rB), ‖bCoeff N ⟨0, h⟩‖ = 1)
    (a_norm_le_one : ∀ N j, ‖aCoeff N j‖ ≤ 1)
    (b_norm_le_one : ∀ N k, ‖bCoeff N k‖ ≤ 1)
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
    simpa only [one_mul] using hEqual N σ
  obtain ⟨_hcount, perm, hperm⟩ :=
    fundamentalTheorem_proportionalMPV_CFBNT A B hA hB
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)
      aCoeff bCoeff (fun _ => (1 : ℂ))
      hA_decomp hB_decomp hProp
      (fun _ => one_ne_zero)
      a_top_norm_one b_top_norm_one a_norm_le_one b_norm_le_one
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
              simpa only [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μA A σ
        _ = mpv (toTensorFromBlocks μB B) σ := hEqual N σ
        _ = ∑ k : Fin rB, (μB k) ^ N * mpv (B k) σ := by
              simpa only [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μB B σ
        _ = ∑ j : Fin rA, (μB (perm j)) ^ N * mpv (B (perm j)) σ := by
              exact
                (Equiv.sum_comp perm (fun k : Fin rB => (μB k) ^ N * mpv (B k) σ)).symm
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
      simpa only [Finset.sum_sub_distrib, sub_smul] using (sub_eq_zero.mpr hsums)
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
        μA j ^ (N0 + 1) * μA j = μA j ^ ((N0 + 1) + 1) := by ring
        _ = (μB (perm j) * ζ j) ^ ((N0 + 1) + 1) := hpow2
        _ = (μB (perm j) * ζ j) ^ (N0 + 1) * (μB (perm j) * ζ j) := by ring
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
            simp only [Bweighted, Acast, hX j i, smul_smul, mul_comm, mul_assoc]
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
            simp only [Aweighted, Acast, Algebra.mul_smul_comm,
              Algebra.smul_mul_assoc, Matrix.mul_assoc]
  refine ⟨perm, hdim, ?_⟩
  have hGaugeWeighted :=
    gaugeEquiv_toTensorFromBlocks_of_blockConj (d := d) (μ := fun _ : Fin rA => (1 : ℂ))
      Aweighted Bweighted X hWeightedConj
  have hA_tot :
      toTensorFromBlocks μA (fun j => cast (congr_arg (MPSTensor d) (hdim j)) (A j)) =
        toTensorFromBlocks (fun _ : Fin rA => (1 : ℂ)) Aweighted := by
    ext i
    simp only [toTensorFromBlocks, Aweighted, Acast, one_smul]
  have hB_tot :
      toTensorFromBlocks (fun j => μB (perm j)) (fun j => B (perm j)) =
        toTensorFromBlocks (fun _ : Fin rA => (1 : ℂ)) Bweighted := by
    ext i
    simp only [toTensorFromBlocks, Bweighted, one_smul]
  rw [hA_tot, hB_tot]
  exact hGaugeWeighted

/-! ## Theorem 4: Power-sum multiset equality (Lem:app_simple support lemma)

This provides the power-sum lemmas from `ScalarPowerSumIdentity.lean`.
The bounded same-cardinality version is the common Newton--Girard input.
The nonzero-entry version below compares possibly unequal cardinalities using
positive powers only; without a nonzero-entry hypothesis, positive powers do not
count zero entries.
-/

/-- **Equal power sums imply equal multisets** (same-cardinality support lemma for
`Lem:app_simple` of arXiv:1606.00608).

If two sequences of complex numbers `α : Fin n → ℂ` and `β : Fin n → ℂ` satisfy
`∑ i, (α i)^k = ∑ i, (β i)^k` for all positive `k`, then `α` and `β` have the same
multiset of values (counted with multiplicity).

This is a corollary of Newton's identities via
`Matrix.sum_pow_eq_implies_multiset_eq` from `ScalarPowerSumIdentity.lean`.
The unequal-cardinality Appendix use requires the nonzero-entry version below. -/
theorem power_sum_eq_implies_multiset_eq (n : ℕ)
    (α β : Fin n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i : Fin n, (α i) ^ k = ∑ i : Fin n, (β i) ^ k) :
    Finset.univ.val.map α = Finset.univ.val.map β :=
  Matrix.sum_pow_eq_implies_multiset_eq α β h

/-- **Bounded equal power sums imply equal multisets** (same-cardinality part of
Lemma `Lem:app_simple`).

If two sequences of complex numbers `α : Fin n → ℂ` and `β : Fin n → ℂ` satisfy
`∑ i, (α i)^k = ∑ i, (β i)^k` for `1 ≤ k ≤ n`, then `α` and `β` have the same
multiset of values counted with multiplicity. -/
theorem power_sum_eq_implies_multiset_eq_of_le_card (n : ℕ)
    (α β : Fin n → ℂ)
    (h : ∀ k : ℕ, 0 < k → k ≤ n →
      ∑ i : Fin n, (α i) ^ k = ∑ i : Fin n, (β i) ^ k) :
    Finset.univ.val.map α = Finset.univ.val.map β := by
  apply Matrix.sum_pow_eq_implies_multiset_eq_of_le_card
  intro k hk hkcard
  exact h k hk (by simpa using hkcard)

/-- **Bounded unequal-cardinality power sums imply equal cardinality and equal
multisets** under a nonzero-entry hypothesis.

If two nonzero finite sequences `α : Fin m → ℂ` and `β : Fin n → ℂ` satisfy
`∑ i, (α i)^k = ∑ i, (β i)^k` for `1 ≤ k ≤ max m n`, then `m = n` and the two
sequences have the same multiset of values counted with multiplicity.

The nonzero-entry hypothesis is mathematically necessary for this positive-power
statement: zero entries have no effect on the sums for `k > 0`. -/
theorem power_sum_eq_implies_card_eq_and_multiset_eq_of_le_max_card
    (m n : ℕ) (α : Fin m → ℂ) (β : Fin n → ℂ)
    (hα : ∀ i, α i ≠ 0) (hβ : ∀ i, β i ≠ 0)
    (h : ∀ k : ℕ, 0 < k → k ≤ max m n →
      ∑ i : Fin m, (α i) ^ k = ∑ i : Fin n, (β i) ^ k) :
    m = n ∧ Finset.univ.val.map α = Finset.univ.val.map β :=
  Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card m n α β hα hβ h

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
    ∀ k, SameMPV (A k) (B k) :=
  fun k => GaugeEquiv.sameMPV ((fundamentalTheorem_equalMPV_CFBNT A B hA hB hSame).1 k)

end Corollaries

end MPSTensor
