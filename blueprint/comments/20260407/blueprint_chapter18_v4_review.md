# Blueprint Review — Chapter 18 (Parent Hamiltonians), v4

**Date:** April 8, 2026
**Reviewer standard:** Full protocol (all 8 criteria), formalization-level verification.
**v3 counterpart:** None (new chapter).
**Primary reference:** [PGVWC07] §2.3, §4 (esp. §4.1.2 Theorem 10, §4.1.3, §4.2)
**Secondary:** [CPGSV21] Appendix D; [FNW92]; [KL18]; [Nac96]

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Mixed. PGVWC07 §4.1.2 argument partially reproduced; key step missing. |
| Repetitive/conflicting statements | One: Thm 18.32 and 18.34 overlap in scope without clear separation. |
| Missing clarifications | Several: Thm 18.34 missing hypothesis on L; Thms 18.32–18.33 missing proofs. |
| Deviations from literature | §18.6 uses [KL18] martingale instead of PGVWC07 ν₂ argument (legitimate). |
| Unused/missing definitions | Def 18.30 (periodic chain ground space) is abstract; unclear if used. |
| Structural/logical issues | Unnecessary Ch 16 dependency; multiple proof-less theorems. |
| Statement-by-statement | Detailed below. |
| AI language | Three instances of formalization language leaking into mathematical text. |

---

# Part A — Source classification

Every result in Chapter 18 is classified by its primary source.

## A1. From [PGVWC07] only

| Blueprint | PGVWC07 | Content | Status |
|---|---|---|---|
| Def 18.1–18.2, Lemma 18.3 | §2.3, §4.1 setup | Ground-space map Γ_L, G_L(A), dimension bound | ✅ Correct |
| Lemma 18.5 | §2.3 (L ~ 2 log D/log d) | Nontriviality criterion d^L > D² | ✅ Correct |
| Def 18.6, Lemma 18.7 | §2.3 | Parent interaction h_L = Π_{G_L⊥} | ✅ Correct |
| Lemmas 18.11–18.14 | §2.3 | MPV frustration-freeness | ✅ Correct |
| Lemmas 18.19–18.20 | §4.1.1 (implicit) | Left/right restriction preserves G_L membership | ✅ Correct |
| Thm 18.21–18.22 | §4.1 (C1 condition) | Γ_L injective + dim G_L = D² for injective A | ✅ Correct |
| Thm 18.23 | §4.1.1 core argument | Intersection property | ✅ **Verified at full rigor** |
| Thm 18.34 | §4.1.2 Theorem 10 | Unique ground state (PBC, TI, injective) | **⚠ Incomplete** |
| Thm 18.35–18.36 | §4.1.2 Theorem 10 + blocking | Block-injective / normal unique ground state | **⚠ No proofs** |
| Thm 18.50 | §4.1.3 Theorems 11–12 | Ground space = span of BNT for multi-block | **⚠ Proof compressed** |

## A2. From [CPGSV21] only

| Blueprint | CPGSV21 | Content | Status |
|---|---|---|---|
| Def 18.37–18.38 | Definition 3.9 | Commuting parent Hamiltonian, NNCPH | ✅ Correct |
| Thm 18.39 | Theorem 3.10 | RFP ⟹ NNCPH | ⚠ Declared, not proved; honestly flagged |
| Defs 18.40–18.41 | Appendix D, §D.2 | Decorrelation, commuting PH structure | ✅ Correct |
| Thms 18.42–18.46 | Prop. D.3 and eq. (D.2) | Decorrelation from commuting PH | ✅ Correct |
| Thm 18.33 | §IV.C | Normal tensor reduces range to L₀+1 | ⚠ No proof, cites [CPGSV21] |

## A3. From [KL18] / [Nac96] / [FNW92]

| Blueprint | Source | Content | Status |
|---|---|---|---|
| Thm 18.47 | [KL18] | Martingale criterion for spectral gap | ✅ **Verified at full rigor** |
| Lemma 18.48 | [Nac96], [FNW92] | Martingale condition for MPS (L=2 only) | ✅ for L=2; honestly limited |
| Thm 18.49 | [FNW92], [KL18] | Spectral gap for MPS parent Hamiltonians | ✅ Correct |

## A4. Blueprint-specific (no single source)

| Blueprint | Content | Status |
|---|---|---|
| Defs 18.8–18.10 | Translated local term, chain Hamiltonian, frustration-free | ✅ Standard |
| Defs 18.15–18.18 | Left/right restriction maps, ground conditions | ✅ Standard (formalization bookkeeping) |
| Lemma 18.25 | Iterated contiguous-window intersection | ✅ Correct |
| Defs 18.26–18.28 | MPV submodule, unique ground state | ✅ Standard |
| Thm 18.29 | 1-dimensionality criterion | ✅ Trivial |
| Def 18.30 | Periodic chain ground space (abstract) | ⚠ Unclear usage |
| Thm 18.31 | MPV nonvanishing | ⚠ Proof sketch only |
| Thm 18.32 | Chain ground space = MPV for block-injective | **⚠ No proof** |
| Lemma 18.4 | dim of coefficient-function space | ✅ Trivial |

---

# Part B — Statement-by-statement verification

## §18.1 Local ground space

**Def 18.1–18.2, Lemmas 18.3–18.5**: All correct, elementary. ✅

**TN diagram (Def 18.1, p.131)**: L-node chain, physical legs up, red X node on closing bond. **Verified ✅**.

## §18.2 Parent interaction and chain Hamiltonian

**Defs 18.6–18.10, Lemmas 18.7, 18.11–18.14**: All correct. ✅

**Lemma 18.11 (MPV window membership)**: The proof is correct — the boundary matrix witnessing membership is the product of A-matrices on the complement of the window, and trace cyclicity rotates the window to the front. ✅

## §18.3 Intersection property and unique ground state

### §18.3.1–18.3.2 Restriction maps

**Defs 18.15–18.18**: Standard. ✅

**Lemma 18.19 (Left restriction)**: ψ(σ₁,...,σ_L,j) = tr(A^{σ₁}...A^{σ_L} · A^j · X) = Γ_L(A^j X)(σ). **Verified ✅.** TN diagram correct.

**Lemma 18.20 (Right restriction)**: ψ(i,σ₁,...,σ_L) = tr(A^i A^σ X) = tr(A^σ · XA^i) = Γ_L(XA^i)(σ). **Verified ✅.** TN diagram correct.

### §18.3.3 Injectivity of Γ_L

**Thm 18.21 (Γ_L injective for injective A, L ≥ 1)**:
If Γ_L(X) = 0, then tr(A^σ X) = 0 for all length-L words σ. Since A is injective, the {A^i} span M_D(C), hence {A^σ : |σ|=L} ⊇ M_D(C) (products of spanning sets span). Trace nondegeneracy gives X = 0.

**Verified ✅.**

**⚠ Minor gap for Lean**: The inclusion span{A^σ : |σ|=L} ⊇ M_D(C) for L > 1 is immediate from span{A^i} = M_D(C) and closure under products, but the proof doesn't state this explicitly.

**Thm 18.22 (dim G_L = D²)**: Lemma 18.3 + Thm 18.21. ✅.

### §18.3.4 The intersection property

**Thm 18.23 (Intersection property, L ≥ 2)**:

Full step-by-step verification:

1. **Right ground** → for each i, ∃! Y_i with ψ(i,σ₂,...,σ_{L+1}) = tr(A^{σ₂}...A^{σ_{L+1}} Y_i). Uniqueness by Thm 18.21. ✅
2. **Left ground** → for each j, ∃! Z_j with ψ(σ₁,...,σ_L,j) = tr(A^{σ₁}...A^{σ_L} Z_j). ✅
3. **Matching on (L−1)-site overlap**: ψ(i,σ₂,...,σ_L,j) is expressed both ways. Equating and using that length-(L−1) products span M_D(C) (L−1 ≥ 1 since L ≥ 2) plus trace nondegeneracy: A^j Y_i = Z_j A^i for all i,j. ✅
4. **Decomposition**: From injectivity, 𝟙 = Σ_j c_j A^j (this is Lemma 16.3 in the text, but is immediate from Def 2.20). Then Y_i = 𝟙 · Y_i = Σ_j c_j A^j Y_i = Σ_j c_j Z_j A^i = X' A^i, where X' = Σ_j c_j Z_j. ✅
5. **Conclusion**: ψ(i,σ) = tr(A^σ Y_i) = tr(A^σ X' A^i) = tr(A^i A^σ X') = Γ_{L+1}(X')(i,σ). ✅

**Fully verified. ✅**

**⚠ Unnecessary dependency**: Step 4 cites Lemma 16.3 (Chapter 16). The content is just "injective ⟹ ∃ coefficients c_j with Σ c_j A^j = 𝟙", which is immediate from Definition 2.20. Citing Ch 16 pulls in the Algebraic FT chapter unnecessarily.

### §18.3.5 Unique ground state

**Lemma 18.25 (Iterated intersection)**: Proof by strong induction, merging adjacent windows via Thm 18.23. ✅

**⚠ Hypothesis**: "Non-wrapping" windows only. The wrap-around requires separate treatment (see Thm 18.34 below).

**Def 18.30 (Periodic chain ground space)**: "Intersection over cyclic window positions and outside configurations of comaps of G_L(A) under the cyclic restriction maps." **⚠ Formalization-speak**, not mathematics. Should be stated concretely.

**Thm 18.31 (MPV nonvanishing)**: Proof sketch only. The full argument should be: If V^(N)(A) = 0, then tr(A^σ) = 0 for all |σ| = N. For |w| = N − L₀ and |u| = L₀: tr(A^w A^u) = 0. L₀-block injectivity means {A^u} span M_D, trace nondegeneracy gives A^w = 0. Iterate until reaching I = 0, contradiction. **⚠ Should expand.**

**Thm 18.32 (Chain ground space = MPV submodule for block-injective, L ≥ 2L₀)**: **⚠ NO PROOF.** Essential for the block-injective case.

**Thm 18.33 (Normal tensor, range L₀+1)**: "See [CPGSV21, §IV.C]." **⚠ No proof.** Requires Ch 9–11 machinery.

**Thm 18.34 (Unique ground state, PBC, injective)**: **⚠ THREE ISSUES:**

**(a) Missing hypothesis on L.** Statement says "interaction range L" without a lower bound. Must require L ≥ 2 (from Thm 18.23). PGVWC07 requires L > L₀; for injective A (L₀ = 1), this gives L ≥ 2.

**(b) Missing hypothesis on N.** Says N ≥ 2 but should specify N ≥ L for the Hamiltonian to make sense on the periodic chain.

**(c) Missing proof — the critical PBC step.** The proof says "uses the periodic boundary condition to constrain X to a scalar multiple of I" but **gives no argument**. The required steps (from PGVWC07 Theorem 10):

> After iterating Lemma 18.25, any ground state has the form |φ⟩ = Σ tr(X A^{i₁}...A^{i_N})|i₁...i_N⟩. By TI+PBC, there is no distinguished first site, so one can also write |φ⟩ = Σ tr(A^{i₁}...A^{i_{L₀}} Y A^{i_{L₀+1}}...A^{i_N})|...⟩. By C1 (= injectivity), the two representations give X = Y. But C1 also means {A^{i₁}...A^{i_{L₀}}} span M_D(C), so X commutes with every matrix, hence X = λI.

**This is the heart of the uniqueness theorem and must be written out.**

**Thms 18.35–18.36**: Statements only, no proofs.

## §18.4 Commuting parent Hamiltonians

**Defs 18.37–18.38**: ✅
**Thm 18.39**: Honestly flagged as unproved. ✅ as declaration.

## §18.5 Decorrelation

**Defs 18.40–18.41, Thms 18.42–18.46**: Verified against [CPGSV21] Appendix D. All correct. ✅

## §18.6 Spectral gap

**Thm 18.47 (Martingale criterion)**: **Verified at full rigor ✅.** Proof correctly expands H², separates overlapping/non-overlapping terms, applies martingale condition with row-sum, obtains H² ≥ γH.

**Lemma 18.48 (MPS martingale condition)**: ✅ for L = 2; honestly limited for L > 2.

**⚠ The bound α < 1/2** (Friedrichs cosine for L = 2) is cited to [Nac96] but not proved in the blueprint. For full formalization this is an external dependency that either needs a proof or an axiom.

**Thm 18.49 (Spectral gap)**: Blocks to injective, applies L = 2 martingale. Divisibility L₀|N required. ✅.

## §18.7 Ground space of non-injective MPS

**Thm 18.50 ⊇**: ✅

**Thm 18.50 ⊆**: **Multiple issues.**
1. G_{L₀+1}(A) ⊆ Σ_k G_{L₀+1}(A_k) by block-diagonal structure. ✅
2. Sum is direct — claims orthogonality of block images. **⚠ Requires block separation (Ch 9/12), not cited.**
3. Per-block iteration using Thm 18.36 — but Thm 18.36 has no proof.
4. Threshold N ≥ 2(L₀+1) — PGVWC07 Thm 12 requires N ≥ 3(b−1)(L₀+1)+L. **⚠ Possible bound mismatch.**

---

# Part C — Cleanup checklist

## Must fix

| # | Item |
|---|---|
| **M1** | Thm 18.34: Write out the PBC uniqueness argument (X commutes with all of M_D(C) ⟹ X = λI) |
| **M2** | Thm 18.34: Add hypothesis L ≥ 2 |
| **M3** | Thm 18.32: Provide proof |
| **M4** | Thm 18.23 step 4: Remove Ch 16 dependency; use Def 2.20 directly or state decomposition locally |

## Should fix

| # | Item |
|---|---|
| **S1** | Thm 18.31: Expand proof sketch |
| **S2** | Thm 18.33: Provide proof or explicit reference chain through Ch 9–11 |
| **S3** | Thm 18.50 ⊆: Cite block separation theorems explicitly |
| **S4** | Thm 18.50: Verify threshold N ≥ 2(L₀+1) against PGVWC07 Thm 12 |
| **S5** | Def 18.30: Rewrite in concrete mathematical terms |
| **S6** | Three AI/formalization language items (AI-1, AI-2, AI-3 below) |

## Low priority

| # | Item |
|---|---|
| L1 | Thm 18.21: Explicitly note span{A^σ : |σ|=L} ⊇ M_D(C) |
| L2 | Lemma 18.25: Clarify wrap vs non-wrap |
| L3 | Note [KL18] deviation from PGVWC07 §4.2 |

---

# Part D — AI-language audit

| # | Location | Text | Fix |
|---|---|---|---|
| AI-1 | Thm 18.39 | "The previous declaration MPSTensor.isNNCPH_of_isRFP was removed" | "A previous proof attempt was found incorrect; this result awaits..." |
| AI-2 | Thm 18.43 | "Convenience wrapper... Delegates to Theorem 18.42" | "Corollary of Theorem 18.42..." |
| AI-3 | Def 18.30 | "comaps of G_L(A) under the cyclic restriction maps" | Rewrite as explicit mathematical intersection |

---

# Part E — TN diagram verification

| Location | Description | Status |
|---|---|---|
| Def 18.1 (p.131) | Γ_L(X): L-node chain, physical legs up, red X on closing bond | ✅ |
| Lemma 18.19 (p.134) | Left restriction: L-node chain, red A^j X boundary | ✅ |
| Lemma 18.20 (p.134) | Right restriction: L-node chain, red XA^i boundary | ✅ |
| Thm 18.23 (p.135) | Intersection: (L+1)-node chain, red X' boundary | ✅ |
| Thm 18.34 (p.135) | PBC unique ground state: chain with red X on closing bond | ✅ |

All 5 diagrams valid.

---

# Final assessment

The intersection property (Thm 18.23) and the martingale spectral gap (Thm 18.47) are correctly proved at full rigor. The local ground-space setup (§18.1–18.2) is clean and standard. The decorrelation material (§18.5) is correctly adapted from [CPGSV21].

The chapter falls below the standard of Chapters 2–14 in several respects: (1) the central uniqueness theorem (18.34) is missing its key proof step, (2) three theorems have no proofs, (3) the multi-block theorem has a compressed proof with uncited dependencies, and (4) there is an avoidable cross-chapter dependency on Ch 16. With the fixes in the cleanup checklist, the chapter would be ready for formalization.
