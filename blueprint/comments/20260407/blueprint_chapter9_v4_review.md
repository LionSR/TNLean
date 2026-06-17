# Blueprint Review — Chapter 9 (Spectral Gap and Block Separation), v3 → v4

**Date:** April 8, 2026
**v3 counterpart:** Chapter 7
**Number mapping:** v3 7.x → v4 9.x (offset +2, plus insertions)

---

## Number mapping (v3 → v4)

| v3 | v4 | Content | Change |
|---|---|---|---|
| Def 7.1 | Def 9.1 | Mixed transfer operator | Renumbered |
| Def 7.2 | Def 9.2 | Rectangular mixed transfer | Renumbered |
| Rmk 7.3 | Rmk 9.3 | Self-transfer identity | Renumbered |
| Thm 7.4 | Thm 9.4 | Iterated mixed transfer | Renumbered |
| Thm 7.5 | Thm 9.5 | Matrix trace at identity | Renumbered |
| Lemma 7.6 | Lemma 9.6 | Trace expansion over matrix units | Renumbered |
| Thm 7.7 | Thm 9.7 | Overlap = transfer trace | Renumbered |
| Thm 7.8 | Thm 9.8 | Rectangular overlap = transfer trace | Renumbered |
| Lemma 7.9 | Lemma 9.9 | Word trace as entrywise inner product | Renumbered |
| — | **Def 9.10** | **Frobenius norm squared** | **New** |
| — | **Lemma 9.11** | **Trace formula for Frobenius norm** | **New** |
| — | **Def 9.12** | **Euclidean-space embedding** | **New** |
| — | **Lemma 9.13** | **Norm of embedded matrix** | **New** |
| Thm 7.10 | Thm 9.14 | Eigenvalue bound | Renumbered |
| Thm 7.11 | Thm 9.15 | Spectral radius bound | Renumbered |
| Thm 7.12 | Thm 9.16 | ρ≥1 ⇒ gauge-phase equiv | **Proof expanded** (5-step structure) |
| Thm 7.13 | Thm 9.17 | Strict spectral gap | Renumbered |
| Thm 7.14 | Thm 9.18 | Rectangular spectral gap | **Proof expanded** (ker argument explicit) |
| Thm 7.15 | Thm 9.19 | Rectangular overlap decay | Renumbered |
| Thm 7.16 | Thm 9.20 | Transfer powers → 0 | Renumbered |
| Thm 7.17 | Thm 9.21 | Overlap decay | Renumbered |
| Rmk 7.18 | Rmk 9.22 | Cross-correlation decay | Renumbered |
| Rmk 7.19 | Rmk 9.23 | Self-correlation persists | Renumbered |
| — | **Thms 9.24–9.29** | **Irreducible-TP spectral gap** | **New §9.8** |
| — | **Defs 9.30–9.31, Lem 9.32, Thms 9.33–9.40** | **Conditional expectation** | **New §9.9** |
| — | **Thm 9.41, Defs 9.42–9.43, Thm 9.44, Rmk 9.45** | **Stationary support** | **New §9.10** |
| — | **Thms 9.46–9.48** | **Wedderburn decomposition** | **New §9.11** |
| — | **Thms 9.49–9.51, Rmk 9.52, Thm 9.53** | **Wolf Ch 6 equivalences** | **New §9.12** |
| — | **Lem 9.54–9.55, Thms 9.56–9.75** | **Peripheral eigenvalue structure** | **New §9.13** |
| Thm 7.20 | Thm 9.76 | Complementary gap ⇒ Tr→1 | Renumbered |
| Thm 7.21 | Thm 9.77 | Self-overlap convergence | Renumbered |

---

## v3 → v4 Changes

### Prior issues resolved

| v3 issue (from `blueprint_chapter7_v3_review.md`) | v4 status |
|---|---|
| 7-S1: Thm 7.12 proof compressed (block-embedding KS argument in one paragraph) | ✅ **Structurally fixed.** Thm 9.16 now has explicit 5-step proof. **⚠ However**, the explicit gauging formulas in Step 1 have swapped exponents — see C9-I0. The proof outline is correct; only the formulas need correction. |
| 7-S2: Thm 7.14 proof compressed (ker argument implicit) | ✅ **Fixed.** Thm 9.18 now explicitly constructs the ker(X') invariance argument: v ∈ ker(X') ⟹ B'ⁱv ∈ ker(X') for all i ⟹ ker(X') invariant under M_{D₂}(ℂ) ⟹ ker(X') = {0}. The adjoint argument for X'† is also stated. |
| 6-A: Defs 7.1/7.2 still separate | Unchanged. Defs 9.1/9.2 remain separate. Acceptable for Lean (different types). |

### Substantive new content

**C9-1. §9.3 Frobenius norm infrastructure (Def 9.10, Lemma 9.11, Def 9.12, Lemma 9.13).**
Four new statements providing the Hilbert–Schmidt norm foundations used in the eigenvalue bound proof. All trivial and correct. The "Re" in Lemma 9.11 (‖X‖²_F = Re tr(X†X)) is technically correct since tr(X†X) is already real and non-negative for any matrix X, but the "Re" is unnecessary. Not an error — just a Lean convenience (avoids needing the lemma that tr(X†X) ∈ ℝ). ✅

**C9-2. §9.8 Spectral gap under irreducible-TP hypotheses (Thms 9.24–9.29).**
Six new theorems paralleling the injective spectral-gap results (§9.4–9.6) but under the weaker hypothesis of irreducibility + TP normalization, following [CPGSV17b].

Statement-by-statement:
- **Thm 9.24** (gauge-equiv from irreducible-TP ρ≥1): Correct statement. The proof sketch says "uses PF fixed points which are PD under irreducibility" and "Cauchy–Schwarz–KS chain yields PD intertwiner." **⚠ The proof is compressed.** It defers to Thm 9.16 but the crucial adaptation — how irreducibility replaces injectivity in the invertibility step (Step 4 of 9.16) — deserves more detail. Under injectivity, X'†X' is PD because it's a nonzero PSD fixed point of an injective channel. Under irreducibility, X'†X' is PD because it's a nonzero PSD fixed point of an irreducible channel (Thm 8.3 upgrades PSD to PD). The spanning argument for X' being an intertwiner is different: injectivity gives Kraus-span = M_D, while irreducibility gives this only eventually (via Wielandt/Burnside). But the intertwining identity A'ⁱX' = X'B'ⁱ for all i is immediate from the Kraus commutation and does not need spanning. So injectivity is actually not needed for the intertwining step — only for the invertibility step, where irreducibility suffices via Thm 8.3. The logic is correct but the proof sketch doesn't articulate this distinction.
- **Thm 9.25** (strict gap, irreducible-TP): Contrapositive of 9.24. ✅
- **Thm 9.26** (transfer power decay, irreducible-TP): Gelfand formula. ✅
- **Thm 9.27** (overlap decay, irreducible-TP): Combine 9.25 + 9.7. ✅
- **Thm 9.28** (rectangular gap, irreducible-TP): **⚠ The proof uses "{B'ⁱ} spans M_{D₂}(ℂ) (irreducibility)" to deduce ker(X') is trivial.** But irreducibility does not give spanning of M_D by the Kraus operators — it gives that no nontrivial projection is invariant. The ker(X') argument works differently: ker(X') is invariant under all B'ⁱ, and irreducibility of the channel means no nontrivial invariant subspace, so ker(X') = {0} or ℂ^{D₂}. This is the correct argument, but the parenthetical "(irreducibility)" is a misnomer for "Kraus-spans M_{D₂}(ℂ)." More precisely: {B'ⁱ} need not span M_{D₂} — the correct statement is that the channel ℰ_B has no nontrivial invariant projection, so ker(X') being B'-invariant forces it to be trivial. The text conflates irreducibility with injectivity here. The conclusion is correct but the stated reason is imprecise.
- **Thm 9.29** (rectangular overlap decay, irreducible-TP): Combine 9.28 + 9.8. ✅

**C9-3. §9.9 Conditional expectation (Defs 9.30–9.31, Lemma 9.32, Thms 9.33–9.40).**
Scalar conditional expectation E_σ(X) = tr(σX)/tr(σ) · 𝟙. This is the primitive-case conditional expectation from [Wol12, Thm 6.15].

- **Lemma 9.32 restates the definition.** E_σ(X) = tr(σX)/tr(σ) · 𝟙 is literally the content of Def 9.31. This is not a mathematical error — it's a Lean convenience (the definition is opaque; the lemma unfolds it). Acceptable. ✅
- **Thm 9.37** (E_σ ∘ T* = E_σ if T(σ) = σ): Verified. E_σ(T*(X)) = tr(σT*(X))/tr(σ) · 𝟙 = tr(T(σ)X)/tr(σ) · 𝟙 = tr(σX)/tr(σ) · 𝟙 = E_σ(X). ✅
- **Thm 9.38** (T* ∘ E_σ = E_σ if T is TP): Verified. T*(E_σ(X)) = T*(c·𝟙) = c·T*(𝟙) = c·𝟙 = E_σ(X), using T* unital ⟺ T TP. ✅
- **Thm 9.40** (E_ρ is conditional expectation onto Fix(T*)): Statement correct for the scalar fixed-point case. The hypothesis "every adjoint fixed point is scalar" is the key restriction — this is the primitive case. Matches [Wol12, Thm 6.15] restricted to the one-block case. ✅

**C9-4. §9.10 Stationary support (Thm 9.41, Defs 9.42–9.43, Thm 9.44, Rmk 9.45).**

- **Thm 9.41** (support projection invariance): The proof correctly derives (𝟙−P)K_i P = 0 from E(ρ) = ρ with ρ ≥ 0. **Verification**: E(ρ) = Σ K_i ρ K_i†. Since ρ = PρP (support), each summand K_i ρ K_i† has range in range(K_i P). The sum equals ρ with range in range(P), so (𝟙−P) K_i ρ K_i† (𝟙−P) = 0 for each i. Since ρ > 0 on range(P), this gives (𝟙−P) K_i P = 0. Then K_i P = P K_i P, so P E(PXP) P = Σ P K_i PXP K_i† P = Σ K_i PXP K_i† = E(PXP). ✅
- **Def 9.42** (stationary state): Defines ρ_∞ as the unique PD density-matrix fixed point for irreducible E. Uniqueness from Thm 8.9 (QPF). ✅
- **Thm 9.44** (supp(ρ_∞) = 𝟙): Correct. P invariant by Thm 9.41; irreducibility forces P ∈ {0, 𝟙}; ρ_∞ ≠ 0 forces P = 𝟙. ✅
- **Rmk 9.45**: Defers Props 6.10–6.11 of [Wol12]. Acceptable.

**C9-5. §9.11 Wedderburn decomposition (Thms 9.46–9.48).**
- **Thm 9.46**: Fix(T*) is semisimple. Standard (finite-dimensional *-subalgebra of M_D(ℂ) is semisimple). **No proof given.** For Lean, this follows from finite-dimensional *-algebra theory.
- **Thm 9.47**: Abstract Wedderburn–Artin. Standard. **No proof given.** Matches [Wol12, Thm 6.14].
- **Thm 9.48**: Concrete block decomposition. Matches [Wol12, Eq. 1.39]. **No proof given.**

**⚠ All three statements lack proofs.** They are standard algebraic results, but for Lean formalization the Wedderburn decomposition is a substantial piece of infrastructure. The blueprint should at minimum cite the proof route (Artin–Wedderburn for semisimple algebras, then embedding via the *-algebra structure).

**C9-6. §9.12 Additional Wolf equivalences (Thms 9.49–9.53).**
- **Thm 9.49** (exponential positivity ⟺ irreducibility): Matches [Wol12, Thm 6.2(3)]. **No proof.** Standard but nontrivial (the converse direction uses the Lie–Trotter product formula or direct spectral analysis).
- **Thm 9.50** (primitivity ⟺ eventual full Kraus rank): Matches [Wol12, Thm 6.8]. **No proof.**
- **Thm 9.51** (primitivity ⟺ conjunction of Kraus rank + normality + strong irreducibility): Matches [Wol12, Thm 6.8]. **No proof.**
- **Rmk 9.52**: Notes pairwise equivalences. ✅
- **Thm 9.53** (Wolf Thm 6.15 scalar case): Restates Thm 9.40 with the Wolf citation. Redundant but harmless (gives the explicit [Wol12] theorem number). ✅

**C9-7. §9.13 Peripheral eigenvalue group structure (Lemmas 9.54–9.55, Thms 9.56–9.75).**
This is a large new section covering [Wol12, Thm 6.6] and the cyclic decomposition.

Key verifications:
- **Lemma 9.54** (peripheral eigenvectors invertible): Verified. E(X†X) = X†X by KS equality (since |μ|=1). X†X is nonzero PSD fixed point; irreducibility gives X†X > 0 (Thm 8.3); hence X invertible. ✅
- **Lemma 9.55** (product closure): Verified. X in multiplicative domain by KS, so E(YX) = E(Y)E(X) = (νμ)(YX). YX ≠ 0 since both X, Y are units (Lemma 9.54). ✅
- **Thm 9.56** (cyclic structure): Correct. Finite subgroup of ℂ× is cyclic. Standard. **⚠ Hypothesis: "irreducible unital Schwarz map" — TP is not required.** This is stronger than the Kraus-map statement (Schwarz maps include non-CP maps). Matches [Wol12, Thm 6.6] which works at the Schwarz level. ✅
- **Thm 9.57** (cyclic group + m|D): Adds TP to get the divisibility. Proof via cyclic projections: m equal-trace projections summing to 𝟙 gives m · tr(P₀) = D. ✅
- **Thm 9.58** (period divides D): Extracted from Thm 9.57. ✅

**§9.13.1 Cyclic decomposition declarations (Defs 9.59–9.62, Thms 9.63–9.71):**
These are largely declaration-style statements (no proofs). They declare the existence and properties of the cyclic projection decomposition. For Lean formalization, these serve as theorem signatures that will need proofs filled in.

- **Defs 9.59–9.62**: Corner preservation, corner subspace, restricted corner map, irreducible restriction. Standard operator-algebraic definitions. ✅
- **Thm 9.63** (peripheral unitary eigenvector): Every peripheral eigenvalue admits a unitary eigenvector. This follows from Lemma 9.54 (X invertible) + polar decomposition. **No proof given.** ✅ statement.
- **Thm 9.64** (powers on peripheral orbit): E(Uⁿ) = μⁿUⁿ. Follows from multiplicative domain membership. **No proof given.** ✅ statement.
- **Thm 9.66** (cyclic projections from peripheral unitary): Constructs m orthogonal projections from powers of U. Standard construction: P_k = (1/m) Σ_{j=0}^{m-1} γ^{-jk} U^j. **No proof given.** ✅ statement.
- **Thms 9.67–9.71**: Cyclic decomposition properties (full decomposition, power preservation, irreducibility of sectors, primitivity of sectors, corner invariance). All standard consequences of the cyclic projection construction. **No proofs given for any.** ✅ statements, all matching [Wol12, §6.3].

**§9.13.2 Peripheral group-structure declarations (Thms 9.72–9.75):**
- **Thm 9.72** (product closure): Restates Lemma 9.55. Redundant.
- **Thm 9.73** (inverse closure): Standard (conjugate of peripheral eigenvalue is peripheral, since the channel preserves *). **No proof.**
- **Thm 9.74** (cyclic group + divisibility): Restates Thm 9.57. Redundant.
- **Thm 9.75** (multiplicity one): Proof given — uses multiplicative domain to reduce any γ-eigenvector to a scalar multiple of U. Verified: if E(X) = γX and E(U) = γU with U unitary, then E(XU†) = E(X)E(U†) = γ · γ̄ · XU† = XU†, so XU† is a fixed point. For irreducible unital maps, the fixed-point space is ℂ·𝟙, so XU† = c·𝟙, hence X = cU. ✅

**C9-8. §9.14 Primitive overlap convergence (Thms 9.76–9.77).**
These are the renumbered v3 Thms 7.20–7.21. Cross-references updated: Def 5.20 (fixed-point projection, was Def 4.20 in v3), Thm 5.21 (power decomposition, was Thm 4.21 in v3). Verified correct.

### Unchanged content

§9.1–9.2 (Defs 9.1–9.9), §9.4–9.7 (Thms 9.14–9.23 statements), §9.14 (Thms 9.76–9.77 statements) are verbatim identical to v3 modulo renumbering and cross-reference updates. Verified by text comparison.

### Non-substantive changes

- All theorem numbers shifted +2 from v3 (7.x → 9.x) plus offsets from new §9.3, §9.8–9.13 insertions.
- External cross-references updated: Thm 8.9/8.10 (was 6.9/6.10 in v3), Thm 7.23/7.24/7.25 (was 5.9/5.10/5.11 in v3), Thm 4.9 (was 3.9 in v3), Def 5.20/Thm 5.21 (was Def 4.20/Thm 4.21 in v3), Def 2.16 (was 2.13 in v3), Def 2.34 (was 2.31 in v3).
- DS gauge conceptual fix preserved: the proof gauges A and B separately, and the disclaimer sentence is verbatim: "one gauges the individual transfer maps to unital form; one does not require the mixed transfer map itself to be simultaneously unital and trace-preserving." However, the explicit formula implementing this gauging has swapped exponents — see C9-I0.

---

## Verification of cross-references

| v4 Reference | Target | Verified |
|---|---|---|
| Thm 8.9 | Quantum Perron–Frobenius (line 2016) | ✅ |
| Thm 8.10 | Right-canonical gauge (line 2025) | ✅ |
| Thm 7.23 | Kraus commutation relation | ✅ |
| Thm 7.24 | KS equality for peripheral eigenvectors | ✅ |
| Thm 7.25 | Left multiplicative identity | ✅ |
| Thm 4.9 | Skolem–Noether (line 939) | ✅ |
| Def 5.20 | Fixed-point projection (line 1128) | ✅ |
| Thm 5.21 | Power decomposition (line 1138) | ✅ |
| Def 2.16 | Gauge-phase equivalence | ✅ |
| Def 2.34 | MPV overlap (line 712) | ✅ |
| Def 2.2 | Word evaluation | ✅ |

---

## Issues found

### C9-I0. Thm 9.16 Step 1: gauging exponents are swapped (must fix)

The proof of Thm 9.16 writes:

> A'ⁱ = ρ_A^{1/2} Aⁱ ρ_A^{-1/2}, and similarly for B. Let X' = ρ_A^{1/2} X ρ_B^{-1/2}.

But Theorem 8.10 (right-canonical gauge) says: choose S with SS† = ρ, set A'ⁱ = S⁻¹ Aⁱ S. Taking S = ρ^{1/2} gives **A'ⁱ = ρ^{-1/2} Aⁱ ρ^{+1/2}** — exponents opposite to what is written.

**Three independent checks confirm the error:**

1. **Unitality fails.** Under the blueprint's formula, Σ A'ⁱ(A'ⁱ)† = ρ^{1/2} [Σ Aⁱ ρ⁻¹ (Aⁱ)†] ρ^{1/2} = ρ^{1/2} ℰ_A(ρ⁻¹) ρ^{1/2}. This equals 𝟙 only if ℰ_A(ρ⁻¹) = ρ⁻¹, which is false in general (ρ is a fixed point of ℰ_A, not ρ⁻¹). Under the corrected formula, Σ A'ⁱ(A'ⁱ)† = ρ^{-1/2} ℰ_A(ρ) ρ^{-1/2} = ρ^{-1/2} ρ ρ^{-1/2} = 𝟙. ✓

2. **Eigenvector equation fails.** Under the blueprint's formulas, F_{A'B'}(X') produces ρ_A^{1/2} [Σ Aⁱ X ρ_B⁻¹ (Bⁱ)†] ρ_B^{1/2}, which equals μX' only if ρ_B commutes with X — not given. Under the corrected formulas (A'ⁱ = ρ_A^{-1/2} Aⁱ ρ_A^{1/2}, X' = ρ_A^{-1/2} X ρ_B^{-1/2}), the intermediate ρ factors cancel cleanly: F_{A'B'}(X') = ρ_A^{-1/2} F_{AB}(X) ρ_B^{-1/2} = μX'. ✓

3. **Direct comparison with Thm 8.10's proof.** Thm 8.10 explicitly shows: A'ⁱ = S⁻¹ Aⁱ S with SS† = ρ gives Σ A'ⁱ(A'ⁱ)† = S⁻¹ ρ (S†)⁻¹ = 𝟙. This requires S⁻¹ on the LEFT of Aⁱ, not S.

**Correct formulas:**
- A'ⁱ = ρ_A^{-1/2} Aⁱ ρ_A^{+1/2}
- B'ⁱ = ρ_B^{-1/2} Bⁱ ρ_B^{+1/2}
- X' = ρ_A^{-1/2} X ρ_B^{-1/2}

**Impact:** The proof outline (5-step structure, separate gauging, block KS argument, Skolem–Noether) is correct. Steps 2–5 do not depend on the explicit formula — only on the gauged tensors forming a unital Kraus family and the eigenvector being correspondingly transformed. So this is a formula-level error, not a structural error. The theorem statement is correct; only the explicit gauging formulas in Step 1 need to be fixed.

**Note on the Lean codebase:** It is plausible that the Lean proof uses the correct formulas (via Theorem 8.10 directly) and that only the blueprint text has the swapped exponents. This should be checked.

**On FT critical path:** Yes. Thm 9.16 is the most-cited result from this chapter in the FT proof chain. Thm 9.24 (irreducible-TP variant) defers to the same gauging construction.

### C9-I1. Thm 9.24 proof compressed (should fix)

The proof of Thm 9.24 says "one uses the Perron–Frobenius fixed points (Theorem 8.9), which are positive definite under irreducibility. The Kadison–Schwarz–Cauchy–Schwarz chain then yields a positive-definite intertwiner." This does not spell out which step of the 5-step proof of Thm 9.16 changes under the weaker hypothesis. The key adaptation is: in Step 4, X'†X' is a nonzero PSD fixed point of ℰ_{B'}, and irreducibility (via Thm 8.3) upgrades it to PD, giving invertibility of X'. The spanning argument from injectivity is not needed — the intertwining identity comes from Kraus commutation (Step 3) alone.

**On FT critical path:** Yes (the irreducible-TP versions are used in Chapter 11 for non-injective blocks).

### C9-I2. Thm 9.28 proof: "spans M_{D₂}" parenthetical imprecise (should fix)

The proof says "Since {B'ⁱ} spans M_{D₂}(ℂ) (irreducibility), the kernel of X' is a B'-invariant subspace, forced to be {0}." But irreducibility ≠ Kraus operators span M_D. Irreducibility means: no nontrivial invariant projection for the channel. The correct argument is: ker(X') is a B'-invariant subspace ⟹ the projection onto ker(X') is an invariant projection ⟹ by irreducibility it's 0 or 𝟙 ⟹ ker(X') = {0} since X' ≠ 0.

The text conflates the injectivity argument (from Thm 9.18, where "{B'ⁱ} spans M_{D₂}" is correct) with the irreducibility argument. The conclusion is correct; the stated reason is imprecise.

**On FT critical path:** Yes (same reason as C9-I1).

### C9-I3. §9.11 Wedderburn theorems lack proofs (low priority)

Thms 9.46–9.48 are stated without proof. They are standard algebraic results (Wedderburn–Artin for finite-dimensional *-algebras), but for Lean formalization the proof route matters. At minimum, a proof sketch or a citation to a specific construction is needed.

**On FT critical path:** Indirectly. The Wedderburn decomposition is used in the canonical-form chapter (Ch 11) for the block structure of the fixed-point algebra. However, the primitive case (one block) is sufficient for the main FT, and the multi-block Wedderburn structure is infrastructure for the general canonical form.

### C9-I4. §9.13.1 declarations lack proofs (low priority)

Thms 9.63–9.71 are declaration-style (statement only, no proof). These cover standard cyclic decomposition theory from [Wol12, §6.3]. For Lean, each needs a proof. The proofs are straightforward from the cyclic projection construction P_k = (1/m) Σ γ^{-jk} U^j but should be sketched.

### C9-I5. §9.13.2 redundant theorems (cosmetic)

Thm 9.72 duplicates Lemma 9.55 (product closure). Thm 9.74 duplicates Thm 9.57 (cyclic group + divisibility). These appear to be Lean-oriented redeclarations (possibly with different type signatures or hypotheses). Acceptable for formalization; slightly cluttered as mathematics.

### C9-I6. Lemma 9.32 restates Definition 9.31 (cosmetic)

E_σ(X) = tr(σX)/tr(σ) · 𝟙 is literally the definition. The lemma exists as a Lean `simp` target (unfolding the opaque definition). Acceptable.

---

## AI-language audit

| # | Location | Text | Status |
|---|---|---|---|
| No AI-language issues detected | | | ✅ |

The chapter header is "Spectral Gap and Block Separation" — standard mathematical language. Section titles are descriptive: "Mixed transfer operator," "Frobenius norm infrastructure," "Conditional expectation from a faithful fixed point," etc. No "pipeline," "assembly," or formalization jargon detected.

---

## Formalization notes

### 9-F1. Mixed transfer types (from 6-F1, 7-F1): intact

Defs 9.1 and 9.2 correctly maintain separate Lean types for square and rectangular mixed transfer.

### 9-F2. TP normalization scope (from 6-F2, 7-F2): intact

Chapter preamble explicitly states: "Starting with the spectral-radius estimates, we assume the trace-preserving normalization." §9.1–9.2 are purely algebraic.

### 9-F3. Gelfand formula (from 7-F4): intact

Thms 9.20, 9.26, 9.76 invoke the Gelfand formula. Mathlib status should be checked.

### 9-F4. Schwarz-level hypotheses in §9.13 (new)

Thm 9.56 requires "irreducible unital Schwarz map" — not necessarily CP. This is mathematically correct (Wolf works at the Schwarz level) but in Lean, the Schwarz inequality may need to be carried as a separate hypothesis rather than derived from CP. The CP specialization (Thm 9.57) adds TP. For the MPS application, the channel is always CP+TP, so the Schwarz-level generality is not strictly needed. But it's correct as stated and matches the literature.

---

## Cleanup checklist

| Priority | Item |
|---|---|
| **Must fix** | C9-I0: Thm 9.16 Step 1 — gauging exponents swapped. A'ⁱ = ρ^{1/2} Aⁱ ρ^{-1/2} should be ρ^{-1/2} Aⁱ ρ^{1/2}; similarly X' formula. Check whether the Lean proof is already correct (likely uses Thm 8.10 directly). |
| **Should fix** | C9-I1: Thm 9.24 — expand proof to specify which step of the 9.16 argument changes under irreducibility |
| **Should fix** | C9-I2: Thm 9.28 — fix parenthetical: "irreducibility" not "{B'ⁱ} spans M_{D₂}" |
| Low priority | C9-I3: Thms 9.46–9.48 — add proof sketches for Wedderburn |
| Low priority | C9-I4: Thms 9.63–9.71 — add proof sketches for cyclic decomposition |
| Cosmetic | C9-I5: Thms 9.72, 9.74 redundant with Lem 9.55, Thm 9.57 |
| Cosmetic | C9-I6: Lemma 9.32 = Def 9.31 |
| Verified ✅ | Thms 9.4–9.9, 9.14–9.15, 9.17, 9.19–9.23, 9.25–9.27, 9.29, 9.33–9.41, 9.44, 9.54–9.58, 9.75–9.77 |
| Verified ✅ | Thm 9.16: statement correct, proof structure (Steps 2–5) correct, Step 1 formulas wrong |
| Verified ✅ | All prior v3 issues (7-S1, 7-S2) structurally resolved |
| Verified ✅ | All cross-references correct |
| Verified ✅ | DS gauge conceptual fix preserved (separate gauging, disclaimer sentence intact) |
| Verified ✅ | No AI-language issues |

---

## Assessment

Chapter 9 in v4 is a major expansion of v3 Chapter 7. The original 21 statements (Defs 7.1–Thm 7.21) grow to 77 statements (Defs 9.1–Thm 9.77), nearly quadrupling the chapter. The two most important prior issues — the compressed proofs of Theorems 7.12 and 7.14 — are both structurally resolved: Thm 9.16 now has an explicit 5-step proof structure with named steps, and Thm 9.18 now has an explicit kernel argument.

**One must-fix issue found (C9-I0):** The explicit gauging formulas in Thm 9.16 Step 1 have swapped exponents: the blueprint writes A'ⁱ = ρ^{1/2} Aⁱ ρ^{-1/2} where it should be ρ^{-1/2} Aⁱ ρ^{+1/2} (per Theorem 8.10). This is verified by three independent checks (unitality fails, eigenvector equation fails, direct comparison with Thm 8.10). The proof structure (Steps 2–5) and theorem statement are correct — this is a formula-level error in the newly expanded Step 1, not a conceptual error. The DS gauge conceptual fix (separate gauging of A and B) remains intact. The Lean codebase likely has the correct formulas via direct application of Thm 8.10; this should be checked.

The new content falls into two categories:

1. **Infrastructure for the irreducible-TP spectral gap** (§9.8): six theorems paralleling the injective versions. These are on the FT critical path and are mathematically correct, though the proofs of Thms 9.24 and 9.28 are compressed and contain one imprecise parenthetical (C9-I2).

2. **Wolf Chapter 6 theory** (§9.9–9.13): conditional expectations, stationary support, Wedderburn decomposition, Wolf equivalences, peripheral eigenvalue structure, and cyclic decomposition. This is a substantial block of standard quantum channel theory. Most statements are correctly stated with appropriate [Wol12] citations. Many lack proofs (declaration-only), which is acceptable at the blueprint level but means significant proof work remains for Lean formalization.

Summary: one must-fix (gauging exponents), two should-fix (compressed proof of Thm 9.24, imprecise parenthetical in Thm 9.28), all on the FT critical path. The remainder are low-priority or cosmetic.
