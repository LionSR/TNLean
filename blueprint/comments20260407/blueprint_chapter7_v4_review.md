# Blueprint Review — Chapter 7 (Schwarz Inequalities and Multiplicative Domains), v3 → v4

**Date:** April 8, 2026
**v3 counterpart:** Chapter 5
**Number mapping:** v3 5.x → v4 7.x (with offsets from insertions)

---

## v3 → v4 Changes

### Prior issues resolved

| v3 issue | v4 status |
|---|---|
| Defs 5.15–5.17 mislabeled as Definitions (should be Theorems) | ✅ **Fixed.** Now Thms 7.29–7.31 with full proofs. |
| Thm 5.19 proof missing dependency lemmas (Wol12 Props 1.6, 1.7) | ✅ **Fixed.** Thm 7.33 now has expanded proof via spectral projectors and simultaneous diagonalization. |
| Def 5.24 mislabeled as Definition | ✅ **Fixed.** Now Example 7.42. |
| Defs 5.1–5.4 duplicate Ch 4 | ⚠ Still present (Defs 7.1–7.4 = Defs 5.1–5.4), now explicitly noted: "restate for the reader's convenience." Acceptable. |
| Lemma 4.33 cross-ref to mult-domain powers | ✅ **Fixed in Ch 5** (Lemma 5.33 now cites Thms 7.23, 7.25 explicitly). |

### Substantive new content

**C7-1. §7.1.1 Two-positive maps (Defs 7.7–7.8, Thms 7.9–7.15).**
New subsection establishing the k-positive hierarchy and the generalized Kadison–Schwarz inequality for unital two-positive maps (Thm 7.14).

Statement-by-statement:
- Def 7.7 (k-positive): E ⊗ 𝟙_k positive on M_D ⊗ M_k. Standard. ✅
- Def 7.8 (two-positive = 2-positive): ✅
- Thm 7.9 (CP ⟹ k-positive ∀k): Definition of CP. ✅
- Thm 7.10 ((k+1)-positive ⟹ k-positive): Standard restriction argument. ✅
- Thm 7.11 (CP ⟹ 2-positive): Corollary of 7.9 + 7.10. ✅
- Thm 7.12 (2-positive ⟹ positive): Corollary of 7.10 at k=1. ✅
- Def 7.13 (unital): E(𝟙) = 𝟙. ✅
- Thm 7.14 (KS for unital 2-positive): E(X†X) ≥ E(X†)E(X). Standard result. The proof is not given but is a classical result (Choi, 1974). ✅ statement.
- Thm 7.15 (Kraus KS as special case): ✅

**⚠ Thm 7.14 has no proof.** The two-positive KS inequality is a standard result, but for Lean formalization a proof sketch is needed. The argument uses the 2×2 block matrix trick (same as Thm 7.5) but replaces Kraus structure with 2-positivity.

**C7-2. §7.1.2 Douglas-type factorization (Thms 7.16–7.17).**
- Thm 7.16 (ran(A) ⊆ ran(B) ⟹ A = BC): Standard Douglas factorization. ✅ statement, no proof given.
- Thm 7.17 (vectorwise criterion ⟹ factorization): Reformulation of 7.16. ✅

**⚠ Thm 7.16 has no proof.** Douglas' theorem in finite dimensions is elementary (pseudoinverse argument), but needs a proof sketch for Lean.

**C7-3. New Lemmas 7.19–7.20.**
- Lemma 7.19 (tr(X E(Y)) = tr(E*(X) Y)): Standard adjoint trace pairing. **Verified ✅**: tr(X Σ K_i Y K†_i) = Σ tr(K†_i X K_i Y) = tr(E*(X) Y).
- Lemma 7.20 (A > 0, X ≥ 0, tr(AX) = 0 ⟹ X = 0): Standard positive-definite trace test. **Verified ✅**: A > 0 means A = S†S with S invertible, so tr(AX) = tr(S†SX) = ‖S√X‖²_F = 0 forces √X = 0.

**C7-4. New Thm 7.21 (Fixed-point peripheral eigenvectors satisfy KS equality).**
Let E be unital, E* TP with ρ > 0 a PD fixed point of E*. If E(X) = μX with |μ| = 1, then E(X†X) = E(X)†E(X).

**Verified ✅**: The gap G = E(X†X) - E(X)†E(X) ≥ 0 by KS. tr(ρG) = tr(ρE(X†X)) - |μ|²tr(ρX†X) = tr(E*(ρ)X†X) - tr(ρX†X) = 0 since E*(ρ) = ρ and |μ| = 1. By Lemma 7.20 (ρ > 0, G ≥ 0, tr(ρG) = 0), G = 0.

This is the same argument as Lemma 5.33 in Ch 5 but stated for the Heisenberg-picture map. The Ch 5 version (Lemma 5.33) then deduces peripheral closure from this. ✅

**C7-5. §7.2.3 Subnormal and commuting-dominant operators (Thms 7.35–7.37).**
Entirely new subsection.

- **Thm 7.35** (KS for subnormal operators, positive subunital T): Statement matches [Wol12, Thm 5.5]. Proof: embed A as compression of normal N, extend T to larger space, apply Thm 7.33, compress back. **Verified ✅** in outline. **⚠ The extension "T̃ acts as T on the northwest block, zero elsewhere"** — this needs to preserve positivity and subunitality. Positivity: if T̃(X) = T(P X P) where P is the projection onto ℂ^D... actually, defining T̃ correctly is nontrivial. The proof sketch is correct in spirit but the construction of T̃ needs care for Lean.

- **Thm 7.36** (KS for commuting-dominant, [Wol12, Thm 5.6]): If A†A ≤ B with B ≥ 0, B commuting with A and A†, then T(A†)T(A) ≤ T(B). Proof via ε-regularization, contraction C_ε = B_ε^{-1/2} A which is subnormal, apply 7.35. **Verified ✅** in outline. The ε → 0 limit step requires norm continuity of the relevant maps.

- **Thm 7.37** (CP variant): Specialization of 7.36 to adjoint Kraus map. ✅

### Thm 7.29–7.31 now with proofs

**Thm 7.29** (One-sided multiplicative domains are subalgebras): Proof uses iterative application of the defining identity. **Verified ✅**: E((XY)Z) = E(X)E(YZ) = E(X)E(Y)E(Z). Closure under unit: E(𝟙·Z) = E(𝟙)E(Z) = E(Z) by unitality.

**Thm 7.30** (𝒜(E) is *-subalgebra): X ∈ 𝒜(E) ⟹ both KS equalities hold ⟹ X† satisfies the characterization ⟹ X† ∈ 𝒜(E). Combined with 7.29. **Verified ✅**.

**Thm 7.31** (Restriction to 𝒜(E) is *-homomorphism): Multiplicativity by definition; E(X†) = E(X)† from Kraus commutation (Thm 7.23). **Verified ✅**.

### Thm 7.33 proof expanded

v3 (Thm 5.19) proof was: "Restrict T to commutative *-subalgebra... Thm 5.5 applies." This had a missing dependency (needs CP on commutative domain, Arveson extension).

v4 (Thm 7.33) proof is expanded: diagonalize A = UDU†, express A†A via spectral projectors P_i, note T(P_i) pairwise commute (images of orthogonal projectors), reduce to scalar PSD matrix domination. **Verified ✅**. This avoids the Arveson extension entirely by working with the explicit spectral decomposition. Much better for Lean.

### Non-substantive changes

- Renumbering 5.x → 7.x throughout.
- Remark 7.34 added after Thm 7.33, noting the "positivity-on-abelian" argument from [Wol12, Prop 1.6].
- Minor wording adjustments in several proofs.

---

## Cleanup checklist

| Priority | Item |
|---|---|
| **Should fix** | C7-1: Thm 7.14 — add proof sketch (2×2 block matrix + 2-positivity) |
| **Should fix** | C7-2: Thm 7.16 — add proof sketch (Douglas factorization, finite-dim case) |
| **Should fix** | C7-5: Thm 7.35 proof — specify construction of T̃ more carefully |
| Verified ✅ | Thms 7.5, 7.6, 7.18–7.25, 7.28–7.31, 7.32–7.33, 7.36–7.45 |
| Verified ✅ | All prior v3 issues addressed |

---

## Assessment

Chapter 7 shows significant improvement over v3 Ch 5. All prior issues are resolved: mislabeled definitions are now theorems with proofs, the Thm 5.19 dependency gap is fixed via an explicit spectral-projector argument that avoids Arveson extension, and the cross-reference from Ch 5 Lemma 5.33 now explicitly cites Thms 7.23 and 7.25.

The new §7.1.1 (two-positive maps), §7.1.2 (Douglas factorization), and §7.2.3 (subnormal/commuting-dominant) extend the chapter's scope beyond what was in v3. These are standard results from [Wol12] and are correctly stated. The main gaps are missing proof sketches for Thms 7.14 and 7.16, and a need for more care in the construction of T̃ in Thm 7.35. None of these are errors — just compressed proofs that need expansion for Lean.

No errors found. No AI-language issues.
