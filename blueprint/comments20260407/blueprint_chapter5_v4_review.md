# Blueprint Review — Chapter 5 (Quantum Channels and Positive Maps), v3 → v4

**Date:** April 7, 2026
**v3 counterpart:** Chapter 4
**Number mapping:** v3 Thm 4.x → v4 Thm 5.x (with offset due to new material)

---

## v3 → v4 Changes

### Substantive changes

**C5-1. Lemma 5.33 proof — more explicit forward references.**
v3 (Lemma 4.33): "multiplicative-domain powers give E(X^n) = μ^n X^n"
v4 (Lemma 5.33): "By Theorem 7.23 (KS equality implies Kraus commutation), X commutes with each Kraus operator; iterating via the left multiplicative identity (Theorem 7.25) gives E(X^n) = μ^n X^n, so μ^n is peripheral."

Assessment: Good improvement — the v3 version was hand-wavy; v4 pins down the exact theorems used. Forward refs to Thm 7.23 and 7.25 need verification. **Checked**: both exist in v4 Ch 7 (Schwarz/multiplicative domain chapter).

**C5-2. New Remark 5.32 (bi-canonical special case).**
Inserted before §5.5.2. Notes that when a map is both unital and TP, the Kadison–Schwarz equality at peripheral eigenvectors (Theorem 7.24) directly shows peripheral eigenvalues are closed under powers. Clarifies the relationship between the simpler bi-canonical argument and the more general adjoint-fixed-point route.

Assessment: Helpful orientation remark. Forward ref to Thm 7.24 verified.

**C5-3. New Thms 5.51–5.55 in §5.8 (Kraus representation).**
Five new theorems extending the Kraus machinery:

- **Thm 5.51** (Orthonormal Kraus transition is unitary): Two HS-orthonormal Kraus families of the same size r, related by K_j = Σ U_{jℓ} K'_ℓ, implies U†U = 1_r. **Verified ✅**: tr(K†_i K_j) = (UU†)_{ji}; orthonormality gives UU† = I; square matrix gives U†U = I.

- **Thm 5.52** (Dual map equality from primal): If Σ B_α X B†_α = Σ A_j X A†_j for all X, then Σ B†_α Y B_α = Σ A†_j Y A_j for all Y. **Verified ✅**: Uses cyclicity of trace and nondegeneracy of trace pairing. Correct.

- **Thm 5.53** (Equal Stinespring Gramians): Specialization of 5.52 at Y = 1. **Verified ✅**. However: proof text says "Specialise kraus_dual_eq_of_map_eq at Y = 1" — this references a **Lean declaration name** instead of Theorem 5.52. **⚠ Formalization language leak** per standing instructions.

- **Thm 5.54** (Rectangular Kraus freedom): **⚠ Dimension/convention error.** The theorem declares V as r₁ × r₂ with V†V = 1, and writes B_α = Σ_j V_{αj} A_j. But {B_α} has r₂ operators (α ∈ Fin(r₂)) and {A_j} has r₁ operators (j ∈ Fin(r₁)), so V_{αj} is naturally an r₂ × r₁ matrix — not r₁ × r₂ as declared. The correct statement should either: (a) declare V as r₂ × r₁ with VV† = I_{r₂}, or (b) keep V as r₁ × r₂ (V†V = I_{r₂}) but write B_α = Σ_j V̄_{jα} A_j (using V†). This will break in Lean if not fixed.

- **Thm 5.55** (General index variant): Inherits the dimension issue from 5.54.

**C5-4. New Lemma 5.57 and Thm 5.58 in §5.9 (Stinespring).**
- Lemma 5.57: Entry formula V_{(i,j),k} = (K_j)_{ik}. Restates Def 5.56 as a lemma. **Verified ✅**: trivially correct.
- Thm 5.58: Stinespring Gram identity V†V = Σ K†_j K_j. **Verified ✅**: (V†V)_{ab} = Σ_{(i,j)} V̄_{(i,j),a} V_{(i,j),b} = Σ_j Σ_i (K̄_j)_{ia} (K_j)_{ib} = Σ_j (K†_j K_j)_{ab}. Correct.

**C5-5. New §5.9.1 — Trace-pairing expansion in transfer-matrix form.**
- Def 5.62 (Trace-self-dual basis): X = Σ_i tr(σ_i X) σ_i. Standard trace-orthonormal basis. **Verified ✅**.
- Def 5.63 (Trace-pairing coefficients): t_{ij} = tr(σ_i T(σ_j)). Standard. **Verified ✅**.
- Thm 5.64 (Expansion): T(ρ) = Σ_{ij} t_{ij} tr(σ_j ρ) σ_i. **Verified ✅**: Expand ρ = Σ_j tr(σ_j ρ) σ_j by trace-self-duality, apply T, expand T(σ_j) = Σ_i tr(σ_i T(σ_j)) σ_i = Σ_i t_{ij} σ_i. Correct.

**C5-6. New §5.10 — Determinant of a quantum channel (Wolf §6.1.1).**
- Def 5.65: Channel determinant (as determinant of the superoperator matrix).
- Def 5.66: Unitary channel T(ρ) = UρU†.
- Thm 5.67: |det T| ≤ 1 for positive TP maps (Wolf Thm 6.1(1)).
- Thm 5.67: |det T| ≤ 1 for positive TP maps (Wolf Thm 6.1(1)). **Verified ✅**: All eigenvalues satisfy |μ| ≤ 1 (standard, [Wol12, Prop 6.1]); |det T| = Π|μ_i| ≤ 1.
- Thm 5.68: |det T| = 1 iff T is a unitary channel (Wolf Thm 6.1(2)). Two issues found:

  **⚠ ERROR in reverse direction proof exponent.** Proof writes |det(U · U†)| = |det U|^{2d²} = 1. The correct exponent is **2D**, not 2d². The eigenvalues of T(X) = UXU† on M_D(C) are {ū_i u_j}_{i,j=1}^D, so det T = (det Ū)^D · (det U)^D, giving |det T| = |det U|^{2D}. The proof confuses d (physical dimension) with D (bond/matrix dimension), or D with D². **Must fix.**

  **⚠ Forward direction proof too compressed.** "Kadison–Schwarz forces each K_i to be a scalar multiple of a unitary" skips: (1) |det T|=1 + all |μ|≤1 → all |μ|=1 → T bijective; (2) T bijective + CPTP → *-automorphism (via KS equality for all eigenvectors); (3) Skolem–Noether → T=U·U†; (4) Kraus freedom → K_i = c_i U. Steps (1)–(2) need expansion for Lean.

**C5-7. New §5.11 — Fixed-point algebra (Wolf Thms. 6.12–6.13).**
Statement-by-statement verification:

- **Def 5.69** (Kraus fixed points): Fix(E) = {X : E(X) = X}. Standard. ✅
- **Thm 5.70** (Fix(E) is a *-subalgebra): E unital + E* has PD fixed point ρ > 0 → Fix(E) is *-subalgebra. **Verified ✅**:
  - Closure under +, scalar mult: linearity. ✅
  - Closure under †: E(X†) = E(X)† for any Kraus map (expand and conjugate), so E(X)=X → E(X†)=X†. ✅
  - Closure under mult: E(X†X) - E(X)†E(X) ≥ 0 by KS (E is unital CP). tr(ρ(E(X†X) - X†X)) = tr(E*(ρ)X†X) - tr(ρX†X) = 0 since E*(ρ) = ρ. So ρ > 0 and gap ≥ 0 forces gap = 0. This puts X in the multiplicative domain, giving E(XY) = E(X)E(Y) = XY. ✅
  - **Note**: the multiplicative domain step uses Thm 7.25 (left mult-domain identity) from Ch 7. This forward dependency is implicit in the proof.

- **Def 5.71** (Adjoint fixed points): Fix(E*) where E*(X) = Σ K†_i X K_i. ✅
- **Thm 5.72** (Fix(E*) is *-subalgebra under E TP + PD fixed point): **Verified ✅**: Apply Thm 5.70 to E*. Check: E* unital ↔ Σ K†_i K_i = I ↔ E is TP (Thm 5.48). (E*)* = E has PD fixed point ρ. Both conditions satisfied.
- **Def 5.73** (Kraus commutant): {X : [X,K_i] = [X,K†_i] = 0 ∀i}. ✅
- **Thm 5.74** (Fix(E*) = Kraus commutant): **Verified ✅**:
  - (⊇): X commutes with all K_i, K†_i → E*(X) = Σ K†_i X K_i = X · Σ K†_i K_i = X (TP). ✅
  - (⊆): Fix(E*) is *-subalgebra (Thm 5.72) → X†X ∈ Fix(E*) → E*(X†X) = X†X → KS equality for E* → X commutes with Kraus operators of E* (which are {K†_i}) → [X, K†_i] = 0. Similarly X† ∈ Fix(E*) gives [X†, K†_i] = 0 → [K_i, X] = 0. ✅

All on FT critical path (used in Ch 9 Wedderburn decomposition).

### Non-substantive changes

**C5-8. Renumbering.** All carried-over content renumbered from 4.x to 5.x with shifted offsets due to insertions.

**C5-9. Citation key change.** [CPGSV17] → [CPGSV17a] in §5.5.2 (Remark 5.35). No content change; likely a bibtex key correction for disambiguation.

**C5-10. §5.12 (QDS pointer).** v3 §4.10 → v4 §5.12, updated "Chapter 13" → "Chapter 15". No content change.

### Unchanged

§5.1 (positive maps/channels), §5.2 (irreducibility), §5.3 (Cesàro), §5.4 (fixed-point projection), §5.5 (peripheral spectrum defs/theorems), §5.5.1 (periodicity removal), §5.6 (representations infrastructure), §5.7 (Choi–Jamiołkowski), existing Stinespring theorems — all verbatim identical to v3 modulo renumbering.

---

## Prior review items status

| Item | v3 status | v4 status |
|---|---|---|
| 4-B: Thm 4.5/5.5 still standalone | Acceptable | Unchanged |
| 4-C: Density matrix properties fragmented | Acceptable | Unchanged |
| 4-F: "Weighted KS equality" phrase | ✅ Fixed in v3 | Remains fixed |
| Lemma 4.33 proof hand-wavy | Partially fixed in v3 | ✅ **Now explicit** (Thms 7.23, 7.25 cited) |

---

## FT-critical-path assessment

- §5.10 (determinant): Not directly on FT path but provides infrastructure for uniqueness arguments.
- §5.11 (fixed-point algebra): **On FT path.** Used in Ch 9 (Wedderburn decomposition, conditional expectations).
- §5.9.1 (trace-pairing expansion): Used in Ch 9 (spectral gap calculations).
- §5.8 new theorems (rectangular Kraus freedom): Used in Stinespring arguments throughout.

---

## Cleanup checklist

| Priority | Item |
|---|---|
| **Must fix** | C5-3: Thm 5.54 dimension/convention error — V declared r₁×r₂ but indexing requires r₂×r₁ |
| **Must fix** | C5-6: Thm 5.68 reverse proof exponent — |det U|^{2d²} should be |det U|^{2D} |
| **Should fix** | C5-6: Thm 5.68 forward proof too compressed — missing steps (1)–(2) for Lean |
| **Should fix** | C5-3: Thm 5.53 proof uses Lean name `kraus_dual_eq_of_map_eq` — should cite Thm 5.52 |
| **Note** | C5-7: Thm 5.70 proof has implicit forward dependency on Ch 7 multiplicative domain (Thm 7.25) |
| Verified ✅ | All forward references (Thms 7.23, 7.24, 7.25, 8.3) |
| Verified ✅ | Thms 5.51, 5.52, 5.57, 5.58, 5.64, 5.67 — all correct |
| Verified ✅ | Thms 5.70, 5.72, 5.74 — all correct (detailed step-by-step) |

---

## Assessment

Chapter 5 is substantially expanded from v3, with all changes being additions rather than modifications. Statement-by-statement verification of all new content found **two errors** and **two items needing expansion**:

1. **Thm 5.54**: Dimension/convention mismatch between declared matrix size (r₁×r₂) and index usage (needs r₂×r₁). Must fix for Lean.
2. **Thm 5.68 reverse proof**: Wrong exponent (2d² instead of 2D). Must fix.
3. **Thm 5.68 forward proof**: Too compressed for formalization — missing the "all eigenvalues on unit circle → *-automorphism" chain. Should expand.
4. **Thm 5.53 proof**: Lean name leak (`kraus_dual_eq_of_map_eq` instead of citing Thm 5.52). Should fix.

The fixed-point algebra results (§5.11) are verified correct at full rigor and are on the FT critical path. All other new theorems verified correct.
