# Scouting Report: arXiv:1606.00608 — Sections 3, 4, Appendices B–D

**Paper**: "Matrix Product Density Operators: Renormalization Fixed Points and Boundary Theories"
**Authors**: Cirac, Perez-Garcia, Schuch, Verstraete (2017, Ann. Phys. 378, 100–149)
**Date of scouting**: 2026-03-25
**Scope**: Everything beyond §2 + Appendix A (already scouted in `factcheck_1606_00608_audit.md`)

---

## Previously Scouted (for reference)

**§2 + Appendix A**: Fundamental Theorem of MPV — canonical forms, BNT, gauge equivalence, Theorem 2.11, Corollary 2.12. **Status: Fully formalized** (CF-BNT families sorry-free; end-to-end pipeline from arbitrary tensor not yet connected).

> **Note on numbering**: This paper uses a single shared counter (Theorem = Definition = Proposition = Corollary = Example) within each section. So §3 items are numbered 3.1–3.14 sequentially across all environment types. We use these actual paper numbers below, with labels like `thm:main-MPS` for cross-reference.

---

## Section 3: Pure States — Renormalization of MPS (lines 373–619)

### §3.1 Renormalization Flow and RFP (Thm 3.1, Def 3.2)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Def 3.2: RFP (pure)** `defRFP` | Tensor A s.t. A^{i₁}A^{i₂} = Σ_j U_{(i₁,i₂),j} A^j for isometry U. Equivalently: E = E² where E is the CPM. | Medium | **Not formalized**. We have CPM composition infrastructure (`Channel/Basic.lean`) and idempotent projection theory (`Channel/FixedPoint/`). |
| **Thm 3.1** `thm:renormalization-flow` | A appears as RG limit ⟺ A^{i₁}A^{i₂} = Σ U A^j (the idempotent condition) | Medium | Not formalized. Proof uses: two Kraus sets give same CPM ⟺ related by physical-index isometry (Stinespring). We have Stinespring in `Channel/Stinespring.lean`. |
| **Convergence of RG flow** (App B) | Starting from CF tensor, blocking always converges | Medium | Not formalized. Uses BNT decomposition + spectral gap (both available). |

### §3.2 Zero Correlation Length (Defs 3.3–3.7, Thm 3.8)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Def 3.3: CID** | Correlations Independent of Distance: ⟨O₁O₂⟩ independent of separation | Easy | Not formalized. |
| **Def 3.5: Local Orthogonality (LO)** `DefLO` | BNT elements satisfy Σ_i A^i_j ⊗ Ā^i_{j'} = 0 for j≠j' | Easy | **Partially present**: `cross_overlap_tendsto_zero` in `MPS/BNT/Construction.lean` proves overlap → 0, which is the asymptotic version. The exact (non-asymptotic) LO is not yet a definition. |
| **Def 3.6: ZCL** | MPS is LO and has CID | Easy | Not formalized as a combined definition. |
| **Def 3.7: Transfer matrix E** | E = Σ_i A^i ⊗ Ā^i (Choi form of CPM) | **Already formalized** | `transferMap` in `MPS/Core/Transfer.lean` is the CPM form E(X) = Σ A^i X A^{i†}. Choi matrix form in `Channel/TransferMatrix.lean`. Mixed transfer `mixedTransferMap` in `Spectral/MixedTransfer.lean`. |
| **Thm 3.8 (ZCL ⟺ E²=E)** `TheoremZCLPure` | For CF tensor: ZCL ⟺ transfer matrix is idempotent | Medium | Not formalized. Forward direction easy from spectral theory. Reverse uses block-injectivity + Lemma app_simple (Newton-Girard, which **we have**: `Algebra/ScalarPowerSumIdentity.lean`). |

**Key observation**: Blueprint ch15 (line 87–91) already notes this equivalence as a remark: "ξ = 0 ⟺ E² = E ⟺ RGFP". Could formalize this cleanly.

### §3.3 Commuting Parent Hamiltonians (Def 3.9)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Parent Hamiltonian** (eq 17) | H_L^(N) = Σ τ_j(P_L^⊥) where P_L^⊥ projects onto orthogonal complement of ground space S_L | Medium | **Partially formalized** in blueprint ch14; `PARENT_HAMILTONIAN_ISSUES.md` tracks 18 tasks across 6 layers. Ground space definition exists. |
| **Def 3.9: Commuting parent Ham** | [τ_j(P_L), P_L] = 0 for j=1,...,L-1. NNCPH = nearest-neighbor case (L=2). | Medium | Not formalized. |
| **biCF → L ≤ 3D⁵ parent Ham** | Direct consequence of Prop 2.10 `propblockinj` (block-injectivity) | Medium | Not formalized (the 3D⁵ bound itself isn't formalized). |

### §3.4 Main Theorems (Thm 3.10, Thm 3.11, Cor 3.12)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Thm 3.10 (RFP ⟺ ZCL ⟺ NNCPH)** `thm:main-MPS` | Three-way equivalence for CF tensors generating MPS | **HIGH VALUE** | Not formalized. RFP⟺ZCL is doable via Thm 3.8. NNCPH⟺RFP uses [Beigi] ground space characterization (external dependency). |
| **Thm 3.11 (RFP structural characterization)** `thm:charact-MPS` | A in CF is RFP ⟺ A^i = ⊕_{j,q} μ_{j,q} X_{j,q} Λ_j U^i_j X_{j,q}^{-1} with isometry condition | Medium-Hard | Not formalized. Proof reduces to Lemma B.1 `lem:charact-NT-pure-RFP` (NT is RFP ⟺ A^i = XΛU^iX^{-1}). Uses E²=E ⟹ E=\|R)(L\| rank-1. |
| **Cor 3.12** `III_cor3` | BNT elements of RFP have form A_j = X_j Λ_j U^i_j X_j^{-1} | Easy (given Thm 3.11) | Not formalized. |
| **MPS form of RFP** (eq 20) | \|V^(N)(A)⟩ = Σ_j (Σ_q e^{iNφ_{j,q}}) U^⊗N \|φ_j⟩^⊗N | Medium | Not formalized. Product state structure after isometry. |

### §3.5 Saturation of the Area Law (Def 3.13, Prop 3.14)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Def 3.13: SAL (pure)** | S_1^(N) = S_2^(N) = ... = S_{N/2}^(N) for von Neumann entropy | Hard (needs entropy) | Not formalized. No von Neumann entropy in codebase. |
| **Prop 3.14 (RFP ⟹ SAL)** `ZCLandSALpure` | Follows from mixed-state case (§4) | Hard | Not formalized. |

---

## Section 4: Mixed States — MPDO (lines 620–1019)

This is the paper's main novel contribution. **None of §4 is formalized.**

### §4.1 MPDO Definition + RFP Definition (Def 4.1)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **MPDO tensor** (eq 22) | Tensor M with 4 indices (2 auxiliary, 2 physical) generating ρ^(N)(M) = tr(M·M·...·M) | Medium | Not formalized. Could be modeled as `MPSTensor (d*d) D` (physical = ket⊗bra) or a dedicated `MPDOTensor d D` structure with hermiticity/PSD constraints. |
| **Def 4.1: RFP (mixed)** `RFPMixedTS` | ∃ tpCPM T,S s.t. S[M₂(X)] = M₁(X) and T[M₁(X)] = M₂(X) | Hard | Not formalized. Requires MPDO infrastructure + tpCPM composition. |
| **Pure case recovery** (eq 28–30) | Def 4.1 reduces to Def 3.2 when MPDO is pure | Medium | Not formalized. |

### §4.2 Boundary Theories (§4.2)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **PEPS definition** | Tensor network on 2D lattice | **Out of scope** | No PEPS infrastructure exists. |
| **Bulk-boundary correspondence** | PEPS RFP ↦ boundary MPDO RFP via transfer operator fixed points | **Out of scope** | Would need 2D TN infrastructure. |
| **Holographic motivation** | RFP MPDO as boundary theory of 2D topological state | Conceptual | Not formalizable without 2D. |

### §4.3 Zero Correlation Length for MPDO (Def 4.2, Def 4.3, Thm 4.4)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Def 4.2: ZCL (mixed)** `DefinitionZCL` | Transfer matrix equation: tr(M·M) = tr(M)·tr(M) (graphical) | Medium | Not formalized. |
| **Def 4.3: PRFP** `def:Puri-RFP` | Purification RFP — M is PRFP if purification A is RFP | Medium | Not formalized. Requires purification construction. |
| **Thm 4.4 (PRFP ⟺ ZCL ⟺ form (27))** | For MPDO with MPS purification | Medium-Hard | Not formalized. |
| **Limitation** | ZCL alone is too weak for mixed states (Example 4.10) | — | — |

### §4.4 Mutual Information & Area Law (Prop 4.5, Thm 4.9)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Prop 4.5 (I_L monotone)** `PropILILp1` | Mutual info I_L ≤ I_{L+1} for MPDO, bounded by 4 log D | Medium (needs entropy) | Not formalized. Proof uses strong subadditivity. |
| **Def 4.6: SAL (mixed)** `def:area-law` | I_1 = I_2 = ... | Easy (given entropy) | Not formalized. |
| **Def 4.7: Simple tensor** | None of BNT elements is nilpotent | Easy | Not formalized. |
| **Def 4.8: GSNNCH** `defrhoNComm` | ρ^(N) ∝ ⊕_x n_x exp(-Σ τ_j(h^(x))) with commuting h | Hard | Not formalized. |
| **Thm 4.9 (main, simple case)** `thm:main-simple` | For simple K in biCF: (i)RFP ⟹ (ii)ZCL+SAL ⟺ (iii)GSNNCH+ZCL ⟹ (iv)structural ⟹ (v)blocked RFP | **VERY HARD** | Not formalized. 500+ lines of proof in Appendix C. |

### §4.5 General Case (Prop 4.13, Thm 4.14, Thm 4.15)

| Item | Description | Formalizability | Our Status |
|------|-------------|-----------------|------------|
| **Prop 4.13 (vertical CF)** `Prop:IV.12` | MPDO tensor in horizontal CF is also in vertical CF; U M̃ U† = ⊕_α μ_α ⊗ M_α | Hard | Not formalized. Uses Lemma L `Lemma-L` (MPV equality ⟹ block equality) + positivity of MPDO. |
| **Thm 4.14 (main, general)** `thm:IV.13` | RFP ⟺ algebra structure ⟺ fusion isometries: O_L(M_α)O_L(M_β) = Σ_γ c_{αβγ}^(L) O_L(M_γ) | **VERY HARD** | Not formalized. This is the paper's headline result. Connects to fusion categories and Levin-Wen string nets. |
| **Thm 4.15 (L-independent c)** | When structure coefficients c_{αβγ} are L-independent: MPDO = Σ λ_i P_i e^{-H_N} with commuting H | **VERY HARD** | Not formalized. |

---

## Appendix B: Proofs of §3 (lines 1203–1311)

| Item | Description | Formalizability | Dependencies |
|------|-------------|-----------------|--------------|
| **RG flow = E↦E² (Thm 3.1)** | CPM identification via Stinespring + blocking = squaring | Medium | Stinespring (have it), isometry equivalence |
| **RG convergence from CF** | BNT decomposition + spectral gap → E^N converges | Medium | BNT (have), spectral gap (have), Newton-Girard (have) |
| **ZCL ⟺ E²=E (Thm 3.8)** `TheoremZCLPure` | Forward: E²=E ⟹ CID obvious from correlation formula. Reverse: E²≠E ⟹ ∃ subleading eigenvalue ⟹ distance-dependent correlations (uses block-injectivity + Newton-Girard) | Medium | Block-injectivity (have), Newton-Girard (have) |
| **Lemma B.1 (NT RFP ⟺ structural)** `lem:charact-NT-pure-RFP` | NT is RFP ⟹ E²=E ⟹ E=\|R)(L\| rank-1 ⟹ A^i = XΛU^iX^{-1}. Key step: CPM→Kraus via isometry | Medium | Fixed point theory (have), Stinespring (have) |
| **Thm 3.10: RFP ⟺ NNCPH** `thm:main-MPS` | Uses [Beigi] characterization of commuting-Hamiltonian ground spaces | Hard | **External dep**: [Beigi] result not in our codebase |

## Appendix C: Proofs of §4 (lines 1312–2090) — THE BIG ONE

This is ~770 lines of dense proofs, the paper's technical core.

### C.1 Proof of Prop 4.5 (I_L monotone) — lines 1316–1321
- Short proof via strong subadditivity. Needs von Neumann entropy + SSA.
- **External dep**: Strong subadditivity inequality.

### C.2 Proof of Thm 4.9 (simple case) — lines 1324–1829

**Case I: K injective (lines 1374–1565)**

| Lemma | Description | Difficulty | Key dependencies |
|-------|-------------|------------|------------------|
| **Prop C.1 (RFP ⟹ ZCL+SAL)** | ZCL from T trace-preserving. SAL from T,S + monotonicity of mutual info. | Medium | tpCPM properties |
| **Lemma C.2 (SAL ⟹ Hayashi decomposition)** | σ₃ = ⊕_k ρ_{Ab₁}^(k) ⊗ ρ_{b₂c}^(k) from SSA equality | Hard | **External dep**: [Hayashi 2003] characterization of SSA equality |
| **Lemma C.3 (SAL ⟹ η structure)** | Injective K + SAL ⟹ ∃ isometry U, tensors r_k,l_k with primitive T matrix | Hard | Hayashi decomposition + injectivity argument |
| **Lemma C.4 (SAL+ZCL ⟹ T rank-1)** | T_{k,h} = a_k b_h with Σ a_k b_k = 1 | Medium | Perron-Frobenius for non-negative matrices |
| **Prop C.5 (structural ⟹ RFP)** | Explicit construction of T and S as compositions of 3 tpCPMs each | Hard | Detailed tpCPM construction |
| **Prop C.6 (SAL ⟹ commuting form)** | σ^(N) ∝ Π B_{n,n+1} with [B,B]=0 | Medium | Direct from η structure |
| **Prop C.7 (commuting+ZCL ⟹ SAL)** | Uses [Beigi] form + ZCL to get SSA equality | Medium | [Beigi] + Hayashi |

**Case II: K simple (lines 1624–1829)**
- Reduces to injective case via BNT element separation
- Key: shows BNT elements satisfy orthogonality (eq. 43), then each generates MPDO with SAL+ZCL

### C.3 Proof of Prop 4.13 (vertical CF) — lines 1830–1922
- **Lemma L**: Y₁V^(N)(A) = Z₁V^(N)(A) for all N ⟹ per-block equality
- Uses block-injectivity + Newton-Girard (both available)
- Positivity of MPDO eliminates p-periodic vectors
- Structural argument for isometry U via gauge comparison

### C.4 Proof of Thm 4.14 (general RFP) — lines 1925–2088
- Most complex proof in the paper
- Uses: vertical CF (Prop 4.13), fixed-point algebra theory ([Wolf Thm 6.14] — **we have this**), block-injectivity, C*-algebra isomorphisms, Newton-Girard
- Constructs explicit T,S maps for (ii)⟹(i) direction

## Appendix D: Additional Results (lines 2091–2299)

### D.1 Alternative RFP Definitions (lines 2096–2177)

| Item | Description | Formalizability |
|------|-------------|-----------------|
| **Gauge-RFP** | Allow gauge transform in T,S definition. Open whether equivalent to Def 4.1 for mixed states. For pure states: equivalent (via E²=E argument). | Medium (pure case) |
| **Strong-RFP** | T,S given by unitary conjugation. Too strong — excludes Fibonacci model. | Low priority |
| **Fibonacci model example** | rank(ρ^(N)) = τ₊^{2N} + τ₋^{2N} (golden ratio), not of form rs^{N-1} | Fun but low priority |

### D.2 Decorrelation ⟺ Commuting Hamiltonians (lines 2181–2290)

| Item | Description | Formalizability |
|------|-------------|-----------------|
| **Def: Decorrelated** | P_{AXB} O_A P_{AXB}^⊥ O_B P_{AXB} = 0 | Easy |
| **Prop D.1** | K_{AXB} corresponds to commuting parent Ham ⟺ regions A,B decorrelated | Medium-Hard |
| **Proof technique** | Uses support projectors, partial traces, commutativity of projectors | Medium |

This is a **dimension-independent** result (not restricted to 1D/MPS). Could be formalized independently.

---

## Formalizability Assessment

### Tier 1: Feasible Now (builds on existing infrastructure)

1. **ZCL ⟺ E²=E (Thm 3.8)** — We have transfer maps, spectral gap, Newton-Girard, block-injectivity. ~200–300 LOC.
2. **RFP definition (pure, Def 3.2)** — Just E²=E in CPM language. ~50 LOC.
3. **Lemma B.1 (NT RFP structural form)** — Uses E²=E ⟹ rank-1 transfer ⟹ Kraus = isometry × diagonal. ~150–200 LOC.
4. **Thm 3.11 (RFP structural characterization)** — Follows from Lemma B.1 + BNT decomposition. ~100 LOC.
5. **Decorrelation definition (Appendix D)** — Pure linear algebra. ~50 LOC.
6. **RG convergence from CF** — Uses existing spectral theory. ~100 LOC.

**Estimated total: ~650–800 LOC**

### Tier 2: Requires Moderate New Infrastructure

1. **Thm 3.10 partial: RFP ⟺ ZCL** — Tier 1 items give both directions. ~50 LOC glue.
2. **MPDO tensor definition** — Extend MPSTensor to 4-index tensors with hermiticity/positivity. ~100–200 LOC.
3. **ZCL for MPDO (Def 4.2)** — Straightforward given MPDO definition. ~50 LOC.
4. **Purification RFP (Def 4.3, Thm 4.1)** — Connect MPS purification to MPDO via partial trace. ~200–300 LOC.
5. **Prop D.1 (decorrelation ⟺ commuting Ham)** — Self-contained linear algebra proof. ~300–400 LOC.

**Estimated total: ~700–950 LOC**

### Tier 3: Requires Significant External Dependencies

1. **Thm 3.10: NNCPH ⟺ RFP** — Needs [Beigi] characterization of commuting-Hamiltonian ground spaces.
2. **von Neumann entropy + strong subadditivity** — Major Mathlib gap. Required for SAL/mutual info.
3. **Hayashi SSA equality characterization** — External dep for Lemma C.2.
4. **Thm 4.9 (simple MPDO case)** — Needs all of the above.

### Tier 4: Very Hard / Out of Scope

1. **Thm 4.14 (general MPDO RFP ⟺ algebra)** — Paper's headline theorem. ~800+ LOC. Needs all of Tier 3 plus C*-algebra isomorphism theory.
2. **Fusion categories / Levin-Wen connection** — Abstract algebra far beyond current scope.
3. **PEPS / boundary theory correspondence** — Needs 2D tensor network infrastructure.

---

## Recommended Formalization Path

### Phase 1: Pure-state RFP characterization (~800 LOC)
**Goal**: Formalize Thm 3.8 (ZCL⟺E²=E) and Thm 3.11 (RFP structural form)

1. Define `IsRFP A` := `transferMap A ∘ transferMap A = transferMap A` (or CPM version)
2. Define `IsZCL A` := `IsLocallyOrthogonal A ∧ IsCID A`
3. Prove ZCL ⟺ E²=E for CF tensors
4. Prove NT + RFP ⟹ A^i = XΛU^iX^{-1} (Lemma B.1 `lem:charact-NT-pure-RFP`)
5. Prove full structural characterization (Thm 3.11 `thm:charact-MPS`)
6. Add to blueprint as new chapter or extend ch14/ch15

**All dependencies available**: transfer maps, spectral theory, BNT, Newton-Girard, Stinespring, fixed-point projections.

### Phase 2: Parent Hamiltonian connection (if [Beigi] available)
**Goal**: Complete Thm 3.10 three-way equivalence

### Phase 3: MPDO foundations (~500 LOC)
**Goal**: Define MPDO tensor, ZCL for mixed states, purification RFP

### Phase 4: Decorrelation theorem (~400 LOC)
**Goal**: Formalize Appendix D (dimension-independent, self-contained)

---

## External Dependencies Needed

| Dependency | Used In | Status in Mathlib |
|------------|---------|-------------------|
| von Neumann entropy S(ρ) = -tr(ρ log ρ) | SAL, mutual info | **Not in Mathlib** |
| Strong subadditivity of vN entropy | Prop 4.5, Lemma C.2 | **Not in Mathlib** |
| Hayashi SSA equality characterization | Lemma C.2 | **Not in Mathlib** |
| [Beigi] commuting-Ham ground space form | Thm 3.10 (iii)⟹(i) | **Not in Mathlib** |
| Stinespring dilation theorem | Thm 3.1 | **Available** in `Channel/Basic.lean` |
| Newton-Girard / power-sum identity | Multiple proofs | **Available** in `ScalarPowerSumIdentity.lean` |
| Wolf Thm 6.14 (fixed-point algebra) | Thm 4.14 proof | **Available** in `Channel/FixedPoint/Algebra.lean` |

---

## Key Takeaway

**§3 (pure RFP)** is the sweet spot: Thm 3.8 + Thm 3.11 are **immediately formalizable** with existing infrastructure, give clean mathematical results (ZCL ⟺ E²=E, structural decomposition), and extend the project's coverage of the paper significantly.

**§4 (mixed MPDO)** is the paper's headline contribution but requires substantial new infrastructure (entropy, SSA, MPDO definitions). The general Thm 4.14 connecting to fusion categories is a long-term goal.

**Appendix D** (decorrelation ⟺ commuting Hamiltonians) is a nice self-contained result that could be formalized independently of everything else.

---

## Proposed Modular Structure

Following the existing codebase conventions (`TNLean/MPS/{Topic}/{File}.lean`), here is a modular layout. Modules are grouped by dependency tier so that each tier can be completed and compiled independently.

### Tier 1 — Pure-state RFP (new directory: `MPS/RFP/`)

```
TNLean/MPS/RFP/
├── Defs.lean                    -- §3.1: IsRFP, IsIdempotentCPM
├── ZeroCorrelationLength.lean   -- §3.2: IsCID, IsLocallyOrthogonal, IsZCL, Thm 3.8 (ZCL ⟺ E²=E)
├── StructuralForm.lean          -- §3.4 + Lem B.1: NT RFP ⟹ A^i = XΛU^iX^{-1}; full CF structural char
├── Convergence.lean             -- App B: RG flow convergence from CF (E^N → idempotent)
└── Assembly.lean                -- Thm 3.10 partial: RFP ⟺ ZCL (two-way; NNCPH direction deferred)
```

**Dependency graph (Tier 1)**:
```
                  MPS/Defs
                  MPS/Core/Transfer
                  MPS/BNT/*
                  Channel/Basic (Stinespring)
                  Channel/FixedPoint/*
                  Spectral/SpectralGap
                  Algebra/ScalarPowerSumIdentity
                     │
              ┌──────┼──────┐
              ▼      ▼      ▼
           Defs   ZCL    Convergence
              │      │
              ▼      ▼
         StructuralForm
              │
              ▼
           Assembly
```

**File details**:

| File | Paper ref | Key definitions/theorems | Est. LOC | Imports from existing |
|------|-----------|-------------------------|----------|-----------------------|
| `Defs.lean` | Def 3.2 | `IsRFP (A : MPSTensor d D)`, `IsIdempotentCPM` (E²=E), equivalence of the two defs via Stinespring | ~80 | `MPS/Defs`, `MPS/Core/Transfer`, `Channel/Stinespring` |
| `ZeroCorrelationLength.lean` | Defs 3.3–3.7, Thm 3.8 | `IsCID`, `IsLocallyOrthogonal`, `IsZCL`, `zcl_iff_idempotent_transfer` | ~250 | `MPS/Core/Transfer`, `MPS/BNT/*`, `Spectral/SpectralGap`, `Algebra/ScalarPowerSumIdentity` |
| `StructuralForm.lean` | Thm 3.11, Lem B.1, Cor 3.12 | `rfp_nt_structural` (A^i = XΛU^iX^{-1}), `rfp_cf_structural` (full block form), `rfp_bnt_structural` | ~200 | `RFP/Defs`, `RFP/ZeroCorrelationLength`, `Channel/FixedPoint/*`, `MPS/BNT/*` |
| `Convergence.lean` | App B (RG convergence) | `rg_flow_converges_of_cf` | ~120 | `MPS/Core/Transfer`, `MPS/BNT/*`, `Spectral/SpectralGap` |
| `Assembly.lean` | Thm 3.10 (partial) | `rfp_iff_zcl` (bidirectional), placeholder for NNCPH | ~80 | `RFP/Defs`, `RFP/ZeroCorrelationLength`, `RFP/StructuralForm` |

### Tier 2 — Parent Hamiltonian infrastructure (extend `MPS/ParentHamiltonian/`)

```
TNLean/MPS/ParentHamiltonian/
├── Correlations.lean            -- EXISTING: one-point, two-point, connected correlator
├── GroundSpace.lean             -- NEW §3.3: S_L ground space, P_L^⊥ projector
├── FrustrationFree.lean         -- NEW: frustration-freeness, parent Hamiltonian H_L^(N)
├── Commuting.lean               -- NEW §3.3: commuting parent Ham, NNCPH definition
└── Decorrelation.lean           -- NEW App D: decorrelation ⟺ commuting Ham (dimension-independent)
```

**File details**:

| File | Paper ref | Key definitions/theorems | Est. LOC | Notes |
|------|-----------|-------------------------|----------|-------|
| `GroundSpace.lean` | §3.3, ch14 blueprint | `groundSpace L A`, `groundSpaceProj L A` | ~150 | Follows blueprint ch14 §14.1 |
| `FrustrationFree.lean` | §3.3 | `parentHamiltonian L N A`, `IsFrustrationFree` | ~150 | Follows blueprint ch14 §14.2 |
| `Commuting.lean` | §3.3, Def 3.9 | `IsCommutingParentHam`, `IsNNCPH`, connection to RFP (needs [Beigi]) | ~120 | Thm 3.10 (iii)⟹(i) gated on [Beigi] |
| `Decorrelation.lean` | App D.2 | `IsDecorrelated`, `decorrelated_iff_commutingHam` | ~350 | Self-contained, no MPS-specific deps beyond `Fin`-indexed Hilbert spaces |

### Tier 3 — MPO/MPDO/LPDO foundations (new top-level directories)

> **Key distinction** (De las Cuevas et al., arXiv:1512.05709):
> - **MPO**: Matrix Product Operator — a 4-index tensor M generating operators ρ^(N)(M) = tr(M···M). No positivity requirement.
> - **MPDO**: An MPO satisfying ρ^(N)(M) ≥ 0 for all N. Positivity is a *global* constraint — hard to check locally.
> - **LPDO** (Locally Purifiable Density Operator): An MPDO admitting a local MPS purification M = A ⊗ Ā. This is a *sufficient* condition for positivity (RMP Fig. 6). The Verstraete–Garcia-Ripoll–Cirac (2004) and Zwolak–Vidal (2004) papers define this form.
>
> Not every MPDO is an LPDO: there exist TI MPDOs with no TI MPS purification (De las Cuevas et al. 2016). The purification bond dimension can also be arbitrarily larger than the MPDO bond dimension (De las Cuevas et al. 2013).
>
> In 1606.00608: §4.3 (PRFP, Thm 4.4) applies **only to LPDOs**. §4.4–4.5 (Thm 4.9, Thm 4.14) work for **general MPDOs**.

```
TNLean/MPO/
├── Defs.lean                    -- MPO tensor: 4-index tensor, operator family ρ^(N)
└── CanonicalForm.lean           -- CF for MPO (horizontal and vertical)

TNLean/MPDO/
├── Defs.lean                    -- MPDO = MPO + positivity: IsPositive (ρ^(N)(M) ≥ 0 ∀ N)
├── LPDO.lean                    -- LPDO = MPDO via local purification: M = A ⊗ Ā
├── ZCL.lean                     -- §4.3: ZCL for mixed states (Def 4.2)
├── PRFP.lean                    -- §4.3: Purification RFP (Def 4.3, Thm 4.4) — LPDO only
├── VerticalCF.lean              -- §4.5, Prop 4.13: horizontal CF ⟹ vertical CF
└── RFP.lean                     -- §4.1, Def 4.1: IsRFP for general MPDO (T,S tpCPM)
```

**File details**:

| File | Paper ref | Key definitions/theorems | Est. LOC | Notes |
|------|-----------|-------------------------|----------|-------|
| `MPO/Defs.lean` | §4.1, eq (22) | `MPOTensor d D := Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ`, `mpo N M` (operator on N sites) | ~100 | Core 4-index tensor type. Physical index = (ket, bra) pair. No positivity. |
| `MPO/CanonicalForm.lean` | §4.5 setup | CF for MPO in horizontal direction, connection to MPV CF theory | ~150 | Reuses `MPS/CanonicalForm/*` by viewing MPO as MPV with doubled physical index |
| `MPDO/Defs.lean` | §4.1 | `IsMPDO (M : MPOTensor d D)` := ρ^(N)(M) is PSD for all N. Hermiticity constraint. | ~100 | Global predicate on MPO. |
| `MPDO/LPDO.lean` | §4.3 eq (24)–(25), RMP Fig 6 | `IsLPDO`: ∃ MPS purification A s.t. M = partial_trace(A ⊗ Ā). `IsLPDO → IsMPDO`. | ~200 | Needs `Channel/PartialTrace`. References: Verstraete–Garcia-Ripoll–Cirac PRL 2004, Zwolak–Vidal PRL 2004. |
| `MPDO/ZCL.lean` | Def 4.2 | `IsZCL_MPDO` (transfer matrix idempotent condition for MPO) | ~100 | Works for all MPO, not just MPDO. |
| `MPDO/PRFP.lean` | Def 4.3, Thm 4.4 | `IsPRFP` (purification is RFP). `prfp_iff_zcl_lpdo`. **Restricted to LPDO.** | ~200 | Uses `LPDO.lean` + `MPS/RFP/*`. Paper notes this is too weak (line 786). |
| `MPDO/VerticalCF.lean` | Prop 4.13, Lem L `Lemma-L` | `verticalCF_of_horizontalCF_mpdo`, `lemmaL_mpv_equality` | ~250 | Uses block-injectivity + Newton-Girard. Works for general MPDO. |
| `MPDO/RFP.lean` | Def 4.1 `RFPMixedTS` | `IsRFP_MPDO (M : MPOTensor d D)` (∃ T,S tpCPM), pure case recovery | ~120 | Works for general MPDO. |

### Tier 4 — Entropy & area law (new top-level directory: `Entropy/`)

These are **gated on Mathlib** getting von Neumann entropy. Could be axiomatized initially.

```
TNLean/Entropy/
├── VonNeumann.lean              -- S(ρ) = -tr(ρ log ρ), basic properties
├── StrongSubadditivity.lean     -- SSA inequality
├── SSAEquality.lean             -- [Hayashi 2003] characterization of SSA equality
└── MutualInformation.lean       -- §4.4: I_L definition, Prop 4.5 (monotonicity)
```

### Tier 5 — Simple & general MPDO RFP theorems (extend `MPDO/`)

```
TNLean/MPDO/
├── ... (Tier 3 files)
├── Simple.lean                  -- Def 4.7: simple tensor (no nilpotent BNT), SAL definition
├── EtaStructure.lean            -- Lem C.3: SAL ⟹ isometry + η_{k,h} + primitive T
├── GibbsForm.lean               -- §4.4: GSNNCH definition (Def 4.8), Prop C.6 (commuting form)
├── SimpleRFP.lean               -- Thm 4.9: (i)⟹(ii)⟺(iii)⟹(iv)⟹(v)
└── GeneralRFP.lean              -- §4.5, Thm 4.14: algebra structure ⟺ fusion isometries (long-term)
```

### Full dependency DAG

```
Tier 1 ──────────────────────────────────────────────────
  MPS/RFP/Defs ◄── existing MPS/*, Channel/Stinespring
       │
  MPS/RFP/ZeroCorrelationLength ◄── Spectral/*, Algebra/*
       │
  MPS/RFP/StructuralForm ◄── Channel/FixedPoint/*
       │
  MPS/RFP/Assembly

Tier 2 ──────────────────────────────────────────────────
  MPS/ParentHamiltonian/GroundSpace
       │
  MPS/ParentHamiltonian/FrustrationFree
       │
  MPS/ParentHamiltonian/Commuting ◄── MPS/RFP/Assembly
       │
  MPS/ParentHamiltonian/Decorrelation  (independent)

Tier 3 ──────────────────────────────────────────────────
  MPO/Defs (top-level, 4-index tensor)
       │
  MPO/CanonicalForm ◄── MPS/CanonicalForm/* (via doubled physical index)
       │
  MPDO/Defs ◄── MPO/Defs (adds positivity predicate)
       │
  MPDO/LPDO ◄── MPS/Defs, Channel/PartialTrace (local purification)
       │
  MPDO/ZCL ◄── MPO/Defs (transfer matrix idempotent, no positivity needed)
       │
  MPDO/PRFP ◄── MPDO/LPDO, MPS/RFP/* (LPDO-only result)
       │
  MPDO/VerticalCF ◄── MPO/CanonicalForm, MPS/BNT/*, Algebra/*
       │
  MPDO/RFP ◄── MPDO/Defs (general MPDO, T/S tpCPM definition)

Tier 4 ──────────────────────────────────────────────────
  Entropy/* (gated on Mathlib)

Tier 5 ──────────────────────────────────────────────────
  MPDO/Simple ◄── Entropy/*
       │
  MPDO/EtaStructure
       │
  MPDO/GibbsForm
       │
  MPDO/SimpleRFP ◄── all of Tier 3
       │
  MPDO/GeneralRFP ◄── Channel/FixedPoint/Algebra (Wolf 6.14)
```

### Blueprint chapter mapping

| Module group | Blueprint chapter | Status |
|-------------|-------------------|--------|
| `MPS/RFP/*` | New ch16 or extend ch15 | To create |
| `MPS/ParentHamiltonian/*` | ch14 (to be created) + ch15 (existing) | Extend |
| `MPO/*` | New ch17a (MPO defs & CF) | To create |
| `MPDO/*` | New ch17b (MPDO/LPDO, RFP) | To create |
| `Entropy/*` | New ch18 (or external) | To create |
| `MPDO/GeneralRFP` | New ch19 | Long-term |

### Naming conventions (following existing codebase)

- **Types**:
  - `MPOTensor d D := Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ` — 4-index tensor (ket, bra, left-virtual, right-virtual)
  - No separate `MPDOTensor` type — an MPDO is an `MPOTensor` satisfying `IsMPDO`
- **Predicates on MPO**:
  - `IsMPDO (M : MPOTensor d D)` — ρ^(N)(M) ≥ 0 for all N (global positivity)
  - `IsLPDO (M : MPOTensor d D)` — ∃ purification MPS tensor A, M = tr_anc(A ⊗ Ā) (local purifiability)
  - `IsLPDO → IsMPDO` (but not converse)
- **Predicates on MPS** (RFP theory):
  - `IsRFP`, `IsZCL`, `IsCID`, `IsLocallyOrthogonal`, `IsDecorrelated`, `IsFrustrationFree`, `IsNNCPH`
- **Theorems**: `zcl_iff_idempotent_transfer`, `rfp_iff_zcl`, `rfp_nt_structural`, `decorrelated_iff_commutingHam`, `isLPDO_of_purification`, `prfp_iff_zcl_of_isLPDO`
- **Namespaces**: `MPSTensor.IsRFP`, `MPOTensor.IsMPDO`, `MPOTensor.IsLPDO`, `MPOTensor.IsRFP`

---

## Compatibility with Existing Parent Hamiltonian Infrastructure

*Checked 2026-03-25 against GitHub issues, PRs, blueprint, and Lean files.*

### Current Parent Hamiltonian status

**Issues** (on GitHub):
- **#190** (tracking): 5 milestone issues (#191–#195), all OPEN
- **#191** [PH 1/5]: Ground space, definitions, basic properties — OPEN, not started in code
- **#192** [PH 2/5]: Unique ground state — OPEN
- **#193** [PH 3/5]: Spectral gap via martingale — OPEN
- **#194** [PH 4/5]: Exponential decay of correlations — OPEN
- **#195** [PH 5/5]: Degenerate ground space = BNT span — OPEN
- Fine-grained PH-0a through PH-5d (#169–#189): all CLOSED (consolidated into the 5 milestone issues)
- **#225**: `Correlations.lean` should move from `ParentHamiltonian/` to `Core/`

**PRs**:
- **PR#226** (OPEN): Moves `Correlations.lean` from `ParentHamiltonian/` to `Core/`
- **PR#224** (OPEN): Blueprint sync adding `\lean`/`\leanok` tags for correlations

**Blueprint**:
- `ch14_parent_hamiltonian.tex`: **Does not exist yet**
- `ch15_correlations.tex`: Exists with definitions + a remark about E²=E ⟺ zero correlation length ⟺ RGFP (line 89–91)

**Lean code**:
- `MPS/ParentHamiltonian/Correlations.lean`: 102 lines. Defines `onePointExpectation`, `twoPointExpectation`, `connectedCorrelator`, `correlationLength`. Two sorries (`connectedCorrelator_eq_sum` and `connectedCorrelator_bound` are tautological placeholders accepting their hypothesis as input).
- No other files in `MPS/ParentHamiltonian/` yet.

**Tracking document**: `PARENT_HAMILTONIAN_ISSUES.md` — comprehensive plan with 18 tasks across 6 layers, matching the RMP review paper (arXiv:2011.12127 §IV.C), NOT 1606.00608.

### Compatibility assessment

| Scouting report module | Existing PH plan | Compatible? | Notes |
|------------------------|------------------|-------------|-------|
| **`MPS/RFP/Defs.lean`** (IsRFP) | Not in PH plan | **No conflict** | New concept, orthogonal to PH infrastructure |
| **`MPS/RFP/ZeroCorrelationLength.lean`** | ch15 remark (line 89–91) says "E²=E ⟺ ξ=0 ⟺ RGFP" | **Compatible** — ch15 already gestures at this equivalence. Our module would formalize it. | The `correlationLength` in `Correlations.lean` is defined as `-1/log‖λ₂‖`. ZCL = this being 0 = λ₂ = 0 = E²=E. Clean connection. |
| **`MPS/RFP/Assembly.lean`** (RFP ⟺ ZCL) | Not in PH plan | **No conflict** | |
| **`MPS/ParentHamiltonian/GroundSpace.lean`** | **PH-0a in issue #191** | **Direct match** — our proposed file has the same name and content as the PH plan | Must coordinate: whoever implements first sets the API |
| **`MPS/ParentHamiltonian/FrustrationFree.lean`** | **PH-0b,c,d in issue #191** | **Direct match** — PH plan calls it `Defs.lean`, we call it `FrustrationFree.lean` | Minor naming difference. PH plan puts parent interaction + Hamiltonian + FF all in `Defs.lean`; we split into `FrustrationFree.lean`. Either works. |
| **`MPS/ParentHamiltonian/Commuting.lean`** | **Not in PH plan** | **Extension** — the PH plan covers general (non-commuting) parent Hamiltonians from [CPGSV21]. Commuting parent Hamiltonians are specific to 1606.00608 §3. | The PH plan's `parentHamiltonian` definition should be general enough that `IsCommutingParentHam` is just a predicate on top. No conflict, just new content. |
| **`MPS/ParentHamiltonian/Decorrelation.lean`** | Not in PH plan | **No conflict** — self-contained, dimension-independent | |
| **`MPS/MPDO/` (all files)** | Not in PH plan | **No conflict** — entirely new territory | |
| **Correlations.lean location** | **PR#226 proposes moving to `MPS/Core/`** | **Tension** — our scouting report assumes it stays in `ParentHamiltonian/`; PR#226 moves it to `Core/`. | If PR#226 merges, update imports in scouting report. The move is sensible: correlations are general MPS infrastructure, not PH-specific. Our RFP modules would import from `MPS/Core/Correlations`. |

### Key compatibility findings

1. **No conflicts with existing PH issues or PRs.** The RFP/MPDO formalization from 1606.00608 §3–4 is **complementary** to the parent Hamiltonian formalization from 2011.12127 §IV.C. They share some definitions (ground space, frustration-free) but the RFP theory adds new concepts (RFP, ZCL, commuting parent Hamiltonians, MPDO) not in the PH plan.

2. **Shared definitions need coordination.** Both plans want:
   - `groundSpace` (PH-0a = our `GroundSpace.lean`)
   - `parentInteraction` / `parentHamiltonian` (PH-0b,c = our `FrustrationFree.lean`)
   - `IsFrustrationFree` (PH-0d)

   **Recommendation**: Let the PH plan (#191) define these first (it's more general). The RFP modules then import and add predicates like `IsCommutingParentHam`, `IsNNCPH`.

3. **Correlations.lean is moving.** PR#226 moves it from `ParentHamiltonian/` to `Core/`. This is good for the RFP modules — they'd import `MPS/Core/Correlations` rather than reaching into `ParentHamiltonian/`. The `correlationLength` definition there is compatible with our ZCL formalization (ZCL ⟺ ξ=0 ⟺ E²=E).

4. **Blueprint ch14 doesn't exist yet.** The PH tracking document (`PARENT_HAMILTONIAN_ISSUES.md`) has a detailed outline for ch14, but the file hasn't been created. Our RFP formalization would need a separate blueprint chapter (ch16 or similar) for RFP-specific content, but the commuting-Hamiltonian parts could go in ch14 once it exists.

5. **The NNCPH ⟺ RFP direction** (Thm 3.10(iii)⟹(i)) requires [Beigi]'s result about commuting-Hamiltonian ground spaces. This is an external dependency not in the PH plan either. Both formalizations would benefit if someone formalized [Beigi].

6. **Source paper difference**: The PH plan sources from the RMP review [CPGSV21] = arXiv:2011.12127. Our RFP/MPDO formalization sources from [CPGSV17] = arXiv:1606.00608. Different papers, overlapping content. The PH plan's parent Hamiltonian definitions are more general; the 1606.00608 RFP theory adds the specialization to commuting Hamiltonians and the RFP ⟺ ZCL ⟺ NNCPH equivalence.

---

## Cross-reference: 1606.00608 vs RMP 2011.12127

The RMP review (arXiv:2011.12127, Cirac–Pérez-García–Schuch–Verstraete, Rev. Mod. Phys. 2021) covers much of the same material as 1606.00608 but in a different organization and at survey level. Here is the precise correspondence, noting what the RMP adds/omits relative to 1606.00608.

### RMP §II.E (Renormalization and phases, lines 858–1069) ↔ 1606.00608 §3–4

| RMP location | 1606.00608 | Content | Notes |
|-------------|------------|---------|-------|
| §II.E.1 `RFPinMPS` (lines 873–931) | §3.1–3.4 | **MPS RFP**: ZCL, E²=E, commuting parent Ham, structural form | RMP is a compressed summary. 1606.00608 has full proofs in App B. |
| RMP line 876–880 | Def 3.3 (CID) | Zero correlation length definition | RMP uses a slightly different formulation with ground-space projector P_S. 1606.00608 uses direct distance-independence. **Substantively equivalent for injective MPS** but the RMP version is more general (applies to degenerate ground spaces). |
| RMP line 886–890, eq (E²=E) | Thm 3.8 `TheoremZCLPure` | ZCL ⟺ E²=E | Identical statement. |
| RMP line 892–895 | Thm 3.10 `thm:main-MPS` | RFP ⟺ ZCL ⟺ commuting parent Ham | RMP cites [cirac:mpdo-rgfp] = 1606.00608 for the proof. |
| RMP line 897–901 | Def 3.13, Prop 3.14 | SAL ⟺ RFP | RMP mentions it; 1606.00608 has the proof (via SSA + mixed-state case). |
| RMP line 906–916, eq (RFPPure) | Thm 3.1, Def 3.2 | A^{i₁}A^{i₂} = Σ U A^j (isometry condition) | Identical. RMP adds a graphical representation (AA=UA figure). |
| RMP line 922–929, eq (fixedMPS) | Thm 3.11, eq (21) | Structural form: |Φ⟩ = ⊗ |φ⟩ (product of entangled pairs) | Identical content. RMP emphasizes the phase classification angle. |
| §II.E.2 `sec:2:MPDO-RGFP` (lines 934–996) | §4.1–4.5 | **MPDO RFP** | RMP is a 60-line summary of the 400-line §4 in 1606.00608. |
| RMP line 937–940, eq (Fig:ZCL-MPDO) | Def 4.2 `DefinitionZCL` | ZCL for MPDO | Identical. |
| RMP line 942–950 | §4.4 (SAL discussion) | ZCL ≠ SAL for mixed states; need both | Identical conceptual content. |
| RMP line 952–958, eq (Fig:TandS) | Def 4.1 `RFPMixedTS` | RFP = ∃ T,S tpCPM | Identical. RMP notes "far less obvious" direction = the main result of 1606.00608. |
| RMP line 963–988, eqs (eq:algebra, idempotent) | Thm 4.14 `thm:IV.13` | MPDO RFP ⟺ algebra structure coefficients | **Key difference**: RMP only states the single-block case ("we do not include the case of multiple blocks"), while 1606.00608 Thm 4.14 handles the general case. |
| RMP line 990–994 | Thm 4.15 | L-independent c ⟹ Gibbs + commuting Ham structure | Identical. |
| RMP line 996 | §4.5 discussion | Connection to Levin-Wen / fusion categories | Identical. |

### RMP §IV.C (Hamiltonians, lines 1972–2300) ↔ 1606.00608 §3.3 + existing PH plan

| RMP location | 1606.00608 | PH plan issue | Content | Notes |
|-------------|------------|---------------|---------|-------|
| §IV.C.1 lines 1985–2011 | §3.3 (eq 17) | **#191** PH-0a,0b,0c | Ground space G_L, parent Hamiltonian, frustration-free | **Same definitions**. RMP is more detailed (includes 2D PEPS version). PH plan follows RMP. |
| §IV.C.1 Thm IV.3 (line 2042) | — | **#192** PH-2c | Unique GS for injective (2L₀ sites) | RMP covers PEPS too. Not in 1606.00608 (which focuses on RFP, not general PH). |
| §IV.C.1 Thm IV.4 (line 2087) | — | **#192** PH-2d | Unique GS for normal (L₀+1 sites) | Same. |
| §IV.C.1 "intersection property" (lines 2049–2079) | — | **#192** PH-2a,2b | Intersection + closure | Full proof in RMP. Not in 1606.00608. |
| §IV.C.1 block-injective (lines 2104–2136) | §2 (Prop 2.10 `propblockinj`) | **#195** PH-3a | Degenerate GS = BNT span | RMP covers this; 1606.00608 uses it as infrastructure for §3–4 but doesn't re-prove it. |
| §IV.C.2 martingale (lines 2166–2188) | — | **#193** PH-4a,4b,4c | Gap via martingale | **Not in 1606.00608 at all**. This is purely RMP/FNW/KL content. |
| §IV.C.2 "All MPS PH are gapped" (line 2185) | — | **#193** PH-4c | Gap theorem | Not in 1606.00608. |
| §IV.C.3 stability (lines 2203–2266) | — | — | LTQO, perturbation stability | Not in 1606.00608. Not in PH plan either (future work). |
| §IV.C.4 converse (lines 2140–2154) | — | — | FF Ham ⟹ MPS (Matsui) | Not in 1606.00608. Not in PH plan. |

### RMP §II.B.3 (Correlations, lines 415–442) ↔ 1606.00608 §3.2 + PH-5*

| RMP location | 1606.00608 | PH plan issue | Content |
|-------------|------------|---------------|---------|
| line 433 (transfer matrix) | Def 3.7 | `MPS/Core/Transfer.lean` | Transfer matrix E definition — **already formalized** |
| line 434 (Perron-Frobenius) | — | — | QPF for transfer matrix — **already formalized** |
| line 436–440 (correlation formula) | Thm 3.8 proof uses this | **#194** PH-5b | C(X,Y;n) = Σ c_i λ_i^n — partially in `Correlations.lean` |
| line 436 (correlation length) | Implicitly in Thm 3.8 | **#194** PH-5d | ξ = -1/log|λ₂| — defined in `Correlations.lean` |

### Key findings from the cross-reference

1. **The RMP is a strict superset** of 1606.00608 for parent Hamiltonians (intersection property, gap theorem, stability, converse). The PH plan (#190–#195) correctly sources from the RMP.

2. **1606.00608 is the primary source** for RFP theory (§3 structural characterization, §4 MPDO theory). The RMP's §II.E summarizes this but cites 1606.00608 for proofs. Our scouting report correctly identifies 1606.00608 as the source for formalization.

3. **ZCL definition subtlety**: The RMP (line 876) defines ZCL using a ground-space projector P_S:
   > ⟨Ψ|AB|Ψ⟩ - ⟨Ψ|A P_S B|Ψ⟩ = 0

   while 1606.00608 Def 3.3 defines CID as:
   > ⟨Ψ|O₁O₂|Ψ⟩ = ⟨Ψ|O₁O₂'|Ψ⟩ (distance-independent)

   These are **equivalent for single ground states** but the RMP version is more natural for degenerate ground spaces (GHZ example). For our formalization (Tier 1, `MPS/RFP/ZeroCorrelationLength.lean`), the E²=E characterization bypasses both — it's the clean formalization target.

4. **The RMP omits the multi-block MPDO case** in Thm 4.14. The RMP (line 977) explicitly says "we do not include the case of multiple blocks." The full generality is only in 1606.00608. This matters for Tier 5 formalization.

5. **No conflicts in formalization strategy**. The two papers are complementary:
   - PH plan (from RMP §IV.C): General parent Hamiltonians, gap, uniqueness, stability
   - RFP scouting (from 1606.00608 §3–4): RFP structural theory, commuting PH equivalence, MPDO

   The only shared definitions are ground space / parent Hamiltonian / frustration-free, and both papers define them identically.

6. **The "commuting parent Hamiltonian ⟺ RFP" equivalence** appears in both papers:
   - RMP line 893–895 cites 1606.00608 for the proof
   - 1606.00608 Thm 3.10 `thm:main-MPS` proves it (via [Beigi])
   - Our `MPS/ParentHamiltonian/Commuting.lean` would bridge between the PH infrastructure (from RMP) and the RFP theory (from 1606.00608)
