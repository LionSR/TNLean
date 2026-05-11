# MPS Fundamental Theorem & Quantum Wielandt — Paper-to-Code Coverage Audit

**Audit date**: 2026-05-08
**Source papers**:
- **PGVWC07**: D. Pérez-García, F. Verstraete, M.M. Wolf, J.I. Cirac, *Matrix Product State Representations*, Quantum Inf. Comput. **7**, 401–430 (2007), arXiv:quant-ph/0608197.
  Source TeX: `Papers/quant-ph_0608197/MPSarchive.tex`
- **CPSV16**: J.I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix Product Density Operators: Renormalization Fixed Points and Boundary Theories*, Ann. Phys. **378**, 100–149 (2017), arXiv:1606.00608.
  Source TeX: `Papers/1606.00608/MPDO-22-12-17-2.tex`
- **SPGWC09** (Wielandt): M. Sanz, D. Pérez-García, M.M. Wolf, J.I. Cirac, *A quantum version of Wielandt's inequality*, IEEE Trans. Inf. Theory **56**, 4668–4673 (2010), arXiv:0909.5347.
  Source TeX: `Papers/0909.5347/main.tex`

**Leaning on** (not audited in detail):
- **CPSV21**: Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. **93**, 045003 (2021), arXiv:2011.12127 — used in `FundamentalTheorem/EqualProportional.lean` for Theorem 4.4 naming.
- **DSSPC17**: De las Cuevas, Schuch, Pérez-García, Cirac, *Continuum limits of matrix product states*, arXiv:1708.00029 — used in `Periodic/FundamentalTheorem.lean`.

**Scope**: This audit covers MPS / pure-state sections of PGVWC07 and CPSV16, plus a full Wielandt source-paper crosswalk (§9). The MPDO / mixed-state sections of CPSV16 (§IV, Appendix C) are listed for completeness but not deeply traced. A separate MPDO coverage audit is recommended.

**Maintainer note** (from #1498, 2026-05-08): "Please please follow CPSV16". For non-periodic FT work, prioritize source-faithful CPSV16 statement/prose and avoid implementation-driven reinterpretations.

---

## 1. Current sorry/axiom statistics

Collected 2026-05-08 with `rg -n "\bsorry\b|axiom" TNLean/MPS/ TNLean/PEPS/`:

| File | Lines | Sorry count | Notes |
|---|---|---|---|
| `TNLean/MPS/Periodic/Overlap/Case3.lean` | 456 | 6 | Periodic overlap Case 3 |
| `TNLean/MPS/Periodic/Overlap/Dichotomy.lean` | 90 | 4 | Overlap dichotomy assembly |
| `TNLean/MPS/Periodic/Overlap/Case2.lean` | 394 | 3 | Periodic overlap Case 2 |
| `TNLean/MPS/Periodic/Overlap/SelfOverlap.lean` | 857 | 2 | Self-overlap convergence |
| `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` | 937 | 3 | Unique ground state |
| `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` | 703 | 1 | Degenerate ground space |
| `TNLean/MPS/ParentHamiltonian/Martingale.lean` | 1569 | 1 | Martingale proof |
| `TNLean/PEPS/FundamentalTheorem.lean` | 738 | 4 | PEPS FT (out of scope) |
| **Total MPS** | — | **20** | Excluding PEPS |

The periodic overlap dichotomy cluster (`Case2`, `Case3`, `Dichotomy`, `SelfOverlap`) accounts for 15 of 20 MPS sorrys — these are tracked by issue #81 ("periodic overlap dichotomy").

---

## 2. Coverage crosswalk: CPSV16 (arXiv:1606.00608)

### 2.1 Section II — Matrix Product Vectors (pure-state canonical form)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| §II Defn (l.132) | 132–139 | MPV definition (`MPV`) | `TNLean/MPS/Defs.lean` | `leanok` |
| Prop (l.249) | 249–251 | After blocking, any tensor can be put in CF generating same MPV | `TNLean/MPS/CanonicalForm/Reduction.lean` (`exists_irreducible_blockDecomp`); `CanonicalForm/Existence.lean` | `leanok` |
| Prop (l.253) | 253–255 | Characterization of CF (no p-periodic, P Aⁱ = P Aⁱ P ⇒ Aⁱ P = P Aⁱ P) | `TNLean/MPS/CanonicalForm/FromPeripheralPrimitive.lean` (`isCanonicalForm_of_peripheralPrimitive`) | `leanok` |
| Prop 2.7 (l.278, `prop:char-BNT`) | 278–280 | BNT characterization: each CF NT is gauge-phase-equivalent to some basis element | `TNLean/MPS/CanonicalForm/BNTGrouping.lean`; `PhaseClassSectorData.lean` (`exists_bnt_sectorDecomp_*`) | **partial** — full BNT construction from CF not yet proved; `BNTGrouping.lean` handles norm-sorting special case; tracked by #1501 |
| Defn "injective" (l.317, `defnbi`) | 317–322 | NT injective if matrices span full M_D; biCF for block-injective CF | `TNLean/MPS/Core/CPPrimitive.lean` (`IsInjective`); `CanonicalForm/BlockDiagonalCommutant.lean` (block-diagonal commutant theorems) | `leanok` |
| Prop (l.342, `propblockinj`) | 342–345 | After blocking ≤ 3D⁵ spins, any CF tensor becomes biCF | Uses Wielandt; `FundamentalTheorem/FiniteLength.lean` imports `WielandtBound` for word-span results | **needs verification** |
| **Theorem II.1** (l.349, `thm1`) | 349–352 | **Fundamental Theorem of MPV (proportional case)** | No faithful Lean theorem at present. The former restricted proportional-comparison declarations were deleted because their coefficient-array hypotheses are not part of the source statement. | **open** |
| **Corollary II.2** (l.354, `II_cor2`) | 354–360 | **Equal MPV case**: same MPVs ⇒ conjugate by invertible X | `TNLean/MPS/FundamentalTheorem/EqualProportional.lean` (`fundamentalTheorem_equalMPV_CFBNT`); `FundamentalTheorem/Basic.lean` (`fundamentalTheorem_singleBlock`, `sameMPV_iff_gaugeEquiv_of_injective`) | `leanok` |

### 2.2 Section III — Pure States: Renormalization of MPS (RFP / ZCL / NNCPH)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem 3.1** (l.398, `thm:renormalization-flow`) | 398–405 | RFP limit ⇔ Aⁱ¹ Aⁱ² = Σ U_(i₁,i₂),j Aʲ for isometry U | `TNLean/MPS/RFP/Defs.lean` (`IsRFP`, `isRFP_iff_kraus_isometry`); `RFP/Convergence.lean` (`rg_flow_converges_of_cf`) | `leanok` |
| Defn RFP (l.420, `defRFP`) | 420–424 | RFP for pure case: AA = UA for isometry U | `TNLean/MPS/RFP/Defs.lean` (`IsRFP`) | `leanok` |
| Defn CID (l.438) | 438–446 | Correlations independent of distance | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`IsCID`) | `leanok` |
| Defn LO (l.468, `DefLO`) | 468–474 | Local orthogonality: ∑ᵢ Aⁱⱼ ⊗ Āⁱⱼ' = 0 | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`IsLocallyOrthogonal`) | `leanok` |
| Defn ZCL (l.476) | 476–478 | ZCL = LO ∧ CID | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`IsZCL`) | `leanok` |
| Defn Transfer matrix (l.482) | 482–488 | 𝔼 = ∑ᵢ Aⁱ ⊗ Āⁱ | `TNLean/MPS/Core/Transfer.lean` (`transferMap`) | `leanok` |
| **Theorem 3.8** (l.500, `TheoremZCLPure`) | 500–503 | **ZCL ⇔ 𝔼² = 𝔼** (i.e., transfer map idempotent) | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`zcl_iff_idempotent_transfer`), `isCID_implies_isRFP` | `leanok` |
| Defn Parent Ham. (l.522) | 522–525 | NNCPH definition | `TNLean/MPS/ParentHamiltonian/Commuting.lean` (`IsNNCPH`) | `leanok` |
| **Theorem 3.10** (l.534, `thm:main-MPS`) | 534–541 | **RFP ⇔ ZCL ⇔ NNCPH** (three-way equivalence) | `TNLean/MPS/RFP/Assembly.lean` (`rfp_iff_zcl` for RFP↔ZCL); `ParentHamiltonian/Commuting.lean` (`rfp_implies_nncph`, `nncph_implies_rfp`) | **partial** — `rfp_implies_nncph` uses `Axioms.rfp_to_nncph_commute` (axiom-backed); `nncph_implies_rfp` uses `Axioms.beigi_nncph_to_rfp` (axiom-backed). Tracked by issues #1484/#1485. |
| **Theorem 3.11** (l.543, `thm:charact-MPS`) | 543–555 | **Structural characterization of RFP**: CF tensor is RFP iff Aⁱ = ⊕ⱼ ⊕_q μ_j,q X_j,q Λ_j Uⁱⱼ X_j,q⁻¹ with U isometry | `TNLean/MPS/RFP/StructuralForm.lean` (`rfp_cf_structural`, `rfp_bnt_structural`, `rfp_nt_structural_full`) | `leanok` |
| Corollary III.3 (l.583, `III_cor3`) | 583–590 | BNT elements of RFP have form A_j = X_j Λ_j Uⁱⱼ X_j⁻¹ | `TNLean/MPS/RFP/StructuralForm.lean` (covered by `rfp_nt_structural`) | `leanok` |
| Prop (l.606) | 606–? | RFP convergence for tensors in CF | `TNLean/MPS/RFP/Convergence.lean` (`rg_flow_converges_of_cf`) | `leanok` |

### 2.3 Section IV — Mixed States (MPDO)

Listed for completeness; detailed MPDO coverage audit is out of scope.

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn RFP (mixed) (l.658) | 658–663 | `RFPMixedTS` — mixed-state RFP via tpCPM T, S | `TNLean/MPS/MPDO/RFP.lean` | `leanok` (defn) |
| Defn Puri-RFP (l.758) | 758–764 | Purification RFP | `TNLean/MPS/MPDO/PRFP.lean` | `leanok` (defn) |
| Prop (l.801, `PropILILp1`) | 801–807 | Mutual information monotonic and bounded | `TNLean/MPS/MPDO/` | **needs verification** |
| Defn SAL (l.811, `def:area-law`) | 811–813 | Saturation of area law | `TNLean/MPS/MPDO/` | **needs verification** |
| Defn GSNNCH (l.829) | 829–837 | Gibbs state of nearest-neighbor commuting Hamiltonian | **out of scope** | — |
| **Theorem 4.9** (l.851, `thm:main-simple`) | 851–893 | **Main simple case**: RFP ⇔ ZCL+SAL ⇔ GSNNCH+ZCL ⇔ (iv) ⇔ (v) | Distributed across `TNLean/MPS/MPDO/` files (`AlgebraStructure.lean`, `BlockedRFPConstruction.lean`, `CommutingForm.lean`) | **partial** — many implications proven; exact mapping needs MPDO-specific audit |
| **Proposition IV.12** (l.945, `Prop:IV.12`) | 945–952 | Vertical CF: tensor in CF also in CF vertically, with isometry U giving block structure | `TNLean/MPS/MPDO/VerticalCF.lean` | **needs verification** |
| **Theorem IV.13** (l.972, `thm:IV.13`) | 972–993 | **Main MPDO theorem**: RFP ⇔ algebra structure with χ_αβγ ⇔ fusion isometries U_αβ | `TNLean/MPS/MPDO/AlgebraStructure.lean` | **partial** — algebra structure formalized; idempotent property tracked in #1484/#1485 |
| Theorem (l.1013) | 1013–? | Boundary projection form | **out of scope** | — |

### 2.4 Appendix A — Proofs of Section II

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn CFII (l.1058) | 1058–1060 | CFII: CF + trace-preserving CPM + full-rank diagonal fixed point | `TNLean/MPS/CanonicalForm/Existence.lean` (`CFII` data) | `leanok` |
| **Lemma `equalMPS`** (l.1080) | 1080–1091 | Two NMPVs: overlap → 0 or 1; if 1, gauge-phase equivalent | `TNLean/MPS/CanonicalForm/` (distributed); `CanonicalForm/GaugePhaseFromOverlap.lean` | **needs verification** |
| **Corollary `eqV`** (l.1121) | 1121–1128 | NMPV overlap → 0 or equal up to phase factor e^{iφN} | Used in BNT construction | **needs verification** |
| **Corollary `Lem1`** (l.1131) | 1131–1133 | Orthogonal NMPVs are eventually linearly independent | `TNLean/MPS/CanonicalForm/PhaseClassSectorData.lean` (`exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv`) | `leanok` |
| **Lemma `Lem:app_simple`** (l.1156) | 1156–1163 | Power-sum equality ⇒ multiset equality | `TNLean/Algebra/ScalarPowerSumIdentity.lean` (imported by `FundamentalTheorem/EqualProportional.lean`) | `leanok` |
| **Corollary `thm:Fundamental-CFII`** (l.1197) | 1197–1199 | CFII version: X, X_k unitary | `TNLean/MPS/FundamentalTheorem/EqualProportional.lean` (CFII variant of fundamental theorem) | **needs verification** |

### 2.5 Appendix B — Proofs of Section III (pure RFP)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Renormalization flow convergence (l.1209–1244) | 1209–1244 | Proof that renormalization flow from CF always converges | `TNLean/MPS/RFP/Convergence.lean` (`rg_flow_converges_of_cf`) | `leanok` |
| **Lemma `lem:charact-NT-pure-RFP`** (l.1274) | 1274–1289 | NT is RFP iff Aⁱ = X Λ Uⁱ X⁻¹ with Λ diagonal positive, U isometry | `TNLean/MPS/RFP/StructuralForm.lean` (`rfp_nt_structural`) | `leanok` |
| Theorem 3.10 RFP⇒NNCPH (l.1305–1307) | 1305–1307 | Proof sketch: RFP ⇒ NNCPH from Theorem 3.11 | `TNLean/MPS/ParentHamiltonian/Commuting.lean` (`rfp_implies_nncph`) | **axiom-backed** (#1484/#1485) |

### 2.6 Appendix C — Proofs of Section IV (mixed states)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Prop `propsimple` (l.1333) | 1333–1341 | RFP ⇒ ZCL + SAL | `TNLean/MPS/MPDO/` | **needs verification** |
| Lemma `Lsigma3` (l.1351) | 1351–1359 | SAL ⇒ direct sum structure for 3-spin reduced state | **out of scope** | — |
| Lemma `propSN` (l.1406) | 1406–1411 | SAL ⇒ isometry U + r_k, l_k with primitive T | **out of scope** | — |
| Lemma `SALZCL` (l.1484) | 1484–1487 | SAL + ZCL ⇒ T rank-1 (factorized) | **out of scope** | — |
| Corollary (l.1503) | 1503–1506 | SAL + ZCL ⇒ structural form | **out of scope** | — |
| Prop `3to5` (l.1510) | 1510–1517 | Structural form ⇒ tpCPM T,S exist (RFP) | **out of scope** | — |
| Prop `3to4` (l.1569) | 1569–1577 | SAL ⇒ GSNNCH form | **out of scope** | — |
| Prop `4to2` (l.1597) | 1597–1601 | GSNNCH + ZCL ⇒ SAL | **out of scope** | — |
| Lemma `lemmus` (l.1647) | 1647–1649 | ZCL ⇒ μ_j,q independent of q | **out of scope** | — |
| Lemma (l.1680) | 1680–1691 | SAL ⇒ orthogonal projectors P_j | **out of scope** | — |
| Prop `prop2to3` (l.1740) | 1740–1743 | SAL + ZCL ⇒ BNTs satisfy (iv) of Theorem 4.9 | **out of scope** | — |
| Prop `prop3to4` (l.1786) | 1786–1789 | (iv) ⇒ GSNNCH | **out of scope** | — |
| Prop `prop4to2` (l.1801) | 1801–1804 | GSNNCH ⇒ SAL | **out of scope** | — |
| Prop `prop2to5` (l.1810) | 1810–1813 | SAL + ZCL ⇒ tpCPM T,S exist | **out of scope** | — |

### 2.7 Appendix D — Proofs of IV.12 / IV.13

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Lemma `Lemma-L`** (l.1835) | 1835–1846 | Operator equality on first spin of MPV ⇒ equality of projected tensors | `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean` (related block-diagonal commutant lemmas) | **needs verification** |
| Proof of Prop IV.12 (l.1861–1922) | 1861–1922 | Vertical CF + isometry proof | `TNLean/MPS/MPDO/VerticalCF.lean` | **needs verification** |
| Proof of Thm IV.13 (l.1925–2010) | 1925–2010 | Algebra structure from RFP, with C*-algebra fixed-point argument | `TNLean/MPS/MPDO/AlgebraStructure.lean` (RFP ⇒ algebra) | **partial** |

### 2.8 Appendix E — Additional results (decorrelation, alternative RFP definitions)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn decorrelated (l.2187) | 2187–2192 | Decorrelated regions definition | **out of scope** | — |
| Defn parent commuting Ham. (l.2206) | 2206–2216 | Parent commuting Hamiltonian subspace definition | **out of scope** | — |
| Prop (l.2221) | 2221–2223 | Decorrelated ⇔ parent commuting Hamiltonian | **out of scope** | — |

---

## 3. Coverage crosswalk: PGVWC07 (quant-ph/0608197)

### 3.1 Section 3 — The canonical form

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem `thm:OBC-Vidal`** (l.431) | 431–443 | Completeness and canonical form for OBC (Vidal form) | `TNLean/MPS/Chain/Defs.lean` (OBC chain definition); left-canonical/right-canonical conditions in `Core/` | `leanok` (definitions); **needs verification** (full completeness theorem) |
| **Theorem `free-OBC`** (l.466) | 466–486 | Freedom in OBC: all representations related by local Y_j, Z_j | `TNLean/MPS/Chain/GaugePhase.lean` (gauge transformations) | `leanok` |
| Theorem "Site-independent matrices" (l.620) | 620–630 | TI state has site-independent MPS representation (bond dim ≤ ND) | `TNLean/MPS/Chain/Defs.lean` (TI chain definitions) | **needs verification** |
| **Theorem `Th:TIcanonical`** (l.742) | 742–763 | TI canonical form: block-diagonal with λ_j > 0, each block satisfies left/right canonical + unique fixed point | `TNLean/MPS/CanonicalForm/Reduction.lean` (`exists_irreducible_blockDecomp`); `CanonicalForm/Existence.lean` (`exists_CFII_data_of_TP_of_isIrreducibleTensor`) | `leanok` |
| **Theorem `Th:periodic`** (l.849) | 849–858 | Periodic decomposition: p eigenvalues of modulus 1 ⇒ superposition of p p-periodic states | `TNLean/MPS/Periodic/Symmetry.lean`, `Periodic/ProjectiveRep.lean` | **partial** — periodic symmetry theory formalized; full theorem statement needs verification |
| Prop `prop-inj` (l.911) | 911–? | C1 condition ⇒ Γ_L injective for L ≥ L₀ | `TNLean/MPS/Core/CPPrimitive.lean` (`IsInjective`), Wielandt span-growth infrastructure | **needs verification** |
| Theorem "Interpretation of Λ" (l.987) | 987–993 | Λ eigenvalues converge to half-chain density matrix eigenvalues | **out of scope** | — |
| **Theorem `thm-uniq`** (l.1002) | 1002–1015 | Uniqueness of TI canonical form (under C1, unique OBC CF, N > 2L₀+D⁴) | `TNLean/MPS/FundamentalTheorem/Basic.lean` (`fundamentalTheorem_singleBlock`, `sameMPV_iff_gaugeEquiv_of_injective` for single-block case); `Chain/FundamentalTheorem.lean` (`fundamentalTheorem_injective_chain`) | **partial** — single-block case fully proved; multi-block TI case with general hypotheses not yet formalized; tracked by #1529 |
| Lemma `lem-same-matr` (l.1022) | 1022–1040 | Same-matrix lemma for T(Y_k)=S(Y_{k+1}) | **out of scope** (purely linear-algebraic) | — |
| Lemma `lem-horn` (l.1053) | 1053–1058 | Horn's lemma: solution space of W(C⊗1)=(B⊗1)W is S⊗M_n | **out of scope** | — |
| Theorem "Obtaining TI canonical form" (l.1154) | 1154–1165 | Solving quadratic equations (S) yields TI D-MPS from unique OBC CF | **out of scope** | — |

### 3.2 Section 4 — Parent Hamiltonians

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Theorem "Uniqueness with OBC" (l.1206) | 1206–1209 | MPS is unique ground state of parent Hamiltonian under C1 (OBC) | `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` | **partial** — 3 sorrys remain |
| **Theorem `uniqueGS`** (l.1272) | 1272–1274 | Uniqueness with TI and PBC under C1 | `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` | **partial** |
| Lemma `lem1` (l.1333) | 1333–? | C1 condition witness lemma | `TNLean/MPS/ParentHamiltonian/` | **needs verification** |
| Lemma `lem:direct-sum` (l.1346) | 1346–? | Direct sum lemma for block decomposition | `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean` (Theorem 3, lines 769–803); `TNLean/MPS/ParentHamiltonian/` | **needs verification** |
| Theorem `2blocks.1` (l.1407) | 1407–1415 | Degeneracy of ground space v1 | `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` | **partial** — 1 sorry |
| Theorem `2blocks.2` (l.1424) | 1424–1428 | Degeneracy of ground space v2 (construction) | `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` | **partial** |

### 3.3 Section 5 — Generation of MPS

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Theorem `Thm:seqwith` (l.1569) | 1569–1573 | Sequential generation with ancilla: all OBC MPS with D-dimensional ancilla | **out of scope** | — |
| Theorem "Sequential generation without ancilla" (l.1589) | 1589–1595 | Without ancilla: D ≤ d | **out of scope** | — |

### 3.4 Section 6 — Classical simulation

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Theorem MPS approximation bound (l.1774) | 1774–1781 | ∃ MPS with bond dim D approximating within Σ ε_k(D) | **out of scope** | — |
| Theorem Rényi entropy bound (l.1794) | 1794–1797 | log ε(D) ≤ (1-α)/α (S^α - log D/(1-α)) | **out of scope** | — |
| Theorem D_L polynomial bound (l.1824) | 1824–1828 | D_L ≤ poly(L) for critical systems | **out of scope** | — |
| Theorem `Thm:ClusterComputation` (l.1938) | 1938–1943 | Simulating 1D measurement-based computation | **out of scope** | — |
| Theorem `Thm:CircuitComputation` (l.1952) | 1952–1959 | Simulating quantum circuits with bounded MPS bond dim | **out of scope** | — |

### 3.5 Section 7 — Open problems / Appendix

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Conj `Conj1` (l.2103) | 2103–2107 | f(D) bound for injectivity length | **out of scope** | — |
| Conj `Conj2` (l.2109) | 2109–2111 | f(D) ~ O(D²) | **out of scope** | — |
| Prop `prop:appendix` (l.2116) | 2116–2118 | If A₀ invertible, L₀ ≤ D² | **out of scope** | — |
| Corollary W-state (l.2181) | 2181–2185 | W-state bond dimension lower bound | **out of scope** | — |
| Theorem "Dichotomy for MPS size" (l.2242) | 2242–? | Dichotomy: bond dim either constant or ≥ poly(N) | **out of scope** | — |

---

## 4. Sorry / gap crosswalk with tracked issues

### 4.1 Periodic overlap dichotomy cluster (issue #81)

| File | Sorrys | Dependency |
|---|---|---|
| `Periodic/Overlap/SelfOverlap.lean` | 2 | Self-overlap convergence converse |
| `Periodic/Overlap/Case2.lean` | 3 | Non-decaying cross-family overlap ⇒ gauge inequivalence |
| `Periodic/Overlap/Case3.lean` | 6 | Non-decaying self-overlap ⇒ gauge equivalence |
| `Periodic/Overlap/Dichotomy.lean` | 4 | Top-level dichotomy assembly |

These 15 sorrys cascade into `Periodic/FundamentalTheorem.lean` (Theorem 3.4 of DSSPC17), which has a conditional proof that takes the dichotomy as a hypothesis.

### 4.2 Parent Hamiltonian cluster (issue #1484/#1485)

| File | Sorrys | Dependency |
|---|---|---|
| `ParentHamiltonian/UniqueGroundState.lean` | 3 | Uniqueness proof incomplete |
| `ParentHamiltonian/DegenerateGS.lean` | 1 | Degenerate ground space construction |
| `ParentHamiltonian/Martingale.lean` | 1 | Martingale convergence argument |

The CPSV16 Theorem 3.10 (RFP ⇔ NNCPH) proof in `ParentHamiltonian/Commuting.lean` uses the `Axioms.rfp_to_nncph_commute` and `Axioms.beigi_nncph_to_rfp` axioms from issue #1484/#1485, which track the incomplete proof of the commuting parent Hamiltonian implications.

### 4.3 PEPS (out of scope)

| File | Sorrys |
|---|---|
| `PEPS/FundamentalTheorem.lean` | 4 |

---

## 5. Note on Theorem 4.4 (CPSV21) naming

The `FundamentalTheorem/EqualProportional.lean` module now records the equal-MPV route and the
power-sum ingredients.  A faithful Lean statement for the CPSV21 proportional theorem, i.e. the
CPSV16 Fundamental Theorem of MPV (Theorem II.1 / `thm1`), remains open after removal of the
restricted coefficient-array theorem surface.

Open target:

- Faithful proportional theorem: CPSV21 Theorem 4.4, corresponding to CPSV16
  Theorem II.1 (`thm1`).

| Lean declaration | Paper | CPSV16 label |
|---|---|---|
| `fundamentalTheorem_equalMPV_CFBNT` | CPSV21 Corollary after Theorem 4.4 | CPSV16 Corollary II.2 (`II_cor2`) |

---

## 6. File-length note

Two oversized Lean files appear in CI file-length checks but are untouched by this doc-only audit:

| File | Lines |
|---|---|
| `TNLean/MPS/MPDO/BiCFDerivation/PairHomogenization.lean` | ~1460 |
| `TNLean/MPS/ParentHamiltonian/Martingale.lean` | ~1569 |

These are known oversized (documented in #1512/#1522) and do not block unrelated doc PRs.

---

## 7. Key remaining coverage gaps

| Priority | Paper | Theorem | Gap description | Tracked by |
|---|---|---|---|---|
| High | CPSV16 | Theorem 3.10 (RFP⇔NNCPH) | `rfp_implies_nncph` / `nncph_implies_rfp` are axiom-backed | #1484, #1485 |
| High | PGVWC07 | Theorem `thm-uniq` (Uniqueness of TI CF) | Multi-block TI case with general hypotheses not formalized | #1529 |
| High | PGVWC07 | Theorem `uniqueGS` (Uniqueness with TI+PBC) | Proof incomplete (3 sorrys) | #1475 / #460 |
| Medium | CPSV16 | Prop 2.7 (`prop:char-BNT`) | Full BNT construction from CF not yet proved | #1501 |
| Medium | CPSV16 | Theorem IV.13 | MPDO main theorem: algebra structure + idempotent | #1484, #1485 |
| Medium | PGVWC07 | Theorem `Th:periodic` | Full periodic decomposition formalization | #81 |
| Low | PGVWC07 | Theorem "Interpretation of Λ" | Λ → density matrix eigenvalues convergence | **out of scope** |

---

## 8. Audit methodology

- Source paper lines counted in `Papers/1606.00608/MPDO-22-12-17-2.tex` and `Papers/quant-ph_0608197/MPSarchive.tex`.
- Lean locations determined by grep for paper citations, theorem names, and type signatures in `TNLean/MPS/`.
- `leanok` status: verified via `rg "\bsorry\b|axiom"` in the referenced Lean files — no sorry/axiom in those specific files means the theorem body compiles. Does **not** guarantee full correctness relative to the paper; formal proof review is separate.
- `needs verification`: paper label exists but Lean mapping is uncertain, incomplete, or unconfirmed. Items marked `needs verification` should be re-checked by a domain expert before claiming coverage.
- `out of scope`: paper result considered outside the MPS Fundamental Theorem core (e.g., simulation bounds, entropy theorems, sequential generation).

---

*This audit follows the CPSV16 source-faithfulness policy from #1498. All references to CPSV16 theorems use source labels (`thm:main-MPS`, `TheoremZCLPure`, `thm:charact-MPS`, `thm:main-simple`, `thm:IV.13`, `prop:char-BNT`, `thm:Fundamental-CFII`) and line ranges from the source `.tex`.*

---

## 9. Coverage crosswalk: SPGWC09 (arXiv:0909.5347) — Quantum Wielandt's Inequality

**Existing audit**: `docs/audits/issue-1449-wielandt-source-audit.md` (2026-05-07) covers the Theorem 1 statement faithfulness and MPS pipeline import inventory. This section provides an expanded source-paper crosswalk.

**Overall status**: **All Wielandt source theorems are `leanok` — zero sorrys, zero axioms** in `TNLean/Wielandt/`. The formalization is fully proved.

### 9.1 Proposition 3 — Equivalence of primitivity notions (l.504–565)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Proposition 3** `prop:equiv` (l.504) | 504–509 | (a) primitive ⇔ (b) eventually full Kraus rank ⇔ (c) strongly irreducible | `TNLean/Wielandt/Primitivity/Equivalence.lean` (full circular equivalence); `Primitivity/EasyDirections.lean` (b→a); `Primitivity/ImpliesStronglyIrreducibleAux.lean` (a→c); `Primitivity/StronglyIrreducibleToFullRank.lean` (c→b) | `leanok` |
| Prop `prop:iq` (l.447) | 447–449 | q(E_A) ≤ i(A) | `TNLean/Wielandt/SourceTheorems/WielandtInequality.lean` (`qIndex_le_iIndex_of_isPrimitivePaper`) | `leanok` |
| Prop (l.478) | 478–482 | For classical stochastic A: p(A)=q(A)=i(A) | **out of scope** (classical specialization) | — |

### 9.2 Lemma 1 — Nonzero-trace word (l.572–590)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Lemma 1** `lemma1` (l.572) | 572–576 | Primitive ⇒ ∃ word of length ≤ D²−d+1 with nonzero trace | `TNLean/Wielandt/SourceTheorems/NonzeroTraceWord.lean` (`exists_nonzero_trace_word_of_isPrimitivePaper_sharp`); internal proof via `SpanGrowth/NonzeroTraceProduct.lean` | `leanok` |
| Cumulative corollary (l.580–584) | 580–584 | dim[T_{D²−d+1}(A)] = D² | `TNLean/Wielandt/SourceTheorems/NonzeroTraceWord.lean` (`cumulativeSpan_eq_top_of_isPrimitivePaper_sharp`) | `leanok` |
| Positive-length variant | — | For D ≥ 2, positive-length word with nonzero trace exists | `TNLean/Wielandt/SourceTheorems/NonzeroTraceWord.lean` (`exists_nonzero_trace_word_of_isPrimitivePaper_sharp_pos`) | `leanok` |

### 9.3 Lemma 2 — Spreading and spanning (l.593–641)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Lemma 2(a)** `lemma2` (l.593) | 593–599 | Primitive + A₁ eigenvector ⇒ H_{D−1}(A,φ) = ℂ^D | `TNLean/Wielandt/SourceTheorems/EigenvectorSpreading.lean` (`vectorSpreadSpan_eq_top_of_isPrimitivePaper_of_eigenvector`); internal proof via `SpanGrowth/EigenvectorSpreading.lean` | `leanok` |
| **Lemma 2(b)** (l.593) | 593–599 | Primitive + noninvertible A₁ ⇒ |φ⟩⟨ψ| ∈ S_{D²−D+1}(A) | `TNLean/Wielandt/SourceTheorems/MatrixSpanSharpBound.lean` (`vecMulVec_mem_wordSpan_of_isPrimitivePaper_of_noninvertible_eigenvector`); internal proof via `RectangularSpan/Universality.lean` | `leanok` |
| Coarse existential 2(b) | — | ∃ N : S_N(A) = M_D(ℂ) | `TNLean/Wielandt/SourceTheorems/MatrixSpanExistence.lean` (`exists_wordSpan_eq_top_of_isPrimitivePaper`) | `leanok` |

### 9.4 Theorem 1 — Quantum Wielandt's inequality (l.645–655)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem 1** `thm:mainthm` (l.645) | 645–655 | Main theorem: i(A) bounds in three cases | `TNLean/Wielandt/SourceTheorems/WielandtInequality.lean` | `leanok` |
| Case (1) general bound | l.649 | i(A) ≤ (D² − d + 1) D² | `iIndex_le_general_of_isPrimitivePaper` | `leanok` |
| Case (2) invertible | l.650–651 | i(A) ≤ D² − d + 1 | `iIndex_le_of_mem_wordSpan_one_of_isUnit` (paper-faithful: X ∈ wordSpan A 1) | `leanok` |
| Case (3) noninvertible | l.652–653 | i(A) ≤ D² | `iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector` (paper-faithful) | `leanok` |
| q ≤ i bound | l.647 | q(E_A) ≤ i(A) (repeated from Prop. `prop:iq`) | `qIndex_le_iIndex_of_isPrimitivePaper` | `leanok` |

**Deviation note (#1049, resolved)**: The original formalization required the special matrix to be a single Kraus operator `A i₀`. This was resolved via one-step augmentation — the current `_of_mem_wordSpan_one_` variants accept an arbitrary element of `S₁(A)`, matching the paper's hypothesis exactly.

### 9.5 Theorem on zero-error capacity (l.736–771)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem** `thm:zero` (l.736) | 736–741 | Zero-error capacity dichotomy: C₀(E^n) ≥ 1 ∀n or C₀(E^{q(E)}) = 0 | **out of scope** (information theory, not MPS) | — |

### 9.6 Theorems on frustration-free Hamiltonians and MPS (l.828–859)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem** (l.828) | 828–831 | If L > i(A), MPS is unique ground state of parent Hamiltonian with spectral gap | PGVWC07 `uniqueGS` / `ParentHamiltonian/UniqueGroundState.lean` (partial, 3 sorrys) | **partial** — see §4.2 |
| **Theorem** (l.850) | 850–858 | Dichotomy for ground states of frustration-free Hamiltonians: D either O(1) or ≥ Ω(N^{1/5}) | **out of scope** | — |

### 9.7 MPS pipeline usage of Wielandt infrastructure

The MPS pipeline imports a focused subset of Wielandt declarations (detail in `docs/audits/issue-1449-wielandt-source-audit.md`, §4):

| MPS file | Wielandt import | Key declaration |
|---|---|---|
| `FundamentalTheorem/FiniteLength.lean` | `WielandtBound` | `wordSpan_eq_top_of_isInjective` |
| `FundamentalTheorem/ProportionalPrimitive.lean` | `Primitivity/ImpliesIrreducible` | `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef` |
| `CanonicalForm/Existence.lean` | `Primitivity/StronglyIrreducibleToFullRank` | `isNormal_of_isPrimitiveMPS_with_posDef` |
| `CanonicalForm/SectorComparison/TPPrimitiveReduction.lean` | `SpanGrowth/VectorToMatrixSpan`, `SpanGrowth/CumulativeSpan`, `RectangularSpan/Basic`, `Primitivity/ToNormal`, `Primitivity/StronglyIrreducibleToFullRank` | Multiple span and primitivity lemmas |
| `ParentHamiltonian/UniqueGroundState.lean` | `SpanGrowth/CumulativeToWordSpan` | `cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one` |
| `ParentHamiltonian/IntersectionProperty.lean` | `SpanGrowth/CumulativeToWordSpan` | Same |
| `ParentHamiltonian/WrappingWindow.lean` | `SpanGrowth/VectorToMatrixSpan` | Vector-to-matrix lemmas |

The `SourceTheorems/` files are **standalone paper-facing** declarations and are not imported by the MPS pipeline — correct design.

### 9.8 Sorry/axiom status for Wielandt

**Zero sorrys, zero axioms** across all 42 Wielandt `.lean` files. The entire quantum Wielandt formalization is fully proved and source-faithful to SPGWC09.
