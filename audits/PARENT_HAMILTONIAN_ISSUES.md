# Parent Hamiltonian Formalization — Tracking Issues

**Area**: MPS/ParentHamiltonian
**Goal**: Formalize the parent Hamiltonian theory for MPS from §IV.C of arXiv:2011.12127 (Cirac–Pérez-García–Schuch–Verstraete RMP review), building on the existing FT-MPS, transfer matrix, and quantum channel infrastructure. Each issue co-develops the **blueprint chapter** and the **Lean proof** together.

**References**:
- [CPGSV21] Cirac, Pérez-García, Schuch, Verstraete, Rev. Mod. Phys. 93, 045003 (2021), arXiv:2011.12127
- [FNW92] Fannes, Nachtergaele, Werner, Commun. Math. Phys. 144, 443 (1992)
- [PGVWC07] Pérez-García, Verstraete, Wolf, Cirac, Quant. Inf. Comput. 7, 401 (2007)
- [KL18] Kastoryano, Lucia, J. Stat. Mech. 2018, 033105 (2018)

**Convention**: Every issue produces **both** a blueprint section (in `ch14_parent_hamiltonian.tex` / `ch15_correlations.tex`) **and** the corresponding Lean file(s). Blueprint definitions carry `\lean{...}` tags and `\leanok` from day one; proofs carry `\leanok` once the Lean proof compiles.

---

## Reading Material

Each issue should be approached by reading the relevant sections from these papers. Local copies are in `Papers/`.

### Primary source
| Paper | Local path | What to read |
|-------|-----------|--------------|
| **[CPGSV21]** Cirac et al., RMP 2021 | `Papers/2011.12127/TN-Review-main.tex` | **§IV.C** (lines 1972–2300): parent Hamiltonian definitions, uniqueness, gaps, stability. **§II.B.3** (lines 433–442): transfer matrix, correlation length, exponential decay formula |

### Foundational papers (proofs)
| Paper | Local path | What to read |
|-------|-----------|--------------|
| **[FNW92]** Fannes–Nachtergaele–Werner, CMP 1992 | *(not local — CMP 144, 443)* | §3–4: original FCS parent Hamiltonian construction, gapped proof, uniqueness. The seminal paper. |
| **[PGVWC07]** Pérez-García et al., QIC 2007 | `Papers/quant-ph_0608197/MPSarchive.tex` | §4: canonical form + injectivity length; §5: parent Hamiltonians; §6: ground space structure. The modern treatment. |
| **[N96]** Nachtergaele, CMP 1996 | *(not local — CMP 175, 565)* | Degenerate MPS, explicit gap bounds, martingale method precursors |

### Gap and martingale method
| Paper | Local path | What to read |
|-------|-----------|--------------|
| **[KL18]** Kastoryano–Lucia, JSTAT 2018 | *(not local — arXiv:1705.09491)* | §2–3: the martingale criterion, proof of necessity and sufficiency. The clean modern treatment of the gap method. |
| **[Knabe88]** Knabe, JSP 1988 | *(not local — JSP 52, 627)* | The finite-size gap criterion |
| **[GM16]** Gosset–Mozgunov, JMP 2016 | *(not local — arXiv:1512.00088)* | Improved Knabe bound: 6/n(n+1) |

### Correlation decay
| Paper | Local path | What to read |
|-------|-----------|--------------|
| **[HK06]** Hastings–Koma, CMP 2006 | *(not local — arXiv:math-ph/0507008)* | Spectral gap → exponential clustering (the converse direction; background context) |
| **[LP22]** Lancien–Pérez-García, AHP 2022 | `Papers/1906.11682/` | Correlation length in random MPS/PEPS; useful for understanding the transfer matrix spectral framework |

### Symmetries & phases (future directions)
| Paper | Local path | What to read |
|-------|-----------|--------------|
| **[SPG11]** Schuch–Pérez-García–Cirac, PRB 2011 | `Papers/1010.3732/` | §III–IV: SPT classification, phases connected by gapped paths. Uses parent Hamiltonian gap stability. |
| **[MPGSC18]** Molnár et al., NJP 2018 | `Papers/1804.04964/paper_normal.tex` | The algebraic FT approach. §3: one-sided inverse, virtual insertion — techniques reusable for intersection property. |

### How to use this table
- **Phase 1 (definitions)**: Read [CPGSV21] §IV.C lines 1985–2012, [PGVWC07] §5
- **Phase 2 (uniqueness)**: Read [CPGSV21] lines 2013–2094 carefully, [FNW92] §3–4, [PGVWC07] §5–6
- **Phase 3 (correlations)**: Read [CPGSV21] §II.B.3 lines 433–442, [LP22] §2
- **Phase 4 (gap)**: Read [KL18] §2–3, [CPGSV21] lines 2160–2200
- **Phase 5 (degenerate)**: Read [CPGSV21] lines 2098–2140, [PGVWC07] §6

---

## Blueprint Files

- `blueprint/src/chapter/ch14_parent_hamiltonian.tex` — Covers Layers 0–4 (definitions, basic properties, uniqueness, degenerate GS, gap)
- `blueprint/src/chapter/ch15_correlations.tex` — Covers Layer 5 (connected correlator, spectral decomposition, exponential decay, correlation length)
- Update `blueprint/src/content.tex` to include both new chapters
- Update `blueprint/src/references.bib` with [FNW92], [PGVWC07], [KL18], [N96]

## Lean Files

```
TNLean/MPS/ParentHamiltonian/
├── GroundSpace.lean            -- PH-0a: G_L definition + dimension bound
├── Defs.lean                   -- PH-0b,c,d: parent interaction, Hamiltonian, FF
├── Basic.lean                  -- PH-1a,b: MPS is ground state, FF property
├── IntersectionProperty.lean   -- PH-2a,b: intersection + closure
├── UniqueGroundState.lean      -- PH-2c,d: uniqueness theorems
├── DegenerateGS.lean           -- PH-3a: ground space = BNT span
├── Martingale.lean             -- PH-4a: abstract martingale criterion
├── Gap.lean                    -- PH-4b,c: gap theorem
└── Correlations.lean           -- PH-5a–d: correlator formula, decay, ξ
```

---

## Tracked Tasks

### Layer 0: Infrastructure / Definitions
📖 **Read first**: [CPGSV21] lines 1985–2012; [PGVWC07] `Papers/quant-ph_0608197/MPSarchive.tex` §5

- [ ] **PH-0a**: Define ground space $\mathcal{G}_L(A)$
  - **Blueprint**: `\begin{definition}[Ground space]` with `\lean{MPSTensor.groundSpace}`, `\leanok`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
  - **Math**: $\mathcal{G}_L = \bigl\{\sum_{i_1,\ldots,i_L} \tr(A^{i_1}\cdots A^{i_L} X)\ket{i_1\cdots i_L} : X \in \MN{D}\bigr\}$
  - **Depends on**: `def:eval_word`, `def:mpv` (ch02)
  - **Key property**: $\dim(\mathcal{G}_L) \leq D^2$ (the image of a $D^2$-dim space)
  - ★★☆

- [ ] **PH-0b**: Define parent interaction $h \geq 0$ with $\ker(h) = \mathcal{G}_L$
  - **Blueprint**: `\begin{definition}[Parent interaction]` with `\lean{MPSTensor.parentInteraction}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Defs.lean`
  - **Math**: Hermitian PSD operator on $(\mathbb{C}^d)^{\otimes L}$ whose kernel equals $\mathcal{G}_L$; concretely the orthogonal projector onto $\mathcal{G}_L^\perp$
  - **Depends on**: PH-0a
  - ★★★

- [ ] **PH-0c**: Define parent Hamiltonian $H_N = \sum_{i=1}^N h_i$
  - **Blueprint**: `\begin{definition}[Parent Hamiltonian]` with `\lean{MPSTensor.parentHamiltonian}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Defs.lean`
  - **Math**: $h_i$ acts as $h$ on sites $i, \ldots, i{+}L{-}1 \pmod{N}$ and as identity elsewhere
  - **Depends on**: PH-0b
  - **Design decision**: represent $N$-site space as `(Fin N → Fin d) → ℂ`, matching existing `mpv`
  - ★★★

- [ ] **PH-0d**: Define frustration-freeness
  - **Blueprint**: `\begin{definition}[Frustration-free Hamiltonian]` with `\lean{MPSTensor.IsFrustrationFree}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Defs.lean`
  - **Math**: $H = \sum h_i \geq 0$ is frustration-free if $H\ket{\psi} = 0$ implies $h_i\ket{\psi} = 0$ for all $i$
  - **Depends on**: PH-0c
  - ★★☆

### Layer 1: Basic Properties
📖 **Read first**: [CPGSV21] lines 2009–2012 (frustration-freeness); [PGVWC07] §5, Proposition 3

- [ ] **PH-1a**: MPS is in the ground space: $H_N\ket{\psi(A)} = 0$
  - **Blueprint**: `\begin{theorem}[MPS is a ground state]` with `\lean{MPSTensor.parentHamiltonian_annihilates}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Basic.lean`
  - **Proof sketch** (for blueprint): Each $h_i\ket{\psi(A)} = 0$ because $\ket{\psi(A)}$ restricted to any $L$ consecutive sites lies in $\mathcal{G}_L$ (by construction, with $X$ = product of matrices on the complement). Sum of zeros is zero.
  - **Depends on**: PH-0a through PH-0d
  - ★★★

- [ ] **PH-1b**: Parent Hamiltonian is frustration-free
  - **Blueprint**: `\begin{corollary}[Frustration-freeness]` with `\lean{MPSTensor.parentHamiltonian_frustrationFree}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Basic.lean`
  - **Proof sketch**: Immediate from PH-1a + each $h_i \geq 0$
  - **Depends on**: PH-1a
  - ★★☆

- [ ] **PH-1c**: Dimension bound $\dim(\mathcal{G}_L) \leq D^2$
  - **Blueprint**: `\begin{lemma}[Dimension bound on ground space]` with `\lean{MPSTensor.groundSpace_finrank_le}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
  - **Proof sketch**: $\mathcal{G}_L$ is the image of $X \mapsto \sum \tr(A^w X)\ket{w}$ from $\MN{D}$, which has dimension $D^2$.
  - **Depends on**: PH-0a
  - ★★☆

- [ ] **PH-1d**: Non-triviality: $d^L > D^2 \implies \mathcal{G}_L \neq (\mathbb{C}^d)^{\otimes L}$
  - **Blueprint**: `\begin{lemma}[Non-trivial parent interaction exists]` with `\lean{MPSTensor.groundSpace_ne_top}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
  - **Proof sketch**: $\dim\mathcal{G}_L \leq D^2 < d^L = \dim((\mathbb{C}^d)^{\otimes L})$, so $\mathcal{G}_L \subsetneq (\mathbb{C}^d)^{\otimes L}$.
  - **Depends on**: PH-1c
  - ★★

### Layer 2: Unique Ground State (Injective Case)
📖 **Read first**: [CPGSV21] lines 2013–2094 (invert-and-regrow argument); [FNW92] §3–4; [PGVWC07] §5–6; also [MPGSC18] `Papers/1804.04964/paper_normal.tex` §3 for the algebraic one-sided-inverse technique (already formalized in `MPS/Chain/OneSidedInverse.lean`)

- [ ] **PH-2a**: Intersection property
  - **Blueprint**: `\begin{lemma}[Intersection property]` with `\lean{MPSTensor.groundSpace_intersection}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/IntersectionProperty.lean`
  - **Math**: For injective $A$: $\mathcal{G}_{1,\ldots,L+1} \cap \mathcal{G}_{2,\ldots,L+2} = \mathcal{G}_{1,\ldots,L+2}$
  - **Proof sketch** (for blueprint): Take $\ket{\phi} \in \mathcal{G}_{1,\ldots,L+1} \cap \mathcal{G}_{2,\ldots,L+2}$. From membership in $\mathcal{G}_{1,\ldots,L+1}$, there exists $X$ with $\phi = \sum \tr(A^w X)\ket{w}$. From membership in $\mathcal{G}_{2,\ldots,L+2}$, there exists $Y$. On the overlap (sites $2,\ldots,L+1$), injectivity gives a left-inverse $A^{-1}$. Apply it to uniquely determine $X$ (and hence $Y$), showing $\phi \in \mathcal{G}_{1,\ldots,L+2}$.
  - **Depends on**: PH-0a, `def:injective` (ch02)
  - **Reference**: \cite{FNW92}, \cite{PGVWC07}
  - ★★★★

- [ ] **PH-2b**: Closure property
  - **Blueprint**: `\begin{lemma}[Closure under extension]` with `\lean{MPSTensor.groundSpace_mono}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/IntersectionProperty.lean`
  - **Math**: $\mathcal{G}_L \hookrightarrow \mathcal{G}_{L+1}$ (appropriate embedding)
  - **Depends on**: PH-0a
  - ★★★

- [ ] **PH-2c**: Unique ground state ($2L_0$ sites)
  - **Blueprint**: `\begin{theorem}[Unique ground state — injective case]` citing \cite{PGVWC07}
  - **Lean tag**: `\lean{MPSTensor.parentHamiltonian_unique_gs_injective}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
  - **Math**: If $A$ is injective after blocking $L_0$ sites, the parent Hamiltonian on $2L_0$ sites has a unique ground state.
  - **Proof sketch**: Iterate the intersection property across the chain. Injectivity forces the boundary condition $X$ to be uniquely determined, hence only one ground state.
  - **Depends on**: PH-2a, PH-2b
  - ★★★★

- [ ] **PH-2d**: Optimal unique ground state ($L_0+1$ sites)
  - **Blueprint**: `\begin{theorem}[Unique ground state — optimal range]` citing \cite{FNW92}, \cite{PGVWC07}
  - **Lean tag**: `\lean{MPSTensor.parentHamiltonian_unique_gs_normal}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
  - **Math**: For a normal MPS with injectivity length $L_0$, the parent Hamiltonian on $L_0+1$ sites has a unique ground state.
  - **Proof sketch**: Refined "regrow by 1" intersection argument.
  - **Depends on**: PH-2a, PH-2b, PH-2c
  - ★★★★

### Layer 3: Degenerate Ground Space (Block-Injective Case)
📖 **Read first**: [CPGSV21] lines 2098–2140 (block structure, topological sectors); [FNW92] §4; [PGVWC07] §6

- [ ] **PH-3a**: Ground space = span of BNT
  - **Blueprint**: `\begin{theorem}[Ground space of block-injective MPS]` citing \cite{FNW92}, \cite{PGVWC07}
  - **Lean tag**: `\lean{MPSTensor.parentHamiltonian_gs_eq_bnt_span}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`
  - **Math**: For $N \geq L_0+1$, the ground space of the parent Hamiltonian equals $\spn\{\ket{V^{(N)}(A_j)} : j = 1,\ldots,g\}$ where $\{A_j\}$ is a basis of normal tensors.
  - **Proof sketch**: Each BNT element generates a ground state (by block structure). Converse: any ground state restricted to an injective block is determined by the intersection property. Block-diagonal structure prevents mixing.
  - **Depends on**: PH-2d, `def:canonical_form_bnt` (ch10)
  - ★★★★★

### Layer 4: Spectral Gap
📖 **Read first**: [KL18] arXiv:1705.09491 §2–3 (the clean modern martingale treatment); [CPGSV21] lines 2160–2200 (martingale method + gap theorem); [FNW92] (original gap proof)

- [ ] **PH-4a**: Martingale criterion (abstract)
  - **Blueprint**: `\begin{theorem}[Martingale criterion for spectral gap]` citing \cite{KL18}
  - **Lean tag**: `\lean{FrustrationFree.spectralGap_of_martingale}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Martingale.lean`
  - **Math**: For a frustration-free $H = \sum h_i$ with projector terms, if for all overlapping pairs:
    $$h_i h_j + h_j h_i \geq -c_{ij}(1-\gamma)(h_i + h_j)$$
    with $\sum c_{ij} \leq 1$, then $\lambda_{\min}^+(H) \geq \gamma$.
  - **Proof sketch**: From $h_i^2 = h_i$ (projectors), expand $H^2 = \sum h_i + \sum' h_ih_j + \sum'' h_ih_j$. The non-overlapping sum $\sum'' \geq 0$. The martingale condition bounds the overlapping sum. Conclude $H^2 \geq \gamma H$.
  - **Note**: Self-contained operator inequality; potential Mathlib contribution
  - **Depends on**: PH-0d
  - ★★★

- [ ] **PH-4b**: Verify martingale condition for MPS
  - **Blueprint**: `\begin{lemma}[Martingale condition for MPS parent Hamiltonians]`
  - **Lean tag**: `\lean{MPSTensor.parentHamiltonian_martingale}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Gap.lean`
  - **Math**: The martingale condition holds for parent Hamiltonian terms of an injective MPS, with constants depending on the tensor $A$ but independent of $N$.
  - **Proof sketch**: Use injectivity to bound the angle between $\ker(h_i)$ and $\ker(h_j)$ away from zero.
  - **Depends on**: PH-4a, PH-2a, existing transfer matrix spectral gap
  - ★★★★

- [ ] **PH-4c**: Gap theorem
  - **Blueprint**: `\begin{theorem}[All MPS parent Hamiltonians are gapped]` citing \cite{FNW92}, \cite{Nachtergaele1996}
  - **Lean tag**: `\lean{MPSTensor.parentHamiltonian_gapped}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Gap.lean`
  - **Math**: $\exists\,\gamma > 0$ such that $\lambda_{\min}^+(H_N) \geq \gamma$ uniformly in $N$.
  - **Depends on**: PH-4a, PH-4b
  - ★★★★

### Layer 5: Correlation Decay
📖 **Read first**: [CPGSV21] §II.B.3 lines 433–442 (transfer matrix spectrum → correlation formula); [LP22] `Papers/1906.11682/` §2 (correlation length framework); [CPGSV21] lines 885–890 (E²=E ↔ zero correlation length)

- [ ] **PH-5a**: Define connected two-point correlator
  - **Blueprint** (in ch15): `\begin{definition}[Connected two-point correlator]` with `\lean{MPSTensor.connectedCorrelator}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Correlations.lean`
  - **Math**: $C(X,Y;n) = \langle X_0 Y_n \rangle - \langle X_0 \rangle \langle Y_n \rangle$
  - **Depends on**: `def:mpv`, `def:transfer_map` (ch02, ch04)
  - ★★☆

- [ ] **PH-5b**: Correlation function as sum of exponentials
  - **Blueprint** (in ch15): `\begin{theorem}[Spectral decomposition of correlations]` citing \cite{CPGSV21}
  - **Lean tag**: `\lean{MPSTensor.connectedCorrelator_eq_sum}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Correlations.lean`
  - **Math**: $C(X,Y;n) = \sum_{j=2}^{D^2} c_{XY}(j)\,\lambda_j^n$ where $\lambda_j$ are eigenvalues of $E$.
  - **Proof sketch**: Write $C(X,Y;n)$ in terms of powers of the transfer matrix. The leading eigenvalue $\lambda_1 = 1$ contributes $\langle X\rangle\langle Y\rangle$ which cancels in the connected part. The remainder is the spectral expansion over $\lambda_2, \ldots, \lambda_{D^2}$.
  - **Depends on**: PH-5a, existing spectral theory in `Spectral/`
  - ★★★

- [ ] **PH-5c**: Exponential decay bound
  - **Blueprint** (in ch15): `\begin{theorem}[Exponential decay of correlations]` citing \cite{FNW92}
  - **Lean tag**: `\lean{MPSTensor.connectedCorrelator_exponential_bound}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Correlations.lean`
  - **Math**: $|C(X,Y;n)| \leq C_{XY} \cdot |\lambda_2|^n = C_{XY} \cdot e^{-n/\xi}$
  - **Proof sketch**: Triangle inequality on the spectral sum; bound each $|\lambda_j| \leq |\lambda_2|$; sum the coefficients.
  - **Depends on**: PH-5b, spectral gap $|\lambda_2| < 1$ (from primitivity, existing)
  - ★★★

- [ ] **PH-5d**: Define correlation length $\xi$
  - **Blueprint** (in ch15): `\begin{definition}[Correlation length]` with `\lean{MPSTensor.correlationLength}`
  - **Lean**: `TNLean/MPS/ParentHamiltonian/Correlations.lean`
  - **Math**: $\xi = -1/\log|\lambda_2(E)|$ where $\lambda_2$ is the second-largest eigenvalue (in modulus) of the transfer matrix $E$.
  - **Depends on**: PH-5c, `Spectral/SpectralGap.lean`
  - ★★

---

## Dependencies on Existing Infrastructure

| Existing component | Files | Status | Used by |
|---|---|---|---|
| `MPSTensor` + `evalWord` + `coeff` + `mpv` | `MPS/Defs.lean` | ✅ | All |
| `IsInjective`, `IsNormal`, `IsNBlkInjective` | `MPS/Defs.lean` | ✅ | PH-2* |
| `GaugeEquiv.sameMPV` | `MPS/Defs.lean` | ✅ | Background |
| `transferMap` | `MPS/Core/Transfer.lean` | ✅ | PH-5* |
| Spectral gap of transfer matrix | `Spectral/SpectralGap.lean` | ✅ | PH-5b,c |
| `IsCanonicalFormBNT` | `MPS/CanonicalForm/` | ✅ | PH-3a |
| FT-MPS (Cor. IV.5) | `MPS/FundamentalTheorem/` | ✅ 0 sorry | Background |
| QPF (Wolf Thm 6.3) | `QPF/Assembly.lean` | ✅ | PH-5b |
| Primitivity / CP maps | `Channel/Primitive.lean` | ✅ | PH-4b |
| Blueprint ch02 (MPS defs) | `ch02_mps.tex` | ✅ | ch14, ch15 |
| Blueprint ch04 (channels) | `ch04_channels.tex` | ✅ | ch15 |
| Blueprint ch06 (spectral) | `ch06_spectral.tex` | ✅ | ch15 |

---

## Suggested Implementation Order

**Phase 1 — Definitions + easy wins** (PH-0a → 0b → 0c → 0d → 1c → 1d → 1a → 1b)
- Write §14.1–14.2 of blueprint simultaneously (8 items × ~20–30 lines/item)
- Delivers: Complete definition layer + basic properties, all with `\leanok`

**Phase 2 — Uniqueness** (PH-2b → 2a → 2c → 2d)
- Write §14.3 of blueprint simultaneously (4 items)
- Delivers: Unique ground state theorem (the flagship result)
- Key challenge: Formalizing the "invert-and-regrow" argument

**Phase 3 — Correlations** (PH-5a → 5d → 5b → 5c)
- Write ch15 of blueprint simultaneously (4 items)
- Delivers: Exponential decay of correlations
- Leverages existing spectral machinery heavily

**Phase 4 — Gap** (PH-4a → 4b → 4c)
- Write §14.4 of blueprint simultaneously (3 items)
- Delivers: All MPS parent Hamiltonians are gapped

**Phase 5 — Degenerate** (PH-3a)
- Write §14.5 of blueprint simultaneously (1 item)
- Delivers: Full ground space characterization

---

## Blueprint Chapter Outlines

### Chapter 14: Parent Hamiltonians (`ch14_parent_hamiltonian.tex`)

```latex
\chapter{Parent Hamiltonians}\label{ch:parent_ham}
% Primary: \cite{Cirac2021Matrix} §IV.C
% Proofs: \cite{Fannes1992Finitely}, \cite{PerezGarcia2007Matrix}

§14.1 The ground space and parent Hamiltonian
  % \cite{Cirac2021Matrix} lines 1985–2012
  % \cite{PerezGarcia2007Matrix} §5
  - Definition: ground space G_L(A)                          [PH-0a]
  - Lemma: dim G_L ≤ D²                                     [PH-1c]
  - Lemma: non-trivial for d^L > D²                         [PH-1d]
  - Definition: parent interaction                           [PH-0b]
  - Definition: parent Hamiltonian                           [PH-0c]
  - Definition: frustration-free                             [PH-0d]

§14.2 Basic properties
  % \cite{Cirac2021Matrix} lines 2009–2012
  - Theorem: MPS is a ground state                           [PH-1a]
  - Corollary: frustration-freeness                          [PH-1b]

§14.3 Uniqueness of the ground state
  % \cite{Fannes1992Finitely} §3–4
  % \cite{PerezGarcia2007Matrix} §5–6
  % \cite{PerezGarcia2008PEPS}
  - Lemma: closure property                                  [PH-2b]
  - Lemma: intersection property                             [PH-2a]
  - Theorem: unique GS for injective MPS (2L₀ sites)        [PH-2c]
  - Theorem: unique GS for normal MPS (L₀+1 sites)          [PH-2d]

§14.4 Spectral gap
  % \cite{Kastoryano2018Martingale} §2–3
  % \cite{Fannes1992Finitely}, \cite{Nachtergaele1996Spectral}
  - Theorem: martingale criterion (abstract)                 [PH-4a]
  - Lemma: martingale condition for MPS                      [PH-4b]
  - Theorem: all MPS parent Hamiltonians are gapped          [PH-4c]

§14.5 Ground space of non-injective MPS
  % \cite{Fannes1992Finitely}, \cite{PerezGarcia2007Matrix} §6
  - Theorem: ground space = span of BNT                      [PH-3a]
```

### Chapter 15: Exponential Decay of Correlations (`ch15_correlations.tex`)

```latex
\chapter{Exponential Decay of Correlations}\label{ch:correlations}
% Primary: \cite{Cirac2021Matrix} §II.B.3
% Also: \cite{Fannes1992Finitely}, \cite{Lancien2021Correlation}

§15.1 Connected correlations
  % \cite{Cirac2021Matrix} lines 433–442
  - Definition: connected two-point correlator               [PH-5a]

§15.2 Spectral decomposition
  % \cite{Cirac2021Matrix} lines 436–440
  - Theorem: correlator as sum of exponentials               [PH-5b]

§15.3 Exponential decay
  % \cite{Fannes1992Finitely}
  % \cite{Hastings2006Spectral} (converse direction, background)
  - Theorem: exponential decay bound                         [PH-5c]
  - Definition: correlation length ξ                         [PH-5d]
  - Remark: zero correlation length ↔ E² = E ↔ RGFP
  - Remark: contrast with PEPS (power-law possible)
```

---

## Design Notes

- **Hilbert space representation**: Use `(Fin N → Fin d) → ℂ` matching the existing `mpv` definition. The $N$-site inner product is `∑ σ, f σ * conj (g σ)`. This avoids introducing new tensor product infrastructure.

- **Parent interaction as projector**: The simplest formalization takes $h = \mathbf{1} - P_{\mathcal{G}_L}$ where $P_{\mathcal{G}_L}$ is the orthogonal projector onto $\mathcal{G}_L$. This automatically satisfies $h \geq 0$ and $\ker(h) = \mathcal{G}_L$.

- **The martingale criterion (PH-4a)** is a self-contained operator inequality that could be contributed to Mathlib independently.

- **Forward direction only**: We formalize MPS structure → exponential decay, which is elementary. The converse (Hastings–Koma: spectral gap → exponential clustering) requires Lieb–Robinson bounds and is out of scope.

- **Blueprint `\uses` chains**: Each definition/theorem in ch14-15 will reference the appropriate ch02/ch04/ch06 definitions via `\uses`, maintaining the dependency graph automatically.
