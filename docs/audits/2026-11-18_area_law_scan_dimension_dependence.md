# Dimension dependence of the two-dimensional area-law proof

This analysis-only note records which steps of the formalized two-dimensional area law
depend on the spatial dimension. It was written for a research discussion about a
three-dimensional area law. Nothing here is a Lean statement or a claim of a theorem.
No Lean or blueprint file is changed.

The source is OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The formalization lives under `TNLean/PEPS/AreaLaw/` on `main` at `7376dab`. The campaign
page is `docs/campaign/openai-area-law-peps-proof`.

Paths below are relative to `TNLean/PEPS/AreaLaw/` unless they start with `TNLean/`.
Every `file:line` was read on `main`. A statement marked **(inferred)** is our own
reasoning about a hypothetical three-dimensional version and was not read from Lean.

## 1. The dependency spine

The final theorem is `uniformAreaLaw` (`AreaLawTheorem.lean:54`). It is proved by
`uniformAreaLaw_closed` (`AreaLawExplicitConstant.lean:179`), which goes through
`uniformAreaLaw_explicit_of_le` (`AreaLawExplicitConstant.lean:105`). That proof feeds
three propositions into the assembly
`regionalEntropy_le_of_collar_amplification_twoFamilies_constants`
(`BoundaryTheorem.lean:319`):

- **Prop 9.6**, the sublinear collar bound;
- **Prop 10.2**, amplification;
- **Prop 11.2**, the two-family decomposition.

The constant is `uniformAreaLawConstantOf q C₂ C₃ = c_D log q + c_M c_D / 2`
(`BoundaryTheorem.lean:285`).

The key declarations follow, grouped by branch. They give "the bound", "the role" and
"Lean" for each step. In the tables, the step is the first column, the source is
`file:line` and the role is one line.

### Assembly

| # | Declaration | file:line | Role |
|---|---|---|---|
| 1 | `regionalEntropy_le_of_collar_amplification_twoFamilies_constants` | `BoundaryTheorem.lean:319` | The proof of Thm 1.1 at fixed constants: for each piece, the bound `I(X_i : Aᶜ ∪ earlier same-family) ≤ c_M n_i^{-100}` |
| 2 | `regionalEntropy_le_residual_add_half_sum` (Lemma 11.1) | `TwoFamilies.lean:61`, `:110` | `S(A) ≤ S(D) + ½ ∑ ε_i` for an ordered two-family partition |
| 3 | `regionalEntropy_le_boundary_of_partition_estimates` | `BoundaryEntropyAssembly.lean:39` | Combines item 2 with `S(D) ≤ \|D\| log q` |
| 4 | `regionalEntropy_eq_zero_of_edgeBoundary_eq_empty` | `ZeroBoundary.lean:166` | The case `b = 0`: the ground state factorizes |

### Collar branch (Props 9.5, 9.6)

| # | Declaration | file:line | Role |
|---|---|---|---|
| 5 | `sublinearCollarBound_real_of_boxEntropy_explicit`, `sublinearCollarBound_real` | `PhysicalCollarInformation.lean:66`, `:249` | Prop 9.6, from a safe-box bound `F_box(r) ≤ B r^{1+boxError}`; the output is listed after this table |
| 6 | `Template.collar_cut_card_le` | `CollarInformation.lean:299` | Cut sizes `≤ 4n` or `8n` and `\|S₀\| ≤ 10 n²` for a template collar |
| 7 | `template_final_mutualInformation_of_boxEntropy_explicit` | `Scan/TemplateFinalInformation.lean:126` | The final template scan: `I ≤ C n^{62497/62500} ≤ C n^{1-ε}` |
| 8 | `finalSharp_error_exponents` | `Scan/FinalSharpErrorPower.lean:36` | The exponent identity `1 + boxError − scannerOmega = 62497/62500 < 1 − ε` |
| 9 | `template_source_entropy_bounds` (template entropy) | `Scan/TemplateSourceEntropy.lean:74` | From safe rectangles `C·size^{1+e}`, gives template `≤ C_e n^{1+e}` and prefixes `≤ C_e (n L^e + n)` |
| 10 | `sum_rpow_cappedDyadicPartition_le` (Lemma 9.4) | `Geometry/CappedDyadicPartitionByScale.lean:48` | The dyadic moment `∑ (2^k)^{1+e} ≤ (A + B/(2^e−1)) L^e`, given side-length budgets |
| 11 | `boxEntropy_le_boxError_explicit` (Prop 9.5) | `Scan/PhysicalBoxBootstrap.lean:390` | `F_box(r) ≤ C r^{1+boxError}`, by the bootstrap |
| 12 | `sourceBootstrap_entropy_improvement_explicit` | `Scan/SourceBootstrapEntropy.lean:144` | One scan round: `n^{1+η}` becomes `n^{1+(1−ℓ)η}`; it assumes `T.card ≤ C_T n²` and rows `≤ n` |
| 13 | `uniform_power_bound_of_boxBootstrapRounds`, `boxBootstrapConstant` | `Scan/ExponentBootstrap.lean:150`, `:121` | The finite exponent iteration `e ↦ (1−ℓ)e`; small scales are absorbed by `V n²` |
| 14 | `boxBootstrapConstant_le_pow_pow` | `Scan/BootstrapIterateBound.lean:98` | The closed bound `C_j ≤ ((A+1)(1+C₀))^{(2K)^M}` on the bootstrap constants |
| 15 | `boxEntropy_le_initialBoxConstant_mul_rpow` (Prop 3.3) | `InitialBoxEstimate.lean:563` | The initial bound `F_box(r) ≤ C₀ r^{1+e₀}` with `0 < e₀ < 1`, from a scale recurrence |
| 16 | `FiniteFamilyTransportBound` | `Scan/ActualRoundTransport.lean:149` | The replica transport input, stated over an arbitrary `Fintype` |

The output of Prop 9.6 (item 5) is:

- `I(A∩T : (A∩T_L)ᶜ) ≤ C n^{1−ε}`;
- the cuts of `X`, `S₀` and `S₀ \ X` have at most `C n` edges;
- `|S₀| ≤ C n²`.

### Amplification branch (Prop 10.2)

| # | Declaration | file:line | Role |
|---|---|---|---|
| 17 | `amplificationBound` | `AmplificationProof.lean:683` | Prop 10.2: some `r ≤ C n^{radiusExponent}` with `I(X' : J) ≤ C n^{-M}` off `N_{2r}(S₀)` |
| 18 | `amplificationTime`, `amplificationRadius` | `Amplification/GoodRealization.lean:103`, `:108` | `t_* = (6/g)(I + w + K log n)` and `r = ⌈(C'(t_* + K log n))^{1/α}⌉` |
| 19 | `amplificationRadius_le_coefficient_mul_rpow` | `Amplification/RadiusBound.lean:56` | `I ≤ C₀ n^{1−ε}` gives `r ≤ C n^{(1−ε)/α}` |
| 20 | `radius_exponent_gaps`, `collar_add_radius_isLittleO` | `Amplification/RadiusScales.lean:43`, `:117` | `1−ε < radiusExponent < β`, so `L + 2r = o(n^β)` |
| 21 | `norm_commutator_le_graphDistance` | `GraphPropagation.lean:161` | The Lieb–Robinson bound on the domain graph |
| 22 | `typicalProjection_failure_le_stretchedExp` | `Amplification/TypicalProjectors.lean:139` | Typical window `w = n^{3/5}`; it uses `\|∂Y\| ≤ C₀ n` |

### Geometry branch (Prop 11.2)

| # | Declaration | file:line | Role |
|---|---|---|---|
| 23 | `twoFamilyDecomposition` | `Geometry/TwoFamilyAssembly.lean:880` | Prop 11.2: `\|D\| ≤ C b`, clearances `2 n_i^β`, `∑ n_i^{-100} ≤ C b` |
| 24 | `Template`, `IsAllowedSlope` | `Geometry/Templates.lean:74`, `:37`; `scale` at `:98` | A union of lattice triangles and rectangles with slopes `0, ∞, ±1`; `Ctpl·pieceCount·(s₀+1) ≤ n` |
| 25 | `card_dyadicLayerIndices_boundary_le` | `Geometry/DyadicLayers.lean:207` | Layer-`k` cells number `≤ 8(2C+1)² b` |
| 26 | `exists_sparse_dyadic_belt_shift`, `layerScale_exponent_le` | `Geometry/FineBelts.lean:88`; `Geometry/DyadicScales.lean:69` | The belt cells are a fraction `2^{-δk/2}` |
| 27 | `cellFanNext`, `initialRegion_sector_assignment_changes_even` | `Geometry/CellFanCycle.lean:68`; `Geometry/InitialSectorCycle.lean:64` | The cyclic order of eight sectors around a mark, and the even number of colour changes |
| 28 | `cellFanRun_connectedComponents_equiv` | `Geometry/FanRunComponents.lean:165` | Removing radial segments cuts a cell into one component per run |
| 29 | `IsUniformRepairInduction`, `uniformRepairInductionStatement_holds` | `Geometry/RepairInductionStatement.lean:42`, `:66–70`; `Geometry/RepairInduction.lean:111` | Repair invariant: same-colour closures meet only in the finite mark set |
| 30 | `IsBirthSeparationConstant`, `IsBeltFacet`, `eventually_fine_clearance` | `Geometry/TwoFamilyAssembly.lean:284`; `Geometry/BeltFacetSeparation.lean:50`; `Geometry/RepairDepth.lean:270` | The birth separation `c₁ u^{ρ₀}` with `c₁ = 1/112` (`Geometry/BirthSeparationInitial.lean:382`), turned into `2 n^β` clearance since `ρ₀ > β` |

### Exponents

The exponents are in `Geometry/Exponents.lean`:

| Exponent | Value | Line |
|---|---|---|
| `boxError` | `2·10⁻⁶` | 29 |
| `amplificationEpsilon` | `10⁻⁵` | 47 |
| `beta` | `1 − boxError` | 50 |
| `amplificationPower` | `10⁶` | 54 |
| `alpha` | `10⁶/(10⁶+1)` | 58 |
| `geometryDelta` | `2·10⁻⁷` | 61 |
| `geometryEll` | `10⁻⁵` | 70 |

`radiusExponent = (1−ε)/α` is defined at `Amplification/RadiusScales.lean:37`.

## 2. Dimension-dependence table

The classes are:

- **(A)** dimension-free: the step works on any finite graph or domain;
- **(B)** uses only geometry that generalizes directly to `ℤ³`;
- **(C)** planar or square-specific.

All carriers are typed `Finset (ℤ × ℤ)` with `ManyBody.planeDomainGraph`; see
`ambientDilation` at `TNLean/Lattice/FiniteDomain.lean:62` and `LocalHamiltonian` at
`TNLean/Lattice/LocalHamiltonian.lean:45`. This typing is not counted as a dependence: the
definitions themselves are graph-generic (`FiniteDomain.lean:50`).

| Step | Items | Class | 3D analogue, or what fails |
|---|---|---|---|
| Two-family entropy cancellation and assembly | 1–4 | A | Unchanged. Linearity in `b` comes only from Prop 11.2's `\|D\| ≤ C b` and `∑ n_i^{-100} ≤ C b` |
| Replica transport bound | 16 | A | Stated over any `Fintype V` |
| Bootstrap iteration and its constant | 13, 14 | A | Volume absorption `V n² → V n³` |
| Prop 3.3 recurrence | 15 | B **(inferred)** | `M³` children, `λ ∈ (M², M³)`, inhomogeneity `C_buf M³ r²`, `e₀ = log_M λ − 2 ∈ (0,1)`. The 2D form is in the first note below |
| Clearance transfer | `Scan/BoxClearanceComparison.lean:48` | B | "At most four" rectangles becomes eight |
| Template entropy and dyadic moment | 9, 10 | A for the lemma, B for the budgets | See the second note below |
| Scan rounds | 7, 12 | B **(inferred)**, with planar inputs | `T.card ≤ n³`, rows `≤ n²`. The row and slab structure of item 24 must be rebuilt |
| Templates as planar polygons | 24 | C as written, B in spirit **(inferred)** | See the third note below |
| Ball counts and Lieb–Robinson | 21, `LatticeCounts.lean:54` | A in mechanism, B in constants | Ball size `1 + 2d(d+1)` becomes the octahedral count `O(d³)` |
| Amplification time and radius | 17–20, 22 | A in mechanism, **cost obstacle** in 3D | See §3, rows 5–6 |
| Dyadic layers and counts | 25 | B | `8(2C+1)³ b`, with `b` the number of crossing edges |
| Belt sparsity | 26 | B, but the exponents need re-tuning **(inferred)** | See §3, row 7 |
| Fans, cyclic sectors, runs, stars and repair wedges | 27–29; `RepairFanCones.lean:38`; `SimultaneousRepair.lean:155` | **C** | See the fourth note below |
| Birth separation by facets | 30 | C (facet lemma); A (`ρ₀ > β` arithmetic) | `IsBeltFacet` is a half-plane `a x₁ + b x₂ ≤ n`. Its proof uses that two non-parallel facet lines meet at an integer point (a `2×2` determinant, `Geometry/BeltFacetSeparation.lean:54–56`). In 3D the facets would be planes, and two planes meet in a line, not a point |

Notes on the rows above:

- **Prop 3.3 recurrence (item 15).** In 2D the recurrence is
  `F(Mr) ≤ ((1−p)M² + p·2(2C_pad+1)M) F(r) + C_buf M² r` (`InitialBoxEstimate.lean:28–36`,
  `:405–430`), with `λ = (1−p/2)M²` and `e₀ = log_M λ − 1`.
- **Template entropy and dyadic moment budgets (items 9, 10).** In 2D the budgets are
  side-length budgets: `4^K·#cap ≤ |S|` (`Geometry/CappedDyadicPartition.lean:200`) and
  `2^k·#mixed ≲ perimeter` (`Geometry/RectangleMixedSquares.lean:30`). In 3D they become
  face-area budgets `4^k·#cells ≲ area` and the moment `∑ (2^k)^{2+e}`.
- **Templates (item 24).** Pieces are lattice triangles or rectangles in `ℝ × ℝ` with four
  slopes (`Templates.lean:37`, `:48`). The scale field `pieceCount·s₀ ≲ n` is a curve-length
  budget. A 3D template must cover a surface, so it needs polyhedra, a budget
  `pieceCount·s₀² ≲ n²`, and slab sections in place of `Geometry/TemplateRowBounds.lean`.
- **Fans, cyclic sectors, runs, stars and repair wedges (items 27–29).**
  - In 2D:
    - the link of a mark is a cycle: `cellFanNext` uses `finRotate 8`;
    - a binary label changes an even number of times around it;
    - equal-label runs are cyclic intervals;
    - radial segments separate a square (a Jordan-type argument);
    - same-colour contacts that are not repaired are isolated points, so the invariant
      "contacts ⊆ marks" holds.
  - What fails in 3D **(inferred)**:
    - the link of a point is a sphere, so there is no cyclic order;
    - in a 2-coloured cubical complex, same-colour cells meet along edges (curves) as well as
      vertices, so the contacts are not a finite set;
    - removing radial segments does not disconnect a cube.

## 3. Cost comparison

Write `b` for the boundary size and `n` for the template scale.

| # | Quantity | 2D bound as in Lean | Naive 3D analogue **(inferred)** | Does the closure survive? **(inferred)** |
|---|---|---|---|---|
| 1 | Sublinear collar bound (Prop 9.6) | See the first note below | See the first note below | Yes as a scan statement, given 3D templates. The trouble is downstream, in row 5 |
| 2 | Template entropy | Template `≤ C_e n^{1+e}`; prefixes `≤ C_e(n L^e + n)` (`Scan/TemplateSourceEntropy.lean:74`); core `C(18 + 4/(2^e−1)) n s₀^e` (`Geometry/TemplateBoxEntropy.lean:40`) | `C_e n^{2+e}`, prefixes `C_e(n² L^e + n²)` | Yes. The factor `1/(2^e−1) ≈ 7·10⁵` at `e = boxError` does not depend on dimension |
| 3 | Dyadic moment (Lemma 9.4) | `∑ (2^k)^{1+e} ≤ (A + B/(2^e−1)) L^e` with `2^k·#cells` budgets (`Geometry/CappedDyadicPartitionByScale.lean:48`) | `∑ (2^k)^{2+e} ≤ (A + B/(2^e−1)) L^e` with `4^k·#cells` budgets | Yes. The geometric-series arithmetic (`Geometry/DyadicWeightedSum.lean:28`) is unchanged |
| 4 | Bootstrap iterate | `e_j = (1−ℓ)^j e₀` and `C_j ≤ ((A+1)(1+C₀))^{(2K)^M}` (`Scan/BootstrapIterateBound.lean:98`) | See the second note below | Yes, given a 3D Prop 3.3 with `e₀ < 1`. It does not close from the trivial volume bound alone: at `e₀ = 1` the gain `1 − e₀` is zero (`Scan/BootstrapParameters.lean:35–49`) |
| 5 | Amplification time | `t_* = (6/g)(I + w + K log n)`, linear in the collar information `I` (`Amplification/GoodRealization.lean:103`) | From `I ≤ C n^{2−ε}` only the upper bound `t_* ≲ n^{2−ε}/g` follows | See row 6 |
| 6 | Amplification radius vs clearance | `r ≤ C n^{(1−ε)/α}` (`Amplification/RadiusBound.lean:56`), which needs `(1−ε)/α < β < 1` (`Amplification/RadiusScales.lean:43`) | The guaranteed radius is only `r ≲ n^{(2−ε)/α} ≈ n²`. This is an upper bound: a smaller information gives a smaller radius | **No, as stated.** The guarantee `L + 2r = o(n^β)` would need `(2 − ε)/α < β < 1`. The available information estimate cannot certify a radius below the clearance scale `n^β`, or even below the template size `n` |
| 7 | Belt sparsity | See the third note below | See the third note below | Yes after re-tuning `ζ`, e.g. `ζ = 1 − δ/4` |
| 8 | Typical window | `w = n^{3/5} ≥ √\|∂Y\|`, with `\|∂Y\| ≤ C₀ n` (`Amplification/TypicalProjectors.lean:139`, lines 164–176) | `w ≳ n` | Harmless next to row 6, but `w` already exceeds the 2D radius budget |
| 9 | Error sum and residual | `∑ n_i^{-100} ≤ C b` and `\|D\| ≤ C b`. They are piece counts such as `repairStage_markIndex_prefix_le` (`Geometry/RepairTotalMarkPrefixCount.lean:57`) and `primaryPitchIndices_error_sum_le` (`Geometry/InitialPrimaryErrorSum.lean:58`) | `(2C+1)³` constants; `27^j` descendants in place of `9^j` | Yes, provided row 7 decays and the class (C) repair of §2 exists |

Notes on the rows above:

- **Row 1 (sublinear collar bound).** In 2D:
  - `I ≤ C n^{1−ε}`;
  - cuts `≤ C n`;
  - `|S₀| ≤ C n²` (`BoundaryTheorem.lean:70`).

  The naive 3D analogue is `I ≤ C n^{2−ε}` (sublinear in the collar area), cuts `≤ C n²`,
  and `|S₀| ≤ C n³`.
- **Row 4 (bootstrap iterate).** The 3D iteration is the same scalar iteration toward
  `r^{2+δ}`, with `V n³` absorption.
- **Row 7 (belt sparsity).**
  - In 2D the ratio `4^{k−ℓ}/2^{p−ℓ} ≤ 4·2^{−δk/2}` (`Geometry/FineBelts.lean:44`) holds
    because `2k − p − ℓ ≤ 2 − δk/2` (`Geometry/DyadicScales.lean:69`), where `ℓ = ⌊ζk⌋`
    and `p = ⌊(1+δ)k⌋`.
  - In 3D the ratio is `8^{k−ℓ}/2^{p−ℓ}`, with exponent `3k − p − 2ℓ`. With the same `ζ`
    and `δ` the exponent is `≈ 0`, so there is **no decay**.

## 4. Verdict

Two barriers stand out. The rest of the spine is (A), or (B) with routine exponent changes.

1. **The amplification radius is linear in the collar information.** This is the most
   substantive barrier, and it is quantitative.
   - Read:
     - the clock time is `t_* = (6/g)(I + w + K log n)` (`Amplification/GoodRealization.lean:103`);
     - the radius comes from it through the Lieb–Robinson light cone
       (`Amplification/GoodRealization.lean:108`, `GraphPropagation.lean:161`);
     - the proof needs `radiusExponent < β`, numerically
       `0.999991 < 0.999998` (`Amplification/RadiusScales.lean:43`, docstring at `:72`);
     - this is used at `BoundaryTheorem.lean:432` to turn Prop 11.2's `2 n^β` clearance
       into Prop 10.2's hypothesis.
   - Inferred:
     - in 3D the natural collar estimate is only sublinear in the collar *area*,
       `I ≤ C n^{2−ε}`, so the radius it guarantees is only `r ≲ n^{(2−ε)/α} ≈ n²`;
     - this is an upper bound, not a lower bound: the obstruction is that the estimate cannot
       certify a radius below the clearance `n^β` that templates of linear size `n` provide,
       not that the radius must exceed `n`;
     - a 3D argument needs either a collar bound `I ≪ n`, which is sublinear in the linear
       size and therefore far stronger than an area law at scale `n`, or an amplification
       mechanism whose time is not linear in `I`.
2. **The two-family colouring with pointwise same-colour contacts is planar.**
   - Read:
     - the repair invariant (`Geometry/RepairInductionStatement.lean:66–70`) requires
       same-colour closures to meet only at the finite mark set;
     - it is established using a cyclic sector order (`Geometry/CellFanCycle.lean:68`), an
       even number of colour changes (`Geometry/InitialSectorCycle.lean:64`), separation of
       a cell by radial segments (`Geometry/FanRunComponents.lean:165`), and planar cross
       products and facets (`Geometry/RepairFanCones.lean:38`,
       `Geometry/BeltFacetSeparation.lean:50`).
   - Inferred:
     - in 3D, same-colour contacts of a 2-coloured cell complex include curves;
     - the repair would have to run along the 1-skeleton (tubes with planar cross-sections)
       and then at vertices;
     - alternatively one could use more families. Lemma 11.1 (`TwoFamilies.lean:61`) is
       stated for `Fin 2`, with the factor `½`, and a `k`-family version was not checked.

The scan machinery itself is planar as written but not in principle **(inferred)**. This
covers the Prop 3.3 recurrence, the bootstrap, template entropy, the dyadic moment and the
transport bound. A 3D version needs polyhedral templates and slab sections, and its exponent
arithmetic closes.

## 5. Candidate low-rank seed proposition (unproved)

This is recorded as a proposition under discussion only. It is not formalized, no Lean
statement is proposed, and no claim is made that it holds.

> **Proposition (low-rank seed, unproved).** Fix a spatial dimension `d`, a local
> dimension `q`, an interaction range `R` and a gap `γ > 0`. Then there is a constant
> `C = C(q, R, γ, d)` with the following property. Let `Λ ⊂ ℤ^d` be a finite domain and `H`
> a Hamiltonian on `Λ` with bounded finite-range interactions, a unique ground state `Γ` and
> spectral gap at least `γ`. Then for every cut `A ⊆ Λ` there is a unit vector `φ` such that:
>
> - its Schmidt rank across `(A, Aᶜ)` is at most `exp(C |∂A|)`;
> - `|⟨φ, Γ⟩|² ≥ exp(−C |∂A|)`.
>
> The constant `C` does not depend on `|Λ|`, `H`, `Γ` or `A`.

How the proposition relates to the approximate-ground-state-projector (AGSP) route:

- **The 1D trade-off in Lean (read).** The one-dimensional formalization uses an AGSP with
  operator Schmidt rank `D` and shrinking factor `δ` subject to the trade-off `D δ ≤ 1/2`.
  This is `exists_cut_product_filtered_output`,
  `TNLean/MPS/AreaLaw/AKLV/Initialization.lean:47`, hypothesis `htrade`. Under it, a product
  vector already has overlap `≥ 1/√(2D)` with the ground state.
- **The trade-off in 2D and above (inferred, following the AGSP literature).**
  - Known AGSPs have `log D` growing at least linearly in `|∂A|`, while `δ` is set by the
    polynomial degree and the gap.
  - For large boundaries `D·δ ≤ 1/2` fails.
  - That condition is what lets a product vector serve as the starting point; the seed is
    meant to replace it.
  - Given a seed with squared overlap `μ = exp(−C|∂A|)` and Schmidt rank `S = exp(C|∂A|)`,
    the normalization estimate behind `exists_cut_product_filtered_output` gives, after `m`
    applications of an AGSP, squared error at most `2δ^m/μ` and Schmidt rank at most
    `S·D^m`. So the small overlap raises the number of filtering steps to
    `m ≈ (C|∂A| + log(1/ε)) / log(1/δ)`, but it imposes no condition `D·δ ≲ μ`.
  - The resulting rank is `exp(C|∂A| + m log D)`. Its logarithm is linear in `|∂A|` only if
    `log D / log(1/δ)` stays bounded independently of `|∂A|`.
  - Whether AGSPs with that ratio exist in two or more dimensions is the open point. Known
    constructions have `log D` growing with the boundary, so the seed does not by itself
    close the AGSP route there. Any further condition needed by a particular entropy
    bootstrap would have to be derived explicitly.
- **The seed and the barriers of §4 (inferred).** The seed is independent of the scan proof
  recorded above. It does not remove either barrier of §4.
