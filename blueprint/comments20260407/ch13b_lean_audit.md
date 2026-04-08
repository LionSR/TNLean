# Audit of `ch13b_symmetry.tex`

Files read:

- `blueprint/src/chapter/ch13b_symmetry.tex`
- all files in `TNLean/MPS/Symmetry/`
- all matches of `TNLean/**/*ymmetr*.lean` and `TNLean/**/*tring*.lean`
- plus the tagged algebra declarations in `TNLean/Algebra/ProjectiveRepresentation.lean` and `TNLean/Algebra/CocycleCohomology.lean`

## Executive summary

Most of the physical-rotation, twisted-tensor, virtual-representation, permutation-twist, and C1/C2/C3 material matches Lean closely.

The main problems are concentrated in:

1. the cocycle/cohomology section, where the blueprint switches to `U(1)` language but Lean uses `Units ℂ = ℂˣ`;
2. the string-order section, where the blueprint uses paper-facing scalar definitions of local symmetry and string order, while Lean formalizes stronger/different virtual-boundary and virtual-unitary witness predicates;
3. several later theorems that omit essential Lean hypotheses;
4. one earlier corollary tagged to a wrapper theorem whose Lean declaration still takes the periodic FT as an explicit hypothesis.

## Requested findings

### 1. `U(1)` in the cocycle section vs `Units ℂ` in Lean

Yes: the blueprint uses `U(1)` language, but Lean uses `Units ℂ`.

- Lean `ScalarCocycle` is `G → G → Units ℂ` at `TNLean/Algebra/ProjectiveRepresentation.lean:25`.
- `IsCoboundary`, `CohomologousTo`, `IsCocycle`, `H2`, and `ProjectivelyEquivalent` all live over that `Units ℂ` API in `TNLean/Algebra/CocycleCohomology.lean:56-134`.
- The blueprint section intro says “establish the quotient `H^2(G,U(1))`” at `ch13b_symmetry.tex:437-441`.
- `def:is_cocycle` says `ω : G × G → U(1)` at `ch13b_symmetry.tex:528-536`.
- `def:h2_u1` says `H^2(G,U(1)) := Z^2(G,U(1))/~` at `ch13b_symmetry.tex:539-548`.

Does it matter?

- For literal blueprint-vs-Lean matching: yes, it matters. `U(1)` is strictly smaller than `Units ℂ`.
- For the current Lean proofs: the implementation only needs nonzero complex scalars, not norm-one scalars, so `Units ℂ` is the correct description of what is actually formalized.
- For the intended physics statement: if the chapter really wants `H^2(G,U(1))`, the blueprint currently overstates what Lean proves. Either the blueprint should say `ℂˣ`/`Units ℂ`, or Lean needs extra results showing the relevant cocycles are actually unit-modulus.

### 2. Do `LocalSymmetry` / `HasStringOrder` match Lean?

No.

`MPSTensor.IsLocalSymmetry` in Lean is:

- `∃ V μ, V` unitary, `‖μ‖ = 1`, `Vᴴ * Λ * V = Λ`, and
- `∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)`

at `TNLean/MPS/Symmetry/StringOrderDefs.lean:261-269`.

The blueprint definition at `ch13b_symmetry.tex:697-703` says instead:

- `‖R_L(u)‖ = ‖R_L(Id)‖` for all `L`.

That is not the same declaration. In Lean, that scalar condition appears later as a theorem-equivalent characterization under substantial hypotheses, not as the definition.

`MPSTensor.HasStringOrder` in Lean is:

- `∃ X Y c, 0 < c ∧ ∀ L, c ≤ ‖stringOrderBoundaryParam A u Λ X Y L‖`

at `TNLean/MPS/Symmetry/StringOrderDefs.lean:273-279`.

The blueprint definition at `ch13b_symmetry.tex:705-711` says instead:

- `∃ c > 0` such that `c ≤ ‖R_L(u)‖` for all `L`,
- with no boundary matrices `X, Y`.

Again, not the same declaration. Lean uses the boundary-refined formulation.

### 3. Which string-order theorems drop essential Lean hypotheses?

The following tagged results do.

`MPSTensor.twistedTransfer_spectralRadius_le_one`

- Blueprint `ch13b_symmetry.tex:824-833` omits `hNorm : transferMap A 1 = 1`.
- Lean theorem at `TNLean/MPS/Symmetry/StringOrder.lean:66` is stated for a concrete eigenpair `(ev, V)` with `V ≠ 0`; the blueprint paraphrase “every eigenvalue satisfies `|λ| ≤ 1`” is reasonable, but only after including the normalization hypothesis.

`MPSTensor.localSymmetry_iff_spectralRadius_one`

- Blueprint `ch13b_symmetry.tex:840-848` omits:
  - `hu : u * uᴴ = 1`
  - `Λ`
  - `hΛpos : Λ.PosDef`
  - `hΛtr : Matrix.trace Λ = 1`
  - `hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ`
  - `hNorm : transferMap A 1 = 1`
- Lean theorem at `TNLean/MPS/Symmetry/StringOrder.lean:294` is not literally “spectral radius one”; it is an equivalence with existence of a unitary eigenvector/eigenvalue witness for `twistedTransferMap A u`.

`MPSTensor.stringOrder_iff_localSymmetry`

- Blueprint `ch13b_symmetry.tex:862-871` omits the same hypotheses as above:
  - `hu`
  - `Λ`
  - `hΛpos`
  - `hΛtr`
  - `hΛfix`
  - `hNorm`
- It also uses blueprint definitions of local symmetry / string order that do not match Lean.
- Lean theorem is at `TNLean/MPS/Symmetry/StringOrder.lean:331`.

`MPSTensor.virtualUnitary_of_stringOrder`

- Blueprint `ch13b_symmetry.tex:883-898` omits:
  - `hu : u * uᴴ = 1`
  - the boundary matrix argument `Λ`
  - `hNorm : transferMap A 1 = 1`
- It also depends on Lean `HasStringOrder A u Λ`, not the blueprint scalar-only version.
- Lean theorem is at `TNLean/MPS/Symmetry/StringOrder.lean:363`.

`MPSTensor.hasStringOrder_of_symmetric_injective`

- Blueprint `ch13b_symmetry.tex:931-945` omits:
  - the specific group element `g`
  - `hUnitary : ∀ g, U g * (U g)ᴴ = 1`
  - `Λ`
  - `hΛpos : Λ.PosDef`
  - `hΛtr : Matrix.trace Λ = 1`
  - `hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ`
  - `hNorm : transferMap A 1 = 1`
- Lean theorem is at `TNLean/MPS/Symmetry/StringOrder.lean:496`.

`MPSTensor.stringOrder_invariant_of_samePhase`

- Blueprint `ch13b_symmetry.tex:964-977` omits:
  - separate injectivity hypotheses `hA`, `hB`
  - `hUnitary`
  - separate symmetry hypotheses `hSymmA`, `hSymmB`
  - both boundary states `Λ_A`, `Λ_B`
  - both positivity/trace/fixed-point/normalization packages
  - the theorem is quantified over `g`
- The actual Lean theorem at `TNLean/MPS/Symmetry/StringOrder.lean:552` does not use `IsSameSPTPhase` directly; it only uses the two symmetry hypotheses.

### 4. The proof near line 801: what exactly is missing?

At `ch13b_symmetry.tex:811-821`, the proof says the missing step is “the conversion of this doubled identity into a local relation on physical indices.”

The exact missing ingredient is:

- define `B_i := V * A_i * Vᴴ`;
- use `CondC2` plus `V * Vᴴ = 1` to prove `transferMap B = transferMap A`;
- then apply Kraus-freedom for equal channels to obtain a unitary matrix `u` such that
  `B_i = ∑_j u i j • A_j`.

That is exactly how Lean proves the theorem in `TNLean/MPS/Symmetry/StringOrderDefs.lean:426`:

- it does **not** “read the doubled identity back” directly from injectivity;
- it uses `kraus_rectangular_freedom` after proving equality of transfer maps.

So the missing step is not a local index manipulation. It is the channel-theoretic theorem saying that two Kraus families for the same CP map differ by a unitary mixing matrix.

### 5. `\notready` / `\leanok` status corrections

These `\leanok` tags are currently misleading unless the blueprint statements are rewritten to match Lean:

- `MPSTensor.zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical`
- `MPSTensor.cohomologousTo_of_isInjective`
- `TNLean.Algebra.ScalarCocycle.IsCocycle`
- `TNLean.Algebra.H2`
- `MPSTensor.IsLocalSymmetry`
- `MPSTensor.HasStringOrder`
- `MPSTensor.twistedTransfer_spectralRadius_le_one`
- `MPSTensor.localSymmetry_iff_spectralRadius_one`
- `MPSTensor.stringOrder_iff_localSymmetry`
- `MPSTensor.virtualUnitary_of_stringOrder`
- `MPSTensor.IsSameSPTPhase`
- `MPSTensor.hasStringOrder_of_symmetric_injective`
- `MPSTensor.stringOrder_invariant_of_samePhase`

Everything else I checked is close enough to keep `\leanok`.

### 6. Missing `[NeZero D]` / `0 < D` hypotheses

The clear missing positivity hypothesis is:

- `MPSTensor.cohomologousTo_of_isInjective` in the blueprint at `ch13b_symmetry.tex:499-526`.

Lean needs `hD : 0 < D` at `TNLean/MPS/Symmetry/CocycleCoboundary.lean:48` to cancel an invertible matrix scalar factor in the projective-representation law.

Related notes:

- `TNLean.Algebra.ProjectiveRepresentation.cocycle_of_assoc` already includes `D > 0` in both blueprint and Lean.
- `MPSTensor.virtual_rep_of_symmetric_injective_cocycle` already includes `D > 0` in both blueprint and Lean.
- The string-order theorems do not need a separate external `[NeZero D]` hypothesis because the Lean proofs derive positivity/nonemptiness from the nonzero eigenvector or from the boundary-state assumptions when needed.

## Tag-by-tag comparison

### Exact or essentially exact matches

These tagged blueprint items match the current Lean declarations up to harmless packaging differences.

- `MPSTensor.rotatePhysical`
- `MPSTensor.transferMap_rotatePhysical`
- `MPSTensor.isLeftCanonical_rotatePhysical`
- `MPSTensor.isIrreducibleTensor_rotatePhysical`
- `MPSTensor.isPeriodic_rotatePhysical`
- `MPSTensor.sameMPV₂_rotatePhysical`
- `MPSTensor.rotatePhysical_toTensorFromBlocks`
- `MPSTensor.isIrreducibleForm_rotatePhysical`
- `MPSTensor.twistedTensor`
- `MPSTensor.IsOnSiteSymmetric`
- `MPSTensor.twistedTensor_mul`
- `MPSTensor.twistedTensor_one`
- `MPSTensor.gaugeEquiv_twistedTensor_of_injective`
- `MPSTensor.virtual_symmetry_eq`
- `MPSTensor.gauge_unique_up_to_scalar`
- `TNLean.Algebra.ScalarCocycle`
- `TNLean.Algebra.ProjectiveRepresentation`
- `TNLean.Algebra.ProjectiveRepresentation.cocycle_of_assoc`
- `MPSTensor.virtual_rep_of_symmetric_injective`
- `MPSTensor.virtual_rep_of_symmetric_injective_cocycle`
- `TNLean.Algebra.ScalarCocycle.IsCoboundary`
- `TNLean.Algebra.ScalarCocycle.CohomologousTo`
- `TNLean.Algebra.ScalarCocycle.CohomologousTo.equivalence`
- `TNLean.Algebra.ScalarCocycle.isCoboundary_iff_cohomologousTo_one`
- `TNLean.Algebra.ProjectivelyEquivalent`
- `TNLean.Algebra.projRep_equiv_iff_cohomologous`
- `MPSTensor.OnSiteSymmetry`
- `MPSTensor.TwistedTensor`
- `MPSTensor.TwistedTensor_one`
- `MPSTensor.TwistedTensor_mul`
- `MPSTensor.twistedTransferMap`
- `MPSTensor.stringOrderParam`
- `MPSTensor.CondC1`
- `MPSTensor.CondC2`
- `MPSTensor.CondC3`
- `MPSTensor.condC2_iff_condC3`
- `MPSTensor.unitary_kraus_mixing`
- `MPSTensor.condC1_imp_condC2`
- `MPSTensor.condC2_imp_condC1_of_injective`

For `MPSTensor.condC2_imp_condC1_of_injective`, the statement matches, but the blueprint proof sketch is stale: Lean proves it using Kraus freedom, not by a direct injectivity/span argument.

### Tagged items that need correction

`MPSTensor.zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical`

- Blueprint corollary at `ch13b_symmetry.tex:176-194` states a direct result.
- Lean theorem at `TNLean/MPS/FundamentalTheorem/Applications.lean:75` is only a wrapper that still takes the periodic equal-case FT as an explicit hypothesis `hPeriodicEq`.

`MPSTensor.cohomologousTo_of_isInjective`

- Blueprint at `ch13b_symmetry.tex:499-526` omits `hD : 0 < D`.
- Lean theorem at `TNLean/MPS/Symmetry/CocycleCoboundary.lean:48` needs it.
- Blueprint says `ω₁ ∼ ω₂`; Lean returns `CohomologousTo ω₂ ω₁`. That direction difference is harmless because cohomology is symmetric.

`TNLean.Algebra.ScalarCocycle.IsCocycle`

- Blueprint at `ch13b_symmetry.tex:528-536` says `ω : G × G → U(1)`.
- Lean at `TNLean/Algebra/CocycleCohomology.lean:66` is over `ScalarCocycle G = G → G → Units ℂ`.

`TNLean.Algebra.H2`

- Blueprint at `ch13b_symmetry.tex:539-548` says `H^2(G,U(1))`.
- Lean at `TNLean/Algebra/CocycleCohomology.lean:122` is the quotient of `Units ℂ`-valued cocycles.

`MPSTensor.IsLocalSymmetry`

- Blueprint at `ch13b_symmetry.tex:697-703` defines local symmetry by equality of scalar string-order magnitudes.
- Lean at `TNLean/MPS/Symmetry/StringOrderDefs.lean:261` defines a virtual-unitary witness predicate with boundary-state invariance.

`MPSTensor.HasStringOrder`

- Blueprint at `ch13b_symmetry.tex:705-711` uses the one-sided scalar parameter `R_L(u)`.
- Lean at `TNLean/MPS/Symmetry/StringOrderDefs.lean:273` uses the boundary-refined predicate with witnesses `X, Y`.

`MPSTensor.twistedTransfer_spectralRadius_le_one`

- Blueprint at `ch13b_symmetry.tex:824-833` drops `hNorm : transferMap A 1 = 1`.
- Lean theorem at `TNLean/MPS/Symmetry/StringOrder.lean:66` is phrased for a concrete eigenpair witness.

`MPSTensor.localSymmetry_iff_spectralRadius_one`

- Blueprint at `ch13b_symmetry.tex:840-848` drops `hu`, `Λ`, `hΛpos`, `hΛtr`, `hΛfix`, `hNorm`.
- It also uses the paper-facing scalar definition of local symmetry instead of the Lean one.
- Lean theorem is at `TNLean/MPS/Symmetry/StringOrder.lean:294`.

`MPSTensor.stringOrder_iff_localSymmetry`

- Blueprint at `ch13b_symmetry.tex:862-871` drops `hu`, `Λ`, `hΛpos`, `hΛtr`, `hΛfix`, `hNorm`.
- It also depends on the mismatched blueprint definitions of `IsLocalSymmetry` and `HasStringOrder`.
- Lean theorem is at `TNLean/MPS/Symmetry/StringOrder.lean:331`.

`MPSTensor.virtualUnitary_of_stringOrder`

- Blueprint at `ch13b_symmetry.tex:883-898` drops `hu`, `Λ`, `hNorm`.
- It also relies on the mismatched blueprint `HasStringOrder`.
- Lean theorem is at `TNLean/MPS/Symmetry/StringOrder.lean:363`.

`MPSTensor.IsSameSPTPhase`

- Blueprint at `ch13b_symmetry.tex:919-928` bakes in “injective” and “both symmetric under `U`” into the prose.
- Lean at `TNLean/MPS/Symmetry/StringOrder.lean:407` defines `IsSameSPTPhase A B U` purely by existence of two projective representations intertwining the twists and having cohomologous cocycles.
- So the blueprint statement is stronger/different than the actual declaration.

`MPSTensor.hasStringOrder_of_symmetric_injective`

- Blueprint at `ch13b_symmetry.tex:931-960` suppresses the actual argument list and several essential hypotheses.
- Lean theorem at `TNLean/MPS/Symmetry/StringOrder.lean:496` needs `g`, `hUnitary`, `Λ`, `hΛpos`, `hΛtr`, `hΛfix`, `hNorm`.

`MPSTensor.stringOrder_invariant_of_samePhase`

- Blueprint at `ch13b_symmetry.tex:964-977` states a broad phase-invariance slogan.
- Lean theorem at `TNLean/MPS/Symmetry/StringOrder.lean:552` is narrower and explicit: it assumes separate symmetry hypotheses for `A` and `B`, two boundary states, and both canonical normalization packages, then proves the equivalence for each `g`.

## Suggested cleanup order

1. Rewrite the cocycle/cohomology section from `U(1)` to `ℂˣ`/`Units ℂ`, unless there is a planned Lean upgrade proving norm-one cocycles.
2. Rewrite `LocalSymmetry` and `HasStringOrder` to the actual Lean definitions.
3. Rewrite the downstream string-order theorems to include the full Lean hypotheses.
4. Fix the proof sketch for `condC2_imp_condC1_of_injective` to mention Kraus freedom explicitly.
5. Add `D > 0` to `cocycle_gauge_independence`.
