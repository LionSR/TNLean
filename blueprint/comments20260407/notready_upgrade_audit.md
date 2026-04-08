# `\notready` audit for proposed `\leanok` upgrades

Audit date: 2026-04-08

Method:
- Read each target declaration in source and checked whether its proof body contains `sorry`.
- For transitive status, used Lean `#print axioms` on the current source when possible; `sorryAx` means the declaration is not sorry-free transitively.
- For stale/missing oleans, noted the current-source compilation issue explicitly.

## Findings

1. `MPSChainTensor.fundamentalTheorem_blockedChain`
   - Status: **SORRY-FREE**
   - Source body in `TNLean/MPS/Chain/BlockedChainFT.lean` has no `sorry`.
   - It is just:
     - `fundamentalTheorem_injective_chain (blockedChain A L n) ...`
   - Current-source axiom check:
     - `MPSChainTensor.fundamentalTheorem_blockedChain` -> `[propext, Classical.choice, Quot.sound]`
     - `MPSChainTensor.fundamentalTheorem_injective_chain` -> `[propext, Classical.choice, Quot.sound]`
     - `MPSTensor.fundamentalTheorem_singleBlock` -> `[propext, Classical.choice, Quot.sound]`

2. `irreducible_semigroup_implies_primitive`
   - Status: **SORRY-FREE**
   - Source body in `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean` has no `sorry`.
   - Current-source axiom check:
     - `irreducible_semigroup_implies_primitive` -> `[propext, Classical.choice, Quot.sound]`

3. `qds_irreducible_iff_primitive`
   - Status: **SORRY-FREE**
   - Source body in `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean` has no `sorry`.
   - Current-source axiom check:
     - `qds_irreducible_iff_primitive` -> `[propext, Classical.choice, Quot.sound]`

4. `MPSTensor.chainGroundSpace_eq_mpvSubmodule`
   - Status: **HAS SORRY (via transitive `sorryAx`, most likely through `MPSTensor.boundary_matrix_commutes` / stale ParentHamiltonian artifacts)**
   - The source body in `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` itself has no literal `sorry`.
   - Direct helper checks:
     - `MPSTensor.contiguous_mem_groundSpace` -> clean
     - `MPSTensor.mpv_mem_chainGroundSpace` -> clean
     - Remaining nontrivial project helper used in the proof is `MPSTensor.boundary_matrix_commutes`
   - Compiled axiom check available from the current environment:
     - `MPSTensor.chainGroundSpace_eq_mpvSubmodule` -> `[propext, sorryAx, Classical.choice, Quot.sound]`
   - Important caveat:
     - Current source is not in a certifiable state here:
       - `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean` currently fails to elaborate (`wordSpan_eq_top_of_isInjective` / `neZero_d_of_isInjective` unresolved).
       - `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` then fails because `WrappingWindow.olean` is missing.
     - So this declaration is not safe to upgrade to `\leanok`.

5. Periodic FT declarations from `ch11_assembly.tex`

   - `MPSTensor.zgauge_construction`
     - Status: **SORRY-FREE**
     - Source body has no `sorry`.
     - Current-source axiom check -> `[propext, Classical.choice, Quot.sound]`

   - `MPSTensor.equalCase_zgauge_pipeline`
     - Status: **SORRY-FREE**
     - Source body has no `sorry`.
     - Current-source axiom check -> `[propext, Classical.choice, Quot.sound]`

   - `MPSTensor.fundamentalTheorem_periodic_equalCase_matching`
     - Status: **SORRY-FREE**
     - Source body has no `sorry`.
     - Current-source axiom check -> `[propext, Classical.choice, Quot.sound]`

   - `MPSTensor.fundamentalTheorem_periodic_equalCase`
     - Status: **SORRY-FREE**
     - Source body has no `sorry`.
     - Current-source axiom check -> `[propext, Classical.choice, Quot.sound]`

6. `TNLean.PEPS.GaugeEquiv.sameState`
   - Status: **HAS SORRY (via `TNLean.PEPS.GaugeEquiv.sameState` itself; also `applyGauge_stateCoeff`)**
   - In `TNLean/PEPS/FundamentalTheorem.lean`, the proof body is directly:
     - `sorry`
   - The immediately preceding theorem `applyGauge_stateCoeff` is also directly `sorry`.
   - Current-source axiom check:
     - `TNLean.PEPS.GaugeEquiv.sameState` -> `[propext, sorryAx, Classical.choice, Quot.sound]`

## Bottom line

Safe for `\leanok` on sorry-freeness grounds:
- `MPSChainTensor.fundamentalTheorem_blockedChain`
- `irreducible_semigroup_implies_primitive`
- `qds_irreducible_iff_primitive`
- `MPSTensor.zgauge_construction`
- `MPSTensor.equalCase_zgauge_pipeline`
- `MPSTensor.fundamentalTheorem_periodic_equalCase_matching`
- `MPSTensor.fundamentalTheorem_periodic_equalCase`

Not safe for `\leanok`:
- `MPSTensor.chainGroundSpace_eq_mpvSubmodule`
- `TNLean.PEPS.GaugeEquiv.sameState`
