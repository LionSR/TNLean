# Issue #782 blocker note — commuting form / GSNNCH branch

## What landed in this branch

This branch adds `TNLean/MPS/MPDO/CommutingForm.lean`, which formalizes the
**target side** of Appendix C.2 / Theorem 4.9(iii):

- a chain-level notion `MPOTensor.CommutingFormData` for a positive two-site
  factor whose translated copies commute on an `N`-site periodic chain,
- the global MPO predicate `MPOTensor.HasCommutingForm`,
- the GSNNCH packaging `MPOTensor.GSNNCHData` / `MPOTensor.IsGSNNCH`, and
- the equivalences
  - `MPOTensor.isGSNNCHAt_iff_exists_commutingForm`,
  - `MPOTensor.isGSNNCH_iff_hasCommutingForm`,
  - `MPOTensor.isGSNNCHWithZCL_iff_hasCommutingForm_and_isZCL`.

So the **downstream API** needed for Theorem 4.9 is now present.

## Honest remaining blocker

The missing theorem is the **upstream entropy / local-structure bridge** that
should produce `HasCommutingForm` from the strong-area-law hypotheses.

The paper route is:

1. SAL gives SSA equality on the relevant tripartite reduction.
2. Hayashi's characterization yields the block decomposition of the middle site.
3. One extracts the local `η_{k,h}` data of Appendix C.2.
4. From that local `η`-structure one constructs the commuting two-site factor
   and proves the global commuting-form identity.

Steps 1–2 are partially available in the repo through the sanctioned entropy
API (`TNLean.Entropy.StrongSubadditivity`, `TNLean.Entropy.MarkovChain`), but
steps 3–4 are not yet formalized for MPDO tensors. In particular, the project
still lacks the MPDO-side local-structure record that would bridge the Hayashi
block decomposition to the explicit two-site commuting factor.

## Precise theorem statement now isolated by the new API

With the new file in place, the mathematically precise remaining theorem is:

> For a simple MPDO tensor satisfying the Appendix C.2 strong-area-law
> hypotheses, prove `MPOTensor.HasCommutingForm`.

Equivalently, once the local `η`-structure is defined, the immediate next Lean
statement should be a theorem of the form

```lean
-- schematic statement, not yet in the library
 theorem hasCommutingForm_of_etaLocalStructure
    {d D : ℕ} {M : MPOTensor d D}
    (hEta : -- output of the local-structure / issue #781 branch --) :
    HasCommutingForm M
```

and the final Appendix C.2 corollary would be

```lean
-- schematic statement, pending future `Simple` / `SAL` predicates
 theorem hasCommutingForm_of_simple_of_sal
    {d D : ℕ} {M : MPOTensor d D}
    (hSimple : ...)
    (hSAL : ...) :
    HasCommutingForm M
```

At that point `MPOTensor.isGSNNCH_of_hasCommutingForm` immediately packages the
result as the GSNNCH side of Theorem 4.9.
