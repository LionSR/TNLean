# Issue #671 — orbit-sum lift, real follow-up (Option C)

## Outcome

This PR does **not** prove the full orbit-sum lift unconditionally. Instead it lands the
full **downstream transport layer** for the non-periodic Gap §1 pipeline and reduces the
remaining blocker to the single named input

```lean
hProjStep :
  ∀ k X,
    IsOrthogonalProjection X →
    X * P k = X →
    P k * X = X →
    IsOrthogonalProjection ((transferMap A†) X)
```

or, equivalently, to the corner-irreducibility endpoint

```lean
∀ k, IsIrreducibleOnCorner (P k) ((transferMap A†) ^ m)
```

for the cyclic projections `P k`.

## What is genuinely new relative to the report-only scout

The scout only asked whether the orbit-sum mechanism looked reusable. This PR makes that
question materially sharper by formalizing everything **after** the orbit-sum step:

1. `cyclic_projection_mem_multiplicativeDomain` plus left/right multiplication transport
   for cyclic projections of `transferMap A†`.
2. A generic compression theorem transporting
   - corner primitivity of `cornerRestriction P T`, and
   - corner irreducibility `IsIrreducibleOnCorner P T`
   across the `*`-preserving compression equivalence `φ` to the compressed sector tensor.
3. Two public non-periodic canonical-form endpoints:
   - `primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_cornerIrreducible`
   - `primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_projStep`

So the remaining gap is no longer the vague “sector-irreducibility lift” of the scout.
It is now precisely:

- either prove `hProjStep`, then call the new public theorem; or
- prove corner irreducibility directly, then call the even more primitive endpoint.

## Why this helps Gap §1

The consumer `exists_sectorDecomp_of_tp_primitive_irr_blocks` wants TP blocks whose
transfer maps are primitive **and** whose tensors are irreducible. The cyclic-sector
existence theorem already provided the TP/compression data, and the channel-level cyclic
results already gave corner primitivity. This PR closes the missing transport from those
corner facts to the compressed sector tensors. What remains is exactly the orbit-sum /
`hProjStep` input needed to produce corner irreducibility.

## Remaining blocker

The honest remaining blocker is still the one-step projection-preservation statement
`hProjStep` for sector-supported orthogonal projections under `transferMap A†`.
That is the non-periodic analogue of the old orbit-sum scout target.
