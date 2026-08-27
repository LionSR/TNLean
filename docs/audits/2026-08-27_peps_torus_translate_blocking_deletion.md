# PEPS torus translate-blocking compatibility deletion

`TNLean/PEPS/TorusBlockingData.lean` contained six superseded declarations with
no in-tree consumers. The maintainer explicitly confirmed that TNLean does not
promise public API compatibility, so the earlier review decision to retain these
names as deprecated compatibility API does not apply. The module is deleted
outright and its import is removed from `TNLean/PEPS.lean`.

## Deleted declarations and direct replacements

| Deleted declaration | Replacement for future code |
|---|---|
| `regionInjectivityDataOf_translate_eq` | use the translation-invariance fixed-point equation `hA a b` directly |
| `translateBlockingData` | reconstruct a `NormalEdgeBlockingData` record from `D' := transportBlockingDataAlong A (translate a b) D`, rewriting the edge by `translateEdge_eq_map` and casting the three injectivity fields along the fixed-point equality described below |
| `translateBlockingData_red` | the `red` projection of that reconstructed record, definitionally equal to `D'.red` |
| `translateBlockingData_blue` | the corresponding projection of `transportBlockingDataAlong` |
| `translateBlockingData_complement` | the corresponding projection of `transportBlockingDataAlong` |
| `isCrossingEdge_translateBlockingData` | `isCrossingEdge_transportBlockingDataAlong` at `translate a b`, after unfolding the reconstructed record and rewriting `translateEdge_eq_map` |

The transport result is indexed by
`regionInjectivityDataOf (A.transport (translate a b))`, not directly by
`regionInjectivityDataOf A`. To migrate the deleted constructor, first set
`D' := transportBlockingDataAlong A (translate a b) D` and prove

```lean
have hι :
    regionInjectivityDataOf (A.transport (translate a b)) =
      regionInjectivityDataOf A := by
  rw [hA a b]
```

Then rebuild the `NormalEdgeBlockingData` record with the same `red`, `blue`, and
`complement` fields as `D'`. Rewrite the endpoint-membership fields with
`translateEdge_eq_map`, and supply the three dependent injectivity fields as
`hι ▸ D'.red_injective`, `hι ▸ D'.blue_injective`, and
`hι ▸ D'.complement_injective`. The remaining disjointness and cover fields are
copied from `D'`. Thus `transportBlockingDataAlong` is the computational core,
but the fixed-point cast and record reconstruction are required at this type.

The live torus proof route constructs blocking data separately at each rectangle
offset rather than translating a reference datum. No compatibility declarations
are retained under the maintainer's explicit no-public-API-compatibility policy.
