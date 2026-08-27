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
| `translateBlockingData` | `transportBlockingDataAlong A (translate a b) D` |
| `translateBlockingData_red` | the corresponding projection of `transportBlockingDataAlong` |
| `translateBlockingData_blue` | the corresponding projection of `transportBlockingDataAlong` |
| `translateBlockingData_complement` | the corresponding projection of `transportBlockingDataAlong` |
| `isCrossingEdge_translateBlockingData` | `isCrossingEdge_transportBlockingDataAlong` at `translate a b` |

The live torus proof route constructs blocking data separately at each rectangle
offset rather than translating a reference datum. No compatibility declarations
are retained under the maintainer's explicit no-public-API-compatibility policy.
