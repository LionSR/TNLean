# PEPS torus translate-blocking compatibility retention

This audit originally proposed deleting `TNLean/PEPS/TorusBlockingData.lean` and
its six public declarations under the repository-local pass-through exception.
Review determined that these names are public API and must remain available for
downstream users. The module and declarations are therefore retained as
deprecated compatibility API rather than deleted.

## Retained declarations and preferred replacements

| Deprecated declaration | Preferred replacement |
|---|---|
| `regionInjectivityDataOf_translate_eq` | use the translation-invariance fixed-point equation `hA a b` directly |
| `translateBlockingData` | `transportBlockingDataAlong A (translate a b) D` |
| `translateBlockingData_red` | the corresponding projection of `transportBlockingDataAlong` |
| `translateBlockingData_blue` | the corresponding projection of `transportBlockingDataAlong` |
| `translateBlockingData_complement` | the corresponding projection of `transportBlockingDataAlong` |
| `isCrossingEdge_translateBlockingData` | `isCrossingEdge_transportBlockingDataAlong` at `translate a b` |

The live torus proof route still constructs blocking data separately at each
rectangle offset rather than translating a reference datum, so production code
need not migrate back to this module. Deprecation preserves source compatibility
while directing new code to the general transport API.
