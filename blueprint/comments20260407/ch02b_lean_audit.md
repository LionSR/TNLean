# Audit of `blueprint/src/chapter/ch02b_mpdo.tex`

Scope:
- Blueprint file reviewed in full: `blueprint/src/chapter/ch02b_mpdo.tex`
- Lean files read:
  - `TNLean/MPS/MPDO/Defs.lean`
  - `TNLean/Channel/DensityRetract.lean`
  - `TNLean/Channel/Semigroup/ReducibleQDS/FixedDensity.lean`
  - all files in `TNLean/MPS/Core/`

## Findings

### 1. LPDO -> MPDO proof sketch is not fully faithful to the Lean proof, and is slightly mathematically inaccurate
- Blueprint proof: `blueprint/src/chapter/ch02b_mpdo.tex:174-190`
- Lean proof: `TNLean/MPS/MPDO/Defs.lean:193-274`

Issue:
- The blueprint says the product decomposes directly as
  `M^{\sigma_1 \tau_1} \cdots M^{\sigma_N \tau_N} = \sum_\kappa P_\kappa \otimes \overline{Q_\kappa}`.
- That is not what the Lean proof proves from the actual LPDO definition. The Lean statement keeps the bond-index identification `e` throughout:
  `(...)= (∑_κ P_κ ⊗ₖ \overline{Q_κ}).submatrix ↑e ↑e`.
- The Lean proof then uses a separate trace-invariance step
  `trace (X.submatrix ↑e ↑e) = trace X`
  before applying `trace_kronecker`.

Why this matters:
- As written, the blueprint proof silently drops the reindexing by `e`.
- Since `e` is part of the LPDO definition itself, this is a real mismatch, not just a presentation choice.

Recommended fix:
- Replace the displayed decomposition with the reindexed version, or add a sentence saying that after transporting along the bond-space identification `e`, the product is a sum of Kronecker products, and trace is invariant under this reindexing.

### 2. Mild formalization-sounding wording: "view"
- Blueprint lines: `31`, `98`, `102`, `109`
- Style guide: `docs/blueprint_style_guide.md:7-9`, `43-49`

Issue:
- "Doubled-index MPS view" is understandable, but "view" is software-leaning rather than mathematical.

Impact:
- Minor. There is no explicit Lean syntax leaking into the prose, and most of the chapter is mathematically phrased.

Recommended fix:
- Prefer "associated MPS tensor with doubled physical index" or similar.

## Tag-by-tag check

| Blueprint tag | Lean declaration | Exists | Statement match | Marker |
|---|---|---|---|---|
| `\lean{MPOTensor}` | `TNLean/MPS/MPDO/Defs.lean:57` | Yes | Yes. Lean has `abbrev MPOTensor (d D : ℕ) := Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ`, matching the family of matrices `M^{ij}`. | `\leanok` correct |
| `\lean{MPOTensor.toMPSTensor}` | `TNLean/MPS/MPDO/Defs.lean:68` | Yes | Yes. Lean maps `Fin (d * d)` to the pair `(ij.divNat, ij.modNat)`, matching the doubled-index MPS construction. | `\leanok` correct |
| `\lean{MPOTensor.evalWord}` | `TNLean/MPS/MPDO/Defs.lean:76` | Yes | Yes. Lean returns `1` on `([], [])`, multiplies along paired words, and returns `0` on mismatched lengths. | `\leanok` correct |
| `\lean{MPOTensor.mpo}` | `TNLean/MPS/MPDO/Defs.lean:113` | Yes | Yes. Lean defines the `N`-site operator as the matrix with entries `trace (evalWord ...)`, indexed by `Fin N → Fin d`. | `\leanok` correct |
| `\lean{MPOTensor.IsHermitian}` | `TNLean/MPS/MPDO/Defs.lean:124` | Yes | Yes. Lean says `∀ i j, M i j = (M j i)ᴴ`. | `\leanok` correct |
| `\lean{MPOTensor.transferMap}` | `TNLean/MPS/MPDO/Defs.lean:131` | Yes | Yes. Lean defines `X ↦ ∑_{i,j} M^{ij} X (M^{ij})^\dagger` as a linear map. | `\leanok` correct |
| `\lean{MPOTensor.transferMap_eq_toMPSTensor}` | `TNLean/MPS/MPDO/Defs.lean:142` | Yes | Yes. Lean identifies the MPO transfer map with `MPSTensor.transferMap (toMPSTensor M)`. | `\leanok` correct |
| `\lean{MPOTensor.transferMap_pos}` | `TNLean/MPS/MPDO/Defs.lean:150` | Yes | Yes. Lean proves PSD preservation: `X.PosSemidef -> (transferMap M X).PosSemidef`. | `\leanok` correct |
| `\lean{MPOTensor.IsMPDO}` | `TNLean/MPS/MPDO/Defs.lean:163` | Yes | Yes. Lean defines `IsMPDO M := ∀ N, (mpo M N).PosSemidef`. | `\leanok` correct |
| `\lean{MPOTensor.IsLPDO}` | `TNLean/MPS/MPDO/Defs.lean:183` | Yes | Mostly yes. The blueprint matches the existential data and the Kronecker-conjugation formula; the only subtlety is that Lean implements the bond-space identification as `.submatrix ↑e ↑e`, which the blueprint explains correctly in the definition. | `\leanok` correct |
| `\lean{MPOTensor.IsLPDO.isMPDO}` | `TNLean/MPS/MPDO/Defs.lean:251` | Yes | Statement matches. The proof sketch, however, omits the essential reindexing-by-`e` step used in Lean. | `\leanok` correct for the theorem, but the proof text should be revised |

## `\leanok` / `\notready` audit

- All 11 tagged declarations exist.
- The chapter uses `\leanok` everywhere and has no `\notready`.
- That is correct for declaration readiness: the corresponding Lean declarations are present and fully proved/defined in `TNLean/MPS/MPDO/Defs.lean`.
- I found no missing `\notready` markers caused by absent or proofless Lean declarations.

## Formalization-speak / Lean jargon check

- No explicit Lean identifiers leak into the prose beyond the `\lean{...}` tags.
- No direct tactic or implementation syntax appears in the body text.
- The only wording I would flag is the repeated use of "view" for the associated doubled-index tensor; this is minor and stylistic.

## Mathematical issues

- The only substantive mathematical issue is in the LPDO -> MPDO proof sketch: it suppresses the bond-space identification `e`, whereas the formal theorem and proof require it.
- Aside from that, the chapter statements are consistent with the Lean signatures.

## Bottom line

- 11/11 `\lean{}` tags checked: all exist.
- 11/11 tagged statements match the Lean declarations at the level expected for the blueprint.
- `\leanok` usage is correct.
- Main revision needed: fix the LPDO -> MPDO proof sketch to keep track of the `e`-reindexing step.
