# Twisted-dimer fusion: the uniform every-pair statements as the only record

This audit records the removal of eighteen zero-consumer public declarations of
the graded quantum-dimer twist under the repository-local retirement rule of
`docs/project_conventions.md` §Style.  Each removed declaration was the
specialization of a uniform every-pair statement to one fixed pair of sectors,
obtained by substituting the pair into the general statement and carrying the
same hypotheses.

## What was removed

The strategy note
`Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex`
(`thm:p6-r44-z2`(v), `eq:p6-r44-z2-fusion`) states the fusion rule
`M_f M_{f'} = (x/2) M_{f+f'} ⊕ (y/2) M_{f+f'+1} ⊕ 0` for an arbitrary pair of
sectors, so the uniform family is the faithful anchor and the fixed-pair
versions are restrictions of it.  The uniform family already covered every
pair; the nine declarations of the pair `(0, 0)` and the three declarations of
each of the other three pairs added no mathematics.

| Removed declaration | Replacement |
|---|---|
| `P6Compression.dimerCompression` | `P6Compression.dimerFusionCompression 0 0` |
| `P6Compression.dimer_remainder` | `P6Compression.dimerFusion_remainder 0 0` |
| `P6Compression.dimer_trace_evalWord` | `P6Compression.dimerFusion_trace_evalWord 0 0` |
| `P6Compression.dimer_isReduction` | `P6Compression.dimerFusion_isReduction 0 0` |
| `P6Compression.dimer_left_mul_right_of_ne` | `P6Compression.dimerFusion_left_mul_right_of_ne 0 0` |
| `P6Compression.dimer_mul_right_eq_right_mul` | `P6Compression.dimerFusion_mul_right_eq_right_mul 0 0` |
| `P6Compression.dimer_left_mul_eq_mul_left` | `P6Compression.dimerFusion_left_mul_eq_mul_left 0 0` |
| `P6Compression.dimer_z_eq` | `P6Compression.dimerFusion_z_eq 0 0` |
| `P6Compression.dimer_dim_eq` | `P6Compression.dimerFusion_dim_eq 0 0` |
| `P6Compression.dimerZeroOneCompression` | `P6Compression.dimerFusionCompression 0 1` |
| `P6Compression.dimerZeroOne_remainder` | `P6Compression.dimerFusion_remainder 0 1` |
| `P6Compression.dimerZeroOne_trace_evalWord` | `P6Compression.dimerFusion_trace_evalWord 0 1` |
| `P6Compression.dimerOneZeroCompression` | `P6Compression.dimerFusionCompression 1 0` |
| `P6Compression.dimerOneZero_remainder` | `P6Compression.dimerFusion_remainder 1 0` |
| `P6Compression.dimerOneZero_trace_evalWord` | `P6Compression.dimerFusion_trace_evalWord 1 0` |
| `P6Compression.dimerOneOneCompression` | `P6Compression.dimerFusionCompression 1 1` |
| `P6Compression.dimerOneOne_remainder` | `P6Compression.dimerFusion_remainder 1 1` |
| `P6Compression.dimerOneOne_trace_evalWord` | `P6Compression.dimerFusion_trace_evalWord 1 1` |

Each replacement is the general statement applied to the pair, with the same
hypotheses and the same conclusion up to reduction of the sector literals:
the removed word-trace identity of the pair `(0, 0)` reads its two targets as
the sectors `0` and `1`, while the general one reads them as `0 + 0` and
`0 + 0 + 1`, and the two expressions are the same by reduction of the
two-element index type.

## What is retained and why

The four exhaustive verifications stay where they are.  Each pair keeps its
assembled letter identity (`P6Compression.dimer_letter_int`,
`dimerZeroOne_letter_int`, `dimerOneZero_letter_int`, `dimerOneOne_letter_int`)
and the two private kernel decisions over the sixty-four letters that prove it;
these are the input of `P6Compression.dimerFusion_letter_int`, which assembles
the four cases into the identity of every pair.  The four-file split exists so
that each kernel decision is elaborated in its own module, and that reason is
unchanged.  The pair-generic constructions of
`TNLean/MPS/FundamentalTheorem/Reduction/Examples/TwistedDimer.lean`
(`dimerCompressionOfLetterIdentity`,
`remainder_dimerCompressionOfLetterIdentity`,
`dimer_trace_evalWord_of_compression`, `dimer_letter_int_of_halves`), the
sector tensors, their normality and their gauge inequivalence are untouched.

**Superseded in part (2026-09-25).** A later refactor removed
`dimerOneZero_letter_int` and `dimerOneOne_letter_int` with their modules
`TwistedDimerPairOneZero.lean` and `TwistedDimerPairOneOne.lean`. The sign rule
`P6Compression.dimerStackedInt_eq_add` (with `dimerBlockInt_eq_add`) shows that
the stacked product of the sectors `f` and `f'` is that of the sectors `0` and
`f + f'`. Hence `dimerFusion_letter_int` needs only the checks of the pairs
`(0, 0)` and `(0, 1)`, which remain in separate modules as before. The modules
now live under `TNLean/MPS/Examples/RFP/`.

## Blueprint

Two nodes of `blueprint/src/chapter/ch25_asymmetric_examples_rfp.tex` tagged
the removed names and are now stated for every pair of sectors, with the two
targets read as the sectors `f + f'` and `f + f' + 1`:

- `thm:asymex_dimer_compression` now tags `P6Compression.dimerFusionCompression`,
  `dimerFusion_isReduction`, `dimerFusion_left_mul_right_of_ne`,
  `dimerFusion_z_eq`, `dimerFusion_dim_eq`, `dimerFusion_remainder`,
  `dimerFusion_mul_right_eq_right_mul` and `dimerFusion_left_mul_eq_mul_left`;
- `thm:asymex_dimer_trace` now tags `P6Compression.dimerFusion_trace_evalWord`.

Both statements were widened, not narrowed: the previous fixed pair is the
instance `f = f' = 0` of the new ones, so each `\leanok` continues to hold, and
no hypothesis was added.

The remark `rem:asymex_dimer_scope` was deleted.  It said that the two theorems
state the case of sector zero multiplied by itself, and argued from the sign
identity of the twists that the same letter decomposition holds for every pair;
both halves are subsumed once the theorems themselves are stated for every
pair.  The operator-level product law it displayed, for every pair and every
positive length, is the subject of the node
`thm:mpdo_twisted_dimer_flag_sector_product_law` of the density-operator
chapter, where it is tagged to `MPOTensor.TwistedDimer.mpo_flagMPO_mul`.
Nothing referenced the deleted label.

## Clearance

Exact-name searches over the repository found no Lean consumer of any of the
eighteen names outside the files that defined them, in `Archive/` or elsewhere,
and no reference under `docs/` apart from the table of this note.  The only
references outside the removed code itself were the two Blueprint nodes above.  The surviving name `dimer_letter_int`, used as a control, was found at
its consumer in `TwistedDimerPairs.lean`.  No compatibility alias is retained,
since TNLean does not promise a stable public Lean interface and every
retirement condition is met.

The five changed modules and their importer
`TNLean.MPS.FundamentalTheorem.Reduction.Examples` were built with the package
linter options after the removal, and the declaration existence of the new
Blueprint tags was checked.
