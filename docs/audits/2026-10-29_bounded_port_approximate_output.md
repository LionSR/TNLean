# Approximate pure outputs of the actual bounded physical-port compiler

Source context: Piroli, Styliaris and Cirac, [arXiv:2103.13367v3](https://arxiv.org/html/2103.13367v3),
main-text paragraphs “Quantum circuits and LOCC” and “Phases of matter”. The latter
compares output states in trace norm after tracing ancillary spins. This is a bounded
compiler consequence of that criterion, not the unrestricted source phase classification.

## Actual statement and derived data

Fix d≥2 and an intermediate dimension bound B before N in a family. For N≥2,
let Ψ be an actual B-bounded depth-T native channel, with physical input/output d.
If ψ and φ are unit vectors and the full chain trace-norm error between
Ψ(|ψ><ψ|) and |φ><φ| is at most ε, the actual compiled unitary U and some unit η satisfy

‖U(V_port ψ ⊗ |0_A>) − V_port φ ⊗ η‖₂ ≤ sqrt(2 ε).

The physical depth remains 2 ceil(log_d B) T. Both the original physical ports and
the full channel identity on every logical operator are retained. The vector norm
is explicitly Euclidean through `WithLp`; the raw Pi sup norm is not used.
No joint-output approximation, overlap bound, simulator or decoupling is supplied.

The actual Γ and U come from `exists_physicalPortIO` and the unitary dilation.
Their equality on all operators gives the actual joint marginal. Trace preservation
and input normalization give its joint unit norm. The actual code is an isometry,
so its conjugation preserves the native full trace-norm error. The upstream generic
coefficient-row estimate derives η on the unchanged environment space. There is no
ε<1 requirement and no lower bound on environment dimension.

## Dependency and completion boundary

Generic matrix/channel mathematics is in QICLean draft
[#1009](https://github.com/LionSR/QICLean/pull/1009), exact candidate
55528b03c8467c8e0508501f2e0ff697d5f4d76a. All three TNLean dependency records
(root lakefile, root manifest and documentation manifest) explicitly use that draft.
Its accepted base 86b3159b98a1608c5e66a875fa670a9687c9867d has identical toolchain,
lakefile and manifest to the old acda92 dependency. The QIC source link used for
native inspection points to that exact isolated candidate worktree; shared caches
and primary QICLean files are unchanged.

Upstream acceptance, repinning to the accepted QIC commit, fresh hosted verification
and downstream integration remain required. The new Blueprint statement and proof
are `notready`. No local Lean/Lake build, elaboration or checkdecls is run.
This supplies no environment reset, source adaptive control order or fixed-block
count; #8640/#8622 remain open. It does not duplicate #10350’s protocol regrouping.
