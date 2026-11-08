# Actual component kernels for two disjoint physical sectors

This source component supports the finite-prefix investigation of SPWC10,
Theorem 5. It does not assert a full all-volume model or a source counterexample.
The local spaces and periodic Hamiltonians are the actual ones already defined.

Disjoint one-letter embeddings have disjoint word ranges at every positive
length. Extension by zero from these ranges is orthogonal in the Euclidean
inner product. For U=E_R(S)+F_R(T), uniqueness of orthogonal projection proves
P_(U orthogonal) E_R = E_R P_(S orthogonal): the projected candidate lies in U,
and its residual is orthogonal to both actual image subspaces. Thus no local
range or projector relation is a premise.

The cyclic active-block coordinate bijections commute with the sitewise word
embeddings. Euclidean naturality is proved on image coordinates and off the
range separately. The shared owner
`Martingale/SpectatorPhysicalEmbedding.lean` supplies the actual fiberwise
identity extension; its proof is not copied. Conjugating this identity by the
actual cyclic coordinate isometries and summing gives
H_U(E_M v)=E_M(H_S v), for 0<R≤M.

The physical isometry is injective, so an embedded sector vector is killed by
the combined sum exactly when its original vector is killed by its own sum.
The second-sector identity follows by swapping the data and commuting the
subspace supremum. Actual image orthogonality then proves
H_U(E_M v+F_M w)=0 iff H_S v=0 and H_T w=0. Neither a whole-kernel decomposition
nor an operator covariance supplier appears in the public assumptions.
A separate actual state decomposition can now use this derived identity.

All statements allow arbitrary local subspaces and finite physical embeddings;
no nonempty-letter assumption is added. Positive interaction length is explicit
because the two empty-word embeddings coincide at length zero.

Independent source/API review checked projection uniqueness, orthogonal sums,
cyclic coordinate naturality, the linear-to-continuous coercions in spectator
transport, exact summation, and injectivity. One avoidable trailing-reflexivity
risk in a private coordinate proof was replaced by an explicit coefficient
calculation. No local Lean, Lake, elaboration or build was run. The six public
declarations and their Blueprint entries remain notready pending hosted checks.
