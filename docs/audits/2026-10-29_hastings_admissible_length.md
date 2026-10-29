# Hastings' entropy bound at an admissible Lieb–Robinson length

The finite-range chain construction now gives a numerical Lieb–Robinson estimate
for arbitrary finite second support and an interaction-proportional velocity
independent of the spectral gap. At an enlarged admissible length it gives both a
positive semidefinite approximate factorization and the printed entropy-bound
shape. The fixed-length corrections are retained.

For range R, let c_R = 2(R+1)2^(2R+1) exp(2R), V = 40 c_R J, and
Xi = max(2 V / Delta, 80). The actual commutator is bounded by
4 |X| ||A|| ||B|| exp(2 c_R J |t| - d), with no factor depending on |Y|.
The cone V |t| <= d therefore gives decay exp(-d/80).
For J > 0 this is the intended source pair. For J = 0 the multiplication
form of the cone remains valid without division by zero.

The earlier endpoint length is zeta = 20(1 + c_R J / Delta), and
2 zeta <= Xi. The positive factorization error
K zeta^3 exp(-l/(12 zeta)) is consequently at most
K Xi^3 exp(-l/(6 Xi)). Here K depends only on R.

The corrected entropy argument at 6 zeta has exponential factor
2^(2 (6 zeta) log q). The logarithm of the cubic factorization constant
is bounded by a constant times log(6 zeta). Increasing the length to Xi
therefore gives c_0 (6 Xi) log(6 Xi) log q 2^((6 Xi) log q), with c_0
depending only on R. The proof uses the physical factorization, entropy gain,
and doubling argument; it does not invoke a later area-law theorem.

The source is Hastings, arXiv:0705.2024v4, equations (lrb), (entbd), (smd),
Lemma 1 and its note added. The source chooses its velocity and length
existentially. Its length convention is corrected explicitly in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex`. The positive operators
are semidefinite, as justified by the note added. The body formulation
with strictly positive projections is kept separate.

Three production modules are added: `Hastings/LiebRobinson.lean`,
`Hastings/PrintedAreaLaw.lean`, and `Hastings/SourceLength.lean`.
Before integration, strict elaboration under the actual module names passed
in 3.98, 5.14, and 3.78 seconds against TNLean 7881dbe5a9
(with documentation-only successor 8153728de5) and QICLean b6660002.
An imported foundation audit of all ten public declarations used only
`propext`, `Classical.choice`, and `Quot.sound`.
Ordinary combined build and compiled blueprint checks are recorded in the
subsequent integration audit; these private checks alone do not establish
that combined verification has passed.

The primary worktree's unrelated untracked drafts were inspected and copied
as frozen sources. They were not modified. The imported graph-distance proof
was adapted to the checked provider, four unused rescaled-velocity helpers
were omitted, and the final admissible pair was composed in `SourceLength`.
The source and comparison documentation explains the mathematical scope
without claiming that the original fixed-length arithmetic was repaired.
