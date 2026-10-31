# The eight- and nine-site Weyl intersections

Context: #10386, child of #10407. These are the two exceptional open-chain
intersection steps whose common middle is shorter than the injectivity
length eight. No local-intersection conclusion is supplied as a hypothesis.

The existing actual boundary conditions supply left/right endpoint charge
functions H_j and K_i normalized by the full word phase. An actual middle
configuration of charge p-c_i-c_j makes the coefficient equations on its
union agree; the nonzero root character cancels, yielding H_j(p)=K_i(p).

Degree six omits exactly (0,4), (1,1), (4,0). The corresponding endpoint
incidence relation is NOT connected on all six possible formal vertices:
when p=c_i the i-vertex is isolated. That endpoint is not realized by an
actual eight-letter word because its seven-letter complement would have
zero charge. The proof therefore compares only active endpoints p≠c_i.
A finite three-edge bridge exists between every active pair. A reference
active letter is derived from the distinct charges c_0 and c_1, not supplied.

Degree seven omits zero. Every endpoint pair has a three-edge bridge,
so the nine-site reconstruction can use a fixed reference endpoint.
The bridge theorems quantify actual finite witnesses and use ordinary
kernel `decide` after the 25 residue cases, not native evaluation or an
experimental graph-connectivity claim. The final edge equalities are
ordinary equality transitivity. No graph record or parallel state family
is introduced.

For an actual eight- or nine-site vector, its endpoint coefficients
therefore reduce to one function of total charge. The existing exact
boundary-space characterization constructs the full boundary matrix.
This derives both requested intersections using the original two local
boundary conditions, primitive fifth root, and no extra supplier.

The general longer intersection, cyclic closure and periodic Hamiltonian
assembly are separate in #10407. A full fixed-interaction model still needs
all those pieces combined with the physical-sector component results.
This change alone asserts no unrestricted source counterexample.

## Verification

No local Lean, Lake, build, elaboration or checkdecls is run, as requested.
All six new public declarations and both Blueprint statements/proofs remain
notready. Native and independent source checks are recorded in the PR;
they do not establish hosted kernel acceptance. No persistent Lean fixtures.

Two independent bounded source/API reviews found no concrete mismatch in the
actual middle-word charge, phase cancellation, finite bridge orientation,
active endpoint restriction, seven-letter tail exclusion, list packaging,
or final common-charge reconstruction. Native checks pass.
