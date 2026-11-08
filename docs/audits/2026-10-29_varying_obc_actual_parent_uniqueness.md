# Actual varying-bond open parent ground-state line

Source: PGVWC07, Theorem 9 and proof, `MPSarchive.tex` lines 1195–1237.
The theorem in this continuation has explicit length N≥2 and a common
finite physical alphabet. The scope note is
`docs/paper-gaps/pgvwc07_open_parent_domain.tex`; no unrestricted source
completion or short-length counterexample is claimed.

The final statement uses the actual open parent Hamiltonian built from
the original rectangular site matrices. No projector kernel, coefficient
section, blocked boundary, normalized state, or separate canonical witness
is supplied as a premise. Its hypotheses are the original sitewise C1,
canonical row-isometry, singleton endpoint bonds and the explicit domain.

The forward inclusion uses the actual positive projector sum kernel
characterization, then the printed canonical adjoint reconstruction through
all sites. `Function.extend List.ofFn` and the existing injection theorem
construct the list coefficient extension internally. The reverse inclusion
uses the actual boundary state's prefix/pair/suffix trace factorization,
with pair witness suffix times boundary times prefix. Singleton endpoint
sums have one term each, so the all-ones rectangular boundary gives exactly
the original chain coefficient, with no normalization factor.

The full-prefix row-isometry yields sum of squared actual coefficients one.
Thus the represented state is nonzero and normalized, and the actual parent
kernel equals its span with dimension one. The already-derived positivity
of that Hamiltonian makes this its ground-state line.

Pinned source APIs were checked against Mathlib c55e6e786f49471c72fbddbec5415808896aec1e
and QICLean acda92aa70e69b37507e422bceb5414036859fe6, including exact git-blob
comparisons for the source snapshot. Independent read-only review found no
concrete remaining issue in the scalar trace, norm, coefficient extension,
or submodule dimension steps. No local Lean, Lake, elaboration or build
was run; all new mathematical entries remain notready pending hosted checks.
