# Common development of the classical area-law constructions

The combined development starts at TNLean main
`c457d2be30e12c770fb7807e822f0ca72739f498`. It retains the removal of permanent
Lean test fixtures and the intervening PEPS results. The companion revision
`b66600027b2e60ccafea43d041d563cdd00cf05b` is based on QICLean main `acda92aa`, with the selected low-energy, entropy,
interpolation and sampling additions compiled together. The Lean toolchain
and Mathlib pin are unchanged.

## Mathematical conclusions

The LVV successive construction begins with the scalar singleton. Each
family is obtained from the preceding one by extension, size trimming,
independent bond trimming and a finite physical Gaussian filter. The
polynomial coefficient and degree precede the length and Hamiltonian; the
chosen families precede every ground pair. For each admissible ground pair, the final family's span contains a
normalized vector with overlap at least $1-(\Delta/169)^2/L$ with that
ground vector. This is a
construction of the successive families, rather than independent
existential choices at the cuts. The sharper printed parameter dependence,
arbitrary-precision bounds and running time remain separate.

The ALVV interval entropy estimate concerns the full physical ground
space, retains coefficient one on $\log r$, and uses the capped gap
$g=\min(\gamma,1)$. An actual normalized global MPS approximation is obtained
by sequential truncation. Approximating one orthonormal ground basis at
accuracy $\varepsilon/(2r)$ gives a total squared error at most
$\varepsilon/4$. Its span is one $r$-dimensional reference space $U$, mutually
$\varepsilon$-close to the ground space, with bond bound $r^2B$ for every
vector. The same $B$ and $U$ are fixed before any block or viable space $S$
to be trimmed. Actual collective trimming gives error
$4\delta+6\varepsilon+4\xi\sqrt{(i-1)r^2B}$ on a prefix of length $i$.
Retuning these errors closes a prescribed budget; this estimate does not
justify the printed $.01\to.015$ choice. No sampled merge tree or
coefficient-one entropy estimate for all of $U$ is asserted.

The source assumption (DG) includes a second distinct spectral value.
The upper bound one for the unique-ground-state gap, proved by an endpoint
unitary, does not extend by that argument to a degenerate ground space.
The three-qubit gap-two example and the remaining comparison with the
uncapped gap are retained in the parameter note.

The AKLV rank estimate is derived from the original supported interactions.
At the central cut of a window of width $s>0$, a polynomial of degree at
most $\ell$ has operator Schmidt rank at most
$[q(\ell+1)]^{16(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}$.
For positive degree, the source base $q\ell$ is available with exponent
$96\max(\lfloor\ell/s\rfloor,\lfloor\sqrt\ell\rfloor)$.
The Chebyshev construction gives one operator with both this rank bound
and the stated spectral suppression. Its inputs include the actual
Hamiltonian's gap and spectral ceiling, as in the bounded spectral lemma.
The two-outer-block robustness theorem, quantitative choice giving the
required rank--suppression tradeoff and entropy argument remain open.

The matrix concentration theorem lives in QICLean. Finite sampling also
constructs one sample satisfying both an actual matrix-mean approximation
and all word-frequency bounds whenever the explicit sum of their failure
bounds is less than one. The physical power-filter application is distinct:
its norm scale depends on the ground energy, and no uniform polynomial
bound in that energy is inferred.

## Source qualifications

The net exponent, independent-trimming radius and commuting-gap count use
the documented corrections. Scope restrictions and the capped-gap estimate
are stated in the theorem entries and paper-gap notes. The false printed
ALVV cluster estimate retains its counterexamples; the soft-truncation,
low-density bootstrap and sampled tree require further mathematics.
The Hastings quantitative and Lieb--Robinson qualifications remain recorded
in their separate notes. The six approaches are compared in
`../formalization/classical-area-law-comparison.md`.

## Verification method

The TNLean worktree was canonically seeded from exact, clean, fully warmed
main before edits. The companion worktree was independently seeded from
exact, clean, fully warmed QICLean main. Ordinary builds and cache changes
use the common lock and verify the pinned prebuilt Mathlib artifacts.
Theorem foundations are inspected with temporary imported Lean sources;
no permanent theorem fixture is added.


The common-import check also identified two remaining declarations shared
between the libraries: the ordered-word coefficient and subtraction under
a local lift. Their TNLean copies are removed; the existing QICLean
declarations are used directly, with no compatibility aliases. Separate
strict checks of both affected TNLean modules passed before repeating the
combined verification.


## Completed combined verification

Verification completed on 29 October 2026 at the exact mathematical
revision `7881dbe5a91f1436913a0a97d9812b0149aa3165`, using companion
revision `b66600027b2e60ccafea43d041d563cdd00cf05b`.

| Check | Result |
|---|---|
| Full TNLean library | Passed, 15,067 jobs |
| Strict changed production sources | Passed, 56 files |
| Existing dependent regressions | Passed, five files |
| Manual imported foundations | Passed, 139 public declarations |
| Blueprint source synchronization | Passed |
| Compiled blueprint declarations | Passed |
| Added reader-facing prose | Passed |
| Added proof-integrity tokens | Passed |

All inspected foundations are among `propext`, `Classical.choice` and
`Quot.sound`. No permanent Lean fixture is added. The build used cached
Mathlib artifacts and reported zero Mathlib source jobs. The earlier
common physical target build also passed 9,777 jobs. The unchanged
50-second strict per-file limit and package options were used.
The changed-file compilation-time check passed with its unchanged limits.
The final build reported 25 seconds for `TwoWindowPolynomialMPOFamily`,
producing a diagnostic warning below the 50-second failure threshold.
An earlier unsuccessful integration snapshot reported 52 seconds for
`PhysicalChebyshevViability`; the same module took 16 seconds in the final
build and passed the strict per-file check. These observations are local
diagnostics, not comparable performance benchmarks.

The companion foundation snapshot `98ec7c9f` separately passed its full
10,344-job build, strict checks, 73-declaration foundations inspection and
compiled blueprint check. The subsequent Chebyshev addition at `b6660002`
passed the full 10,345-job companion build and its strict, imported
foundations and blueprint checks. Both used prebuilt Mathlib artifacts.

The repository-wide prose scan reports pre-existing issue-reference
wording in unchanged PEPS files. The added-prose check above passes; those
unrelated files are preserved. The source statements and proofs are
unchanged by this completion record.
