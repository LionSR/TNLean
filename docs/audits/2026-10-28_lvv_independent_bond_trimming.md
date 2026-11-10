# Independent bond trimming in the successive viable-set construction

The bond-trimming step of Landau, Vazirani and Vidick is implemented by independently
trimming each member of the finite left family at every internal cut. The resulting family
is chosen before the ground-state energy and ground vector. Combined with the existing
size-trimming argument, it has polynomial cardinality, polynomial bond dimension and
viability error at most one half.

The source is arXiv:1307.5143v1, `algo53.tex`, Claim `c:2` (lines 520–527), Claim `c:trim`
(lines 549–559), and Lemma `l:mpsapprox` (lines 325–328). This establishes the size and bond
steps with the library's existing constant-cut bond bound. It does not establish the
sampled-projector step or the final induction.

## Construction and source comparison

The size-trimming proof now retains its orthonormal right-coordinate presentation. For
each admissible ground vector it supplies an isometry $W$, a unit vector $u$, all of whose
left columns lie in the same previously selected family, and a physical vector
$\phi=(I\otimes W)u$ with ground-state overlap at least $11/12$.
The finite family, including the optimizer choices in the size step, is selected before
the ground pair; this order is preserved by the final theorem.

Each column of $u$ is successively Schmidt-truncated. Independently truncating these
columns need not be the Schmidt truncation of $\phi$. The proof does not identify the two
operations. Instead, it uses the following aggregate estimate. If the comparison vector
$v$ has cut rank at most $r$ and $w$ is the independently trimmed physical vector, then

$$
 |\langle\phi-w,v\rangle|
 \le (i-1)\|u\|\|v\|\sqrt{r/(m+1)}.
$$

Right contraction does not increase the internal cut rank of the reference columns, and
Cauchy–Schwarz combines the column estimates. Isometry of $W$ supplies the required norm
identity and contraction estimate.

The chain approximation theorem supplies a unit reference with overlap at least $47/48$
and bond $r(L)$ fixed before the ground vector. This reference is used to estimate the
actual column trimmings; it does not replace the finite-family construction.
The radius $m=(48L)^2r(L)$ gives overlap loss at most $1/48$. Normalizing the resulting
nonzero vector gives ground-state overlap at least $1/2$. Its left support lies in the
span of the independently trimmed family.

The quadratic radius replaces the printed linear radius. The correction is documented in
the companion library's [trimming-radius note](https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf).
The size estimate retains the constant-cut bond and corrected net exponent documented in
[the local constant-bond note](../paper-gaps/lvv13_constant_bond.tex). No sharper printed
dependence is claimed.

## Principal declarations

- `leftConfigOfFinEquiv` and `rank_cutMatrix_leftConfigOfFin` identify the numbered left
  block and transport internal cut ranks.
- `successiveSchmidtTrim` and `columnwiseSchmidtTrim` give the actual successive and
  independent column operations, with norm, rank and overlap estimates.
- `bondTrimSet` is the image of the finite family under the actual trimming operation.
  Its cardinality does not increase, and each member has the asserted bond bound.
- `exists_size_trimmed_column_family_polynomial` retains the orthonormal-column data in
  the size step. The earlier public size-step statements remain consequences.
- `exists_bond_trimming_reference` derives the comparison vector from the existing chain
  approximation theorem at accuracy $1/(2304L)$.
- `exists_bondTrimmingRadius_lvvReferenceBond_polynomial` proves a uniform bound
  $m(L)\le C_1L^{p_1}$ with natural degree, with $C_1,p_1$ fixed by local dimension and gap.
- `ChainHamiltonian.exists_size_bond_trimmed_family_polynomial` constructs the final
  finite family before every ground pair and proves cardinality, bond and viability bounds.

## Verification recorded on 28 October 2026

The baseline is origin/main `856cfe29955d1192c956626632695bc4d8b40587`. The authoritative
main worktree completed the full locked build before the checks below.

Every changed mathematical module and the unchanged finite-boundary-selection module was
compiled as an actual separate module against its imports, with the repository's strict
Lean options and warnings treated as errors. Outputs were written to a private copy of
the warmed artifact namespace. Source hashes were checked before and after compilation;
the authoritative dependency and repository caches were not altered. The final family
theorem, the additional polynomial bound, and their dependencies passed these checks.
The regression file `scripts/lvv_bond_trimming_regression.lean` checks the foundation
dependencies of the new public declarations against `propext`, `Classical.choice` and
`Quot.sound`.

The changed blueprint files pass the pinned LaTeX formatter and configured ChkTeX checks.
The import generator, reader-facing prose check and whitespace check pass. The tactic
pattern scan of the viable-set directory found no repeated pattern at its default
threshold. After integration into the independently seeded worktree, blueprint declaration
synchronization passes with the prebuilt companion dependencies present.

The original canonical seed completed without a restart. The integrated ordinary locked
module and full-library builds, strict imported foundation fixture and compiled blueprint
declaration check have now passed. Completion marks have been added to the new blueprint
chapter. The precise integrated scope is recorded in
[the verification audit](2026-10-28_lvv_integrated_verification.md).
