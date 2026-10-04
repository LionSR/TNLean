# Jordan-aware physical connected correlations

Source: `Papers/2011.12127/TN-Review-main.tex`:433–441, with the correction
already recorded in the correlator Jordan-block source note.

The all-separation formula uses binomial coefficients before any division
by an eigenvalue. Mathlib's public generalized-eigenspace decomposition and
commuting binomial powers construct the coefficients. The cutoff is the
existing least generalized-eigenspace stabilization index, not a new Jordan
representation. Two short private matrix-pairing lemmas compose these APIs.
The private QIC Cesaro helper is neither accessed by a generated private
name nor copied or exposed; it only provided a useful reuse-audit comparison
and is insufficient as stated for the small-separation cases.

For nonzero eigenvalues, existing falling-factorial polynomials give the
polynomial coefficient, with degree strictly below the stabilization index.
Zero eigenvalues remain in a finite transient; no division by zero or
incorrect polynomial-times-zero-power formula is used. The formula includes
adjacent physical blocks at separation zero.

The physical normal-tensor theorem reuses the actual finite-support
correlator and existing channel peripheral bounds. Nonzero complementary
eigenvalues are shown to be actual transfer eigenvalues through zero trace
of their eigenvectors. Generalized-eigenspace stabilization by dimension
bounds the transient by D².

A shared normal-gauge witness is extracted from the already published
arbitrary-gauge decay proof. The existing decay theorem's signature remains
unchanged and its proof reuses that witness. The expansion uses the same
positive left/right fixed pair and exact physical gauge covariance. A single
canonical representative supplies all sharp Jordan indices, while frequency
membership is transported to the original tensor's transfer spectrum.

This work is stacked on PR #8552, exact base 5b311792. The source's broader
class with singular fixed matrices remains outside the normal-tensor result;
the existing source-gap note remains open for that scope. No QIC source,
pinned dependency, or upstream publication is changed.

A fresh audit of all 53 open PR changed-file lists found only the intended
parent-stack overlap (#8541 and #8552) on the correlation modules, chapter
and source note. The three new expansion modules have no competing PR.
Independent read-only mathematical review confirmed the normalization,
all-separation binomial formula, zero transient, degree bounds, and original
transfer-spectrum transport.
