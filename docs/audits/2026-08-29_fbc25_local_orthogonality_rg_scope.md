# Source-scope audit: local orthogonality, RG limits, and state-level ground spaces

**Date:** 2026-08-29

**Tracking:** [issue #7348](https://github.com/LionSR/TNLean/issues/7348),
under [issue #7261](https://github.com/LionSR/TNLean/issues/7261)

**Target source:** A. Franco Rubio and A. Bochniak, arXiv:2502.20257,
`Papers/2502.20257/main.tex`

**Upstream source for the MPS terminology:** J. I. Cirac, D.
Pérez-García, N. Schuch, and F. Verstraete, arXiv:1606.00608,
`Papers/1606.00608/MPDO-22-12-17-2.tex`

**Repository snapshot:** `origin/main` at `522bc8c15`

## Conclusion

Lemma `lemma:modif` in arXiv:2502.20257 assumes exact local
orthogonality at the physical scale at which the displayed MPS tensors are
used.  In matrix notation, for distinct injective blocks \(A_x\) and \(A_y\),
this is

\[
  \mathbb E_{x,y}
    = \sum_i A_x^i\otimes\overline{A_y^i}
    = 0,
  \qquad x\ne y.
\]

The sentence immediately before the lemma says that this condition can be
obtained by “blocking until we approach a fixed point of the renormalization
group.”  It specifies no topology, no error estimate, no limiting tensor, and
no finite blocking length.  In particular, it does not assert that some finite
blocking makes the displayed mixed transfer matrix exactly zero.  The exact
hypothesis of `lemma:modif` and the preceding asymptotic motivation must
therefore remain separate.

TNLean already contains the exact mixed-transfer predicate needed for the
lemma, together with exact renormalization-fixed-point and parent-Hamiltonian
theory.  Those results do not fill the missing implication from asymptotic
blocking to exact local orthogonality.  They also do not compare state-level
gauging with Hamiltonian-level gauging.  The target paper explicitly leaves
that Hamiltonian comparison and the dimension of the common \(+1\) eigenspace
for future work.

## 1. The exact hypothesis of `lemma:modif`

### 1.1 The contraction drawn in the target paper

The MPS preliminaries write a block-injective tensor as

\[
  A^i=\bigoplus_k \mu_k A_k^i,
\]

where the \(A_k\) are injective tensors
(`Papers/2502.20257/main.tex:174-179`).  In the state-level gauging section,
the block label is denoted by \(x\in\mathsf X\).  Lines 4215-4231 assume that,
for \(x\ne y\), contracting the physical leg of \(A_x\) with that of the
complex-conjugate tensor \(A_y^*\) gives zero while leaving both pairs of
virtual legs open.  This is precisely

\[
  \sum_i A_x^i\otimes\overline{A_y^i}=0.
\]

The equivalent rectangular linear-map form is

\[
  \mathcal E_{x,y}(X)
    =\sum_i A_x^i X(A_y^i)^\dagger
    =0
\]

for every \(D_x\times D_y\) matrix \(X\).  This is the convention implemented
by `Kraus.mixedMapLM A_x A_y`.  Accordingly,
`MPSTensor.IsBNTLocallyOrthogonal blocks` in
`TNLean/MPS/RFP/ZeroCorrelationLength.lean` is exactly the family of equations

```text
∀ x y, x ≠ y → Kraus.mixedMapLM (blocks x) (blocks y) = 0.
```

The similarly named `MPSTensor.IsLocallyOrthogonal` is not the appropriate
predicate here: it is a one-block convention defined to mean self-transfer
idempotence.  Its own documentation and Chapter 26 distinguish it from the
mixed-sector condition.

### 1.2 The physical scale is the current unit cell

The diagram at lines 4215-4231 has one physical contraction.  Thus the lemma
assumes local orthogonality at one site relative to the tensor and physical
space currently under discussion.  The unitary in its conclusion acts on two
such sites,

\[
  \widetilde\lambda_{g,h}\in \mathrm U(\mathcal H^{\otimes 2}).
\]

If \(L\) original sites have first been grouped into one new site, the blocked
letters are

\[
  A_x^{\boldsymbol i}
    =A_x^{i_1}\cdots A_x^{i_L},
  \qquad \boldsymbol i=(i_1,\ldots,i_L),
\]

and exact local orthogonality at that scale would mean

\[
  \sum_{\boldsymbol i}
    A_x^{\boldsymbol i}\otimes
    \overline{A_y^{\boldsymbol i}}
    =\mathbb E_{x,y}^{L}
    =0.
\]

The target paper does not introduce such an \(L\) in `lemma:modif`, and does
not quantify an \(L\) in the preceding sentence.  Thus the faithful formal
statement is conditional on exact local orthogonality of the supplied block
family at the supplied physical scale.  It is not an existential statement
about a further finite blocking.

### 1.3 Where exactness enters the proof

Lines 4257-4325 compare the vectors \(v(g,h,x)\) and \(v(g,h,y)\).  The proof
inserts the original fusion unitary and reduces their inner product to mixed
contractions between the \((x,y)\) sectors and between the
\((gh[x],gh[y])\) sectors.
Exact local orthogonality makes this inner product exactly zero.
The mutually orthogonal sector subspaces then allow the distinct scalars
\(L^x_{g,h}\) to be absorbed into one unitary
\(\widetilde\lambda_{g,h}\).

A small mixed-transfer norm would give only approximate orthogonality.  The
paper supplies no stability estimate that turns such an approximation into
the exact unitary equation

\[
  \widetilde\lambda_{g,h}v(g,h,x)=v(e,gh,x)
\]

for every block \(x\).  The asymptotic RG language is therefore not a
substitute for the lemma's exact hypothesis.

## 2. What the RG sentence does and does not state

### 2.1 The target paper gives no limiting statement

The relevant sentence is `Papers/2502.20257/main.tex:4214`.  It contains none
of the following data:

- a sequence of tensors or transfer maps;
- a topology or norm;
- a candidate limiting tensor;
- a rate or an error tolerance;
- a claim of eventual equality after a finite number of blockings.

The summary at line 469 similarly says that state-level gauging may be
performed “possibly after blocking so that we approach a renormalization group
fixed point,” but adds no mathematical specification.  These sentences give
physical motivation for imposing local orthogonality.  They are not a theorem
that discharges the hypothesis of `lemma:modif`.

Three statements must not be conflated:

1. **Exact finite blocking:** there is an \(L<\infty\) such that
   \(\mathbb E_{x,y}^{L}=0\) for every \(x\ne y\).
2. **Asymptotic mixed-sector decay:**
   \(\mathbb E_{x,y}^{L}\to0\) as \(L\to\infty\).
3. **Exact fixed-point structure:** the whole tensor at the limiting scale has
   an idempotent self-transfer map.

The first statement is strictly stronger than the second: convergence to zero
does not imply that any finite term is zero.  The lemma assumes exact local
orthogonality of the tensors already supplied at its working scale; it does
not assert the first statement for any tensor before that scale was chosen.
Its explanatory prose suggests only the second or third statement and does
not choose between them.

### 2.2 The Cirac source makes the asymptotic route more precise, but not finite

The target sentence has no local citation.  The paper's bibliography entry
`Cirac17`, used for the preceding canonical-form discussion, is
arXiv:1606.00608.  That source supplies the relevant terminology:

- lines 382-394 define one RG step by blocking two sites and quotienting by a
  physical isometry;
- lines 396-424 characterize tensors which appear as limits as exact
  renormalization fixed points;
- lines 467-474 define local orthogonality by the same mixed-transfer equation
  \(\sum_i A_j^i\otimes\overline{A_{j'}^i}=0\);
- lines 1205-1209 identify blocking with
  \(\mathcal E\mapsto\mathcal E^2\);
- lines 1211-1244 discuss convergence of the transfer powers of a tensor in
  canonical form.

The Cirac text works with equivalence classes under physical isometries and
with powers of finite-dimensional transfer maps.  It does not state a norm or
topology explicitly in the cited passages.  More importantly, its printed
claim that every canonical-form flow converges is false in the presence of
uncontrolled relative phases between repeated copies.  The tensor

\[
  A^1=\operatorname{diag}(1,e^{2\pi i/3})
\]

has a dyadic transfer orbit which alternates on an off-diagonal matrix unit.
This is proved by `MPSTensor.cubePhaseTensor_not_tendsto_dyadic_transferMap` and
documented in
`docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex`.

Primitive single-block convergence and mixed-sector decay remain valid under
their stated hypotheses.  Neither result implies exact vanishing at a finite
blocking length.

## 3. Comparison with maintained renormalization declarations

The following declarations are mathematically exact.  The last column records
their role relative to the target sentence; being an exact theorem in TNLean
does not make it the theorem asserted by arXiv:2502.20257.

| Declaration | Exact formal content | Role for the target sentence |
| --- | --- | --- |
| `MPSTensor.blockTensor` | Groups a specified number \(L\) of physical sites, with blocked letters given by products of length \(L\). | It expresses a supplied finite blocking. It does not choose an \(L\) or prove local orthogonality. |
| `MPSTensor.transferMap_blockTensor` | The self-transfer map of `blockTensor A L` is the \(L\)-th power of the self-transfer map of \(A\). | It identifies exact blocking with transfer iteration, but concerns the diagonal self-transfer map. |
| `MPSTensor.IsBNTLocallyOrthogonal` | Every off-diagonal rectangular mixed transfer map of a block family is zero. | This is the exact contraction assumed by `lemma:modif` and is the appropriate reusable hypothesis. |
| `MPSTensor.HasPhysicalBlockingIsometry` and `MPSTensor.IsTransferIdempotent` | Two letters are related to one by a physical isometry if and only if the self-transfer map is idempotent. | These are exact RFP predicates. They concern a tensor already at a fixed point, not eventual finite blocking of an arbitrary tensor. |
| `MPSTensor.AppearsAsRenormalizationFlowLimit` | The transfer matrix of a tensor is the limit of a dyadic transfer-matrix orbit with the same bond dimension. `Tendsto` uses the ordinary topology of the finite-dimensional complex matrix space. | This is a precise formal interpretation of “appears as a limit.” It neither asserts convergence of every supplied initial tensor nor eventual equality at finite time. |
| `MPSTensor.appearsAsRenormalizationFlowLimit_iff_isTransferIdempotent` | A transfer matrix occurs as such a dyadic limit exactly when its transfer map is idempotent. | This characterizes possible limit points. It is not an eventual-blocking theorem. |
| `MPSTensor.rg_flow_converges_of_cf` | For each primitive block in the stated auxiliary canonical-form family, the dyadic powers of its self-transfer map converge pointwise to an idempotent map. | This is a possible diagonal comparison tool. It deliberately does not assert convergence of the full weighted repeated-copy tensor and says nothing by itself about exact off-diagonal vanishing. |
| `Kraus.mixedMapLM_pow_tendsto_zero_of_spectralRadius_lt_one` and `MPSTensor.mixedTransfer_pow_tendsto_zero` | Under a strict mixed-transfer spectral-radius bound, or the stronger normalized injective hypotheses of the MPS specialization, mixed-transfer powers converge pointwise to zero. | These are the closest formal counterparts of asymptotic cross-sector orthogonality. Their conclusion is a limit, not \(\mathbb E_{x,y}^{L}=0\) for some finite \(L\). |
| `MPSTensor.isBNTLocallyOrthogonal_of_isTransferIdempotent_directSum` | If the whole unweighted direct-sum tensor is already an exact RFP, and its nonzero-dimensional blocks are irreducible, left-canonical, and pairwise gauge-phase distinct, then its off-diagonal mixed transfer maps vanish exactly. | This is an exact RFP-to-local-orthogonality theorem under explicit hypotheses. It does not prove that blocking an arbitrary target-paper tensor reaches such a direct-sum RFP in finitely many steps. |

Consequently, no new target-paper version of blocking, transfer iteration, or
local orthogonality is needed.  Formalizing `lemma:modif` may use the existing
mixed-transfer predicate directly.  A future theorem deriving that predicate
from blocking would need a separate statement and proof; the present sources
do not supply one.

## 4. Hamiltonians and ground spaces

### 4.1 What the target paper leaves open

The discussion at `Papers/2502.20257/main.tex:5196-5198` makes two future-work
statements.

First, if the original Hamiltonian has a unique MPS ground state, one may gauge
that state and form a parent Hamiltonian for the resulting MPS.  The paper then
asks how this parent Hamiltonian is related to the Hamiltonian obtained by
gauging the original Hamiltonian, and conversely how their ground-state
subspaces compare.  It gives no equality, inclusion, unitary equivalence, or
spectral statement.

Second, the modified state-level Gauss-law projectors need not commute on the
whole Hilbert space.  Their common \(+1\) eigenspace is nonempty because it
contains the gauged MPS.  The paper leaves open whether the dimension of this
space is bounded or grows with system size; the small-system numerics are
reported only as preliminary evidence compatible with growth.

The assertion that the projectors commute on their common \(+1\) eigenspace
does not give a global commutation theorem: on that intersection each
projector restricts to the identity.  In particular, the product-projector
formula from the earlier commuting case
(`Papers/2502.20257/main.tex:457-465`) cannot be transferred to the modified
state-level projectors.

The paper does not state that this common eigenspace exhausts the physical
Hilbert space.  It also does not state that either gauging construction
preserves a spectral gap.  Uniqueness of the original ground state in the
outlook scenario is not a uniform-gap hypothesis.

### 4.2 What the maintained parent-Hamiltonian theory proves

TNLean's parent-Hamiltonian declarations are exact, but they concern the
canonical parent Hamiltonian attached to one supplied MPS tensor:

- `MPSTensor.groundSpace A L` is the local MPS space
  \(G_L(A)=\operatorname{range}\Gamma_L\), not a Gauss-law eigenspace.
- `MPSTensor.parentInteraction A L` is the orthogonal projector onto
  \(G_L(A)^\perp\).
- `MPSTensor.parentHamiltonian A L N` is the sum of the translated local
  parent interactions on an \(N\)-site periodic chain.
- `MPSTensor.chainGroundSpace A L N` is the intersection of the corresponding
  cyclic local MPS constraints.
- `MPSTensor.ker_parentHamiltonian_eq_chainGroundSpace` identifies that
  intersection with the kernel of this same parent Hamiltonian when
  \(0<N\) and \(L\le N\).
- `MPSTensor.parentHamiltonian_annihilates` proves that the MPS vector is in
  the kernel.  It does not say that this vector spans the kernel without
  additional injectivity hypotheses.

There are also exact uniqueness and gap theorems, with their own hypotheses.
For example, `MPSTensor.parentHamiltonian_unique_gs` assumes positive-length
block injectivity, while
`MPSTensor.IsPrimitiveMPS.exists_parentHamiltonianES_gap_eighth_mul` assumes a
primitive MPS tensor with a positive-definite fixed point and concludes a gap
for its canonical parent Hamiltonians at selected interaction ranges and
system sizes.  None of these declarations contains a Hamiltonian-level gauging
map or compares two gauging constructions.  They therefore cannot establish
gap preservation or equality of the two ground spaces considered at line
5196 of the target paper.

Finally, `MPSTensor.groundSpace_finrank_le` gives

\[
  \dim G_L(A)\le D^2
\]

for the local MPS space of a tensor with bond dimension \(D\).  This bound does
not apply to the common \(+1\) eigenspace of the modified Gauss laws.  The two
spaces are defined by different operators, and no declaration identifies
them.  In particular, the local MPS bound must not be used to decide whether
the state-level gauge-invariant subspace stays bounded or grows with the chain
length.

## 5. Faithful boundary for subsequent work

The following conclusions are justified by the sources and maintained
formalization:

1. `lemma:modif` may be formalized under the exact hypothesis
   `MPSTensor.IsBNTLocallyOrthogonal blocks`, at the physical scale of the
   supplied tensors.
2. Blocking and RG convergence may be studied separately, using the existing
   blocking, self-transfer, and mixed-transfer declarations with their exact
   hypotheses.
3. Any approximate version of `lemma:modif` would require a new quantitative
   statement; it is not present in arXiv:2502.20257.
4. Any Hamiltonian-level comparison requires definitions and hypotheses which
   relate the state-gauging construction to a gauged Hamiltonian.  The target
   paper marks this as future work.
5. Any theorem about the size or thermodynamic behavior of the common \(+1\)
   eigenspace requires additional mathematics beyond the existence of the one
   gauged MPS.

This audit does **not** assert an exact finite blocking, a spectral gap or its
preservation, a global product projector for the modified Gauss laws, equality
of Hamiltonian-level and state-level ground spaces, or growth of the common
\(+1\) eigenspace.

No Blueprint declaration status changes follow from this audit: it adds no
Lean declaration and completes no source theorem.  The existing tracking issue
already records the audit as the scope prerequisite for the conditional
formalization of `lemma:modif`.
