# Twisted-dimer unitary bond–flag factorization

Date: September 5, 2026. Scope: the project construction discussed in issues #7776 and #7751, read live on this date. Both issues were open. This note records mathematical provenance and the direct operator calculation formalized in `TNLean/MPS/MPDO/TwistedDimerUnitaryFactorization.lean` in PR #7780. The coordinating parent confirmed a clean targeted build and axiom audit on this date; the exact declarations are recorded below. The strict non-decoration specification in #7751 remains unresolved.

## Source provenance

The following SHA256 digests were recomputed from the local files on September 5, 2026. Line anchors below refer to these exact bytes. The three construction notes are locally available but ignored; they were not force-added. Their relevant excerpts are preserved here so that this tracked note is self-contained.

| Source | SHA256 |
| --- | --- |
| `Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex` | `01cad261200337e3b8ea53dc20900c005ed1bcb6123f2205a1cd381c86163ff7` |
| `Notes/OpenProblemsTN/strategies/p6_round46_mechanism_and_positioning.tex` | `3fffa297889e88d7825c90ad168722b1b3707580a7e8badef86c587e5af5df50` |
| `Notes/OpenProblemsTN/problems/p6_rfp_structure_constant_l_dependence.tex` | `316163fa7d3d1ae17e27c49f31d532b51ec76929e295157f9f81dd24b9fcfe91` |
| `Papers/1606.00608/MPDO-22-12-17-2.tex` | `c814f0de2792d5ee21fe102894781316de633aa559e0602610de5c9f72cf0e90` |

CPSV16, arXiv:1606.00608, source line 995 after the theorem labelled `thm:IV.13`, asks whether RFP structure coefficients can depend on length. Its precise concluding question is:

```tex
More concretely, whether there exist RFP $M$ for which $c_{\alpha,\beta,\gamma}^{(L)}$ depends on $L$.
```

That question motivates the example only. Neither the twisted-dimer construction nor the controlled unitary below is a printed CPSV16 result.

Round 44 introduces conditions N1–N3 at lines 213–226. N3, lines 223–226, reads exactly:

```tex
\item\label{it:p6-r44-n3} It is not a tensor product of a length-independent
fixed point with a simple length-dependent one; equivalently, the fusion
algebra is not a tensor product of an integer fusion ring with a
one-generator algebra.
```

The purported N3 proof, lines 375–378, is:

```tex
\ref{it:p6-r44-n2} is \cref{prop:p6-r44-gauge}, and \ref{it:p6-r44-n3} holds
because a tensor product of the toric-code boundary with a simple dimer has
fusion $O_fO_{f'}=\tr(C^L)\,O_{f\oplus f'}$ with a single channel, whereas
\cref{eq:p6-r44-z2-algebra} has two channels with distinct weights.
```

The same note, lines 381–391, records:

```tex
\begin{remark}[The deformed fusion algebra]\label{rem:p6-r44-deformed}
In the basis $O_\pm=O_L(\hat M_0)\pm O_L(\hat M_1)$ the algebra
\cref{eq:p6-r44-z2-algebra} reads $O_+^2=2(\alpha^L+\beta^L)O_+$,
$O_-^2=2(\alpha^L-\beta^L)O_-$, $O_+O_-=0$: a two-dimensional semisimple
algebra $\C\oplus\C$ for every $L$, as for the toric-code boundary, but whose
canonical basis of normal tensors is not a basis of scaled idempotents. The
weights $x^L,y^L$ are the spectrum of the bond state, and the $\Z_2$ structure
is the pairing between the bond-sign parity and the flag parity visible in
\cref{eq:p6-r44-z2-state}. As $y\to0$ the second channel closes and one
recovers the toric-code boundary tensored with a pure Bell dimer, whose
coefficients are rescalable to $\{1,0\}$.
```

The consolidated note explicitly acknowledges the limitation at lines 619–626; its concluding clause is:

```tex
presentation-free reading of the ratios in (N3) depends, observed only
numerically; and the exclusion in (N3) of decorations whose simple factor
itself has several blocks, which the ratio argument does not address.
```

Round 46, subsection `sec:p6-round46-channels`, lines 462–535, proves a related two-way channel statement. The forward channel discards and re-prepares a bond register, while changing its adjacent flag. The backward channel measures and resets that register. The displayed identities, under label `eq:p6-r46-twoway`, are:

```tex
\Bigl(\prod_m\mathcal F_m\Bigr)(\rho^0_N)=\rho^\lambda_N,\qquad
\Bigl(\prod_m\mathcal B_m\Bigr)(\rho^\lambda_N)=\rho^0_N .
```

These channels are not asserted to be inverse linear maps on the whole operator space. The source theorem calls its register circuits depth one and range two. This note does not transfer that terminology to circuits whose indivisible subsystems are whole physical sites. Nor does two-way conversion of these particular states establish unitary conjugacy. The following unitary calculation is independent of that channel theorem.

## What the N3 argument does not prove

The word “equivalently” requires a specified equivalence relation on tensors and a theorem relating it to fusion data. Neither follows from counting the nonzero coefficients in one displayed basis. The proof compares a toric-code boundary decorated by a one-generator simple dimer with the displayed two-channel multiplication. It does not exclude all simple decorations with several blocks, nor all changes of basis, blocking operations, physical coordinate changes, or virtual gauges.

Even the abstract algebra at each fixed positive length is insufficient: the source itself diagonalizes it as $\mathbb C\oplus\mathbb C$. If the displayed coefficients $\alpha^L\pm\beta^L$ are nonzero, rescaling $O_\pm$ by their respective multiplication constants gives two orthogonal idempotents. Such length-dependent algebra bases need not be admissible BNT changes. Conversely, an obstruction to positive rescaling of the two displayed BNT labels is not a theorem excluding arbitrary tensor factors. Thus neither that rescaling obstruction nor non-simplicity proves the original N3 sentence.

## Direct controlled-unitary calculation

Use the computational basis $|0\rangle,|1\rangle$ on each qubit. On a two-qubit bond define normalized Bell vectors and their rank-one projectors by

$$
|\Phi_\pm\rangle=2^{-1/2}(|00\rangle\pm|11\rangle),\qquad
P_\pm=|\Phi_\pm\rangle\langle\Phi_\pm|.
$$

These four-dimensional bond projectors should not be confused with the two-dimensional sign projectors used to write the coefficient matrices in the original tensor. Set

$$
\sigma=\tfrac78P_++\tfrac18P_-,\qquad
\sigma'=\tfrac78P_+-\tfrac18P_-.
$$

On a flag qubit let $X|f\rangle=|f\oplus1\rangle$ and $Z|f\rangle=(-1)^f|f\rangle$. On the full eight-dimensional bond–flag space put

$$
Q=I-P_-,\qquad V=Q\otimes I+P_-\otimes X.
$$

Orthogonality gives $QP_-=P_-Q=0$. Since $Q$ and $P_-$ are self-adjoint projections and $X^\dagger=X$, $X^2=I$, one obtains

$$
V^\dagger=V,\qquad V^2=Q\otimes I+P_-\otimes I=I.
$$

In particular, this is a unitary on the entire local space, not just on the support of the bond state. Its complement action is specified by $Q\otimes I$. The mixed terms vanish because $\sigma$ commutes with $P_-$. Using $XZX=-Z$ gives

$$
V(\sigma\otimes I)V^\dagger=\sigma\otimes I,
$$

$$
V(\sigma\otimes Z)V^\dagger=\sigma'\otimes Z.
$$

## Positive-length operator identity and physical coordinates

Let $N>0$, with cyclic sites $m\in\mathbb Z/N\mathbb Z$. A physical site has registers $(L_m,R_m,F_m)$. In incoming-cell coordinates the $m$th gate acts on $((R_{m-1},L_m),F_m)$. These cells use disjoint individual registers, even though gates on adjacent cells involve the same whole physical site.

For an explicit coordinate convention matching issue #7776, assign bond and flag coordinates to the outgoing bond instead:

$$
e_N(s)=(b,f),\qquad b_m=(R_m,L_{m+1}),\qquad f_m=F_{m+1}.
$$

Its inverse reconstructs site $j$ as

$$
(L_j,R_j,F_j)=((b_{j-1})_2,(b_j)_1,f_{j-1}).
$$

Thus this is a permutation of all computational basis configurations, including for $N=1$. The current Lean definition uses incoming cells $e_N^{\mathrm{in}}(s)_m=((R_{m-1},L_m),F_m)$ instead: the outgoing cell used here satisfies $e_N^{\mathrm{out}}(s)_m=e_N^{\mathrm{in}}(s)_{m+1}$. Simultaneously cyclically permuting the identical bond–flag cells leaves the resulting physical matrices unchanged. In the separated bond-string and flag-string coordinates define

$$
(U_N)_{(b,f),(c,g)}=\prod_m V_{(b_m,f_m),(c_m,g_m)},\qquad
\omega_N=2^{-N}(I^{\otimes N}+Z^{\otimes N}).
$$

For $N>0$, $\omega_N$ is the trace-one uniform state on even-parity flags. Finite tensor products of the local identities give $U_N^\dagger=U_N$ and both $U_NU_N^\dagger=I$ and $U_N^\dagger U_N=I$, as well as

$$
U_N(\sigma^{\otimes N}\otimes\omega_N)U_N^\dagger
=2^{-N}\bigl(\sigma^{\otimes N}\otimes I^{\otimes N}
 +(\sigma')^{\otimes N}\otimes Z^{\otimes N}\bigr).
$$

Write $E_N|s\rangle=|e_N(s)\rangle$ for the physical regrouping unitary. The actual closed operator of the project's tensor satisfies

$$
\rho_N(T)=E_N^\dagger U_N(\sigma^{\otimes N}\otimes\omega_N)U_N^\dagger E_N.
$$

Here is an entrywise check against the existing tensor, rather than an appeal to the channel construction. Both $\sigma$ and $\sigma'$ vanish outside the span of $|00\rangle,|11\rangle$. Their entries on $|aa\rangle,|bb\rangle$ are respectively $C_0(a,b)$ and $C_1(a,b)$, where

$$
C_0=\begin{pmatrix}1/2&3/8\\3/8&1/2\end{pmatrix},\qquad
C_1=\begin{pmatrix}3/8&1/2\\1/2&3/8\end{pmatrix}.
$$

Consequently the regrouped expression vanishes unless both ket and bra satisfy $R_m=L_{m+1}$ and their flags agree. When they do, its entry is

$$
2^{-N}\sum_{k=0}^1\prod_m C_k(L_m,L'_m)(-1)^{kF_m}.
$$

Cyclic relabeling of the product is valid also at $N=1$. This is exactly the closed-chain formula in `TNLean/MPS/MPDO/TwistedDimerMPDO.lean:220–221`, using the coefficient definition in `TwistedDimer.lean`. The existing declaration is `MPOTensor.TwistedDimer.mpo_T_entry_formula`, whose hypothesis is explicitly positive length. This audit inspected that source and the bit-coordinate definitions; it did not run Lean builds.

The positive-length restriction cannot be removed. At $N=0$ the original closed MPO is the trace of the identity on its eight-dimensional virtual space, namely $8$. The displayed bond–flag expression instead has empty bond product $1$ and $\omega_0=1+1=2$, hence value $2$.

## Conclusion and formalization boundary

The displayed bond–flag coupling can be removed by an explicit whole-space unitary after the stated neighboring-register regrouping. This is a project-derived operator-family factorization. It is not an on-site tensor factorization or a virtual-gauge equivalence, and no whole-site depth-one or other formal circuit-depth theorem is claimed. The operator identity does not itself classify the factors as renormalization fixed-point tensors. A strict non-decoration assertion allowing only some of those operations still needs a precise specification and a separate argument in #7751.

The formalization in `TNLean/MPS/MPDO/TwistedDimerUnitaryFactorization.lean`, included in PR #7780, proves `MPOTensor.TwistedDimer.mpo_eq_unitary_factorization` with the explicit hypothesis `hN : 0 < N` and conclusion `mpo T N = chainUnitary N * decoratedState N * (chainUnitary N)ᴴ`. In the same namespace, `localV_conjTranspose`, `localV_mul_self`, and `localV_conjugate` prove the local identities; `chainUnitary_conjTranspose`, `chainUnitary_mul_conjTranspose`, and `chainUnitary_conjTranspose_mul` prove the full-space self-adjointness and both unitary laws for every natural length. The coordinating parent reported a clean 3058-job targeted build with no warnings and an axiom audit of the factorization and unitary laws containing only `propext`, `Classical.choice`, and `Quot.sound`. This audit did not duplicate that build.

Blueprint coverage in `blueprint/src/chapter/ch21_mpdo_rfp_bnt_coefficients.tex` uses the incoming-cell convention and the physical-coordinate identity exactly as formalized. The labels are `def:mpdo_twisted_dimer_controlled_flip`, `lem:mpdo_twisted_dimer_bond_state_entries`, `lem:mpdo_twisted_dimer_controlled_flip`, `def:mpdo_twisted_dimer_bond_flag_regrouping`, and `thm:mpdo_twisted_dimer_unitary_factorization`. These results do not settle strict N3 in #7751.

## Flag identification and normalization, issue #7782

The live issue #7782 and `TNLean/MPS/MPDO/TwistedDimerFactorStates.lean` were read on September 5, 2026. The parent confirmed compilation and an axiom audit using only the three standard axioms above. The initial factor-state implementation is commit `aca5e6100`; the current source was inspected for the exact declarations below.

In namespace `MPOTensor.TwistedDimer`, `evenFlagState_eq_mpo_Mhat` identifies the flag operator with the existing density-normalized CPSV16 Example 4.12 tensor at every natural length:

$$
\omega_N=\rho^{(N)}(\widehat M),\qquad \widehat M=\tfrac12 M.
$$

At zero length both sides are $2$. The source anchor is `Papers/1606.00608/MPDO-22-12-17-2.tex:932–939`, which prints the unnormalized expression $I^{\otimes N}+Z^{\otimes N}$. The factor uses the halved tensor, not that printed tensor. Its channel fixed-point property and positive-length density normalization were already proved in `CPSVExample412NormalizedRFP.lean`; they are reused, not inferred merely from the operator factorization. The declaration `evenFlagState_has_rfpRepresentation` packages this existing MPDO and channel representation, while `evenFlagState_posSemidef` and `trace_evenFlagState` state positivity and trace one for $N>0$. The Blueprint links to `thm:cpsv_example412_normalized_rfp_maps` rather than duplicating those channel proofs.

The same module proves `sigma_posSemidef`, `trace_sigma`, and `trace_powN_sigma`. In particular, the mixed Bell bond matrix is positive and normalized, and every finite tensor power has trace one. The declarations `decoratedState_posSemidef`, `trace_decoratedState`, and `trace_mpo_T` then show that the independent factors and the conjugated twisted-dimer operator are density operators at every positive length. These are normalization statements; by themselves they do not construct a bond RFP tensor.

Normalization of the flag representatives matters separately from normalization of the physical density family. Raw $I,Z$ representatives have constant group-ring multiplication coefficients but transfer value $2$. Replacing them by $I/\sqrt2,Z/\sqrt2$ gives the geometric coefficient $(1/\sqrt2)^L$ at length $L$, since each product acquires one additional factor $1/\sqrt2$ per letter. Rescaling back removes this dependence but loses spectral normalization. No attached normalized vertical coefficient classification or source-global unit-weight canonical form follows from the flag identification.

The corresponding new Blueprint labels are `thm:mpdo_twisted_dimer_flag_factor` and `thm:mpdo_twisted_dimer_factor_normalization`.

## The exact bond RFP tensor, issue #7783

The live issue #7783 and the base implementation `TNLean/MPS/MPDO/TwistedDimerBondRFP.lean`, commit `e50d9f802`, were inspected on September 5, 2026. The parent confirmed compilation and an axiom audit using only the three standard axioms. This is an independent channel proof for a specified bond tensor, not a classification inferred solely from the earlier operator identity.

The source is `Notes/OpenProblemsTN/strategies/p6_round44_graded_dimer_twist.tex:162–193`, proposition `prop:p6-r44-dimer`. Its SHA256 was recomputed again for this continuation and still equals `01cad261200337e3b8ea53dc20900c005ed1bcb6123f2205a1cd381c86163ff7`. The local ignored file was not added. The bond-state definition at lines 162–165 is:

```tex
Let $C$ be a positive $2\times2$ matrix with $\tr C=1$, eigenvalues
$x_1,x_2$, and no vanishing entry. Let $\sigma_C=\sum_{rs}C_{rs}|rr\rangle
\langle ss|$ and let $\rho_N=\bigotimes_n\sigma_C^{(R_n,L_{n+1})}$ on sites
$\C^2_L\otimes\C^2_R$.
```

The relevant channel assertion at lines 175–176 reads:

```tex
$Q$ satisfies \cref{eq:p6-r44-def41} with $\mathcal T(X)=\Pi(X\otimes\sigma_C)
\Pi^\dagger$ and $\mathcal S=\tr_{R_1L_2}\circ\Pi^\dagger(\cdot)\Pi$.
```

Its channel proof at lines 185–188 is:

```tex
$(QQ)^{ab}=C_{pp'}E_{pp'}\otimes\sigma_C\otimes E_{qq'}$ because
$\sum_{tt'}C_{tt'}E_{tt'}\otimes E_{tt'}=\sigma_C$; this is
$\mathcal T(Q^{ab})$, and tracing out the inserted bond returns $Q^{ab}$ since
$\tr\sigma_C=1$.
```

The source also discusses canonical forms and fusion coefficients, but this continuation formalizes only the displayed bond state and its preparation/partial-trace mechanism. In explicit physical and virtual indices the implemented tensor is

$$
Q^{(l,r),(l',r')}=C_{ll'}E_{(l,l'),(r,r')},\qquad
C=\begin{pmatrix}1/2&3/8\\3/8&1/2\end{pmatrix}.
$$

This matrix-unit formula fixes the index convention without relying on the source's compressed notation. Both physical and virtual dimensions are four. In namespace `MPOTensor.TwistedDimer` the declaration is `sigmaDimer`; `incomingBondEquiv` sends a site configuration to the bonds $(R_{m-1},L_m)$. The theorem `mpo_sigmaDimer_eq_bondProduct` proves

$$
\rho^{(N)}(Q)=B_N^\dagger\sigma^{\otimes N}B_N\quad(N>0),
$$

where $B_N$ is the corresponding basis permutation. The declarations `sigmaDimer_isMPDO` and `trace_mpo_sigmaDimer` prove positivity and trace one. At $N=0$ the closed tensor gives $4$, not the empty bond product $1$.

The basis permutation `bondInsertionEquiv` is $J:((l,r),(u,v))\mapsto((l,u),(v,r))$. The maps `sigmaDimerRefine` and `sigmaDimerCoarse` are respectively

$$
\mathcal T_Q(Y)=J(Y\otimes\sigma)J^\dagger,
\qquad
\mathcal S_Q(W)=\operatorname{tr}_{\mathrm{bond}}(J^\dagger WJ).
$$

Their complete positivity and trace preservation are proved by `sigmaDimerRefine_isKrausCPTP` and `sigmaDimerCoarse_isKrausCPTP`, using preparation, reindexing, and partial-trace results rather than a copied specialized Kraus calculation. The retraction `sigmaDimerCoarse_refine` holds for every input operator. The theorems `sigmaDimerRefine_physClose1` and `sigmaDimerCoarse_physClose2` prove the two physical-closure equations for every virtual boundary matrix, not only for the periodic density family. They give `sigmaDimer_isRFPViaTS`.

The exact bond state here has nonzero eigenvalues $7/8,1/8$. The previously formalized tensor `RescalingStableLengthDependentRFP.R` instead has nonzero bond eigenvalues $25/32,7/32$; its canonical-form and simplicity results are not certificates for this new tensor. No global source-unit-weight canonical form, simplicity theorem, canonical multiplicity matrix, or attached normalized vertical coefficient classification is asserted for $Q$ in this continuation. The independent RFP classification does not prove strict on-site or virtual-gauge equivalence for the twisted dimer or a circuit-depth statement, and strict N3 remains unresolved.

The new Blueprint labels are `def:mpdo_twisted_dimer_bond_tensor`, `thm:mpdo_twisted_dimer_bond_product`, `def:mpdo_twisted_dimer_bond_channels`, and `thm:mpdo_twisted_dimer_bond_rfp`.

## Attachment to the two explicit tensor families

The completed bond module, commit `e3b600353`, additionally identifies the independent factors with the two actual tensor families. The parent confirmed compilation, positive-length equality tests, and the standard-axiom audit before these declarations were added to the Blueprint.

The declaration `MPOTensor.TwistedDimer.onsiteBondFlagEquiv` separates the bond qubits and flags without moving qubits between sites. Write its basis permutation as

$$
H_N|((l_m,r_m,f_m))_m\rangle
=|((l_m,r_m))_m\rangle\otimes|(f_m)_m\rangle.
$$

In the Blueprint's incoming-cell convention, `onsiteBondFlagEquiv_incoming` is the identity $(B_N\otimes I)H_N=S_NE_N$. Here $B_N$ reads incoming bonds from the bond-site chain, $E_N$ forms the incoming bond–flag cells, and $S_N$ separates their bond and flag strings. All maps read the same incoming bonds $(R_{m-1},L_m)$ and unchanged flags $F_m$.

For $N>0$, `decoratedState_eq_mpo_factors` proves

$$
D_N=H_N^\dagger\bigl(\rho^{(N)}(Q)\otimes\rho^{(N)}(\widehat M)\bigr)H_N.
$$

With $U_N$ now denoting the physical-coordinate unitary as in the Blueprint, `mpo_eq_unitary_mpo_factors` gives

$$
\rho^{(N)}(T)=U_NH_N^\dagger
\bigl(\rho^{(N)}(Q)\otimes\rho^{(N)}(\widehat M)\bigr)H_NU_N^\dagger.
$$

Thus the factors in the operator identity are attached to the exact independently classified bond and flag RFP tensors. This conclusion uses both the product formulas and the separate channel proofs, rather than inferring channel fixed-point structure from unitary equivalence of closed states. At $N=0$ the proposed first identity fails: $D_0=2$, whereas the product of the two empty MPOs is $4\cdot2=8$.

Although $H_N$ only separates on-site registers, $U_N$ crosses site boundaries. Neither equality proves strict on-site tensor equivalence, virtual-gauge equivalence, a circuit-depth bound, simplicity, or an attached canonical vertical coefficient formula. In particular, they do not settle N3. Blueprint labels: `def:mpdo_twisted_dimer_onsite_split` and `thm:mpdo_twisted_dimer_rfp_factor_attachment`.
