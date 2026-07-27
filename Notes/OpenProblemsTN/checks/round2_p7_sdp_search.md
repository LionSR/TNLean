# Round 2, P7: channel SDP search and exact deformed-toric obstruction

## Executive verdict

The deformed toric family in the strategy note gives a counterexample to the static converse once it is put in the trace-normalized canonical gauge.  For every rational

\[
0<|q|<1,
\qquad
M_{00}=\frac{I}{2},\quad M_{11}=\frac{qZ}{2},\quad M_{01}=M_{10}=0,
\]

the generated states are

\[
\rho_N(q)=2^{-N}\bigl(I^{\otimes N}+q^N Z^{\otimes N}\bigr).
\]

They are positive, have zero correlation length (ZCL), and saturate the mutual-information area law (SAL), exactly as in the strategy note.  Nevertheless, there are no CPTP coarse-graining and fine-graining maps between one and two sites.  More strongly, there are no such maps between any two consecutive block sizes $k$ and $k+1$.  The obstruction has an exact rational strict dual certificate for rational $q$, so it is not a solver-tolerance effect.

The obstruction sits in the non-simple part of the tensor.  The horizontal BNT element proportional to $Z$ is nilpotent in the relevant sense: tracing any one of its physical sites gives $\operatorname{tr}(Z)=0$, so the entire term is annihilated by a one-site partial trace.  Thus this does not conflict with the simple-tensor theorem.

This supplies a negative answer to `prob:static-rfp(a)`, including its ``possibly after blocking'' version, provided the problem's stated definitions are used.  Before presenting it as a theorem, the recommended next step is a short source-level check with the authors that no extra convention excludes subleading nilpotent BNT coefficients $0<|q|<1$.

The requested Fibonacci mutual-information numbers were **not** inferable from the supplied derivation note.  The note itself correctly states that the golden-ratio weights do not determine the finite-ring reduced density matrices.  I traced the primary sources, but they do not supply a directly machine-readable, gauge-fixed local boundary MPDO in the conventions needed here.  Consequently, no $I_1,I_2$ values are reported or claimed.  The exact weight-squaring and trace-preservation obstruction is confirmed below, but the unpublished entropy recollection remains unverified.

## 1. Provenance and implementation

### Sources inspected

1. `Notes/OpenProblemsTN/strategies/p7_static_channel_derivations.tex`, read in full.
2. `Notes/OpenProblemsTN/problems/p7_static_vs_channel_rfp.tex`, especially `prob:static-rfp` and `prob:ts-vs-algebra`.
3. Primary arXiv source of Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, including Definition 4.1 and the Fibonacci appendix example.
4. Primary arXiv source of Bultinck--Mariën--Williamson--Şahinoğlu--Haegeman--Verstraete, arXiv:1511.08090, including the graphical string-net MPO formula and Fibonacci $F$-symbols.

Items 3--4 were used only to check conventions and to search for the missing Fibonacci tensor.  The SDP and counterexample derivation below are original computations based on the strategy note.

### Code and numerical environment

The implementation is in:

- `checks/round2_p7_sdp.py`;
- `checks/round2_p7_sdp_results.json`;
- the JSON output stores the complete machine-readable solver statuses and residuals.

It uses CVXPY 1.9.2 and SCS 3.2.11 in an isolated Python environment, with requested SCS accuracy $2\times10^{-7}$ and at most $2\times10^5$ iterations.  The code implements the input-first Choi convention

\[
J_\Phi=\sum_{a,b}E_{ab}\otimes\Phi(E_{ab}),
\qquad
\Phi(Y)_{uv}=\sum_{a,b}Y_{ab}J_{(a,u),(b,v)}.
\]

For every channel it imposes:

1. $J_\Phi\succeq0$;
2. $\operatorname{tr}_{\rm out}J_\Phi=I_{\rm in}$;
3. all $D^2$ closure equations, including equations with zero closure matrices.

The two channel directions are solved independently.  This is legitimate because the definition imposes no nonlinear relation between their Choi matrices.

### Important normalization correction

As printed in the strategy note, $M_{00}=I$ and $M_{11}=qZ$.  This gauge cannot satisfy the channel identities even at $q=1$: trace preservation would require a channel to send $I_2$ to $I_4$, although their traces are $2$ and $4$.  SCS correctly declares both directions infeasible.

The normalized canonical gauge is

\[
M_{00}=I/2,
\qquad
M_{11}=qZ/2.
\]

It generates the normalized state $2^{-N}(I^{\otimes N}+q^N Z^{\otimes N})$ and makes the known toric point $q=1$ feasible.  This correction changes no normalized static state, ZCL calculation, or SAL calculation, but it is essential because the tensor-level CPTP identities preserve trace.

## 2. Positive controls

### Product MPDO

The product tensor has $D=1$ and $M_{00}=\operatorname{diag}(0.7,0.3)$.  Both directions were feasible:

| map | SCS status | minimum Choi eigenvalue | TP residual | closure residual |
|---|---:|---:|---:|---:|
| $1\to2$ | optimal | $5.69\times10^{-2}$ | $9.55\times10^{-9}$ | $8.05\times10^{-9}$ |
| $2\to1$ | optimal | $2.09\times10^{-1}$ | $1.67\times10^{-15}$ | $6.11\times10^{-16}$ |

Exact channels also exist: discard and prepare the appropriate product state in either direction.

### Toric boundary, $q=1$

After the $1/2$ normalization, both arities are feasible:

| arity pair | direction | status | minimum Choi eigenvalue | TP residual | closure residual |
|---|---|---:|---:|---:|---:|
| $1\leftrightarrow2$ | forward | optimal | $-9.24\times10^{-9}$ | $3.21\times10^{-9}$ | $8.43\times10^{-9}$ |
| $1\leftrightarrow2$ | reverse | optimal | $-8.62\times10^{-17}$ | $5.55\times10^{-16}$ | $6.66\times10^{-16}$ |
| $2\leftrightarrow3$ | forward | optimal | $-3.44\times10^{-9}$ | $9.73\times10^{-9}$ | $2.23\times10^{-9}$ |
| $2\leftrightarrow3$ | reverse | optimal | $-5.14\times10^{-17}$ | $1.33\times10^{-15}$ | $6.38\times10^{-16}$ |

The small negative eigenvalues in the forward solutions are at SCS feasibility tolerance.  Exact parity-measure/prepare channels verify feasibility independently.  Let

\[
P_\pm^{(k)}=\frac{I\pm Z^{\otimes k}}2,
\qquad
\tau_\pm^{(k)}=\frac{P_\pm^{(k)}}{2^{k-1}}.
\]

At $q=1$, measuring the input parity and preparing $\tau_\pm$ on the output gives exact channels in both directions.

## 3. Parameter scan

The complete scan used

\[
q\in\{-1,-0.9,-0.75,-0.5,-0.25,-0.1,0,0.1,0.25,0.5,0.75,0.9,1\}.
\]

Here `F` means SCS `optimal` and `I` means SCS `infeasible`.

| $q$ | $1\to2$ | $2\to1$ | $2\to3$ | $3\to2$ |
|---:|:---:|:---:|:---:|:---:|
| $-1$ | F | F | F | F |
| $-0.9$ | F | I | F | I |
| $-0.75$ | F | I | F | I |
| $-0.5$ | F | I | F | I |
| $-0.25$ | F | I | F | I |
| $-0.1$ | F | I | F | I |
| $0$ | F | F | F | F |
| $0.1$ | F | I | F | I |
| $0.25$ | F | I | F | I |
| $0.5$ | F | I | F | I |
| $0.75$ | F | I | F | I |
| $0.9$ | F | I | F | I |
| $1$ | F | F | F | F |

Thus the numerics expose a sharp, non-marginal phase diagram: the fine-graining direction is feasible throughout $[-1,1]$, while the reverse direction is feasible only at $q=0,\pm1$.

The forward feasibility has a direct exact construction.  Measure $k$-site parity, pass the resulting classical bit through a binary symmetric channel with correlation $q$, and prepare the normalized $(k+1)$-site parity sector.  This sends

\[
\frac{I_{2^k}}{2^k}\longmapsto\frac{I_{2^{k+1}}}{2^{k+1}},
\qquad
\frac{q^k Z^{\otimes k}}{2^k}
\longmapsto
\frac{q^{k+1}Z^{\otimes(k+1)}}{2^{k+1}}.
\]

## 4. Exact dual certificate and all-blocking theorem

For $k\ge2$, consider a hypothetical reverse channel

\[
\mathcal S_k:\mathcal M_{2^k}\to\mathcal M_{2^{k-1}}
\]

which maps the $k$-site closures to the $(k-1)$-site closures.  The two nonzero closure equations force

\[
\mathcal S_k(I)=2I,
\qquad
\mathcal S_k(Z^{\otimes k})=\frac{2}{q}Z^{\otimes(k-1)}.
\]

Let

\[
P_+^{(k)}=\frac{I+Z^{\otimes k}}2\succeq0
\]

and choose a computational basis vector $v$ whose $Z^{\otimes(k-1)}$ eigenvalue is $-\operatorname{sgn}(q)$.  Complete positivity would imply

\[
0\le \langle v|\mathcal S_k(P_+^{(k)})|v\rangle
=1-\frac1{|q|},
\]

which is strictly negative when $0<|q|<1$.  This proves exact infeasibility for every consecutive pair of block sizes, not only $1\leftrightarrow2$ and $2\leftrightarrow3$.

This is also an explicit strict Choi-dual separator.  Use the two interpolation constraints with input matrices

\[
Y_0=\frac{I}{2^k},
\qquad
Y_1=\frac{q^kZ^{\otimes k}}{2^k},
\]

and dual output matrices

\[
H_0=2^{k-1}|v\rangle\langle v|,
\qquad
H_1=\frac{2^{k-1}}{q^k}|v\rangle\langle v|.
\]

Their adjoint image is

\[
Y_0^{\mathsf T}\otimes H_0+Y_1^{\mathsf T}\otimes H_1
=P_+^{(k)}\otimes|v\rangle\langle v|\succeq0,
\]

while pairing the same multipliers with the required outputs gives

\[
1-\frac1{|q|}<0.
\]

For rational $q$, every entry of this certificate is rational.  At the representative point $q=1/2$:

- for $2\to1$, $(H_0,H_1)=(2,8)|v\rangle\langle v|$ and the dual pairing is $-1$;
- for $3\to2$, $(H_0,H_1)=(4,32)|v\rangle\langle v|$ and the dual pairing is again $-1$.

No trace-preserving dual multiplier is needed: positivity plus the two closure equations already contradict each other.  This is stronger and cleaner than rationalizing a noisy solver-returned dual vector.

The $1\to2$ reverse case is the same formula with $k=2$.  More generally, if one first blocks $r$ original sites into one supersite, the requested one-to-two map is a reverse map from $2r$ original sites to $r$ original sites.  Its closure equations force an amplification by $q^{-r}$, and the same positive-parity test gives $1-|q|^{-r}<0$.  Therefore **no finite blocking restores the RFP channel property**.

## 5. Static properties and non-simplicity

For $|q|\le1$, the eigenvalues of $\rho_N(q)$ are

\[
2^{-N}(1\pm q^N),
\]

each with multiplicity $2^{N-1}$, hence positivity is exact.  Every proper reduction is maximally mixed because tracing one site annihilates $Z^{\otimes N}$.  Therefore separated correlations factorize (ZCL), and

\[
I_L=N\log2-S(\rho_N(q))
\]

is independent of every admissible region size $L$ (SAL).

The same trace identity proves non-simplicity.  The horizontal BNT contains the $qZ$ component.  For $q\ne0$,

\[
\operatorname{tr}(qZ)=0,
\]

so a partial trace over one site annihilates every periodic operator generated by this BNT element.  This is precisely the nilpotent behavior excluded by the simple-tensor results.

## 6. Fibonacci $\rho$ versus $\rho^2$

### What is verified exactly

With $\phi=(1+\sqrt5)/2$ and sector weights $(1,\phi)$, the normalized distributions are

\[
p=(\phi^{-2},\phi^{-1})
=\left(\frac{3-\sqrt5}{2},\frac{\sqrt5-1}{2}\right),
\]

and

\[
p^{[2]}=\frac{(1,\phi^2)}{1+\phi^2}
=\left(\frac{5-\sqrt5}{10},\frac{5+\sqrt5}{10}\right).
\]

A symbolic Wolfram Language check verified both normalizations and the unequal sector trace ratios

\[
\frac{p_1^{[2]}}{p_1}=\frac{5+\sqrt5}{10},
\qquad
\frac{p_\tau^{[2]}}{p_\tau}=\frac{5+3\sqrt5}{10},
\qquad
\frac{p_\tau^{[2]}/p_\tau}{p_1^{[2]}/p_1}=\phi.
\]

Thus the inherited sectorwise CP map cannot be trace preserving after squaring.  This confirms the weight obstruction in the strategy note.

### Why the requested $I_1,I_2$ table is not present

The supplied note explicitly proves that the weights do not determine the transfer operator or the finite-ring reductions.  It even gives channels with the same Fibonacci fixed density matrix and spectra $\{1,t,t,t\}$ for arbitrary $t\in[0,1]$.  Hence no valid computation of $I_1$ and $I_2$ can use the two golden-ratio weights alone.

The primary source arXiv:1606.00608 gives, for one vacuum BNT element, only

\[
A^{ijk}_{\alpha\beta}=\delta_{i\alpha}\delta_{k\beta}N_{ijk},
\]

with a support rule for $N_{ijk}$, not the complete weighted boundary MPDO needed for the entropy calculation.  ArXiv:1511.08090 gives the string-net MPO graphically in terms of $G$-symbols and supplies the Fibonacci $F$-symbols, but not as a gauge-fixed numerical tensor in the index convention of the P7 note.  Translating that graph is a substantive reconstruction step; guessing it would destroy provenance.

Accordingly, for $N=4,\ldots,8$ the honest status is:

| $N$ | $I_1(\rho)$ | $I_2(\rho)$ | $I_1(\rho^2)$ | $I_2(\rho^2)$ |
|---:|:---:|:---:|:---:|:---:|
| 4 | not determined from supplied data | not determined | not determined | not determined |
| 5 | not determined from supplied data | not determined | not determined | not determined |
| 6 | not determined from supplied data | not determined | not determined | not determined |
| 7 | not determined from supplied data | not determined | not determined | not determined |
| 8 | not determined from supplied data | not determined | not determined | not determined |

This is a failed deliverable item, not a negative numerical result.  The unpublished Cirac--Pérez-García entropy recollection remains to be verified from an explicit local tensor.

## 7. Implications and next steps

1. **Highest priority: validate the counterexample's scope with the source conventions.** The proof is elementary and exact.  Check only that the canonical-form definition permits the subleading nilpotent coefficient $q$ and that SAL is intended at each fixed ring size exactly as quoted.
2. **If confirmed, write the result as a proposition.** The one-parameter family proves ZCL+SAL $\not\Rightarrow$ RFP even after arbitrary finite blocking.  The proof needs no SDP machinery once discovered.
3. **Interpret the missing static condition.** The counterexample isolates a natural candidate strengthening: static data must control nilpotent BNT amplitudes that disappear under proper reductions.  ZCL and SAL cannot see them, while reversibility requires their trace-norm distinguishability not to shrink.  A promising $\Sigma$ is therefore an ``absence of hidden decaying nilpotent sectors'' or, more operationally, preservation of distinguishability for boundary-conditioned closures.
4. **Relation to $\Sigma_2$ and $\Sigma_3$.** Every proper local reduction here is maximally mixed, so a purely local compatible-Markov condition of the stated $\Sigma_2$ type is also blind to the obstruction.  Thus $\Sigma_2$ as currently phrased is unlikely to suffice.  The obstruction is instead visible at the boundary-conditioned operator-system level used by the SDP.
5. **Fibonacci follow-up.** Obtain a gauge-fixed numerical boundary MPO directly from one of the original authors or from the code used for arXiv:1511.08090.  Record the precise map from categorical labels to matrix indices, verify positivity and normalization for $N=4$, and only then compute the four entropy columns for $N=4,\ldots,8$ at high precision.

## Reproduction

From an environment containing CVXPY and SCS:

```sh
python checks/round2_p7_sdp.py
```

The script writes the complete machine-readable solver statuses and residuals to `checks/round2_p7_sdp_results.json`.
