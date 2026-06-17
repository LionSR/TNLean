# Issue #599 follow-up — corner-support to multiplicative-domain is false as stated

## Outcome

I did **not** add a theorem to `TNLean/Channel/Schwarz/MultiplicativeDomainFull.lean`.
After inspecting the current multiplicative-domain API and testing the proposed
statement in a scratch file, I found that the intended theorem is **false even
for unital selfadjoint TP Kraus maps**.

So the obstruction on PR #696 is **not** a missing Lean lemma of the exact form

```lean
P * X = X → X * P = X → X ∈ KadisonSchwarz.multiplicativeDomain K
```

with `P ∈ MD(T)` fixed by `T`. One needs a stronger hypothesis describing the
**fixed-point algebra inside the corner**, not just corner support.

## Explicit counterexample

Take the dephasing channel on `M₂(ℂ)` with Kraus family

$$K_0 = E_{00}, \qquad K_1 = E_{11},$$

so

$$T(X) = K_0 X K_0^\dagger + K_1 X K_1^\dagger$$

is the diagonal conditional expectation.

Set

$$P := 1, \qquad X := E_{01}.$$

Then:

1. `P` is an orthogonal projection.
2. `T(P) = P`.
3. `P ∈ KadisonSchwarz.multiplicativeDomain K` by
   `KadisonSchwarz.one_mem_multiplicativeDomain`.
4. `P * X = X = X * P`.

But `X` is **not** in the multiplicative domain, because

$$T(XX^\dagger) = T(E_{00}) = E_{00},$$
while
$$T(X)T(X)^\dagger = 0.$$

Hence

$$T(XX^\dagger) \ne T(X)T(X)^\dagger,$$

so `X ∉ KadisonSchwarz.rightMultiplicativeDomain K`, therefore
`X ∉ KadisonSchwarz.multiplicativeDomain K`.

This already refutes the proposed theorem in the strongest possible way:
choosing `P = 1` makes the corner condition vacuous, so the statement would
force `MD(T) = M₂(ℂ)` for every unital CP map.

## Checked scratch formalization

I verified the concrete counterexample in the worktree-local scratch file

```text
Scratch/Issue599Counterexample.lean
```

with

```bash
cd .worktrees/issue-599-mult-domain && lake env lean Scratch/Issue599Counterexample.lean
```

The scratch file proves:

- `dephasingKraus_unital : KadisonSchwarz.IsUnitalKraus dephasingKraus`
- `offDiag_not_mem_multiplicativeDomain :
    E01 ∉ KadisonSchwarz.multiplicativeDomain dephasingKraus`
- the support equalities `1 * E01 = E01` and `E01 * 1 = E01`

I am **not** committing that scratch file, since the correct deliverable here is
an audit, not a new negative theorem in the library.

## What current TNLean already proves nearby

There is already a valid fixed-point-to-multiplicative-domain result:

- `Kraus.mem_multiplicativeDomain_of_mem_fixedPoints`
- `Kraus.fixedPoints_in_multiplicativeDomain`

in `TNLean/Channel/FixedPoint/Algebra.lean`.

So if an element is an actual fixed point of the channel (under the usual
faithful invariant-state hypotheses), then multiplicative-domain membership is
available. What fails is the attempted shortcut from **corner support alone**.

## Implication for PR #696 / issue #599

The remaining gap for `hProjStep` cannot be closed by a theorem whose only new
input is

- `P ∈ MD(T)`,
- `T(P) = P`, and
- `P X = X = X P`.

That theorem is false.

The right next target has to involve one of the following stronger statements:

1. a description of the fixed points of the sector-restricted map,
2. a sectorwise fixed-point decomposition of Wolf-type `Fix(T^m)` / `Fix((T^*)^m)`, or
3. a theorem identifying the corner dynamics with a genuine `*`-homomorphism or
   conditional expectation on the relevant fixed-point algebra.

In other words: for #599 the missing ingredient is a **fixed-point-algebra
statement**, not a pure multiplicative-domain closure statement for corner
support.
