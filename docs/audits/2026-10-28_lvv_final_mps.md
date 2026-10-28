# Normalized MPS extraction from the final viable span

The theorem `IsViableMPS.exists_openMPS` completes the endpoint extraction for a
successive viable-set construction. Given a final $(L,s,b,\delta)$-viable family, it
produces a full-chain vector $\psi$ satisfying

$$
 \|\psi\|=1,\qquad |\langle\psi,\Gamma\rangle|\ge1-\delta,
 \qquad \psi\text{ is an open-boundary MPS of bond dimension at most }s\max\{1,b\}.
$$

The source is [Landau, Vazirani and Vidick, arXiv:1307.5143v1](https://arxiv.org/pdf/1307.5143v1),
`algo53.tex`, Claim `c:2`, lines 520–527, and the final induction, lines 652–678.
This is an endpoint implication from an actual final family. It does not assume or
assert the intermediate induction, filtering construction or choice of its parameters.

The finite-span bound is proved independently of ground-state approximation. The
existing `isOpenMPS_of_mem_span` in `OpenMPSSpan.lean` writes an actual finite linear
combination, takes its coefficient matrices at each internal cut, and uses rank subadditivity.
The existing left-span theorem applies this to the linear reading of left coordinates.
The new `isOpenMPS_leftChain_of_mem_span` removes its outer effective-bound maximum:
for a nonempty family the product $|S|\max\{1,b\}$ is already at least one; for an empty
family the span contains only zero, whose internal cut matrices have rank zero. This
gives the exact full-chain-coordinate bond bound $|S|\max\{1,b\}$ without duplicating
the finite-sum proof.

The second new theorem, `IsViable.exists_openMPS_of_forall_isLeftOpenMPS`, uses
`IsViable.exists_fullLeftVector` at the final cut. The right block has exactly one
configuration, so the normalized viable witness is in the span of the final left
family. The full-left coordinate equivalence is an isometry. Pulling back the witness
preserves its norm and overlap and supplies the finite-span bond bound. The headline
then enlarges the actual family cardinality to its recorded bound $s$.

There is no use of an independent area-law theorem, an existence theorem for ground-state
MPS approximation, or a hypothetical tensor representation. No extra hypothesis such as
$b>0$, $s>0$, $\delta<1$, $q>0$ or $L>0$ is introduced. The existing effective bound
$\max\{1,b\}$ follows the convention already documented in the viable-set definition.

The actual module `ViableSet/FinalMPS.lean` passed strict separate-module compilation
with all standard linters and warnings treated as errors in 17.12 seconds. Its SHA-256
is `3331466360c51d6e475ff744a07f67314e367e3955398289b5f3bd7b301d5cc3`.
Manual foundation checks import the actual compiled module and inspect the three new
declarations. They passed in 3.97 seconds and report only `propext`, `Classical.choice`
and `Quot.sound`. They are kept under `/tmp`, with no permanent Lean test fixture committed,
in accordance with the current project conventions.

Static blueprint synchronization and reverse declaration coverage pass. The chapter passes
the repository LaTeX formatter and ChkTeX configuration; prose, whitespace, proof-integrity
and tactic-pattern checks pass as well. No compiled blueprint or ordinary build result
is asserted by these static checks.

The endpoint dependency is an unchanged local copy of the coordinator's
`ViableSet/Endpoints.lean`, SHA-256
`ff2b1b95552fd46a15b0298a2dfa00f4bc8526dc6a679dda170c193f5da43a70`.
It passed separate strict checking in 4.74 seconds and is excluded from this contribution's
patch. The finite-span dependency has SHA-256
`98dbe41242c88660d86c8ecad2cd22ed90f32a2fcec8adfb2dcd4c61d89c6a85` and is unchanged.
Compilation uses the agent's already seeded worktree and private temporary artifacts;
no Mathlib source is compiled, no shared cache is modified, and no duplicate ordinary
build is started. Ordinary integration and compiled blueprint declaration checks remain
the coordinator's verification.
