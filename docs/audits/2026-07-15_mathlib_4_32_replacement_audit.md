# Mathlib 4.32 replacement audit

Date: 2026-07-15.

This audit records Mathlib material newly available, or newly more useful, in
the upgrade from Mathlib 4.31 to Mathlib 4.32. Its purpose is to identify
places where TNLean can replace local auxiliary development by standard
Mathlib declarations, to distinguish exact replacements from project-specific
results that should remain local, and to record upgrade breakages separately
from the repository's pre-existing warning backlog.

This is an audit document, not an upgrade-repair change. No TNLean theorem or
proof is intentionally changed by this audit.

## Dependency pins and comparison range

The dependency pins inspected in the worktree are:

- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib tag: `v4.32.0`.
- Mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`.

The comparison baseline is:

- Mathlib tag: `v4.31.0`.
- Mathlib commit: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

The Mathlib range `v4.31.0..v4.32.0` contains 711 non-merge commits and
2,334 changed paths. The audit searched that range by commit subject and source
path, searched declarations by name and type, inspected the defining Mathlib
source, and matched the resulting APIs against concrete TNLean declarations and
use sites.

The Mathlib cache for the 4.32 worktree was fetched successfully. The first
cache command was issued before a project session had been activated and was
rejected for that reason; after opening the project through Lean diagnostics,
the cache fetch was retried and succeeded.

## Executive summary

There are three substantive Mathlib 4.32 developments relevant to current
TNLean code.

1. **Direct isometric continuous functional calculus for ordinary square
   matrices is the strongest replacement.** Under
   `Matrix.Norms.L2Operator`, Mathlib now supplies
   `Matrix.instIsometricContinuousFunctionalCalculus` directly on
   `Matrix n n 𝕜`. This removes the reason for
   `TNLean/Channel/DensityRetract.lean` to transport matrix absolute value and
   its continuity through `CStarMatrix`.

2. **The determinant/kernel/nondegeneracy API is now substantially better.**
   In particular, `Matrix.exists_mulVec_eq_zero_iff` directly converts
   determinant singularity into a nonzero kernel vector. TNLean has already
   adopted it in two places. It can also shorten the final determinant argument
   in `TNLean/MPS/BNT/Basic.lean` by eliminating an intermediate injectivity and
   unit-matrix detour.

3. **Self-adjoint decomposition has been abstracted and the positive-map API
   has changed.** The new `SelfAdjointDecompose` class supports the receiver-
   style theorem `IsSelfAdjoint.map'`. The former alias `map_isSelfAdjoint` is
   deprecated. This is both a useful abstraction and a concrete 4.32 upgrade
   break in `TNLean/Channel/Basic.lean`, because the replacement has a different
   argument order.

The initial full 4.32 upgrade build did **not** pass. It exposed four failing
TNLean targets:

- `TNLean.Channel.Basic`;
- `TNLean.Algebra.NewtonGirard`;
- `TNLean.PEPS.FundamentalTheorem.Uniqueness`;
- `TNLean.PEPS.NormalEdgeGaugeFamily`.

These failures are documented below. This audit does not claim that a repaired
full build passed. In particular, the initial-build evidence must not be read as
a verification of any proposed repair.

Most warnings printed by the initial build are not new 4.32 upgrade problems.
The only TNLean deprecation warning tied directly to a 4.32 API change was the
`map_isSelfAdjoint` warning in `TNLean/Channel/Basic.lean`; the large remainder
was overwhelmingly the pre-existing style/header backlog. Warning counts below
are counts from the incomplete initial build, not complete repository totals.

## Mathlib 4.32 material found

### Direct isometric CFC for ordinary square matrices

Relevant Mathlib commit:

- `a53f9216345ba66b3a21ec82f01c008b1bbef989` —
  `feat(CStarAlgebra): IsometricCFC instance for square RCLike matrices (#40272)`
  (2026-06-24).

Relevant declaration:

```lean
Matrix.instIsometricContinuousFunctionalCalculus
```

Its type is:

```lean
{𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] :
  IsometricContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint
```

Module/import:

```lean
import Mathlib.Analysis.Matrix.Order
```

The instance is deliberately scoped:

```lean
open scoped Matrix.Norms.L2Operator
```

The defining source explains that this is the CFC associated with the operator
norm obtained by identifying matrices with continuous linear endomorphisms of
`EuclideanSpace 𝕜 n`.

#### Exact TNLean target

The target is `TNLean/Channel/DensityRetract.lean`:

- lines 24--26: a local `ContinuousFunctionalCalculus` instance on
  `CStarMatrix (Fin D) (Fin D) ℂ`;
- lines 28--30: a local `IsometricContinuousFunctionalCalculus` instance on the
  same `CStarMatrix` type;
- lines 78--80: `matrixAbs`;
- lines 82--127: `continuous_matrixAbs`.

The current proof of `continuous_matrixAbs` is not merely a local theorem call.
It:

1. sends an ordinary matrix to `CStarMatrix`;
2. defines `g A = star A * A` there;
3. applies `Continuous.cfc_of_mem_nhdsSet` to `Real.sqrt`;
4. transports the result back through `CStarMatrix.ofMatrixL.symm`; and
5. proves compatibility with the ordinary-matrix CFC through
   `CStarMatrix.ofMatrixStarAlgEquiv` and `StarAlgHomClass.map_cfc`.

Mathlib 4.32 makes this transport layer unnecessary. With
`Matrix.Norms.L2Operator` open, the CFC can be run directly on
`Matrix (Fin D) (Fin D) ℂ`. At the highest level, the continuity statement is
now expected to reduce directly to:

```lean
exact CFC.continuous_abs
```

Equivalently, if the proof is kept expanded, the existing
`Continuous.cfc_of_mem_nhdsSet` argument can be applied directly to ordinary
matrices with `A ↦ star A * A`, without introducing `CStarMatrix`, `F`, `hF`,
`hEq`, or the star-algebra-equivalence transport calculation.

Recommended action:

- open `Matrix.Norms.L2Operator` in this file;
- remove the two local `CStarMatrix` CFC instances;
- replace the transported continuity proof by the ordinary-matrix CFC theorem;
- then remove imports used only by the `CStarMatrix` transport, after checking
  the resulting file's actual import requirements.

Status: **true replacement** of an ad hoc implementation layer. The local
notion `matrixAbs` may remain as project vocabulary, but its infrastructure and
continuity proof no longer need to be local.

Important caveat: this instance is for the L2 operator norm scope. It does not
replace TNLean's distinct `Matrix.Norms.Operator`/`linftyOp` infrastructure, and
it should not be used to identify those norms definitionally.

### Determinants, kernel vectors, and matrix nondegeneracy

Relevant Mathlib commits:

- `b49d30f68e4cf14987f1724c5db8b3b193af6b9f` —
  `feat(LinearAlgebra/Matrix/Nondegenerate): more API and generalize to non-domains (#39634)`
  (2026-07-01).
- `d530c3afdcda4ac38c10f6fec4556806d91e29a0` —
  `chore(LinearAlgebra/Matrix/Nondegenerate): generalize lemmas to CommSemiring (#41271)`
  (2026-07-02).

Principal module/import:

```lean
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
```

Supporting definitions are in:

```lean
Mathlib.LinearAlgebra.Matrix.Nondegenerate
```

Relevant declarations include:

- `Matrix.exists_mulVec_eq_zero_iff`;
- `Matrix.exists_vecMul_eq_zero_iff`;
- `Matrix.nondegenerate_iff_det_ne_zero`;
- `Matrix.separatingLeft_iff_det_ne_zero`;
- `Matrix.separatingRight_iff_det_ne_zero`;
- `Matrix.separatingLeft_iff_forall_vecMul_eq_zero`;
- `Matrix.separatingRight_iff_forall_mulVec_eq_zero`;
- `Matrix.Nondegenerate.eq_zero_of_mulVec_eq_zero`;
- `Matrix.Nondegenerate.eq_zero_of_vecMul_eq_zero`.

For a finite square matrix over an integral domain, the key theorem is:

```lean
Matrix.exists_mulVec_eq_zero_iff :
  (∃ v, v ≠ 0 ∧ M *ᵥ v = 0) ↔ M.det = 0
```

The broader nondegeneracy and separating-side API is useful when a proof is
naturally phrased as cancellation of left or right multiplication. For TNLean's
current complex-matrix arguments, however,
`Matrix.exists_mulVec_eq_zero_iff` is the most direct replacement.

#### TNLean uses already on the canonical API

`TNLean/Spectral/GaugeConstruction.lean:128--137` defines the local theorem
`det_ne_zero_of_ker_all`. Its final singularity step already uses:

```lean
rw [Matrix.exists_mulVec_eq_zero_iff.symm] at h_det
```

`TNLean/Channel/Irreducible/Growth/KernelDescent.lean:148--155` already uses:

```lean
obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
```

These are good 4.32-style uses. They should not be wrapped again under another
local determinant/kernel equivalence.

#### Further exact simplification in BNT

The remaining clear target is `TNLean/MPS/BNT/Basic.lean:324--352`, inside
`exists_invertible_changeBasis`. After proving the local fact

```lean
hmulVec_zero : ∀ a, U.mulVec a = 0 → a = 0
```

the current proof constructs:

1. `hinj : Function.Injective U.mulVec`;
2. `hunit : IsUnit U` via `Matrix.mulVec_injective_iff_isUnit`; and
3. `hdet : U.det ≠ 0` via `Matrix.isUnit_iff_isUnit_det`.

The final block can instead be reduced to the singular-kernel contradiction:

```lean
have hdet : U.det ≠ 0 := by
  intro hdet
  obtain ⟨a, ha, hUa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact ha (hmulVec_zero a hUa)
```

This removes the local `hinj` and `hunit` proof devices while preserving the
statement and the mathematical route.

Status: **true replacement of final proof plumbing**, not a replacement of the
BNT change-of-basis theorem itself.

#### Non-replacement in gauge construction

Mathlib does not replace
`TNLean/Spectral/GaugeConstruction.det_ne_zero_of_ker_all`. The
project-specific content is that invariance of `ker X` under every matrix,
together with `X ≠ 0`, forces the kernel to be trivial. Mathlib only supplies
the final conversion between determinant zero and existence of a nonzero
kernel vector. The local theorem should remain.

### Self-adjoint decomposition and positive maps

Relevant Mathlib commit:

- `a163fd2f6fb7408d4102dbb5faaca2b635ba1c0d` —
  `feat: introduce SelfAdjointDecompose class (#40530)` (2026-06-23).

Principal module/import:

```lean
import Mathlib.Algebra.Order.Star.Basic
```

The CFC-generated instance is in:

```lean
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
```

Relevant declarations are:

- `SelfAdjointDecompose`;
- `IsSelfAdjoint.exists_nonneg_sub_nonneg`;
- `IsSelfAdjoint.map'`.

The class records that every self-adjoint element can be written as the
difference of two nonnegative elements:

```lean
class SelfAdjointDecompose (R : Type*) [AddGroup R] [Star R] [PartialOrder R] : Prop where
  exists_nonneg_sub_nonneg {a : R} (ha : IsSelfAdjoint a) :
    ∃ b c, 0 ≤ b ∧ 0 ≤ c ∧ a = b - c
```

The map theorem is receiver-style:

```lean
IsSelfAdjoint.map' :
  IsSelfAdjoint a → F → IsSelfAdjoint (f a)
```

Mathlib retains the old name only as a deprecated alias:

```lean
@[deprecated (since := "2026-06-12")]
alias map_isSelfAdjoint := IsSelfAdjoint.map'
```

#### Exact TNLean target and upgrade failure

The target is `TNLean/Channel/Basic.lean:199--207`, the local theorem
`IsPositiveMap.map_isHermitian`. Its final line currently uses the old
function-style order:

```lean
map_isSelfAdjoint hE.toPositiveLinearMap X hX.isSelfAdjoint
```

Under Mathlib 4.32 this first emits the deprecation warning and then fails with
a type mismatch: the first explicit argument of the replacement is expected to
be an `IsSelfAdjoint` proof, not the positive linear map.

The receiver-style adaptation is:

```lean
exact IsSelfAdjoint.isHermitian
  (hX.isSelfAdjoint.map' hE.toPositiveLinearMap)
```

Recommended action:

- update the call to `IsSelfAdjoint.map'` with receiver-style argument order;
- retain `IsPositiveMap.toPositiveLinearMap`;
- retain `IsPositiveMap.map_isHermitian` as the useful bridge from TNLean's
  concrete matrix positivity predicate to the local Hermitian vocabulary.

This is an **API adaptation**, not a reason to replace TNLean's positive-map
interface wholesale. Likewise,
`TNLean/Channel/Schwarz/PositiveMapProperties.lean` can continue to prove
`IsPositiveMap.map_conjTranspose` through the bridged Mathlib positive map; no
new local self-adjoint decomposition should be introduced.

## File-by-file replacement map

### `TNLean/Channel/DensityRetract.lean`

Status: **strong exact infrastructure replacement**.

Use `Matrix.instIsometricContinuousFunctionalCalculus` under
`Matrix.Norms.L2Operator`. Keep the project-level `matrixAbs` name if useful,
but remove the two local `CStarMatrix` CFC instances and the transport proof in
`continuous_matrixAbs`.

### `TNLean/MPS/BNT/Basic.lean`

Status: **small exact proof simplification**.

After proving triviality of the `mulVec` kernel, use
`Matrix.exists_mulVec_eq_zero_iff` directly to establish determinant
nonvanishing. Remove the intermediate injectivity and `IsUnit` constructions.
The BNT theorem itself remains local.

### `TNLean/Spectral/GaugeConstruction.lean`

Status: **canonical Mathlib final step already adopted; main theorem remains
local**.

Keep `det_ne_zero_of_ker_all`. Continue using
`Matrix.exists_mulVec_eq_zero_iff` for the last singularity conversion.

### `TNLean/Channel/Irreducible/Growth/KernelDescent.lean`

Status: **canonical Mathlib API already adopted**.

The determinant-zero branch already extracts a nonzero kernel vector by
`Matrix.exists_mulVec_eq_zero_iff.mpr`. No replacement wrapper is needed.

### `TNLean/Channel/Basic.lean`

Status: **required 4.32 API adaptation, local bridge retained**.

Replace the deprecated function-style `map_isSelfAdjoint` call by
`hX.isSelfAdjoint.map' hE.toPositiveLinearMap`. Keep
`IsPositiveMap.toPositiveLinearMap` and `IsPositiveMap.map_isHermitian`.

### `TNLean/PEPS/FundamentalTheorem/Uniqueness.lean`

Status: **required 4.32 API adaptation, not a replacement opportunity**.

At lines 393 and 418, install the available `Nonempty` proof as an instance and
use `Matrix.det_zero` without an explicit argument.

### `TNLean/PEPS/NormalEdgeGaugeFamily.lean`

Status: **required 4.32 API adaptation, not a replacement opportunity**.

At line 153, install the `hne : Nonempty (Fin n)` branch as an instance and use
`Matrix.det_zero` without an explicit argument.

### `TNLean/Algebra/NewtonGirard.lean`

Status: **4.32 elaboration/performance regression to repair separately**.

No new Mathlib 4.32 theorem found in this audit directly replaces the local
Newton--Girard development. The observed timeouts are proof-elaboration
failures, not evidence that the mathematical statements should be deleted.

## Important non-replacements and caveats

- `Matrix.instIsometricContinuousFunctionalCalculus` is tied to
  `Matrix.Norms.L2Operator`. It does not replace TNLean's infinity-induced
  operator norm or establish equality with `linftyOp`.
- `Matrix.exists_mulVec_eq_zero_iff` replaces determinant/kernel conversion,
  not project-specific arguments establishing kernel invariance, triviality of
  invariant kernels, BNT change-of-basis structure, or irreducibility descent.
- `SelfAdjointDecompose` and `IsSelfAdjoint.map'` support the existing bridge to
  `PositiveLinearMap`; they do not replace TNLean's concrete `IsPositiveMap`,
  channel, Kraus, Choi, trace-preserving, partial-trace, or tensor-map APIs.
- The new nondegeneracy and separating-side lemmas are valuable general API,
  but introducing local aliases for all of them would recreate the pass-through
  layer this audit is intended to avoid.
- No direct Mathlib 4.32 replacement was found for the local Newton--Girard
  recursion. Its upgrade failure should be treated as an elaboration repair.
- The `Matrix.det_zero` change is a source-compatible simplification only after
  call sites are adjusted to typeclass style; old explicit-argument calls no
  longer elaborate.

## Mathlib 4.32 upgrade breakages observed

A full `lake build` was run after the 4.32 cache fetch. The build stopped with
four failed required targets. The saved initial-build log was
`/tmp/tnlean_mathlib432_build.log`.

### 1. `TNLean.Channel.Basic`: deprecated alias and argument-order change

Location:

```text
TNLean/Channel/Basic.lean:207
```

Observed warning:

```text
`map_isSelfAdjoint` has been deprecated: Use `IsSelfAdjoint.map'` instead
```

Observed error: `hE.toPositiveLinearMap` was supplied where the replacement
expected an `IsSelfAdjoint` proof. This is a direct consequence of moving from
the old function-style invocation to receiver-style `IsSelfAdjoint.map'`.

Proposed adaptation:

```lean
hX.isSelfAdjoint.map' hE.toPositiveLinearMap
```

### 2. `TNLean.Algebra.NewtonGirard`: deterministic heartbeat timeouts

Locations:

```text
TNLean/Algebra/NewtonGirard.lean:140
TNLean/Algebra/NewtonGirard.lean:163
TNLean/Algebra/NewtonGirard.lean:193
TNLean/Algebra/NewtonGirard.lean:201
```

The first three diagnostics are deterministic `whnf` timeouts at the default
200,000-heartbeat limit. The line-201 unknown-private-constant error for
`T_trace_recursion` is downstream fallout after the private theorem failed to
compile, not an independent missing declaration.

The expensive proof shapes are the broad `congr 1`/`ring` step in
`jacobi_formula_charpolyRev` and the nested `congr 1` matrix-trace rewrites in
`T_trace_recursion`. A repair should first make those congruences more explicit
and reduce normalization, rather than merely adding a global heartbeat bound.
No repaired full build is claimed here.

### 3. `TNLean.PEPS.FundamentalTheorem.Uniqueness`: `Matrix.det_zero` binder change

Locations:

```text
TNLean/PEPS/FundamentalTheorem/Uniqueness.lean:393
TNLean/PEPS/FundamentalTheorem/Uniqueness.lean:418
```

Relevant Mathlib commit:

- `bbd5fcf3ae648b745376f9f06b251e6b6d168e92` —
  `chore(LinearAlgebra/Matrix): make det_zero simp (#40699)` (2026-06-22).

In Mathlib 4.31 the theorem was:

```lean
theorem det_zero (_ : Nonempty n) : det (0 : Matrix n n R) = 0
```

In Mathlib 4.32 it is:

```lean
@[simp] theorem det_zero [Nonempty n] : det (0 : Matrix n n R) = 0
```

The old calls `Matrix.det_zero ⟨i⟩` therefore try to apply an equality as a
function. The local nonempty proof must instead be installed as an instance,
after which `Matrix.det_zero` is used without an explicit argument.

### 4. `TNLean.PEPS.NormalEdgeGaugeFamily`: the same `Matrix.det_zero` binder change

Location:

```text
TNLean/PEPS/NormalEdgeGaugeFamily.lean:153
```

The branch already has `hne : Nonempty (Fin n)`, but the old call
`Matrix.det_zero hne` is no longer valid. Install `hne` as the local
`Nonempty (Fin n)` instance, then use `Matrix.det_zero` directly.

## Warning triage

The initial, incomplete build printed 363 first-line warning diagnostics. These
should not be treated as 363 Mathlib 4.32 upgrade regressions.

The dominant categories were pre-existing repository style issues:

- 287 short-copyright/header warnings;
- 22 module-docstring-placement warnings;
- 17 additional header-format warnings;
- 6 recommendations about unnecessary `show` tactic use;
- 2 recommendations to use `;` rather than `<;>`;
- smaller numbers of unused-hypothesis, unused-section-variable, no-op tactic,
  and declaration-kind style warnings.

There were also ten deprecation warnings in the `Gametheory` dependency:

- six uses of deprecated `Set.mem_diff`;
- one use of deprecated `PNat.one_le`;
- three uses of deprecated `continuous_finset_sum`.

Those are dependency warnings, not TNLean replacement targets.

The one TNLean deprecation warning directly attributable to the 4.32 upgrade
was:

```text
TNLean/Channel/Basic.lean:207:
`map_isSelfAdjoint` has been deprecated: Use `IsSelfAdjoint.map'` instead
```

That warning is upgrade-relevant because the replacement's argument order also
causes the build failure described above.

The style linter also emitted parser diagnostics while examining header text in
`TNLean/Spectral/MPVOverlapTrace.lean` at occurrences of the `ᴴ` notation.
These appeared inside `linter.style.header` output and were not one of the four
required targets reported as failed by Lake.

Because the build terminated at four failed targets, the warning counts are
lower bounds for that run. In particular, the absence of a warning later in the
build log is not evidence that the repository contains no such warning. The
correct triage is therefore:

1. fix the four compilation blockers first;
2. fix the single TNLean 4.32 deprecation together with its compilation repair;
3. keep dependency deprecations separate; and
4. treat the large style/header surface as the existing cleanup backlog, not as
   evidence that Mathlib 4.32 introduced hundreds of semantic regressions.

## Recommended order of work

1. **Repair `IsSelfAdjoint.map'` usage in `TNLean/Channel/Basic.lean`.**
   This is a small, clear API adaptation and unblocks a foundational channel
   module.

2. **Repair the three `Matrix.det_zero` call sites.**
   Install local `Nonempty` instances and use the now-simp theorem without an
   explicit argument. These are mechanical changes.

3. **Repair the two expensive proof shapes in `NewtonGirard`.**
   Prefer explicit `congrArg`/`calc` steps and narrow algebraic rewrites before
   considering heartbeat increases.

4. **Run focused builds of the four previously failing targets.**
   This should precede any replacement cleanup, so upgrade compatibility and
   refactoring are not conflated.

5. **Run the full root build.**
   Only a successful root build after the repairs can establish 4.32 upgrade
   compatibility. This audit does not report such a success.

6. **Apply the direct matrix-CFC cleanup.**
   Remove the `CStarMatrix` transport in `DensityRetract` under
   `Matrix.Norms.L2Operator`, then minimize imports.

7. **Apply the BNT determinant simplification.**
   Replace the injective-to-unit-to-determinant chain by
   `Matrix.exists_mulVec_eq_zero_iff`.

8. **Triage warnings in separate batches.**
   Keep semantic deprecations, dependency warnings, and style/header work in
   distinct changes.

## Verification performed and limitations

The following verification was performed for this audit:

- confirmed the Lean 4.32 and Mathlib 4.32 pins;
- confirmed the exact Mathlib 4.31 and 4.32 commits;
- counted the Mathlib comparison range;
- fetched the Mathlib 4.32 cache successfully;
- inspected the defining source and exact types/modules of:
  `Matrix.instIsometricContinuousFunctionalCalculus`,
  `Matrix.exists_mulVec_eq_zero_iff`,
  `Matrix.nondegenerate_iff_det_ne_zero`, `SelfAdjointDecompose`,
  `IsSelfAdjoint.map'`, and `Matrix.det_zero`;
- inspected the exact 4.31-to-4.32 source change for `Matrix.det_zero`;
- matched the APIs to the TNLean declarations and line ranges listed above;
- ran an initial full `lake build` and retained its log at
  `/tmp/tnlean_mathlib432_build.log`;
- classified the four failed required targets and separated the upgrade-specific
  deprecation from the pre-existing warning backlog.

The initial full build failed. No statement in this document should be read as
claiming that a repaired focused build or repaired full build passed. Proposed
proof adaptations are recommendations for the follow-up upgrade repair and
replacement work.
