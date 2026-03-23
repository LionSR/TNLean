/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic
import TNLean.Channel.Semigroup.Perturbation
import TNLean.Channel.Semigroup.Resolvent
import TNLean.Channel.Semigroup.Primitivity
import TNLean.Channel.Semigroup.GeneratorDefs
import TNLean.Channel.Semigroup.LindbladForm
import TNLean.Channel.Semigroup.KossakowskiForm
import TNLean.Channel.Semigroup.ReducibleQDS

/-!
# Wolf Chapter 7 — Semigroup Structure: Public Theorem Index

This module serves as a **navigational index** that maps the formalized theorems
in this project to the numbering in:

> M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012), Chapter 7.

Each entry lists the Wolf result, its status (fully formalized / partially
formalized / not yet formalized), and the Lean declaration(s) that correspond.

No new proofs are introduced here; this is a documentation-only index module.

---

## §7.1 Continuous one-parameter semigroups

### §7.1.1 Dynamical semigroups

**Definitions:**
* `IsDynSemigroup` — dynamical semigroup (Wolf Eq. 7.1)
  — `TNLean.Channel.Semigroup.Basic`
* `IsContinuousDynSemigroup` — norm-continuous dynamical semigroup
  — `TNLean.Channel.Semigroup.Basic`
* `expSemigroupCLM` / `expSemigroup` — the exponential semigroup `exp(t•L)`
  — `TNLean.Channel.Semigroup.Basic`

**Wolf Proposition 7.1** (continuous semigroup → exponential form) — FORMALIZED ✓
* Forward direction (`exp(t•L)` is a continuous semigroup): FORMALIZED
  - `expSemigroupCLM_add` — semigroup law
  - `expSemigroupCLM_zero` — initial condition
  - `expSemigroupCLM_continuous` — continuity
  - `expSemigroup_isDynSemigroup` — combined semigroup law
  - `expSemigroup_isContinuousDynSemigroup` — combined
* Derivative (Wolf Eq. 7.2):
  - `hasDerivAt_expSemigroupCLM` — `d/dt exp(t•L) = exp(t•L) * L`
  - `hasDerivAt_expSemigroupCLM_zero` — at t=0, derivative is L
* Reverse direction (any continuous semigroup = exp(tL)):
  - `continuousDynSemigroup_eq_exp` — Prop 7.1
  - `generator_unique` — uniqueness of generator

### Wolf Lemma 7.1 (Duhamel/perturbation formula) — FORMALIZED ✓
* `duhamel_formula` — `TNLean.Channel.Semigroup.Perturbation`
  Proof: FTC via `intervalIntegral.integral_eq_sub_of_hasDerivAt` on the
  CLM-valued function `s ↦ exp((t-s)L) * exp(sL')` with derivative
  `exp((t-s)L) * (L'-L) * exp(sL')`.

### Wolf Corollary 7.1 (perturbation bound) — FORMALIZED ✓
* `perturbation_bound` — `TNLean.Channel.Semigroup.Perturbation`
* `perturbation_bound_unit_norm` — simplified version for channels

---

## §7.1.2 Quantum dynamical semigroups

### Wolf Proposition 7.5 (irreducibility implies primitivity for QDS)
— PARTIALLY FORMALIZED (helper lemmas complete; main theorem has 2 infrastructure gaps)

* `IsQuantumDynSemigroup` — quantum dynamical semigroup definition
  — `TNLean.Channel.Semigroup.Primitivity`
* `irreducible_semigroup_implies_primitive` — 1→3 direction
  — `TNLean.Channel.Semigroup.Primitivity`
* `qds_irreducible_iff_primitive` — full 1↔3 equivalence
  — `TNLean.Channel.Semigroup.Primitivity`

---

## §7.1.2 GKSL/Lindblad Generator Theory

### Definitions
* `GeneratorDecomp` — (φ, κ) decomposition L(ρ) = φ(ρ) - κρ - ρκ†
  — `TNLean.Channel.Semigroup.GeneratorDefs`
* `IsCCP` — conditionally completely positive map
  — `TNLean.Channel.Semigroup.GeneratorDefs`
* `IsTraceAnnihilating` — tr(L(ρ)) = 0 for all ρ
  — `TNLean.Channel.Semigroup.GeneratorDefs`
* `LindbladForm` — standard Lindblad form with Hamiltonian and Lindblad operators
  — `TNLean.Channel.Semigroup.LindbladForm`
* `KossakowskiForm` — Kossakowski matrix form
  — `TNLean.Channel.Semigroup.KossakowskiForm`
* `IsGKSLGenerator` — generates a CPTP semigroup
  — `TNLean.Channel.Semigroup.LindbladForm`

**Wolf Proposition 7.2** (conditional complete positivity) — PARTIALLY FORMALIZED
* `GeneratorDecomp.isCCP` — CCP definition via (φ,κ) form ✅
* `ccp_implies_choi_projected_posSemidef` — 1→2 direction: STUB
* `choi_projected_posSemidef_implies_ccp` — 2→1 direction: SORRY

**Wolf Proposition 7.3** (CP semigroup ↔ CCP generator) — SORRY
* `cp_semigroup_iff_ccp_generator` — equivalence statement: FORMALIZED
* `cp_semigroup_implies_ccp_generator` — forward direction: SORRY
* `ccp_generator_implies_cp_semigroup` — reverse direction (Lie-Trotter): SORRY

**Wolf Proposition 7.4** (freedom in generator representation) — FORMALIZED ✅
* `generator_shift_invariance` — shift invariance: FORMALIZED ✅
* `exists_traceless_kraus_shift` — traceless Kraus operators exist: FORMALIZED ✅

**Wolf Theorem 7.1** (GKSL/Lindblad generator) — PARTIALLY FORMALIZED
* `LindbladForm.isTraceAnnihilating` — Lindblad form is trace-annihilating ✅
* `GeneratorDecomp.traceAnnihilating_of_traceConstraint` — φ*(1)=κ+κ† ⟹ TA ✅
* `LindbladForm.toLinearMap_eq_generatorDecomp` — Lindblad = (φ,κ) form ✅
* `gksl_iff_lindbladForm` — GKSL ↔ Lindblad form (modulo Prop 7.3 sorry inputs) ✅
* `gksl_iff_ccp_and_traceAnnihilating` — GKSL ↔ CCP + TA (modulo Prop 7.3) ✅
* `kossakowski_iff_lindblad` — Kossakowski ↔ Lindblad form: FORMALIZED ✅
* `isTracePreservingMap_expSemigroup_of_isTraceAnnihilating` — TA → TP semigroup ✅
* `isTraceAnnihilating_of_isTracePreservingMap_semigroup` — TP semigroup → TA ✅

---

### Wolf Proposition 7.6 (reducible QDS) — PARTIALLY FORMALIZED

* `IsReducibleQDS` — reducible QDS definition
  — `TNLean.Channel.Semigroup.ReducibleQDS`
* `HasRankDeficientFixedDensity` — condition (1): rank-deficient fixed density
* `HasRankDeficientKernelElement` — condition (2): rank-deficient kernel element
* `HasInvariantCompression` — condition (3): invariant compression
* `HasBlockUpperTriangularLindblad` — condition (4): block-upper-triangular Lindblad
* `wolf_prop_7_6_one_iff_two` — (1) ↔ (2): FORMALIZED ✅
* `generatorPreservesCompression_of_semigroupPreservesCompression` — semigroup→generator: FORMALIZED ✅
* `sum_conjTranspose_mul_self_eq_zero_imp` — sum-of-squares vanishing: FORMALIZED ✅
* `wolf_prop_7_6_four_implies_three` — (4) → (3): partially formalized (reduces to two sorry lemmas)
* `wolf_prop_7_6_three_implies_four` — (3) → (4): SORRY

---

## Not yet formalized

* Wolf Corollary 7.2 (necessary conditions for relaxation)
* Wolf Theorem 7.2 (kernel of Liouvillian)
-/
