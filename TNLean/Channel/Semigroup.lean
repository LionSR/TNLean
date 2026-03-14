/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic
import TNLean.Channel.Semigroup.Perturbation
import TNLean.Channel.Semigroup.Primitivity

/-!
# Wolf Chapter 7 — Semigroup Structure: Public Theorem Index

This module serves as a **navigational index** that maps the formalized theorems
in this project to the numbering in:

> M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012), Chapter 7.

Each entry lists the Wolf result, its status (fully formalized / partially
formalized / not yet formalized), and the Lean declaration(s) that correspond.

No new proofs are introduced here; this is a documentation-only re-export.

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

**Wolf Proposition 7.1** (continuous semigroup → exponential form) — PARTIALLY FORMALIZED
* Forward direction (`exp(t•L)` is a continuous semigroup): FORMALIZED
  - `expSemigroupCLM_add` — semigroup law
  - `expSemigroupCLM_zero` — initial condition
  - `expSemigroupCLM_continuous` — continuity (SORRY)
  - `expSemigroup_isDynSemigroup` — combined semigroup law
  - `expSemigroup_isContinuousDynSemigroup` — combined (SORRY via continuous)
* Derivative (Wolf Eq. 7.2):
  - `hasDerivAt_expSemigroupCLM` — `d/dt exp(t•L) = exp(t•L) * L` (SORRY)
  - `hasDerivAt_expSemigroupCLM_zero` — at t=0, derivative is L
* Reverse direction (any continuous semigroup = exp(tL)):
  - `continuousDynSemigroup_eq_exp` — Prop 7.1 (SORRY)
  - `generator_unique` — uniqueness of generator (SORRY)

### Wolf Lemma 7.1 (Duhamel/perturbation formula) — SORRY
* `duhamel_formula` — `TNLean.Channel.Semigroup.Perturbation`

### Wolf Corollary 7.1 (perturbation bound) — SORRY
* `perturbation_bound` — `TNLean.Channel.Semigroup.Perturbation`
* `perturbation_bound_unit_norm` — simplified version for channels

---

## §7.1.2 Quantum dynamical semigroups

### Wolf Proposition 7.5 (irreducibility implies primitivity for QDS)
— SORRY (structure and statement formalized)

* `IsQuantumDynSemigroup` — quantum dynamical semigroup definition
  — `TNLean.Channel.Semigroup.Primitivity`
* `irreducible_semigroup_implies_primitive` — 1→3 direction
  — `TNLean.Channel.Semigroup.Primitivity`
* `qds_irreducible_iff_primitive` — full 1↔3 equivalence
  — `TNLean.Channel.Semigroup.Primitivity`

---

## Not yet formalized

* Wolf Proposition 7.2 (conditional complete positivity)
* Wolf Proposition 7.3 (CP dynamical semigroups)
* Wolf Proposition 7.4 (freedom in generator representation)
* Wolf Theorem 7.1 (GKSL/Lindblad generator)
* Wolf Proposition 7.6 (reducible QDS)
* Wolf Corollary 7.2 (necessary conditions for relaxation)
* Wolf Theorem 7.2 (kernel of Liouvillian)

These results depend on the Choi-Jamiolkowski isomorphism (Ch2) and
GKSL/Lindblad theory, which are being formalized separately.
-/
