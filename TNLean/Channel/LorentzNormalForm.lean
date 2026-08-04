/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.LorentzNormalForm.Basic
import TNLean.Channel.LorentzNormalForm.Infimum
import TNLean.Channel.LorentzNormalForm.NormalForm
import TNLean.Channel.LorentzNormalForm.QubitNormalForm

/-!
# Lorentz normal form for quantum channels (Wolf Section 2.3, Propositions 2.8–2.11)

Thin module assembling the normal-form development for quantum channels under
filtering operations from four focused sub-modules.

* `TNLean.Channel.LorentzNormalForm.Basic` — SL-filtering operations, the
  doubly-stochastic predicates, and the shared Kronecker-conjugation and
  partial-trace identities.
* `TNLean.Channel.LorentzNormalForm.Infimum` — the compactness/minimisation
  argument (Wolf Equation (2.36)): attainment of the infimum and the AM–GM
  optimality lemmas.
* `TNLean.Channel.LorentzNormalForm.NormalForm` — Wolf Proposition 2.9, the
  generic normal form for CP maps with full Kraus rank, in square and
  rectangular forms.
* `TNLean.Channel.LorentzNormalForm.QubitNormalForm` — the Pauli-basis
  predicates for the qubit Lorentz normal form (Wolf Proposition 2.11;
  existence pending).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.3][Wolf2012QChannels]
-/
