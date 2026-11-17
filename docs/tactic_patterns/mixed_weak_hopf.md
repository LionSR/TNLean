# Extending mixed-path identities to the endpoints

The integral-average formula and local commutation in
`MPS/Symmetry/MPOSymmetry/MixedWeakHopfAverage.lean` hold first on `(0,1)`.
Both sides are continuous, so `Set.EqOn.closure` and `closure_Ioo` extend
them to `[0,1]`. Use this existing Mathlib theorem instead of separately
constructing a closed equalizer and applying `closure_minimal` each time.

The older parent-commutation module has the same pattern but is owned by
concurrent issue #10763; it is intentionally unchanged. No custom tactic or
new generic topological lemma is needed. The scoped tactic-pattern scan
reported only existing repetitions outside the new modules.
