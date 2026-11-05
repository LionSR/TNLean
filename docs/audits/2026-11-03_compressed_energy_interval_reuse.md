# Reuse of the compressed-energy interval

The original regional-energy theorem and the soft word-energy theorem now
use the single QIC variational interval lemma. Their public signatures are
byte-identical to the checked source at revision
`38e847070a43b508cc3d01362efd7ced8cd8314f`. The actual orthogonal
compressions, ordered eigenvalues, trial vectors and energy shifts are
unchanged.

Both changed sources and their seven actual downstream consumers passed
private strict checks against that fully built TN revision and its own QIC
revision `4743a375465299fef1e1f536d22342fa1f745374`, with the new QIC helper
as an explicit fresh object. The final canonical-energy theorem passed in
19.808 seconds. The complete selected importer graph was re-elaborated;
unchanged consumers were not loaded from objects built before the changed
dependency. Imported inspection of both changed declarations reported only
`propext`, `Classical.choice` and `Quot.sound` (6.519 seconds).

The tactic ledger records the shared variational statement. These private
checks supplement the next combined ordinary gates. No provider, dependency
pin or cache was changed, and no Mathlib source was compiled.
