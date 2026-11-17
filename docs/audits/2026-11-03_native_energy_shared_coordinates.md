# Shared coordinates in the native regional energy estimate

The two private regional-operator coordinate calculations are removed from
RegionalEnergyEstimate.lean. The existing consumer now calls the explicit
exterior-first conjugation identity in QICLean's new
Entropy/RegionalOperatorCoordinates.lean. Its public theorem statement is
byte-identical, including its original candidate-loss bound; no energy or
generation claim changes. The same generic coordinate proof is now available
for the actual canonical tensor coordinates used by improving families.

Sources, imported objects, root inputs and prebuilt Mathlib hashes were
guarded. No provider or cache was changed and no Mathlib source was compiled.
The manifest records exact source hashes and verification evidence. Ordinary
combined and compiled blueprint checks remain required after adoption.
