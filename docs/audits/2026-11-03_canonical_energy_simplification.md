# Energy and Ritz corollary: compilation simplification

In particular, the physical family is selected once, the energy function is
chosen once for each successful seed before the vector-wise conclusions, and
the same canonical root, literal refinement and actual Ritz space are
retained. The existing green canonical approximation theorem is unchanged.

The proof now separates the calibrated-word energy argument into
`ALVV/CalibratedRootEnergy.lean`. Its lemma identifies the prescribed ground
energy with the actual spectral minimum, proves the needed count bound,
and applies the existing root energy-assignment theorem to the same
targets and operator words. It has no arbitrary terminal proposition as an
argument. The final corollary retains its energy function together with the
unchanged refinement and Ritz conclusions. No mathematical assumption,
resource limit, dependency revision or proof option was changed.
