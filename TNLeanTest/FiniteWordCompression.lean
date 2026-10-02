import TNLean.MPS.FundamentalTheorem.Reduction.FiniteWordCompression

/-!
# Signature and axiom checks for finite word compression

The examples below ensure that the alphabet size is independent of the target
bond dimension. The guarded axiom reports exclude nonstandard axioms from the
main public statements.
-/

open scoped Matrix

namespace Kraus

variable {n d D : ℕ}
variable (A : MPSTensor n d) (B : MPSTensor n D)

example (hD : d ≤ D) :
    HasWordCompressionUpTo A B (D - d + 1) ↔ HasInvariantSubquotient A B :=
  finiteWordCompression_iff_hasInvariantSubquotient (A := A) (B := B) hD

/-- Regression: alphabet size `4`, target bond dimension `2`, and source bond dimension `3`
are genuinely independent. -/
example (A : MPSTensor 4 2) (B : MPSTensor 4 3) :
    HasWordCompressionUpTo A B (3 - 2 + 1) ↔ HasInvariantSubquotient A B :=
  finiteWordCompression_iff_hasInvariantSubquotient (A := A) (B := B) (by decide)

example (A : MPSTensor 4 2) (B : MPSTensor 4 3)
    (V : Matrix (Fin 3) (Fin 2) ℂ) (W : Matrix (Fin 2) (Fin 3) ℂ)
    (h : WordCompressionUpTo A B V W (3 - 2 + 1)) :
    AllWordCompression A B V W :=
  allWordCompression_of_finiteWordCompression (A := A) (B := B) (V := V) (W := W)
    (by decide) h

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'Kraus.allWordCompression_of_finiteWordCompression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kraus.allWordCompression_of_finiteWordCompression

/-- info: 'Kraus.invariantSubquotient_of_finiteWordCompression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kraus.invariantSubquotient_of_finiteWordCompression

/-- info: 'Kraus.exists_allWordCompression_of_hasInvariantSubquotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kraus.exists_allWordCompression_of_hasInvariantSubquotient

/-- info: 'Kraus.finiteWordCompression_iff_hasInvariantSubquotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kraus.finiteWordCompression_iff_hasInvariantSubquotient

end AxiomChecks

end Kraus
