/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.Subalgebra

/-!
# Computational equivalences of star-subalgebras

These are the star-preserving forms of the existing subalgebra
identifications by an injective homomorphism and by equality. Their
underlying maps are exactly the Mathlib algebra equivalences. They keep
the ambient value of every element explicit when prescribing support
factor coordinates, as in Schumacher–Werner bruleU/bruleV and the
translation of factors in defBBq, quant-ph/0405174, lines 980–1001 and
1199–1226.
-/

namespace StarSubalgebra

variable {R A B : Type*} [CommSemiring R] [StarRing R]
  [Ring A] [Algebra R A] [StarRing A] [StarModule R A]
  [Ring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- The restriction of an injective star-algebra homomorphism identifies
an actual star-subalgebra with its image. This retains the underlying
Mathlib subalgebra equivalence, adding only preservation of star. -/
noncomputable def equivMapOfInjective (S : StarSubalgebra R A)
    (f : A →⋆ₐ[R] B) (hf : Function.Injective f) :
    S ≃⋆ₐ[R] S.map f :=
  StarAlgEquiv.ofAlgEquiv (S.toSubalgebra.equivMapOfInjective f.toAlgHom hf)
    (fun x => Subtype.ext (map_star f (x : A)))

/-- The image equivalence evaluates as the original ambient map. -/
@[simp] theorem equivMapOfInjective_coe (S : StarSubalgebra R A)
    (f : A →⋆ₐ[R] B) (hf : Function.Injective f) (x : S) :
    (S.equivMapOfInjective f hf x : B) = f (x : A) := rfl

/-- Equal star-subalgebras are identified without changing ambient
values, using Mathlib's equality equivalence for their subalgebras. -/
def equivOfEq (S T : StarSubalgebra R A) (h : S = T) : S ≃⋆ₐ[R] T :=
  StarAlgEquiv.ofAlgEquiv
    (S.toSubalgebra.equivOfEq T.toSubalgebra (congrArg StarSubalgebra.toSubalgebra h))
    (fun _ => Subtype.ext rfl)

/-- The equality equivalence leaves every ambient value unchanged. -/
@[simp] theorem equivOfEq_coe (S T : StarSubalgebra R A) (h : S = T) (x : S) :
    (S.equivOfEq T h x : A) = (x : A) := rfl

end StarSubalgebra
