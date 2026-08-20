/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausIterateChoi
import TNLean.Kraus.Wielandt.Primitivity.StronglyIrreducibleToFullWordSpan

/-!
# Wolf's primitive-channel criterion

For a trace-preserving finite Kraus family, irreducibility together with
primitivity implies eventual full word span. Equivalently, the Choi matrices of
all sufficiently large powers of its Kraus map are positive definite. These are
the implications from item 1 to items 3 and 4 of Wolf, Theorem 6.8, with
irreducibility explicit because the project predicate `IsPrimitive` only
controls the peripheral spectrum.
-/

open scoped Matrix ComplexOrder

namespace Kraus

variable {r D : ℕ}

/-- Wolf, Theorem 6.8, item 1 implies item 3: a trace-preserving finite Kraus
family whose map is irreducible and primitive has eventually full word span. -/
theorem hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive
    [NeZero D] (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (hTP : IsTP K)
    (hIrr : IsIrreducibleMap (mapLM K))
    (hPrim : IsPrimitive (mapLM K)) :
    HasEventuallyFullWordSpan K :=
  Kraus.hasEventuallyFullWordSpan_of_isPrimitive_irreducible
    K hTP hIrr hPrim

/-- Wolf, Theorem 6.8, item 1 implies item 4: under trace preservation,
irreducibility and primitivity force the Choi matrices of all sufficiently
large Kraus-map powers to be positive definite. -/
theorem eventually_choiMatrix_mapLM_pow_posDef_of_isIrreducibleMap_of_isPrimitive
    [NeZero D] (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (hTP : IsTP K)
    (hIrr : IsIrreducibleMap (mapLM K))
    (hPrim : IsPrimitive (mapLM K)) :
    ∀ᶠ m : ℕ in Filter.atTop,
      (ChoiJamiolkowski.choiMatrix ((mapLM K) ^ m)).PosDef :=
  (eventually_choiMatrix_mapLM_pow_posDef_iff_hasEventuallyFullWordSpan K).2
    (hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive K hTP hIrr hPrim)

end Kraus
