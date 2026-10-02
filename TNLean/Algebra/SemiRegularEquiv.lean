/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationDelta
import Mathlib.RepresentationTheory.Intertwining

/-!
# Semi-regularity under equivalence of representations

An equivalence of representations preserves the occurrence of every irreducible
representation: composition with the equivalence sends nonzero intertwining maps
to nonzero intertwining maps. Thus semi-regularity does not depend on coordinates.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 4.5,
`Papers/1001.3807/paper_v3.tex`, lines 1010–1013. This is the equivalence principle
for the occurrence condition in that definition.
-/

namespace Representation

variable {G V W : Type*} [Group G]
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An equivalence preserves every irreducible occurrence, hence semi-regularity.
Source: SCP10, Definition 4.5, lines 1010–1013. -/
theorem IsSemiRegular.of_equiv (hρ : ρ.IsSemiRegular) (e : ρ.Equiv σ) :
    σ.IsSemiRegular := by
  intro E _ _ _ τ hτ
  obtain ⟨f, hf⟩ := hρ E τ hτ
  refine ⟨e.toIntertwiningMap.comp f, ?_⟩
  intro hzero
  apply hf
  ext x
  change f x = 0
  apply e.toLinearEquiv.injective
  change e (f x) = e 0
  have hx := congrArg (fun k : IntertwiningMap τ σ => k x) hzero
  simpa using hx

/-- Equivalent representations are semi-regular simultaneously.
Source: SCP10, Definition 4.5, lines 1010–1013. -/
theorem Equiv.isSemiRegular_iff (e : ρ.Equiv σ) :
    ρ.IsSemiRegular ↔ σ.IsSemiRegular :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

end Representation
