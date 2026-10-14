/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Logic.Equiv.Basic

/-!
# Physical configurations with one carrying party at each site

Suppose each site has a designated party whose physical coordinate reads that
site bijectively. Every remaining party has a subsingleton physical coordinate
alphabet. Reading configurations at the assigned sites is then a bijection on
the full configuration spaces. The site assignment itself need not be
injective, and no scalar local tensor is discarded or required to equal one.

This auxiliary implication isolates the coordinate identification needed for
physical outputs at unit parties in the polynomial-PEPS manuscript,
`07-assembly.tex`, lines 26–27 and `eq:protocol-density`, revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The actual protocol must supply the stated ownership and coordinate properties.
-/

namespace TNLean.PEPS.Approximation

/-- Complete physical configurations are read bijectively when every site has
one designated carrying party and every other party's physical coordinate
alphabet is subsingleton. The coordinate readout of each designated party is
bijective. This does not constrain the scalar factors in other parties' tensors.
Auxiliary to polynomial-PEPS `07-assembly.tex`, lines 26–27 and
`eq:protocol-density`. -/
theorem bijective_party_configuration_map
    {Party Site A : Type*} {Out : Party → Type*}
    (site : Party → Site) (owner : Site → Party)
    (howner : Function.LeftInverse site owner)
    (out : (p : Party) → A → Out p)
    (hout : ∀ v, Function.Bijective (out (owner v)))
    (hdormant : ∀ p, p ∉ Set.range owner → Subsingleton (Out p)) :
    Function.Bijective (fun x : Site → A ↦ fun p ↦ out p (x (site p))) := by
  classical
  constructor
  · intro x y h
    funext v
    apply (hout v).injective
    have hentry := congrFun h (owner v)
    simpa only [howner v] using hentry
  · intro y
    let x : Site → A := fun v ↦
      (Equiv.ofBijective (out (owner v)) (hout v)).symm (y (owner v))
    refine ⟨x, ?_⟩
    funext p
    by_cases hp : p ∈ Set.range owner
    · obtain ⟨v, rfl⟩ := hp
      simpa only [howner v, x, Equiv.coe_ofBijective] using
        (Equiv.ofBijective (out (owner v)) (hout v)).apply_symm_apply (y (owner v))
    · letI := hdormant p hp
      exact Subsingleton.elim _ _

end TNLean.PEPS.Approximation
