/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.LocalAlgebra.BipartiteLocalAlgebra
import TNLean.QCA.QuasiLocal.QuasiLocal

/-!
# Commutation of observables with disjoint finite supports

Observables on disjoint finite regions commute after embedding into a common local algebra. The
same conclusion holds in the algebraic local algebra and in its quasi-local completion.

This is local tensor-factor infrastructure used by the QCA appendix, rather than a separately
named result of the source.

## Main results

* `SpinChain.localInclusion_commute_of_disjoint` — disjoint finite-region observables commute in
  the algebra on their union.
* `SpinChain.localObservable_commute_of_disjoint` — their algebraic-local images commute.
* `SpinChain.SupportedIn.commute_of_disjoint` — algebraic observables with disjoint supports
  commute.
* `SpinChain.quasiLocalObservable_commute_of_disjoint` — their quasi-local images commute.
* `SpinChain.QuasiLocalSupportedIn.commute_of_disjoint` — quasi-local observables with disjoint
  finite supports commute.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2300.
-/

namespace SpinChain

section Local

variable {d : ℕ} {Λ Γ : Finset ℤ}

/-- Finite-region observables supported on disjoint regions commute after inclusion into the
algebra on their union.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem localInclusion_commute_of_disjoint (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d Λ) (B : LocalAlgebra d Γ) :
    Commute (localInclusion (d := d) Finset.subset_union_left A)
      (localInclusion Finset.subset_union_right B) := by
  have hA := ManyBody.subregionPlace_mem_supportedOperators (X := fun _ : ℤ ↦ Fin d)
    (Finset.subset_union_left : Λ ⊆ Λ ∪ Γ) A
  have hB := ManyBody.subregionPlace_mem_supportedOperators (X := fun _ : ℤ ↦ Fin d)
    (Finset.subset_union_right : Γ ⊆ Λ ∪ Γ) B
  exact ManyBody.commute_of_mem_supportedOperators_of_disjoint hA hB
    (Finset.disjoint_left.mpr fun _ hwΛ hwΓ ↦
      Finset.disjoint_left.mp hΛΓ (Finset.mem_subtype.mp hwΛ) (Finset.mem_subtype.mp hwΓ))

/-- Canonical algebraic-local observables from disjoint regions commute.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem localObservable_commute_of_disjoint (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d Λ) (B : LocalAlgebra d Γ) :
    Commute (localObservable d Λ A) (localObservable d Γ B) := by
  rw [commute_iff_eq, ← localObservable_localInclusion d Finset.subset_union_left A,
    ← localObservable_localInclusion d Finset.subset_union_right B,
    ← map_mul, (localInclusion_commute_of_disjoint hΛΓ A B).eq, map_mul]

/-- Algebraic local observables with disjoint finite supports commute.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem SupportedIn.commute_of_disjoint {X Y : AlgebraicLocalAlgebra d}
    (hX : SupportedIn X Λ) (hY : SupportedIn Y Γ) (hΛΓ : Disjoint Λ Γ) :
    Commute X Y := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  exact localObservable_commute_of_disjoint hΛΓ A B

/-- Canonical quasi-local observables from disjoint regions commute.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem quasiLocalObservable_commute_of_disjoint [NeZero d] (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d Λ) (B : LocalAlgebra d Γ) :
    Commute (quasiLocalObservable d Λ A) (quasiLocalObservable d Γ B) := by
  rw [commute_iff_eq]
  change algebraicToQuasiLocal d (localObservable d Λ A) *
      algebraicToQuasiLocal d (localObservable d Γ B) =
    algebraicToQuasiLocal d (localObservable d Γ B) *
      algebraicToQuasiLocal d (localObservable d Λ A)
  rw [← map_mul, (localObservable_commute_of_disjoint hΛΓ A B).eq, map_mul]

/-- Quasi-local observables with disjoint finite supports commute.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem QuasiLocalSupportedIn.commute_of_disjoint [NeZero d]
    {X Y : QuasiLocalAlgebra d} (hX : QuasiLocalSupportedIn X Λ)
    (hY : QuasiLocalSupportedIn Y Γ) (hΛΓ : Disjoint Λ Γ) :
    Commute X Y := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  exact quasiLocalObservable_commute_of_disjoint hΛΓ A B

end Local

end SpinChain
