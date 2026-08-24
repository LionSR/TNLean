/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.BipartiteLocalAlgebra
import TNLean.QCA.FinitePropagation

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
  rw [commute_iff_eq]
  ext x y
  change (∑ z, localInclusion Finset.subset_union_left A x z *
      localInclusion Finset.subset_union_right B z y) =
    ∑ z, localInclusion Finset.subset_union_right B x z *
      localInclusion Finset.subset_union_left A z y
  simp only [localInclusion_apply]
  simp_rw [Config.splitEquiv_snd_eq_iff_restrict_right hΛΓ,
    Config.splitEquiv_snd_eq_iff_restrict_left hΛΓ]
  let e := Config.disjointUnionEquiv (d := d) hΛΓ
  change (∑ z, (A (e x).1 (e z).1 * if (e x).2 = (e z).2 then 1 else 0) *
      (B (e z).2 (e y).2 * if (e z).1 = (e y).1 then 1 else 0)) =
    ∑ z, (B (e x).2 (e z).2 * if (e x).1 = (e z).1 then 1 else 0) *
      (A (e z).1 (e y).1 * if (e z).2 = (e y).2 then 1 else 0)
  have hleft :
      (∑ z : Config d (Λ ∪ Γ),
        (A (e x).1 (e z).1 * if (e x).2 = (e z).2 then 1 else 0) *
          (B (e z).2 (e y).2 * if (e z).1 = (e y).1 then 1 else 0)) =
        ∑ p : Config d Λ × Config d Γ,
          (A (e x).1 p.1 * if (e x).2 = p.2 then 1 else 0) *
            (B p.2 (e y).2 * if p.1 = (e y).1 then 1 else 0) := by
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  have hright :
      (∑ z : Config d (Λ ∪ Γ),
        (B (e x).2 (e z).2 * if (e x).1 = (e z).1 then 1 else 0) *
          (A (e z).1 (e y).1 * if (e z).2 = (e y).2 then 1 else 0)) =
        ∑ p : Config d Λ × Config d Γ,
          (B (e x).2 p.2 * if (e x).1 = p.1 then 1 else 0) *
            (A p.1 (e y).1 * if p.2 = (e y).2 then 1 else 0) := by
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  calc
    _ = ∑ p : Config d Λ × Config d Γ,
        (A (e x).1 p.1 * if (e x).2 = p.2 then 1 else 0) *
          (B p.2 (e y).2 * if p.1 = (e y).1 then 1 else 0) := hleft
    _ = A (e x).1 (e y).1 * B (e x).2 (e y).2 := by
      rw [Fintype.sum_prod_type]
      simp
    _ = B (e x).2 (e y).2 * A (e x).1 (e y).1 := mul_comm _ _
    _ = ∑ p : Config d Λ × Config d Γ,
        (B (e x).2 p.2 * if (e x).1 = p.1 then 1 else 0) *
          (A p.1 (e y).1 * if p.2 = (e y).2 then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = _ := hright.symm

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
