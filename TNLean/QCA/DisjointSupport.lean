/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.FinitePropagation

/-!
# Commutation of observables with disjoint finite supports

Observables on disjoint finite regions commute after embedding into a common local algebra. The
same conclusion holds in the algebraic local algebra and in its quasi-local completion.

This is local tensor-factor infrastructure used by the QCA appendix, rather than a separately
named result of the source.

## Main results

* `SpinChain.localInclusion_mul_comm_of_disjoint` — disjoint finite-region observables commute in
  the algebra on their union.
* `SpinChain.localObservable_mul_comm_of_disjoint` — their algebraic-local images commute.
* `SpinChain.SupportedIn.mul_comm_of_disjoint` — algebraic observables with disjoint supports
  commute.
* `SpinChain.quasiLocalObservable_mul_comm_of_disjoint` — their quasi-local images commute.
* `SpinChain.QuasiLocalSupportedIn.mul_comm_of_disjoint` — quasi-local observables with disjoint
  finite supports commute.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2300.
-/

namespace SpinChain

namespace Config

/-- A configuration on a disjoint union is determined by its restrictions to both regions.

This is elementary finite tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
private lemma eq_of_restrict_eq_restrict {d : ℕ} {Λ Γ : Finset ℤ}
    {x y : Config d (Λ ∪ Γ)}
    (hΛ : restrict Finset.subset_union_left x = restrict Finset.subset_union_left y)
    (hΓ : restrict Finset.subset_union_right x = restrict Finset.subset_union_right y) :
    x = y := by
  funext i
  rcases Finset.mem_union.mp i.2 with hiΛ | hiΓ
  · exact congrFun hΛ ⟨i, hiΛ⟩
  · exact congrFun hΓ ⟨i, hiΓ⟩

/-- Splitting configurations on a union of disjoint regions into the two restrictions. -/
private def disjointUnionEquiv {d : ℕ} {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) :
    Config d (Λ ∪ Γ) ≃ Config d Λ × Config d Γ where
  toFun x := (restrict Finset.subset_union_left x, restrict Finset.subset_union_right x)
  invFun x i := if hiΛ : (i : ℤ) ∈ Λ then x.1 ⟨i, hiΛ⟩ else
    x.2 ⟨i, (Finset.mem_union.mp i.2).resolve_left hiΛ⟩
  left_inv x := by
    apply eq_of_restrict_eq_restrict
    · funext i
      simp [restrict]
    · funext i
      simp [restrict, hΛΓ.notMem_of_mem_right_finset i.2]
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [restrict]
    · funext i
      simp [restrict, hΛΓ.notMem_of_mem_right_finset i.2]

private lemma splitEquiv_snd_eq_iff_restrict_right {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x y : Config d (Λ ∪ Γ)) :
    (splitEquiv Finset.subset_union_left x).2 =
        (splitEquiv Finset.subset_union_left y).2 ↔
      restrict Finset.subset_union_right x = restrict Finset.subset_union_right y := by
  constructor
  · intro h
    funext i
    exact congrFun h ⟨i, Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right Λ i.2, hΛΓ.notMem_of_mem_right_finset i.2⟩⟩
  · intro h
    funext i
    have hiΓ : (i : ℤ) ∈ Γ :=
      (Finset.mem_union.mp (Finset.mem_sdiff.mp i.2).1).resolve_left
        (Finset.mem_sdiff.mp i.2).2
    exact congrFun h ⟨i, hiΓ⟩

private lemma splitEquiv_snd_eq_iff_restrict_left {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x y : Config d (Λ ∪ Γ)) :
    (splitEquiv Finset.subset_union_right x).2 =
        (splitEquiv Finset.subset_union_right y).2 ↔
      restrict Finset.subset_union_left x = restrict Finset.subset_union_left y := by
  constructor
  · intro h
    funext i
    exact congrFun h ⟨i, Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_left Γ i.2, hΛΓ.notMem_of_mem_left_finset i.2⟩⟩
  · intro h
    funext i
    have hiΛ : (i : ℤ) ∈ Λ :=
      (Finset.mem_union.mp (Finset.mem_sdiff.mp i.2).1).resolve_right
        (Finset.mem_sdiff.mp i.2).2
    exact congrFun h ⟨i, hiΛ⟩

end Config

section Local

variable {d : ℕ} {Λ Γ : Finset ℤ}

/-- Finite-region observables supported on disjoint regions commute after inclusion into the
algebra on their union.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem localInclusion_mul_comm_of_disjoint (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d Λ) (B : LocalAlgebra d Γ) :
    localInclusion (d := d) Finset.subset_union_left A *
        localInclusion Finset.subset_union_right B =
      localInclusion Finset.subset_union_right B *
        localInclusion Finset.subset_union_left A := by
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
theorem localObservable_mul_comm_of_disjoint (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d Λ) (B : LocalAlgebra d Γ) :
    localObservable d Λ A * localObservable d Γ B =
      localObservable d Γ B * localObservable d Λ A := by
  rw [← localObservable_localInclusion d Finset.subset_union_left A,
    ← localObservable_localInclusion d Finset.subset_union_right B,
    ← map_mul, localInclusion_mul_comm_of_disjoint hΛΓ, map_mul]

/-- Algebraic local observables with disjoint finite supports commute.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem SupportedIn.mul_comm_of_disjoint {X Y : AlgebraicLocalAlgebra d}
    (hX : SupportedIn X Λ) (hY : SupportedIn Y Γ) (hΛΓ : Disjoint Λ Γ) :
    X * Y = Y * X := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  exact localObservable_mul_comm_of_disjoint hΛΓ A B

/-- Canonical quasi-local observables from disjoint regions commute.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem quasiLocalObservable_mul_comm_of_disjoint [NeZero d] (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d Λ) (B : LocalAlgebra d Γ) :
    quasiLocalObservable d Λ A * quasiLocalObservable d Γ B =
      quasiLocalObservable d Γ B * quasiLocalObservable d Λ A := by
  change algebraicToQuasiLocal d (localObservable d Λ A) *
      algebraicToQuasiLocal d (localObservable d Γ B) =
    algebraicToQuasiLocal d (localObservable d Γ B) *
      algebraicToQuasiLocal d (localObservable d Λ A)
  rw [← map_mul, localObservable_mul_comm_of_disjoint hΛΓ, map_mul]

/-- Quasi-local observables with disjoint finite supports commute.

This is elementary tensor-factor infrastructure underlying arXiv:1703.09188, Appendix,
lines 2292--2300. -/
theorem QuasiLocalSupportedIn.mul_comm_of_disjoint [NeZero d]
    {X Y : QuasiLocalAlgebra d} (hX : QuasiLocalSupportedIn X Λ)
    (hY : QuasiLocalSupportedIn Y Γ) (hΛΓ : Disjoint Λ Γ) :
    X * Y = Y * X := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, rfl⟩ := hY
  exact quasiLocalObservable_mul_comm_of_disjoint hΛΓ A B

end Local

end SpinChain
