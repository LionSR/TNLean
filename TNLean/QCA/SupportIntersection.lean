/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.SingletonGeneration
import TNLean.QCA.QuasiLocalCommutant

/-!
# Intersection of finite supports

An observable supported on two finite regions is supported on their
intersection. The existing outside-commutant characterization and finite
one-site generation prove this directly, without another tensor-factor
presentation or another support predicate.

Source context: Schumacher–Werner, quant-ph/0405174, local observable
algebras and commutation on disjoint regions; arXiv:1703.09188,
Appendix lines 2285–2306.
-/

namespace SpinChain

/-- Finite support is preserved by intersection. Source context:
arXiv:1703.09188, Appendix, lines 2285–2306. -/
theorem QuasiLocalSupportedIn.inter {d : ℕ} [NeZero d]
    {X : QuasiLocalAlgebra d} {Λ Γ : Finset ℤ}
    (hΛ : QuasiLocalSupportedIn X Λ) (hΓ : QuasiLocalSupportedIn X Γ) :
    QuasiLocalSupportedIn X (Λ ∩ Γ) := by
  classical
  rw [quasiLocalSupportedIn_iff_commute_disjoint]
  intro Δ hΔ Y hY
  obtain ⟨B, rfl⟩ := hY
  change Commute X (algebraicToQuasiLocal d (localObservable d Δ B))
  apply commute_map_localObservable_of_singletons (algebraicToQuasiLocal d) Δ X ?_ B
  intro x hx C
  have hout : x ∉ Λ ∨ x ∉ Γ := by
    by_contra h
    push_neg at h
    exact Finset.disjoint_left.mp hΔ hx (Finset.mem_inter.mpr h)
  rcases hout with hxΛ | hxΓ
  · have hdisjoint : Disjoint ({x} : Finset ℤ) Λ := by simpa using hxΛ
    have h := (quasiLocalSupportedIn_iff_commute_disjoint X Λ).mp hΛ
      {x} hdisjoint (quasiLocalObservable d {x} C) ⟨C, rfl⟩
    exact h
  · have hdisjoint : Disjoint ({x} : Finset ℤ) Γ := by simpa using hxΓ
    have h := (quasiLocalSupportedIn_iff_commute_disjoint X Γ).mp hΓ
      {x} hdisjoint (quasiLocalObservable d {x} C) ⟨C, rfl⟩
    exact h

end SpinChain
