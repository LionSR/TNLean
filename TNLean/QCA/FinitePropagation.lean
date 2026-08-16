/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.QuasiLocal
import TNLean.QCA.RegionSumset

/-!
# Finite propagation on the quasi-local algebra

A quasi-local observable is supported in a finite region when it lies in the range of that
region's canonical embedding. A quasi-local star-automorphism propagates within a finite
neighborhood when it sends every observable supported in \(\Lambda\) to one supported in
\(\Lambda + \mathcal N\), uniformly over finite regions \(\Lambda\).

This file records equivalent support, range-inclusion, and finite-region witness formulations of
that condition, together with neighborhood monotonicity and forward-composition closure.

## Main definitions

* `SpinChain.QuasiLocalSupportedIn` — membership in a finite-region observable algebra.
* `SpinChain.PropagatesWithin` — propagation bounded by a fixed finite neighborhood.
* `SpinChain.HasFinitePropagation` — existence of a finite propagation neighborhood.

## Main results

* `SpinChain.QuasiLocalSupportedIn.quasiLocalObservable` — every embedded finite-region
  observable is supported in its region.
* `SpinChain.QuasiLocalSupportedIn.mono` — support is monotone under region enlargement.
* `SpinChain.propagatesWithin_iff_quasiLocalObservable` — the universal pointwise formulation.
* `SpinChain.propagatesWithin_iff_range_subset` — the range-inclusion formulation.
* `SpinChain.propagatesWithin_iff_exists_local` — the finite-region witness formulation.
* `SpinChain.PropagatesWithin.mono` — propagation is monotone under neighborhood enlargement.
* `SpinChain.PropagatesWithin.trans` — forward propagation bounds compose by region sumset.
* `SpinChain.HasFinitePropagation.exists_superset` — valid neighborhoods can contain any finite set.
* `SpinChain.HasFinitePropagation.trans` — finite forward propagation is closed under composition.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, line 2298.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

namespace SpinChain

/-- A quasi-local observable is supported in the finite region \(\Lambda\) when it belongs to the
range of the canonical map from \(\mathcal A_\Lambda\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
def QuasiLocalSupportedIn {d : ℕ} [NeZero d] (x : QuasiLocalAlgebra d)
    (Λ : Finset ℤ) : Prop :=
  x ∈ Set.range (quasiLocalObservable d Λ)

namespace QuasiLocalSupportedIn

variable {d : ℕ} [NeZero d] {x : QuasiLocalAlgebra d} {Λ Γ : Finset ℤ}

/-- Every finite-region observable, embedded in the quasi-local algebra, is supported in its
region.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma quasiLocalObservable (A : LocalAlgebra d Λ) :
    QuasiLocalSupportedIn (SpinChain.quasiLocalObservable d Λ A) Λ :=
  ⟨A, rfl⟩

/-- A quasi-local observable is supported in a region exactly when it has a representative in
that region's finite observable algebra.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma iff_exists :
    QuasiLocalSupportedIn x Λ ↔
      ∃ A : LocalAlgebra d Λ, SpinChain.quasiLocalObservable d Λ A = x :=
  Iff.rfl

/-- Quasi-local support is monotone under enlargement of the finite region.

Source: arXiv:1703.09188, Appendix, lines 2292--2298. -/
lemma mono (hx : QuasiLocalSupportedIn x Λ) (hΛΓ : Λ ⊆ Γ) :
    QuasiLocalSupportedIn x Γ := by
  obtain ⟨A, rfl⟩ := hx
  exact ⟨localInclusion hΛΓ A, quasiLocalObservable_localInclusion d hΛΓ A⟩

end QuasiLocalSupportedIn

/-- A quasi-local star-automorphism propagates within the finite neighborhood \(\mathcal N\) when
it sends observables supported in every finite region \(\Lambda\) to observables supported in
\(\Lambda + \mathcal N\).

Source: arXiv:1703.09188, Appendix, line 2298. -/
def PropagatesWithin {d : ℕ} [NeZero d]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) (𝓝 : Finset ℤ) : Prop :=
  ∀ (Λ : Finset ℤ) (x : QuasiLocalAlgebra d), QuasiLocalSupportedIn x Λ →
    QuasiLocalSupportedIn (ω x) (regionSumset Λ 𝓝)

/-- A quasi-local star-automorphism has finite forward propagation when it propagates within some
finite neighborhood.

Source: arXiv:1703.09188, Appendix, line 2298. -/
def HasFinitePropagation {d : ℕ} [NeZero d]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) : Prop :=
  ∃ 𝓝 : Finset ℤ, PropagatesWithin ω 𝓝

variable {d : ℕ} [NeZero d]
  {ω η : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d} {𝓝 𝓜 : Finset ℤ}

namespace PropagatesWithin

/-- Propagation is preserved when the finite neighborhood is enlarged.

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma mono (hω : PropagatesWithin ω 𝓝) (h𝓝𝓜 : 𝓝 ⊆ 𝓜) :
    PropagatesWithin ω 𝓜 := by
  intro Λ x hx
  exact (hω Λ x hx).mono (regionSumset_mono_right Λ h𝓝𝓜)

/-- Forward propagation bounds compose: applying first `ω` and then `η` enlarges support by
`𝓝` and then by `𝓜`, hence by their region sumset.

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma trans (hω : PropagatesWithin ω 𝓝) (hη : PropagatesWithin η 𝓜) :
    PropagatesWithin (ω.trans η) (regionSumset 𝓝 𝓜) := by
  intro Λ x hx
  rw [← regionSumset_assoc]
  exact hη (regionSumset Λ 𝓝) (ω x) (hω Λ x hx)

end PropagatesWithin

namespace HasFinitePropagation

/-- Any prescribed finite set is contained in some propagation neighborhood of an automorphism
with finite forward propagation.

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma exists_superset (hω : HasFinitePropagation ω) (𝓢 : Finset ℤ) :
    ∃ 𝓜 : Finset ℤ, 𝓢 ⊆ 𝓜 ∧ PropagatesWithin ω 𝓜 := by
  obtain ⟨𝓚, h𝓚⟩ := hω
  exact ⟨𝓚 ∪ 𝓢, Finset.subset_union_right, h𝓚.mono Finset.subset_union_left⟩

/-- Finite forward propagation is closed under composition, with the first automorphism applied
before the second.

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma trans (hω : HasFinitePropagation ω) (hη : HasFinitePropagation η) :
    HasFinitePropagation (ω.trans η) := by
  obtain ⟨𝓝, h𝓝⟩ := hω
  obtain ⟨𝓜, h𝓜⟩ := hη
  exact ⟨regionSumset 𝓝 𝓜, h𝓝.trans h𝓜⟩

end HasFinitePropagation

/-- Propagation within \(\mathcal N\) can be checked pointwise on the canonical image of each
finite-region observable algebra.

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma propagatesWithin_iff_quasiLocalObservable :
    PropagatesWithin ω 𝓝 ↔
      ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ),
        QuasiLocalSupportedIn (ω (quasiLocalObservable d Λ A)) (regionSumset Λ 𝓝) := by
  constructor
  · intro h Λ A
    exact h Λ _ (QuasiLocalSupportedIn.quasiLocalObservable A)
  · intro h Λ x hx
    obtain ⟨A, rfl⟩ := hx
    exact h Λ A

/-- Propagation within \(\mathcal N\) is equivalent to inclusion of the image range of every
finite-region observable algebra in the range for \(\Lambda + \mathcal N\).

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma propagatesWithin_iff_range_subset :
    PropagatesWithin ω 𝓝 ↔
      ∀ Λ : Finset ℤ,
        Set.range (ω ∘ quasiLocalObservable d Λ) ⊆
          Set.range (quasiLocalObservable d (regionSumset Λ 𝓝)) := by
  rw [propagatesWithin_iff_quasiLocalObservable]
  apply forall_congr'
  intro Λ
  rw [Set.range_subset_iff]
  rfl

/-- Propagation within \(\mathcal N\) is equivalent to the existence, for every finite-region
observable, of a representative on \(\Lambda + \mathcal N\) for its image.

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma propagatesWithin_iff_exists_local :
    PropagatesWithin ω 𝓝 ↔
      ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ),
        ∃ B : LocalAlgebra d (regionSumset Λ 𝓝),
          ω (quasiLocalObservable d Λ A) =
            quasiLocalObservable d (regionSumset Λ 𝓝) B := by
  rw [propagatesWithin_iff_quasiLocalObservable]
  constructor
  · intro h Λ A
    obtain ⟨B, hB⟩ := h Λ A
    exact ⟨B, hB.symm⟩
  · intro h Λ A
    obtain ⟨B, hB⟩ := h Λ A
    exact ⟨B, hB.symm⟩

end SpinChain
