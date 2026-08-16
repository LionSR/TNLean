/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval
import TNLean.QCA.QuasiLocal
import TNLean.QCA.RegionSumset

/-!
# Finite propagation on the quasi-local algebra

A quasi-local observable is supported in a finite region when it lies in the range of that
region's canonical embedding. A quasi-local star-automorphism propagates within a finite
neighborhood when it sends every observable supported in \(\Lambda\) to one supported in
\(\Lambda + \mathcal N\), uniformly over finite regions \(\Lambda\).

This file records equivalent support, range-inclusion, and finite-region witness formulations of
that condition, together with neighborhood monotonicity, forward-composition closure, and
normalization to a symmetric interval. It also provides two-sided convenience predicates that
require propagation bounds separately for an automorphism and its inverse.

## Main definitions

* `SpinChain.QuasiLocalSupportedIn` — membership in a finite-region observable algebra.
* `SpinChain.PropagatesWithin` — propagation bounded by a fixed finite neighborhood.
* `SpinChain.HasFinitePropagation` — existence of a finite propagation neighborhood.
* `SpinChain.PropagatesWithinTwoSided` — a common neighborhood bound for an automorphism and
  its inverse.
* `SpinChain.HasTwoSidedFinitePropagation` — separate finite propagation bounds for an
  automorphism and its inverse.

## Main results

* `SpinChain.QuasiLocalSupportedIn.quasiLocalObservable` — every embedded finite-region
  observable is supported in its region.
* `SpinChain.QuasiLocalSupportedIn.mono` — support is monotone under region enlargement.
* `SpinChain.propagatesWithin_iff_quasiLocalObservable` — the universal pointwise formulation.
* `SpinChain.propagatesWithin_iff_range_subset` — the range-inclusion formulation.
* `SpinChain.propagatesWithin_iff_exists_local` — the finite-region witness formulation.
* `SpinChain.exists_subset_symmetric_Icc` — every finite integer region lies in some
  symmetric interval.
* `SpinChain.PropagatesWithin.mono` — propagation is monotone under neighborhood enlargement.
* `SpinChain.PropagatesWithin.trans` — forward propagation bounds compose by region sumset.
* `SpinChain.PropagatesWithin.exists_symmetric_Icc` — a propagation neighborhood can be enlarged
  to a symmetric interval.
* `SpinChain.HasFinitePropagation.exists_superset` — valid neighborhoods can contain any finite set.
* `SpinChain.HasFinitePropagation.trans` — finite forward propagation is closed under composition.
* `SpinChain.HasFinitePropagation.exists_symmetric_Icc` — finite propagation admits a symmetric
  interval witness.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, line 2298.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

open scoped Pointwise

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

/-- A finite neighborhood is a two-sided propagation bound when it bounds both an automorphism
and its inverse.

This is a derived convenience predicate, not the forward-only QCA definition in either cited
source. Context: arXiv:1703.09188, Appendix, line 2298; Schumacher--Werner, Definition 1. -/
def PropagatesWithinTwoSided {d : ℕ} [NeZero d]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) (𝓝 : Finset ℤ) : Prop :=
  PropagatesWithin ω 𝓝 ∧ PropagatesWithin ω.symm 𝓝

/-- A quasi-local star-automorphism has two-sided finite propagation when it and its inverse each
have finite forward propagation, possibly with different finite neighborhoods.

This is a derived convenience predicate, not the forward-only QCA definition in either cited
source. Context: arXiv:1703.09188, Appendix, line 2298; Schumacher--Werner, Definition 1. -/
def HasTwoSidedFinitePropagation {d : ℕ} [NeZero d]
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) : Prop :=
  HasFinitePropagation ω ∧ HasFinitePropagation ω.symm

/-- Reflection fixes every symmetric integer interval.

This is an elementary fact about finite neighborhoods. Context: arXiv:1703.09188, Appendix,
line 2298. -/
@[simp]
lemma neg_symmetric_Icc (R : ℕ) :
    -(Finset.Icc (-(R : ℤ)) (R : ℤ)) = Finset.Icc (-(R : ℤ)) (R : ℤ) := by
  ext n
  simp only [Finset.mem_neg, Finset.mem_Icc]
  constructor
  · rintro ⟨n, ⟨hnlo, hnhi⟩, rfl⟩
    exact ⟨neg_le_neg hnhi, by simpa using neg_le_neg hnlo⟩
  · rintro ⟨hnlo, hnhi⟩
    exact ⟨-n, ⟨neg_le_neg hnhi, by simpa using neg_le_neg hnlo⟩, neg_neg n⟩

/-- Every finite set of integers is contained in a symmetric interval
\([-R,R] \cap \mathbb Z\).

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma exists_subset_symmetric_Icc (𝓝 : Finset ℤ) :
    ∃ R : ℕ, 𝓝 ⊆ Finset.Icc (-(R : ℤ)) (R : ℤ) := by
  refine ⟨𝓝.sup Int.natAbs, ?_⟩
  intro n hn
  rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs]
  exact_mod_cast Finset.le_sup hn

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

/-- A finite propagation neighborhood can be enlarged to a symmetric interval
\([-R,R] \cap \mathbb Z\).

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma exists_symmetric_Icc (hω : PropagatesWithin ω 𝓝) :
    ∃ R : ℕ, 𝓝 ⊆ Finset.Icc (-(R : ℤ)) (R : ℤ) ∧
      PropagatesWithin ω (Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
  obtain ⟨R, h𝓝R⟩ := exists_subset_symmetric_Icc 𝓝
  exact ⟨R, h𝓝R, hω.mono h𝓝R⟩

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

/-- Finite forward propagation admits a symmetric-interval witness
\([-R,R] \cap \mathbb Z\).

Source: arXiv:1703.09188, Appendix, line 2298. -/
lemma exists_symmetric_Icc (hω : HasFinitePropagation ω) :
    ∃ R : ℕ, PropagatesWithin ω (Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
  obtain ⟨𝓝, h𝓝⟩ := hω
  obtain ⟨R, _, hR⟩ := h𝓝.exists_symmetric_Icc
  exact ⟨R, hR⟩

end HasFinitePropagation

namespace PropagatesWithinTwoSided

/-- A common two-sided propagation neighborhood remains valid after enlargement.

This is an elementary consequence of forward-neighborhood monotonicity and is not a separate
claim of the cited sources. -/
lemma mono (hω : PropagatesWithinTwoSided ω 𝓝) (h𝓝𝓜 : 𝓝 ⊆ 𝓜) :
    PropagatesWithinTwoSided ω 𝓜 :=
  ⟨hω.1.mono h𝓝𝓜, hω.2.mono h𝓝𝓜⟩

/-- A forward bound by \(\mathcal N\) and an inverse bound by \(-\mathcal N\) have the common
neighborhood \(\mathcal N\cup(-\mathcal N)\).

This only enlarges two supplied bounds. It does not derive inverse propagation from forward
propagation. -/
lemma of_reflected (hω : PropagatesWithin ω 𝓝) (hωinv : PropagatesWithin ω.symm (-𝓝)) :
    PropagatesWithinTwoSided ω (𝓝 ∪ (-𝓝)) :=
  ⟨hω.mono Finset.subset_union_left, hωinv.mono Finset.subset_union_right⟩

/-- A common two-sided propagation neighborhood can be enlarged to a symmetric interval.

This is an elementary consequence of finite-neighborhood enlargement and is not a separate claim
of the cited sources. -/
lemma exists_symmetric_Icc (hω : PropagatesWithinTwoSided ω 𝓝) :
    ∃ R : ℕ, 𝓝 ⊆ Finset.Icc (-(R : ℤ)) (R : ℤ) ∧
      PropagatesWithinTwoSided ω (Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
  obtain ⟨R, h𝓝R⟩ := exists_subset_symmetric_Icc 𝓝
  exact ⟨R, h𝓝R, hω.mono h𝓝R⟩

end PropagatesWithinTwoSided

namespace HasTwoSidedFinitePropagation

/-- Separate finite propagation bounds for an automorphism and its inverse have one common
finite neighborhood.

This only combines supplied forward and inverse bounds. It does not prove that the inverse has
finite propagation. -/
lemma exists_common_neighborhood (hω : HasTwoSidedFinitePropagation ω) :
    ∃ 𝓝 : Finset ℤ, PropagatesWithinTwoSided ω 𝓝 := by
  obtain ⟨⟨𝓝, h𝓝⟩, ⟨𝓜, h𝓜⟩⟩ := hω
  exact ⟨𝓝 ∪ 𝓜, h𝓝.mono Finset.subset_union_left, h𝓜.mono Finset.subset_union_right⟩

/-- Two-sided finite propagation admits one symmetric-interval neighborhood for the automorphism
and its inverse.

This only combines and enlarges supplied forward and inverse bounds. It does not prove inverse
locality from forward locality. -/
lemma exists_symmetric_Icc (hω : HasTwoSidedFinitePropagation ω) :
    ∃ R : ℕ, PropagatesWithinTwoSided ω (Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
  obtain ⟨𝓝, h𝓝⟩ := hω.exists_common_neighborhood
  obtain ⟨R, _, hR⟩ := h𝓝.exists_symmetric_Icc
  exact ⟨R, hR⟩

end HasTwoSidedFinitePropagation

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
