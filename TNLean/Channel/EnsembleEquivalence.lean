/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.WolfProps
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Equivalence of ensembles by zero-padded unitary mixing

Wolf's *Quantum Channels & Operations: Guided Tour* states the equivalence of
ensembles (§2, line 277 of `Notes/WolfNoteTexSource/ch02_representations.tex`) as
follows. Two ensembles of not necessarily normalized vectors `{ψⱼ}` and `{φ_ℓ}`
satisfy
`∑ⱼ |ψⱼ⟩⟨ψⱼ| = ∑_ℓ |φ_ℓ⟩⟨φ_ℓ|`
iff there is a **unitary** `U` with `|ψⱼ⟩ = ∑_ℓ Uⱼ_ℓ |φ_ℓ⟩`, where the smaller
of the two families is padded with zero vectors so that both are indexed alike.
No relation between the two cardinalities is assumed.

This file supplies that statement. The existing
`WolfProps.pureEnsembleDensity_eq_iff_exists_isometric_mixing` assumes
`card ι₂ ≤ card ι₁` and produces a tall isometry; padding removes both the
hypothesis and the tallness, because on a common index set an isometry is
square, hence unitary.

## Main definitions

* `WolfProps.padZero` — padding a family indexed by `Fin m` to one indexed by
  `Fin n` with zero vectors.

## Main results

* `WolfProps.pureEnsembleDensity_of_extendZero` — extending a family by zero
  vectors along an injection of index sets leaves the ensemble density
  unchanged.
* `WolfProps.pureEnsembleDensity_sumElim_zero`,
  `WolfProps.pureEnsembleDensity_zero_sumElim` — the two zero paddings onto the
  disjoint union of the index sets.
* `WolfProps.padZero_castLE` — the padded family agrees with the original on
  the retained indices.
* `WolfProps.pureEnsembleDensity_padZero` — padding to a longer family leaves
  the ensemble density unchanged.
* `WolfProps.pureEnsembleDensity_eq_iff_exists_unitary_mixing_of_pad` — the
  equivalence relative to families on a common index set whose densities agree
  with the two ensembles, canonically the zero paddings.
* `WolfProps.pureEnsembleDensity_eq_iff_exists_unitary_mixing` — Wolf's
  statement with the disjoint union `ι₁ ⊕ ι₂` as common index set.
* `WolfProps.pureEnsembleDensity_eq_iff_exists_unitary_mixing_fin` — Wolf's
  statement with `Fin (max m n)` as common index set.

## Design notes

Padding contributes no new mathematics. Zero vectors add zero rank-one terms to
the density operator, so both densities survive the passage to the common index
set; the ensembles are then equinumerous, the tall isometry supplied by
`WolfProps.exists_isometric_mixing_of_pureEnsembleDensity_eq` is square, and a
square isometry over a finite index set is unitary.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §2, Proposition 2.4
  ("Equivalence of ensembles", Eq. (2.10))][Wolf2012QChannels]
-/

open scoped Matrix

variable {D : ℕ}

namespace WolfProps

/-! ### Zero padding leaves the ensemble density unchanged -/

/-- Extending an ensemble by zero vectors leaves its density operator unchanged.

Here `e` injects the original index set into the larger one, `Ψ` restricts along
`e` to the original family, and `Ψ` vanishes off the image of `e`. Wolf's
"padded with zero vectors" is exactly this situation. -/
theorem pureEnsembleDensity_of_extendZero {ι₁ ι : Type*} [Fintype ι₁] [Fintype ι]
    (ψ : ι₁ → (Fin D → ℂ)) (Ψ : ι → (Fin D → ℂ)) {e : ι₁ → ι}
    (he : Function.Injective e) (hres : ∀ i, Ψ (e i) = ψ i)
    (hpad : ∀ k, (∀ i, e i ≠ k) → Ψ k = 0) :
    pureEnsembleDensity Ψ = pureEnsembleDensity ψ := by
  classical
  unfold pureEnsembleDensity
  have hzero : ∀ k ∈ (Finset.univ : Finset ι), k ∉ Finset.univ.image e →
      Matrix.vecMulVec (Ψ k) (star (Ψ k)) = 0 := by
    intro k _ hk
    have hne : ∀ i, e i ≠ k := fun i hi =>
      hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    simp [hpad k hne]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hzero,
    Finset.sum_image fun i _ j _ hij => he hij]
  simp only [hres]

/-- Padding a family indexed by `ι₁` with zero vectors on `ι₂` leaves its
density operator unchanged. -/
theorem pureEnsembleDensity_sumElim_zero {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (ψ : ι₁ → (Fin D → ℂ)) :
    pureEnsembleDensity (Sum.elim ψ (0 : ι₂ → (Fin D → ℂ))) = pureEnsembleDensity ψ :=
  pureEnsembleDensity_of_extendZero ψ _ Sum.inl_injective (fun _ => rfl)
    (fun k hk => by cases k with
      | inl i => exact absurd rfl (hk i)
      | inr _ => rfl)

/-- Padding a family indexed by `ι₂` with zero vectors on `ι₁` leaves its
density operator unchanged. -/
theorem pureEnsembleDensity_zero_sumElim {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (φ : ι₂ → (Fin D → ℂ)) :
    pureEnsembleDensity (Sum.elim (0 : ι₁ → (Fin D → ℂ)) φ) = pureEnsembleDensity φ :=
  pureEnsembleDensity_of_extendZero φ _ Sum.inr_injective (fun _ => rfl)
    (fun k hk => by cases k with
      | inl _ => rfl
      | inr j => exact absurd rfl (hk j))

/-- Pad a family of `m` vectors with zero vectors to a family of `n` vectors.
Only the first `min m n` entries survive; the intended use is `m ≤ n`. -/
def padZero {m n : ℕ} (ψ : Fin m → (Fin D → ℂ)) (k : Fin n) : Fin D → ℂ :=
  if h : (k : ℕ) < m then ψ ⟨k, h⟩ else 0

@[simp]
theorem padZero_castLE {m n : ℕ} (h : m ≤ n) (ψ : Fin m → (Fin D → ℂ)) (i : Fin m) :
    padZero (n := n) ψ (Fin.castLE h i) = ψ i := by
  simp [padZero]

/-- Zero padding from `Fin m` to `Fin n` leaves the ensemble density unchanged. -/
theorem pureEnsembleDensity_padZero {m n : ℕ} (h : m ≤ n) (ψ : Fin m → (Fin D → ℂ)) :
    pureEnsembleDensity (padZero (n := n) ψ) = pureEnsembleDensity ψ := by
  refine pureEnsembleDensity_of_extendZero ψ _ (e := Fin.castLE h)
    (fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij))
    (padZero_castLE h ψ) (fun k hk => ?_)
  have hk' : ¬ (k : ℕ) < m := fun hlt => hk ⟨k, hlt⟩ (Fin.ext rfl)
  simp [padZero, hk']

/-! ### Wolf's equivalence of ensembles -/

/-- **Equivalence of ensembles** (Wolf §2, line 277 of
`Notes/WolfNoteTexSource/ch02_representations.tex`), relative to families `Ψ`,
`Φ` on a common index set `ι` whose densities agree with those of `ψ` and `φ`.
The canonical such families are the zero paddings of the two ensembles.

Two ensembles of not necessarily normalized vectors induce the same density
operator iff those families are related by a unitary mixing matrix
`Ψ i = ∑_ℓ U i ℓ • Φ ℓ`. No relation between the cardinalities of the original
index sets is assumed. -/
theorem pureEnsembleDensity_eq_iff_exists_unitary_mixing_of_pad
    {ι₁ ι₂ ι : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι] [DecidableEq ι]
    (ψ : ι₁ → (Fin D → ℂ)) (φ : ι₂ → (Fin D → ℂ)) (Ψ Φ : ι → (Fin D → ℂ))
    (hΨ : pureEnsembleDensity Ψ = pureEnsembleDensity ψ)
    (hΦ : pureEnsembleDensity Φ = pureEnsembleDensity φ) :
    pureEnsembleDensity ψ = pureEnsembleDensity φ ↔
      ∃ U : Matrix ι ι ℂ, U ∈ Matrix.unitaryGroup ι ℂ ∧
        ∀ i, Ψ i = fun a => ∑ ℓ, U i ℓ * Φ ℓ a := by
  constructor
  · intro hρ
    obtain ⟨U, hU, hmix⟩ :=
      exists_isometric_mixing_of_pureEnsembleDensity_eq Ψ Φ (hΨ.trans (hρ.trans hΦ.symm)) le_rfl
    refine ⟨U, ?_, hmix⟩
    -- On a common index set the isometry is square, so `Uᴴ U = 1` already
    -- forces `U Uᴴ = 1`.
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using hU
  · rintro ⟨U, hU, hmix⟩
    have hUiso : Uᴴ * U = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
    have hpad := pureEnsembleDensity_eq_of_isometric_mixing Ψ Φ U hUiso hmix
    rwa [hΨ, hΦ] at hpad

/-- **Equivalence of ensembles** (Wolf §2, line 277 of
`Notes/WolfNoteTexSource/ch02_representations.tex`), with the disjoint union
`ι₁ ⊕ ι₂` as the common index set.

Two ensembles `{ψⱼ}_{j ∈ ι₁}` and `{φ_ℓ}_{ℓ ∈ ι₂}` of not necessarily normalized
vectors satisfy `∑ⱼ |ψⱼ⟩⟨ψⱼ| = ∑_ℓ |φ_ℓ⟩⟨φ_ℓ|` iff, after padding both families
with zero vectors on the complementary index set, there is a unitary `U` with
`ψⱼ = ∑_ℓ Uⱼ_ℓ φ_ℓ`. There is no cardinality hypothesis. -/
theorem pureEnsembleDensity_eq_iff_exists_unitary_mixing
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (ψ : ι₁ → (Fin D → ℂ)) (φ : ι₂ → (Fin D → ℂ)) :
    pureEnsembleDensity ψ = pureEnsembleDensity φ ↔
      ∃ U : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ, U ∈ Matrix.unitaryGroup (ι₁ ⊕ ι₂) ℂ ∧
        ∀ i, Sum.elim ψ (0 : ι₂ → (Fin D → ℂ)) i =
          fun a => ∑ ℓ, U i ℓ * Sum.elim (0 : ι₁ → (Fin D → ℂ)) φ ℓ a :=
  pureEnsembleDensity_eq_iff_exists_unitary_mixing_of_pad ψ φ _ _
    (pureEnsembleDensity_sumElim_zero ψ) (pureEnsembleDensity_zero_sumElim φ)

/-- **Equivalence of ensembles** (Wolf §2, line 277 of
`Notes/WolfNoteTexSource/ch02_representations.tex`), with `Fin (max m n)` as the
common index set.

An ensemble of `m` vectors and an ensemble of `n` vectors induce the same
density operator iff, after padding both with zero vectors to length
`max m n`, there is a unitary `U` with `ψⱼ = ∑_ℓ Uⱼ_ℓ φ_ℓ`. There is no
relation assumed between `m` and `n`. -/
theorem pureEnsembleDensity_eq_iff_exists_unitary_mixing_fin {m n : ℕ}
    (ψ : Fin m → (Fin D → ℂ)) (φ : Fin n → (Fin D → ℂ)) :
    pureEnsembleDensity ψ = pureEnsembleDensity φ ↔
      ∃ U : Matrix (Fin (max m n)) (Fin (max m n)) ℂ,
        U ∈ Matrix.unitaryGroup (Fin (max m n)) ℂ ∧
        ∀ i, padZero ψ i = fun a => ∑ ℓ, U i ℓ * padZero φ ℓ a :=
  pureEnsembleDensity_eq_iff_exists_unitary_mixing_of_pad ψ φ _ _
    (pureEnsembleDensity_padZero (le_max_left m n) ψ)
    (pureEnsembleDensity_padZero (le_max_right m n) φ)

end WolfProps
