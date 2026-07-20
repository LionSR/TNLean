/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Api
import TNLean.MPS.SharedInfra.GaugePhase

/-!
# Auxiliary lemmas for sector matching

Shared overlap and linear-independence lemmas used by both exact and
proportional matching of BNT canonical-form sectors.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- If the overlap of two irreducible normalized BNT blocks does not decay,
then the left MPV state is an exact scalar multiple of the right MPV state at
every length. -/
lemma exists_state_scalar_of_nondecaying_overlap
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {j : Fin P.basisCount} {k : Fin Q.basisCount}
    (hnd : ¬ Tendsto (fun N : ℕ =>
      mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0)) :
    ∃ α : ℕ → ℂ, ∀ N : ℕ,
      mpvState (d := d) (P.basis j) N =
        α N • mpvState (d := d) (Q.basis k) N := by
  classical
  haveI hjdim : NeZero (P.basisDim j) := ⟨(hP.basis_dim_pos j).ne'⟩
  haveI hkdim : NeZero (Q.basisDim k) := ⟨(hQ.basis_dim_pos k).ne'⟩
  have hDim : P.basisDim j = Q.basisDim k := by
    by_contra hne
    exact hnd <|
      mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (P.basis j) (Q.basis k)
        (hP.basis_irreducible j) (hQ.basis_irreducible k)
        (hP.basis_left_canonical j) (hQ.basis_left_canonical k)
        hne
  have hGPE :
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hDim) (P.basis j)) (Q.basis k) := by
    by_contra hNot
    exact hnd <|
      mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
        (hdim := hDim) (A := P.basis j) (B := Q.basis k)
        (hA_irr := hP.basis_irreducible j)
        (hB_irr := hQ.basis_irreducible k)
        (hA_norm := hP.basis_left_canonical j)
        (hB_norm := hQ.basis_left_canonical k)
        (hNot := hNot)
  obtain ⟨X, ζ, hζ, hConj⟩ := hGPE
  refine ⟨fun N : ℕ => (ζ ^ N)⁻¹, ?_⟩
  intro N
  apply PiLp.ext
  intro σ
  have hQ_mpv :
      mpv (Q.basis k) σ = ζ ^ N * mpv (P.basis j) σ := by
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) hDim) (P.basis j))
      (B := Q.basis k) X ζ hConj N σ,
      mpv_cast_dim hDim (P.basis j) N σ]
  have hζN : ζ ^ N ≠ 0 := pow_ne_zero N hζ
  simp only [mpvState_apply]
  calc
    mpv (P.basis j) σ = (ζ ^ N)⁻¹ * (ζ ^ N * mpv (P.basis j) σ) := by
      rw [inv_mul_cancel_left₀ hζN]
    _ = (ζ ^ N)⁻¹ * mpv (Q.basis k) σ := by
      rw [← hQ_mpv]

/-- Eventual linear independence for the family consisting of the `P`-blocks
whose indices lie in a finset `T`, together with all `Q`-blocks, assuming all
`T`-to-`Q` overlaps decay. -/
lemma restricted_combined_family_eventually_li
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (T : Finset (Fin P.basisCount))
    (hTQ : ∀ (j : Fin P.basisCount), j ∈ T → ∀ k : Fin Q.basisCount,
      Tendsto (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0)) :
    ∀ᶠ N in atTop,
      LinearIndependent ℂ
        (Sum.elim
          (fun j : {j : Fin P.basisCount // j ∈ T} =>
            mpvState (d := d) (P.basis j.1) N)
          (fun k : Fin Q.basisCount =>
            mpvState (d := d) (Q.basis k) N)) := by
  classical
  let C : (x : Sum {j : Fin P.basisCount // j ∈ T} (Fin Q.basisCount)) →
      MPSTensor d
        (Sum.elim (fun j : {j : Fin P.basisCount // j ∈ T} => P.basisDim j.1)
          (fun k : Fin Q.basisCount => Q.basisDim k) x) :=
    Sum.rec
      (motive := fun x => MPSTensor d
        (Sum.elim (fun j : {j : Fin P.basisCount // j ∈ T} => P.basisDim j.1)
          (fun k : Fin Q.basisCount => Q.basisDim k) x))
      (fun j => P.basis j.1) (fun k => Q.basis k)
  have h_self : ∀ x,
      Tendsto (fun N : ℕ => mpvOverlap (d := d) (C x) (C x) N) atTop
        (𝓝 (1 : ℂ)) := by
    intro x
    cases x with
    | inl j => simpa [C] using hP.basis_normalized_self_overlap j.1
    | inr k => simpa [C] using hQ.basis_normalized_self_overlap k
  have h_cross : ∀ x y, x ≠ y →
      Tendsto (fun N : ℕ => mpvOverlap (d := d) (C x) (C y) N) atTop
        (𝓝 (0 : ℂ)) := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            have hij : i.1 ≠ j.1 := by
              intro hval
              apply hxy
              exact congrArg Sum.inl (Subtype.ext hval)
            simpa [C] using hP.cross_overlap_basis_tendsto_zero hij
        | inr k =>
            simpa [C] using hTQ i.1 i.2 k
    | inr k =>
        cases y with
        | inl i =>
            simpa [C] using
              (tendsto_mpvOverlap_zero_swap (d := d) (A := P.basis i.1)
                (B := Q.basis k) (N := id) (hTQ i.1 i.2 k))
        | inr l =>
            have hkl : k ≠ l := by
              intro hkl
              apply hxy
              simp [hkl]
            simpa [C] using hQ.cross_overlap_basis_tendsto_zero hkl
  have hLI :=
    eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal C h_self h_cross
  refine hLI.mono ?_
  intro N hN
  have key :
      (fun x : Sum {j : Fin P.basisCount // j ∈ T} (Fin Q.basisCount) =>
        mpvState (d := d) (C x) N) =
        Sum.elim
          (fun j : {j : Fin P.basisCount // j ∈ T} =>
            mpvState (d := d) (P.basis j.1) N)
          (fun k : Fin Q.basisCount =>
            mpvState (d := d) (Q.basis k) N) := by
    funext x
    cases x <;> rfl
  rw [← key]
  exact hN

end MPSTensor
