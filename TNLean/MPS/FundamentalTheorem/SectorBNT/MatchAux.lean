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

/-- **Shared bijection construction from forward and backward existential matches.**
Given two injective maps built from per-sector existential matches, finite
cardinality comparison turns the forward injection into a bijection
`β : Fin Q.basisCount ≃ Fin P.basisCount`. -/
lemma bijection_from_matches {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hFwd : ∀ k : Fin Q.basisCount,
      ∃ (j : Fin P.basisCount) (h : P.basisDim j = Q.basisDim k),
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis j)) (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0))
    (hBwd : ∀ j : Fin P.basisCount,
      ∃ (k : Fin Q.basisCount) (h : Q.basisDim k = P.basisDim j),
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (Q.basis k)) (P.basis j) ∧
        ¬ Tendsto (fun N : ℕ => mpvOverlap (d := d) (Q.basis k) (P.basis j) N) atTop (𝓝 0)) :
    ∃ β : Fin Q.basisCount ≃ Fin P.basisCount,
      ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis (β k)) (Q.basis k) N) atTop (𝓝 0) := by
  classical
  let φ₀ : Fin Q.basisCount → Fin P.basisCount := fun k => (hFwd k).choose
  have φ₀_spec : ∀ k : Fin Q.basisCount,
      ∃ h : P.basisDim (φ₀ k) = Q.basisDim k,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (φ₀ k)))
            (Q.basis k) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (φ₀ k)) (Q.basis k) N)
          atTop (𝓝 0) := fun k => (hFwd k).choose_spec
  have rebase_centre_P :
      ∀ (j j' : Fin P.basisCount) (_hj : j = j')
        {kv : Fin Q.basisCount}
        (h_t : P.basisDim j' = Q.basisDim kv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (P.basis j')) (Q.basis kv)),
        ∃ h_t' : P.basisDim j = Q.basisDim kv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (P.basis j)) (Q.basis kv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hφ₀_inj : Function.Injective φ₀ := by
    intro k₁ k₂ hjEq
    obtain ⟨h₁, GE₁, _⟩ := φ₀_spec k₁
    obtain ⟨h₂, GE₂, _⟩ := φ₀_spec k₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_P (φ₀ k₁) (φ₀ k₂) hjEq h₂ GE₂
    have hQdim : Q.basisDim k₁ = Q.basisDim k₂ := h₁.symm.trans h₂'
    have hQGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hQdim) (Q.basis k₁))
            (Q.basis k₂) :=
      gaugePhaseEquiv_cast_compose_via_centre (A := P.basis (φ₀ k₁))
        (B := Q.basis k₁) (C := Q.basis k₂) h₁ h₂' GE₁ GE₂'
    exact hQ.basis_distinct k₁ k₂ hne hQdim hQGE
  let ψ₀ : Fin P.basisCount → Fin Q.basisCount := fun j => (hBwd j).choose
  have ψ₀_spec : ∀ j : Fin P.basisCount,
      ∃ h : Q.basisDim (ψ₀ j) = P.basisDim j,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (Q.basis (ψ₀ j)))
            (P.basis j) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (Q.basis (ψ₀ j)) (P.basis j) N)
          atTop (𝓝 0) := fun j => (hBwd j).choose_spec
  have rebase_centre_Q :
      ∀ (k k' : Fin Q.basisCount) (_hk : k = k')
        {jv : Fin P.basisCount}
        (h_t : Q.basisDim k' = P.basisDim jv)
        (_GE : GaugePhaseEquiv
                  (cast (congr_arg (MPSTensor d) h_t) (Q.basis k')) (P.basis jv)),
        ∃ h_t' : Q.basisDim k = P.basisDim jv,
          GaugePhaseEquiv
              (cast (congr_arg (MPSTensor d) h_t') (Q.basis k)) (P.basis jv) := by
    rintro _ _ rfl _ h_t GE
    exact ⟨h_t, GE⟩
  have hψ₀_inj : Function.Injective ψ₀ := by
    intro j₁ j₂ hkEq
    obtain ⟨h₁, GE₁, _⟩ := ψ₀_spec j₁
    obtain ⟨h₂, GE₂, _⟩ := ψ₀_spec j₂
    by_contra hne
    obtain ⟨h₂', GE₂'⟩ :=
      rebase_centre_Q (ψ₀ j₁) (ψ₀ j₂) hkEq h₂ GE₂
    have hPdim : P.basisDim j₁ = P.basisDim j₂ := h₁.symm.trans h₂'
    have hPGE :
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hPdim) (P.basis j₁))
            (P.basis j₂) :=
      gaugePhaseEquiv_cast_compose_via_centre (A := Q.basis (ψ₀ j₁))
        (B := P.basis j₁) (C := P.basis j₂) h₁ h₂' GE₁ GE₂'
    exact hP.basis_distinct j₁ j₂ hne hPdim hPGE
  have hCardQP : Fintype.card (Fin Q.basisCount) ≤ Fintype.card (Fin P.basisCount) :=
    Fintype.card_le_of_injective φ₀ hφ₀_inj
  have hCardPQ : Fintype.card (Fin P.basisCount) ≤ Fintype.card (Fin Q.basisCount) :=
    Fintype.card_le_of_injective ψ₀ hψ₀_inj
  have hCard : Fintype.card (Fin Q.basisCount) = Fintype.card (Fin P.basisCount) :=
    le_antisymm hCardQP hCardPQ
  have hφ₀_bij : Function.Bijective φ₀ :=
    (Fintype.bijective_iff_injective_and_card φ₀).2 ⟨hφ₀_inj, hCard⟩
  let β : Fin Q.basisCount ≃ Fin P.basisCount := Equiv.ofBijective φ₀ hφ₀_bij
  refine ⟨β, ?_⟩
  intro k
  simpa [β] using φ₀_spec k

end MPSTensor
