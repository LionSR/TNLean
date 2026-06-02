/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.DominantMatch
import TNLean.MPS.SharedInfra.GaugePhase

/-!
# Exact block matching for BNT canonical forms

Two BNT canonical forms with the same positive-length MPV family have exact
single-sector matches: for each sector of one decomposition, some sector of the
other has the same bond dimension, is gauge-phase equivalent after the dimension
cast, and has non-decaying overlap.  The argument uses fixed-length linear
independence to force an exact coefficient contradiction, so no per-sector
unit-modulus copy-weight hypothesis is needed.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- Re-index a sum over a finite family through a finite map by collecting the
coefficients in the fibres of the map. -/
private lemma sum_fiber_smul
    {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommMonoid V] [Module ℂ V]
    (φ : ι → κ) (a : ι → ℂ) (v : κ → V) :
    (∑ i : ι, a i • v (φ i)) =
      ∑ k : κ, (∑ i : ι, if φ i = k then a i else 0) • v k := by
  classical
  calc
    (∑ i : ι, a i • v (φ i))
        = ∑ i : ι, ∑ k : κ, (if φ i = k then a i else 0) • v k := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hinner :
              (∑ k : κ, (if φ i = k then a i else 0) • v k)
                = a i • v (φ i) := by
            simp [ite_smul, eq_comm]
          exact hinner.symm
    _ = ∑ k : κ, ∑ i : ι, (if φ i = k then a i else 0) • v k := by
          rw [Finset.sum_comm]
    _ = ∑ k : κ, (∑ i : ι, if φ i = k then a i else 0) • v k := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_smul]

/-- If the overlap of two irreducible normalized BNT blocks does not decay,
then the left MPV state is an exact scalar multiple of the right MPV state at
every length. -/
private lemma exists_state_scalar_of_nondecaying_overlap
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
private lemma restricted_combined_family_eventually_li
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

/-- Exact non-decaying-overlap extraction at a fixed `P`-sector.  The proof is
by exact finite-dimensional coefficient comparison, not by a coefficient limit. -/
private lemma exists_nondecaying_overlap_exact
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ¬ Tendsto (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N) atTop (𝓝 0) := by
  classical
  by_contra hNo
  push Not at hNo
  let T : Finset (Fin P.basisCount) :=
    Finset.univ.filter fun j : Fin P.basisCount =>
      ∀ k : Fin Q.basisCount,
        Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0)
  have hj₀T : j₀ ∈ T := by
    simp [T, hNo]
  have hTQ : ∀ (j : Fin P.basisCount), j ∈ T → ∀ k : Fin Q.basisCount,
      Tendsto (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0) := by
    intro j hj k
    simpa [T] using (Finset.mem_filter.mp hj).2 k
  have hNotT_nondecay : ∀ j : Fin P.basisCount, j ∉ T →
      ∃ k : Fin Q.basisCount,
        ¬ Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0) := by
    intro j hjT
    have hnot : ¬ (∀ k : Fin Q.basisCount,
        Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (Q.basis k) N) atTop (𝓝 0)) := by
      intro hall
      exact hjT (by simp [T, hall])
    push Not at hnot
    exact hnot
  have hScalar : ∀ c : {j : Fin P.basisCount // j ∉ T},
      ∃ k : Fin Q.basisCount, ∃ α : ℕ → ℂ, ∀ N : ℕ,
        mpvState (d := d) (P.basis c.1) N =
          α N • mpvState (d := d) (Q.basis k) N := by
    intro c
    obtain ⟨k, hk⟩ := hNotT_nondecay c.1 c.2
    obtain ⟨α, hα⟩ := exists_state_scalar_of_nondecaying_overlap hP hQ hk
    exact ⟨k, α, hα⟩
  choose kOf αOf hStateOf using hScalar
  letI : Fintype {j : Fin P.basisCount // j ∈ T} := Subtype.fintype (fun j => j ∈ T)
  letI : Fintype {j : Fin P.basisCount // j ∉ T} := Subtype.fintype (fun j => j ∉ T)
  have hLI : ∀ᶠ N in atTop,
      LinearIndependent ℂ
        (Sum.elim
          (fun j : {j : Fin P.basisCount // j ∈ T} =>
            mpvState (d := d) (P.basis j.1) N)
          (fun k : Fin Q.basisCount =>
            mpvState (d := d) (Q.basis k) N)) :=
    restricted_combined_family_eventually_li hP hQ T hTQ
  have hCoeff_eventually_zero :
      ∀ᶠ N : ℕ in atTop, P.coeff N j₀ = 0 := by
    refine (hLI.and (Filter.eventually_atTop.mpr ⟨1, fun N hN => hN⟩)).mono ?_
    intro N hN
    rcases hN with ⟨hLIN, hNpos⟩
    have hPstate :
        mpvState (d := d) P.toTensor N =
          ∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N := by
      refine mpvState_eq_sum_of_decomp (d := d) P.toTensor P.basis
        (N := N) (fun j => P.coeff N j) ?_
      intro σ
      simpa [smul_eq_mul] using P.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hQstate :
        mpvState (d := d) Q.toTensor N =
          ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := by
      refine mpvState_eq_sum_of_decomp (d := d) Q.toTensor Q.basis
        (N := N) (fun k => Q.coeff N k) ?_
      intro σ
      simpa [smul_eq_mul] using Q.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hStateEq : mpvState (d := d) P.toTensor N = mpvState (d := d) Q.toTensor N := by
      apply PiLp.ext
      intro σ
      simpa [mpvState_apply, mpv] using hEqual N hNpos σ
    have hPQsum :
        (∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N) =
          ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := by
      calc
        (∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N)
            = mpvState (d := d) P.toTensor N := hPstate.symm
        _ = mpvState (d := d) Q.toTensor N := hStateEq
        _ = ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := hQstate
    let sumT : MPVSpace d N :=
      ∑ t : {j : Fin P.basisCount // j ∈ T}, P.coeff N t.1 •
        mpvState (d := d) (P.basis t.1) N
    let sumC : MPVSpace d N :=
      ∑ c : {j : Fin P.basisCount // j ∉ T}, P.coeff N c.1 •
        mpvState (d := d) (P.basis c.1) N
    let sumQ : MPVSpace d N :=
      ∑ k : Fin Q.basisCount, Q.coeff N k •
        mpvState (d := d) (Q.basis k) N
    let agg : Fin Q.basisCount → ℂ := fun k =>
      ∑ c : {j : Fin P.basisCount // j ∉ T},
        if kOf c = k then P.coeff N c.1 * αOf c N else 0
    let sumAgg : MPVSpace d N :=
      ∑ k : Fin Q.basisCount, agg k • mpvState (d := d) (Q.basis k) N
    have hSplitP : sumT + sumC = sumQ := by
      have hsplit :=
        Fintype.sum_subtype_add_sum_subtype
          (p := fun j : Fin P.basisCount => j ∈ T)
          (f := fun j : Fin P.basisCount =>
            P.coeff N j • mpvState (d := d) (P.basis j) N)
      change
        (∑ t : {j : Fin P.basisCount // j ∈ T}, P.coeff N t.1 •
            mpvState (d := d) (P.basis t.1) N) +
          (∑ c : {j : Fin P.basisCount // j ∉ T}, P.coeff N c.1 •
            mpvState (d := d) (P.basis c.1) N) =
        ∑ k : Fin Q.basisCount, Q.coeff N k •
          mpvState (d := d) (Q.basis k) N
      exact hsplit.trans hPQsum
    have hC_subst :
        sumC = ∑ c : {j : Fin P.basisCount // j ∉ T},
          (P.coeff N c.1 * αOf c N) •
            mpvState (d := d) (Q.basis (kOf c)) N := by
      refine Finset.sum_congr rfl ?_
      intro c _
      calc
        P.coeff N c.1 • mpvState (d := d) (P.basis c.1) N
            = P.coeff N c.1 •
                (αOf c N • mpvState (d := d) (Q.basis (kOf c)) N) := by
              rw [hStateOf c N]
        _ = (P.coeff N c.1 * αOf c N) •
                mpvState (d := d) (Q.basis (kOf c)) N := by
              rw [smul_smul]
    have hC_group :
        (∑ c : {j : Fin P.basisCount // j ∉ T},
          (P.coeff N c.1 * αOf c N) •
            mpvState (d := d) (Q.basis (kOf c)) N) = sumAgg := by
      simpa [sumAgg, agg] using
        (sum_fiber_smul (φ := kOf)
          (a := fun c : {j : Fin P.basisCount // j ∉ T} => P.coeff N c.1 * αOf c N)
          (v := fun k : Fin Q.basisCount => mpvState (d := d) (Q.basis k) N))
    have hMain : sumT + sumAgg = sumQ := by
      calc
        sumT + sumAgg = sumT + sumC := by
          rw [← hC_group, ← hC_subst]
        _ = sumQ := hSplitP
    let coeff : Sum {j : Fin P.basisCount // j ∈ T} (Fin Q.basisCount) → ℂ :=
      Sum.elim (fun t => P.coeff N t.1) (fun k => agg k - Q.coeff N k)
    have hZeroCombined :
        ∑ x : Sum {j : Fin P.basisCount // j ∈ T} (Fin Q.basisCount),
          coeff x •
            Sum.elim
              (fun t : {j : Fin P.basisCount // j ∈ T} =>
                mpvState (d := d) (P.basis t.1) N)
              (fun k : Fin Q.basisCount =>
                mpvState (d := d) (Q.basis k) N) x = 0 := by
      have hQsub :
          (∑ k : Fin Q.basisCount, (agg k - Q.coeff N k) •
              mpvState (d := d) (Q.basis k) N)
            = sumAgg - sumQ := by
        simp [sumAgg, sumQ, sub_smul, Finset.sum_sub_distrib]
      have hZero : sumT +
          (∑ k : Fin Q.basisCount, (agg k - Q.coeff N k) •
              mpvState (d := d) (Q.basis k) N) = 0 := by
        calc
          sumT +
              (∑ k : Fin Q.basisCount, (agg k - Q.coeff N k) •
                mpvState (d := d) (Q.basis k) N)
              = sumT + (sumAgg - sumQ) := by rw [hQsub]
          _ = (sumT + sumAgg) - sumQ := by abel
          _ = 0 := sub_eq_zero.mpr hMain
      simpa [coeff, sumT] using hZero
    have hcoeff :=
      Fintype.linearIndependent_iff.mp hLIN coeff hZeroCombined
        (Sum.inl ⟨j₀, hj₀T⟩)
    simpa [coeff] using hcoeff
  exact (hP.coeff_not_eventually_zero j₀) hCoeff_eventually_zero

/-- Exact single-block matching without a per-sector unit-modulus hypothesis.

The proof first obtains a non-decaying overlap by an exact coefficient-comparison
argument over the partition of `P`-sectors that decay against all `Q`-sectors.
It then recovers dimension equality and gauge-phase equivalence by the same
overlap-dichotomy contrapositives used in `exists_block_match_of_sameMPVPos`. -/
theorem exists_block_match_exact
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ∃ h : P.basisDim j₀ = Q.basisDim k₀,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis j₀)) (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N) atTop (𝓝 0) := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_nondecaying_overlap_exact
    (P := P) (Q := Q) hP hQ j₀ hEqual
  haveI hj₀dim : NeZero (P.basisDim j₀) := ⟨(hP.basis_dim_pos j₀).ne'⟩
  haveI hk₀dim : NeZero (Q.basisDim k₀) := ⟨(hQ.basis_dim_pos k₀).ne'⟩
  have hDim : P.basisDim j₀ = Q.basisDim k₀ := by
    by_contra hne
    exact hk₀ <|
      mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (P.basis j₀) (Q.basis k₀)
        (hP.basis_irreducible j₀) (hQ.basis_irreducible k₀)
        (hP.basis_left_canonical j₀) (hQ.basis_left_canonical k₀)
        hne
  have hGPE :
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) (Q.basis k₀) := by
    by_contra hNot
    exact hk₀ <|
      mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
        (hdim := hDim) (A := P.basis j₀) (B := Q.basis k₀)
        (hA_irr := hP.basis_irreducible j₀)
        (hB_irr := hQ.basis_irreducible k₀)
        (hA_norm := hP.basis_left_canonical j₀)
        (hB_norm := hQ.basis_left_canonical k₀)
        (hNot := hNot)
  exact ⟨k₀, hDim, hGPE, hk₀⟩

end MPSTensor
