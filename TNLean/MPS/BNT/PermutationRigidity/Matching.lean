import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Overlap.SelfOverlapAux
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.Topology.TendstoHelpers

open scoped BigOperators Matrix
open Filter Finset

namespace MPSTensor

/-! ## Full permutation/phase matching (paper hypotheses, no span-equality)

We now combine the two non-vanishing-overlap lemmas with the existing overlap-decay dichotomy
(`mpvOverlap_tendsto_zero` / `mpvOverlap_tendsto_zero_of_dim_ne`) to obtain the full permutation
statement, without assuming span equality.
-/

/-! ### Shared matching kernels -/

private lemma eq_dim_of_not_tendsto_zero_mpvOverlap
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    {j : Fin gA} {k : Fin gB}
    (h_nonzero :
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0))
    (h_zero_of_dim_ne :
      dimA j ≠ dimB k →
        Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0)) :
    dimA j = dimB k := by
  by_contra hdim
  exact h_nonzero (h_zero_of_dim_ne hdim)

private lemma gaugePhaseEquiv_of_not_tendsto_zero_mpvOverlap
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    {j : Fin gA} {k : Fin gB}
    (hdim : dimA j = dimB k)
    (h_nonzero :
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0))
    (h_zero_of_not_gauge :
      ¬ GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (A j))
          (B k) →
        Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0)) :
    GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim) (A j))
      (B k) := by
  by_contra hNot
  exact h_nonzero (h_zero_of_not_gauge hNot)

private lemma tendsto_norm_mpvOverlap_one_of_scaled_self
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (s : ℕ → ℂ)
    (hSelf :
      Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) atTop (nhds 1))
    (hs_norm : ∀ N, ‖s N‖ = 1)
    (hScale :
      ∀ N, mpvOverlap (d := d) A B N = s N * mpvOverlap (d := d) B B N) :
    Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) atTop (nhds 1) := by
  have hEq :
      (fun N => ‖mpvOverlap (d := d) A B N‖) =
        fun N => ‖mpvOverlap (d := d) B B N‖ := by
    ext N
    rw [hScale N, norm_mul, hs_norm N, one_mul]
  simpa [hEq] using hSelf

private lemma ne_zero_of_norm_eq_one (ζ : ℂ) (hζ_norm : ‖ζ‖ = 1) : ζ ≠ 0 := by
  intro h0
  simp [h0] at hζ_norm

private lemma rightMatching_injective_of_gaugePhaseEquiv
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (f : Fin gB → Fin gA)
    (hf_dim : ∀ k : Fin gB, dimA (f k) = dimB k)
    (hf_gauge : ∀ k : Fin gB,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim k)) (A (f k)))
        (B k))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0)) :
    Function.Injective f := by
  intro k1 k2 hk
  by_contra hne
  have h_cross : Tendsto (fun N => mpvOverlap (d := d) (B k1) (B k2) N) atTop (nhds 0) :=
    hB_off k1 k2 hne
  have h_cross_norm_zero : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖)
      atTop (nhds 0) := by
    simpa only [norm_zero] using h_cross.norm
  obtain ⟨X1, ζ1, _, hX1⟩ := hf_gauge k1
  obtain ⟨X2, ζ2, _, hX2⟩ := hf_gauge k2
  have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k1) σ = ζ1 ^ N * mpv (A (f k1)) σ := by
    intro N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hf_dim k1)) (A (f k1)))
      (B := B k1) X1 ζ1 hX1 N σ,
      mpv_cast_dim (hf_dim k1) (A (f k1)) N σ]
  have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k2) σ = ζ2 ^ N * mpv (A (f k1)) σ := by
    intro N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hf_dim k2)) (A (f k2)))
      (B := B k2) X2 ζ2 hX2 N σ,
      mpv_cast_dim (hf_dim k2) (A (f k2)) N σ,
      hk.symm]
  have hAA_norm_tendsto :
      Tendsto (fun N => ‖mpvOverlap (d := d) (A (f k1)) (A (f k1)) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A (f k1)) (hA_self (f k1))
  have hBB1_norm : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k1) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (B k1) (hB_self k1)
  have hBB2_norm : Tendsto (fun N => ‖mpvOverlap (d := d) (B k2) (B k2) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (B k2) (hB_self k2)
  have hζ1_norm : ‖ζ1‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB1_norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A (f k1)) (B := B k1) (ζ := ζ1) hmpv1)
  have hζ2_norm : ‖ζ2‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB2_norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A (f k1)) (B := B k2) (ζ := ζ2) hmpv2)
  have hζ2 : ζ2 ≠ 0 := ne_zero_of_norm_eq_one ζ2 hζ2_norm
  have hmpv_rel : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k1) σ = (ζ1 ^ N * (ζ2 ^ N)⁻¹) * mpv (B k2) σ := by
    intro N σ
    have hζ2N : ζ2 ^ N ≠ 0 := pow_ne_zero N hζ2
    calc
      mpv (B k1) σ = ζ1 ^ N * mpv (A (f k1)) σ := hmpv1 N σ
      _ = (ζ1 ^ N * (ζ2 ^ N)⁻¹) * (ζ2 ^ N * mpv (A (f k1)) σ) := by
        have : (ζ1 ^ N * (ζ2 ^ N)⁻¹) * (ζ2 ^ N * mpv (A (f k1)) σ) =
            ζ1 ^ N * mpv (A (f k1)) σ := by
          calc
            (ζ1 ^ N * (ζ2 ^ N)⁻¹) * (ζ2 ^ N * mpv (A (f k1)) σ)
                = ζ1 ^ N * ((ζ2 ^ N)⁻¹ * ζ2 ^ N) * mpv (A (f k1)) σ := by ring
            _ = ζ1 ^ N * 1 * mpv (A (f k1)) σ := by simp [inv_mul_cancel₀ hζ2N]
            _ = ζ1 ^ N * mpv (A (f k1)) σ := by ring
        exact this.symm
      _ = (ζ1 ^ N * (ζ2 ^ N)⁻¹) * mpv (B k2) σ := by
        rw [hmpv2 N σ]
  have hCross_eq : ∀ N : ℕ,
      mpvOverlap (d := d) (B k1) (B k2) N =
        (ζ1 ^ N * (ζ2 ^ N)⁻¹) * mpvOverlap (d := d) (B k2) (B k2) N := by
    intro N
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
      (A := B k1) (B := B k2) (N := N)
      (c := ζ1 ^ N * (ζ2 ^ N)⁻¹) (h := hmpv_rel N) (C := B k2)
  have hs_norm : ∀ N, ‖ζ1 ^ N * (ζ2 ^ N)⁻¹‖ = 1 := by
    intro N
    simp [norm_pow, norm_inv, hζ1_norm, hζ2_norm]
  have hCross_norm_one : Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖)
      atTop (nhds 1) :=
    tendsto_norm_mpvOverlap_one_of_scaled_self
      (d := d)
      (A := B k1) (B := B k2)
      (s := fun N => ζ1 ^ N * (ζ2 ^ N)⁻¹)
      (hSelf := hBB2_norm)
      (hs_norm := hs_norm)
      (hScale := hCross_eq)
  exact (hCross_norm_one.ne_nhds one_ne_zero) h_cross_norm_zero

private lemma leftMatching_injective_of_gaugePhaseEquiv
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (g : Fin gA → Fin gB)
    (hg_dim : ∀ j : Fin gA, dimA j = dimB (g j))
    (hg_gauge : ∀ j : Fin gA,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hg_dim j)) (A j))
        (B (g j)))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ))) :
    Function.Injective g := by
  intro j1 j2 hj
  by_contra hne
  have h_cross : Tendsto (fun N => mpvOverlap (d := d) (A j1) (A j2) N) atTop (nhds 0) :=
    hA_off j1 j2 hne
  have h_cross_norm_zero : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖)
      atTop (nhds 0) := by
    simpa only [norm_zero] using h_cross.norm
  obtain ⟨X1, ζ1, _, hX1⟩ := hg_gauge j1
  obtain ⟨X2, ζ2, _, hX2⟩ := hg_gauge j2
  have hmpvB1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B (g j1)) σ = ζ1 ^ N * mpv (A j1) σ := by
    intro N σ
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) (hg_dim j1)) (A j1))
      (B := B (g j1)) X1 ζ1 hX1 N σ,
      mpv_cast_dim (hg_dim j1) (A j1) N σ]
  have hmpvB2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B (g j1)) σ = ζ2 ^ N * mpv (A j2) σ := by
    intro N σ
    have htmp : mpv (B (g j2)) σ = ζ2 ^ N * mpv (A j2) σ := by
      rw [mpv_eq_pow_mul_of_gaugePhase
        (A := cast (congr_arg (MPSTensor d) (hg_dim j2)) (A j2))
        (B := B (g j2)) X2 ζ2 hX2 N σ,
        mpv_cast_dim (hg_dim j2) (A j2) N σ]
    exact Eq.ndrec
      (motive := fun k : Fin gB => mpv (B k) σ = ζ2 ^ N * mpv (A j2) σ)
      htmp hj.symm
  have hB_norm_tendsto :
      Tendsto (fun N => ‖mpvOverlap (d := d) (B (g j1)) (B (g j1)) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (B (g j1)) (hB_self (g j1))
  have hA1_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j1) N‖)
      atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A j1) (hA_self j1)
  have hA2_norm_tendsto : Tendsto (fun N => ‖mpvOverlap (d := d) (A j2) (A j2) N‖)
      atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A j2) (hA_self j2)
  have hζ1_norm : ‖ζ1‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hA1_norm_tendsto hB_norm_tendsto
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A j1) (B := B (g j1)) (ζ := ζ1) hmpvB1)
  have hζ2_norm : ‖ζ2‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hA2_norm_tendsto hB_norm_tendsto
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A j2) (B := B (g j1)) (ζ := ζ2) hmpvB2)
  have hζ1 : ζ1 ≠ 0 := ne_zero_of_norm_eq_one ζ1 hζ1_norm
  have hmpv_rel : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (A j1) σ = (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpv (A j2) σ := by
    intro N σ
    have hζ1N : ζ1 ^ N ≠ 0 := pow_ne_zero N hζ1
    have hInv : (ζ1 ^ N)⁻¹ * mpv (B (g j1)) σ = mpv (A j1) σ := by
      rw [hmpvB1 N σ, inv_mul_cancel_left₀ hζ1N]
    calc
      mpv (A j1) σ = (ζ1 ^ N)⁻¹ * mpv (B (g j1)) σ := hInv.symm
      _ = (ζ1 ^ N)⁻¹ * (ζ2 ^ N * mpv (A j2) σ) := by rw [hmpvB2 N σ]
      _ = (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpv (A j2) σ := by ring
  have hCross_eq : ∀ N : ℕ,
      mpvOverlap (d := d) (A j1) (A j2) N =
        (ζ2 ^ N * (ζ1 ^ N)⁻¹) * mpvOverlap (d := d) (A j2) (A j2) N := by
    intro N
    exact mpvOverlap_eq_mul_of_mpv_eq_mul (d := d)
      (A := A j1) (B := A j2) (N := N)
      (c := ζ2 ^ N * (ζ1 ^ N)⁻¹) (h := hmpv_rel N) (C := A j2)
  have hs_norm : ∀ N, ‖ζ2 ^ N * (ζ1 ^ N)⁻¹‖ = 1 := by
    intro N
    simp [norm_pow, norm_inv, hζ1_norm, hζ2_norm]
  have hCross_norm_one : Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖)
      atTop (nhds 1) :=
    tendsto_norm_mpvOverlap_one_of_scaled_self
      (d := d)
      (A := A j1) (B := A j2)
      (s := fun N => ζ2 ^ N * (ζ1 ^ N)⁻¹)
      (hSelf := hA2_norm_tendsto)
      (hs_norm := hs_norm)
      (hScale := hCross_eq)
  exact (hCross_norm_one.ne_nhds one_ne_zero) h_cross_norm_zero

private theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_rightMatching
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (f : Fin gB → Fin gA)
    (hf_inj : Function.Injective f)
    (hle_AB : gA ≤ gB)
    (hf_dim : ∀ k : Fin gB, dimA (f k) = dimB k)
    (hf_gauge : ∀ k : Fin gB,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim k)) (A (f k)))
        (B k)) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  have hle_BA : gB ≤ gA := by
    simpa only [Fintype.card_fin] using (Fintype.card_le_of_injective f hf_inj)
  have hg : gA = gB := Nat.le_antisymm hle_AB hle_BA
  have hcard : Fintype.card (Fin gB) = Fintype.card (Fin gA) := by
    simp [hg]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩
  let e : Fin gB ≃ Fin gA := Equiv.ofBijective f hf_bij
  refine ⟨hg, e.symm, ?_⟩
  intro j
  have hfe : f (e.symm j) = j :=
    Equiv.ofBijective_apply_symm_apply f hf_bij j
  have hdim : dimA j = dimB (e.symm j) := by
    simpa only [hfe] using hf_dim (e.symm j)
  refine ⟨hdim, ?_⟩
  simpa only using
    (gaugePhaseEquiv_cast_idx_left
      (A := A) (B := B) (i₁ := f (e.symm j)) (i₂ := j)
      (k := e.symm j) hfe (hf_dim (e.symm j)) (hf_gauge (e.symm j)))

end MPSTensor
