import TNLean.MPS.BNT.PermutationRigidity.NonzeroOverlap
import TNLean.MPS.Overlap.SelfOverlapAux

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

/--
**Unfaithful:** This proof transitively calls
`exists_nonzero_overlap_of_proportional_decomp` and its `_left` variant,
both of which are currently `sorry`. Documented in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.
Elimination: when the two `_overlap_*` lemmas are proved per
\#1559 Stage C, this `_core` theorem is automatically faithful (its body
is forwarding-only). -/
private theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_core
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ)
    (h_zero_of_dim_ne : ∀ {j : Fin gA} {k : Fin gB},
      dimA j ≠ dimB k →
        Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0))
    (h_zero_of_not_gauge :
      ∀ {j : Fin gA} {k : Fin gB} (hdim : dimA j = dimB k),
        ¬ GaugePhaseEquiv (d := d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B k) →
          Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0)) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  have hExistsB : ∀ k : Fin gB,
      ∃ j : Fin gA,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) :=
    exists_nonzero_overlap_of_proportional_decomp
      (A := A) (B := B) (_A_total := A_total) (_B_total := B_total)
      (_aCoeff := aCoeff) (_bCoeff := bCoeff) (_c := c)
      (_hA_decomp := hA_decomp) (_hB_decomp := hB_decomp)
      (_hProp := hProp) (_hB_self := hB_self) (_hB_off := hB_off)
  let f : Fin gB → Fin gA := fun k => (hExistsB k).choose
  have hf_spec : ∀ k : Fin gB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A (f k)) (B k) N) atTop (nhds 0) :=
    fun k => (hExistsB k).choose_spec
  have hf_dim : ∀ k : Fin gB, dimA (f k) = dimB k := by
    intro k
    exact eq_dim_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (h_nonzero := hf_spec k)
      (h_zero_of_dim_ne := fun hne => h_zero_of_dim_ne (j := f k) (k := k) hne)
  have hf_gauge : ∀ k : Fin gB,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim k)) (A (f k)))
        (B k) := by
    intro k
    exact gaugePhaseEquiv_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (hdim := hf_dim k)
      (h_nonzero := hf_spec k)
      (h_zero_of_not_gauge :=
        fun hNot => h_zero_of_not_gauge (j := f k) (k := k) (hf_dim k) hNot)
  have hf_inj : Function.Injective f :=
    rightMatching_injective_of_gaugePhaseEquiv
      (A := A) (B := B) (f := f) (hf_dim := hf_dim) (hf_gauge := hf_gauge)
      (hA_self := hA_self) (hB_self := hB_self) (hB_off := hB_off)
  have hExistsA : ∀ j : Fin gA,
      ∃ k : Fin gB,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k) N) atTop (nhds 0) :=
    exists_nonzero_overlap_of_proportional_decomp_left
      (A := A) (B := B) (_A_total := A_total) (_B_total := B_total)
      (_aCoeff := aCoeff) (_bCoeff := bCoeff) (_c := c)
      (_hA_decomp := hA_decomp) (_hB_decomp := hB_decomp)
      (_hProp := hProp) (_hA_self := hA_self) (_hA_off := hA_off)
  let g : Fin gA → Fin gB := fun j => (hExistsA j).choose
  have hg_spec : ∀ j : Fin gA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B (g j)) N) atTop (nhds 0) :=
    fun j => (hExistsA j).choose_spec
  have hg_dim : ∀ j : Fin gA, dimA j = dimB (g j) := by
    intro j
    exact eq_dim_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (h_nonzero := hg_spec j)
      (h_zero_of_dim_ne := fun hne => h_zero_of_dim_ne (j := j) (k := g j) hne)
  have hg_gauge : ∀ j : Fin gA,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hg_dim j)) (A j))
        (B (g j)) := by
    intro j
    exact gaugePhaseEquiv_of_not_tendsto_zero_mpvOverlap (A := A) (B := B)
      (hdim := hg_dim j)
      (h_nonzero := hg_spec j)
      (h_zero_of_not_gauge :=
        fun hNot => h_zero_of_not_gauge (j := j) (k := g j) (hg_dim j) hNot)
  have hg_inj : Function.Injective g :=
    leftMatching_injective_of_gaugePhaseEquiv
      (A := A) (B := B) (g := g) (hg_dim := hg_dim) (hg_gauge := hg_gauge)
      (hA_self := hA_self) (hA_off := hA_off) (hB_self := hB_self)
  have hle_AB : gA ≤ gB := by
    simpa only [Fintype.card_fin] using (Fintype.card_le_of_injective g hg_inj)
  exact exists_eq_numBlocks_and_equiv_gaugePhase_of_rightMatching
    (A := A) (B := B) (f := f) hf_inj hle_AB hf_dim hf_gauge

/--
**Permutation rigidity for basis-of-normal-tensors (BNT) decompositions, primitive branch,
paper hypothesis set.**

Two BNT-like families `A j` and `B k` with asymptotically orthonormal overlaps, together with
explicit decompositions of proportional full MPV families `A_total`, `B_total`, agree blockwise up
to a permutation, dimension equality, and gauge-phase equivalence.

In canonical-form applications the coefficient arrays are obtained after dominant-weight
normalization, so the relevant data are `(μ j / μ 0)^N` and the discarded dominant factors are
absorbed into the proportionality constant.

This is the span-equality-free analogue of
`exists_eq_numBlocks_and_equiv_gaugePhase_of_overlapOrtho`.

**Unfaithful:** Transitively `sorry` via the `_core` theorem and the two
`_overlap_*` lemmas it calls. See those for elimination plan; tracked in
\#1559 Stage C. -/
theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_inj : ∀ j, IsInjective (A j))
    (hB_inj : ∀ k, IsInjective (B k))
    (hA_norm : ∀ j, (∑ i : Fin d, (A j i)ᴴ * (A j i)) = 1)
    (hB_norm : ∀ k, (∑ i : Fin d, (B k i)ᴴ * (B k i)) = 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  classical
  refine exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_core
    (A := A) (B := B)
    (hA_self := hA_self) (hA_off := hA_off)
    (hB_self := hB_self) (hB_off := hB_off)
    (A_total := A_total) (B_total := B_total)
    (aCoeff := aCoeff) (bCoeff := bCoeff)
    (c := c)
    (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
    (hProp := hProp)
    ?_ ?_
  · intro j k hne
    exact mpvOverlap_tendsto_zero_of_dim_ne
      (A j) (B k) (hA_inj j) (hB_inj k) (hA_norm j) (hB_norm k) hne
  · intro j k hdim hNot
    exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      (hdim := hdim) (A := A j) (B := B k)
      (hA_inj := hA_inj j) (hB_inj := hB_inj k)
      (hA_norm := hA_norm j) (hB_norm := hB_norm k)
      hNot

/-- NT / irreducible version of
`exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp`.

This is the same permutation-matching argument, but the two contradiction steps that formerly
used injective overlap decay are replaced by the NT lemmas
`mpvOverlap_tendsto_zero_of_irreducible_TP` and
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`.

**Unfaithful:** Transitively `sorry` via the `_core` theorem; same
elimination plan as the public wrapper. Tracked in \#1559 Stage C. -/
theorem exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_of_irreducible_TP
    {d gA gB : ℕ}
    {dimA : Fin gA → ℕ} {dimB : Fin gB → ℕ}
    [∀ j, NeZero (dimA j)] [∀ k, NeZero (dimB k)]
    {DtotA DtotB : ℕ}
    (A : (j : Fin gA) → MPSTensor d (dimA j))
    (B : (k : Fin gB) → MPSTensor d (dimB k))
    (hA_irr : ∀ j, IsIrreducibleTensor (A j))
    (hB_irr : ∀ k, IsIrreducibleTensor (B k))
    (hA_norm : ∀ j, (∑ i : Fin d, (A j i)ᴴ * (A j i)) = 1)
    (hB_norm : ∀ k, (∑ i : Fin d, (B k i)ᴴ * (B k i)) = 1)
    (hA_self : ∀ j,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j →
      Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ k,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ k₁ k₂, k₁ ≠ k₂ →
      Tendsto (fun N => mpvOverlap (d := d) (B k₁) (B k₂) N) atTop (nhds 0))
    (A_total : MPSTensor d DtotA)
    (B_total : MPSTensor d DtotB)
    (aCoeff : ℕ → Fin gA → ℂ) (bCoeff : ℕ → Fin gB → ℂ)
    (c : ℕ → ℂ)
    (hA_decomp : ∀ N (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin gA, (aCoeff N j) * mpv (A j) σ)
    (hB_decomp : ∀ N (σ : Fin N → Fin d),
      mpv B_total σ = ∑ k : Fin gB, (bCoeff N k) * mpv (B k) σ)
    (hProp : ∀ N (σ : Fin N → Fin d), mpv A_total σ = c N * mpv B_total σ) :
    ∃ _h : gA = gB,
      ∃ perm : Fin gA ≃ Fin gB,
        ∀ j : Fin gA,
          ∃ hdim : dimA j = dimB (perm j),
            GaugePhaseEquiv (d := d)
              (cast (congr_arg (MPSTensor d) hdim) (A j))
              (B (perm j)) := by
  classical
  refine exists_eq_numBlocks_and_equiv_gaugePhase_of_proportional_decomp_core
    (A := A) (B := B)
    (hA_self := hA_self) (hA_off := hA_off)
    (hB_self := hB_self) (hB_off := hB_off)
    (A_total := A_total) (B_total := B_total)
    (aCoeff := aCoeff) (bCoeff := bCoeff)
    (c := c)
    (hA_decomp := hA_decomp) (hB_decomp := hB_decomp)
    (hProp := hProp)
    ?_ ?_
  · intro j k hne
    exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
      (A j) (B k) (hA_irr j) (hB_irr k) (hA_norm j) (hB_norm k) hne
  · intro j k hdim hNot
    exact mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      (hdim := hdim) (A := A j) (B := B k)
      (hA_irr := hA_irr j) (hB_irr := hB_irr k)
      (hA_norm := hA_norm j) (hB_norm := hB_norm k)
      hNot

end MPSTensor
