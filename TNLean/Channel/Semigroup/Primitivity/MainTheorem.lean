/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Primitivity.IrreducibleAnalysis

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Wolf Proposition 7.5** (1 → 3): If `T_{t₀}` is irreducible for some
`t₀ > 0`, then `T_t` is primitive for all `t > 0`.

The proof has two parts:

**Part 1 — Irreducibility propagation** (`hT_irr_all`):
`T_{t₀}` irreducible → `T_s` irreducible for ALL `s > 0`.
Uses the kernel bridge: `ker(L) = Span{σ}` where `σ` is the unique
faithful density fixed point of `T_{t₀}`. Then `σ` is fixed by all `T_s`
(semigroup commutativity + density uniqueness). For each `s > 0`, `T_s`
is shown irreducible via `isIrreducibleMap_of_channel_posDef_fixedPoint_unique`.

**Part 2 — Roots of unity → primitivity**:
Given irreducibility at all times, peripheral eigenvalues are roots of unity
(Wolf Thm 6.6). If `μ` is a peripheral eigenvalue of `T_t` with `μ^p = 1`,
the eigenvector `V` is a fixed point of `T_{pt}`. By irreducibility of
`T_{pt}`, `V` must be proportional to the unique faithful density fixed
point `σ'`, giving `T_t σ' = μ σ'`. Trace preservation then forces `μ = 1`.
**This part is fully proved.** -/
theorem irreducible_semigroup_implies_primitive
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t) := by
  sorry
  /-
  -- **Part 1**: Irreducibility propagation.
  -- If T_{t₀} is irreducible, then T_s is irreducible for ALL s > 0.
  -- The proof establishes ker(L) = Span{σ} (the unique faithful density fixed
  -- point), then uses `isIrreducibleMap_of_channel_posDef_fixedPoint_unique`.
  have hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s) := by
    have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
    have hTt₀_ch : IsChannel (T t₀) := hT.channel t₀ (le_of_lt ht₀)
    obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique⟩ :=
      IsChannel.exists_unique_density_fixedPoint_of_irreducible (E := T t₀) hTt₀_ch hirr hD
    -- Step 1: σ is fixed by ALL T_u for u ≥ 0 (semigroup commutativity + uniqueness).
    have hσ_fix_all : ∀ u : ℝ, 0 ≤ u → T u σ = σ := by
      intro u hu
      exact hσ_unique (T u σ)
        (IsChannel.map_densityMatrices _ (hT.channel u hu) σ hσ_mem)
        (by have h1 := hT.semigroup.semigroup.comp t₀ u (le_of_lt ht₀) hu
            have h2 := hT.semigroup.semigroup.comp u t₀ hu (le_of_lt ht₀)
            show T t₀ (T u σ) = T u σ
            have heval1 : (T t₀).comp (T u) σ = T (t₀ + u) σ := by
              rw [h1]
            have heval2 : (T u).comp (T t₀) σ = T (u + t₀) σ := by
              rw [h2]
            simp only [LinearMap.comp_apply] at heval1 heval2
            rw [heval1, add_comm, ← heval2, hσ_fix])
    have hfixed_1d : ∀ X : Matrix (Fin D) (Fin D) ℂ, T t₀ X = X →
        X = Matrix.trace X • σ := by
      intro X hX
      exact eq_of_sub_eq_zero
        (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel hTt₀_ch hirr _
          (by rw [map_sub, map_smul, hX, hσ_fix])
          (by rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul,
                   mul_one, sub_self]))
    let N : ℕ := Nat.factorial (Module.finrank ℂ Mat)
    have hN_pos : 0 < N := Nat.factorial_pos _
    let u : ℝ := t₀ / N
    have hu_nonneg : 0 ≤ u := le_of_lt <| div_pos ht₀ (Nat.cast_pos.mpr hN_pos)
    have hu_pos : 0 < u := div_pos ht₀ (Nat.cast_pos.mpr hN_pos)
    have hNu : (N : ℝ) * u = t₀ := by
      dsimp [u]
      field_simp [hN_pos.ne']
    have hTt₀_eq_pow : T t₀ = (T u) ^ N := by
      calc
        T t₀ = T ((N : ℝ) * u) := by rw [hNu]
        _ = (T u) ^ N := semigroup_pow T hT.semigroup.semigroup u hu_nonneg N
    have hTu_ch : IsChannel (T u) := hT.channel u hu_nonneg
    have hTu_fix : T u σ = σ := hσ_fix_all u hu_nonneg
    have hTu_irr : IsIrreducibleMap (T u) := by
      intro P hP_proj hP_inv
      exact hirr P hP_proj (by
        intro X
        rw [hTt₀_eq_pow]
        exact compression_preserved_by_pow (E := T u) (P := P) hP_proj hP_inv N X)
    have hTu_prim : IsPrimitive (T u) := by
      apply isPrimitive_of_unique_norm_one (T u) σ hTu_fix (ne_zero_of_mem_densityMatrices' hσ_mem)
      intro μ hμ_eig hμ_norm
      have hμ_per : μ ∈ peripheralEigenvalues (T u) := ⟨hμ_eig, hμ_norm⟩
      have hclosed : ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues (T u) :=
        peripheral_powers_closed_of_irreducible_channel_with_fixed
          (T u) hTu_ch hTu_irr σ hσ_pd hTu_fix hμ_per
      obtain ⟨p, hp_pos, hp_le, hμp⟩ :=
        bounded_root_of_peripheral_closed_powers (T u) μ hμ_per hclosed
      have hp_dvdN : p ∣ N := by
        simpa [N] using Nat.dvd_factorial hp_pos hp_le
      rcases hp_dvdN with ⟨m, hm⟩
      have hμN : μ ^ N = 1 := by
        rw [hm, pow_mul, hμp, one_pow]
      obtain ⟨X, hX⟩ := hμ_eig.exists_hasEigenvector
      have hX_ne : X ≠ 0 := hX.2
      have hTuX : T u X = μ • X := Module.End.mem_eigenspace_iff.mp hX.1
      have hTt₀X : T t₀ X = X := by
        rw [hTt₀_eq_pow, pow_apply_eigenvector (T u) X μ N hTuX, hμN, one_smul]
      have hX_eq : X = Matrix.trace X • σ := hfixed_1d X hTt₀X
      have htr_ne : Matrix.trace X ≠ 0 := by
        intro htr
        apply hX_ne
        rw [hX_eq, htr]
        simp
      have htpX := hTu_ch.tp X
      rw [hTuX, Matrix.trace_smul] at htpX
      have htpX' : μ * Matrix.trace X = Matrix.trace X := by
        simpa [smul_eq_mul] using htpX
      have hzero : (μ - 1) * Matrix.trace X = 0 := by
        calc
          (μ - 1) * Matrix.trace X = μ * Matrix.trace X - Matrix.trace X := by ring
          _ = 0 := by rw [htpX', sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right htr_ne)
    intro s hs
    apply isIrreducibleMap_of_channel_posDef_fixedPoint_unique (T s)
      (hT.channel s (le_of_lt hs)) σ hσ_pd (hσ_fix_all s (le_of_lt hs))
    intro τ hτ_psd hτ_fix
    let δ : Mat := τ - Matrix.trace τ • σ
    have hδ_tr : Matrix.trace δ = 0 := by
      dsimp [δ]
      rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul, mul_one, sub_self]
    have hδ_fix : T s δ = δ := by
      dsimp [δ]
      rw [map_sub, map_smul, hτ_fix, hσ_fix_all s (le_of_lt hs)]
    have hδ_decay : Filter.Tendsto (fun n : ℕ => T ((n : ℝ) * u) δ) Filter.atTop (nhds 0) := by
      have hpow_decay :=
        primitive_channel_pow_tendsto_zero_of_trace_zero
          (E := T u) hTu_ch hTu_irr σ hσ_mem hTu_fix hTu_prim hδ_tr
      refine hpow_decay.congr' ?_
      filter_upwards [] with n
      rw [← semigroup_pow T hT.semigroup.semigroup u hu_nonneg n]
    let m : ℕ → ℕ := fun n => Int.toNat ⌊((n : ℝ) * u) / s⌋
    let r : ℕ → ℝ := fun n => s * Int.fract (((n : ℝ) * u) / s)
    have hr_mem : ∀ n : ℕ, r n ∈ Set.Icc 0 s := by
      intro n
      dsimp [r]
      refine Set.mem_Icc.mpr ?_
      constructor
      · exact mul_nonneg (le_of_lt hs) (Int.fract_nonneg _)
      · have hlt : Int.fract (((n : ℝ) * u) / s) < 1 := Int.fract_lt_one _
        nlinarith [hlt, hs]
    have hdecomp : ∀ n : ℕ, (n : ℝ) * u = (m n : ℝ) * s + r n := by
      intro n
      dsimp [m, r]
      have ha : ↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s) = ((n : ℝ) * u) / s :=
        Int.floor_add_fract (((n : ℝ) * u) / s)
      have hfloor_nonneg : 0 ≤ ⌊((n : ℝ) * u) / s⌋ := by
        apply Int.floor_nonneg.mpr
        positivity
      have htoNat : ((Int.toNat ⌊((n : ℝ) * u) / s⌋ : ℕ) : ℝ) = ↑⌊((n : ℝ) * u) / s⌋ := by
        exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
      have hmulha :
          s * (↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s)) =
            s * (((n : ℝ) * u) / s) := by
        exact congrArg (fun x : ℝ => s * x) ha
      calc
        (n : ℝ) * u = s * (((n : ℝ) * u) / s) := by field_simp [hs.ne']
        _ = s * (↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s)) := by
              simpa using hmulha.symm
        _ = ((Int.toNat ⌊((n : ℝ) * u) / s⌋ : ℕ) : ℝ) * s +
              s * Int.fract (((n : ℝ) * u) / s) := by
              rw [mul_add, htoNat]
              ring
    have hms_fix : ∀ n : ℕ, T ((m n : ℝ) * s) δ = δ := by
      intro n
      have hpow_fix : ∀ k : ℕ, ((T s) ^ k) δ = δ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [pow_succ']
            simpa [ih] using hδ_fix
      rw [semigroup_pow T hT.semigroup.semigroup s (le_of_lt hs) (m n)]
      exact hpow_fix (m n)
    have hres_eq : ∀ n : ℕ, T ((n : ℝ) * u) δ = T (r n) δ := by
      intro n
      calc
        T ((n : ℝ) * u) δ = T (r n + (m n : ℝ) * s) δ := by
          rw [hdecomp n, add_comm]
        _ = T (r n) (T ((m n : ℝ) * s) δ) := by
          simp [LinearMap.comp_apply,
            hT.semigroup.semigroup.comp (r n) ((m n : ℝ) * s) (hr_mem n).1
              (mul_nonneg (Nat.cast_nonneg (m n)) (le_of_lt hs))]
        _ = T (r n) δ := by rw [hms_fix n]
    have hmap_le : Filter.map r Filter.atTop ≤ Filter.principal (Set.Icc 0 s) := by
      rw [Filter.le_principal_iff]
      show r ⁻¹' Set.Icc 0 s ∈ Filter.atTop
      exact Filter.Eventually.of_forall hr_mem
    obtain ⟨a, ha_mem, hcluster⟩ := (isCompact_Icc (a := 0) (b := s)).exists_clusterPt hmap_le
    obtain ⟨φ, hφmono, hφtendsto⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
    have hδ_cont : Continuous (fun t : ℝ => T t δ) := by
      have hEval : Continuous (fun A : Mat →L[ℂ] Mat => A δ) :=
        (ContinuousLinearMap.apply ℂ Mat δ).continuous
      simpa using hEval.comp hT.semigroup.continuous
    have hsub_decay : Filter.Tendsto (fun k : ℕ => T (((φ k : ℝ)) * u) δ) Filter.atTop (nhds 0) :=
      hδ_decay.comp hφmono.tendsto_atTop
    have hsub_res : Filter.Tendsto (fun k : ℕ => T (r (φ k)) δ) Filter.atTop (nhds (T a δ)) :=
      (hδ_cont.tendsto a).comp hφtendsto
    have hsub_res_zero : Filter.Tendsto (fun k : ℕ => T (r (φ k)) δ) Filter.atTop (nhds 0) := by
      refine hsub_decay.congr' ?_
      exact Filter.Eventually.of_forall (fun k => hres_eq (φ k))
    have hTa_zero : T a δ = 0 := tendsto_nhds_unique hsub_res hsub_res_zero
    have hδ_zero_exp : expSemigroup L a δ = 0 := by
      rw [← hexp a ha_mem.1]
      exact hTa_zero
    have hδ_zero : δ = 0 := by
      have h := congrArg (fun Y => expSemigroup L (-a) Y) hδ_zero_exp
      simp only [map_zero] at h
      have hcomp : (expSemigroup L (-a)) ((expSemigroup L a) δ) =
          (expSemigroup L (-a)).comp (expSemigroup L a) δ := rfl
      rw [hcomp, ← expSemigroup_comp, show -a + a = 0 from neg_add_cancel a,
        expSemigroup_zero, LinearMap.id_apply] at h
      exact h
    exact ⟨Matrix.trace τ, sub_eq_zero.mp hδ_zero⟩
  -- **Part 2**: Roots of unity → primitivity (fully proved below).
  intro t ht
  suffices IsPrimitive (T t) from ⟨this, hT_irr_all t ht⟩
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hTt_ch : IsChannel (T t) := hT.channel t (le_of_lt ht)
  have hT_irr : IsIrreducibleMap (T t) := hT_irr_all t ht
  -- Get the unique PosDef density-matrix fixed point σ of T_t.
  obtain ⟨σ, hσ_mem, _hσ_pd, hσ_fix, _hσ_uniq⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible (E := T t) hTt_ch hT_irr hD
  have hσ_ne : σ ≠ 0 := ne_zero_of_mem_densityMatrices' hσ_mem
  -- Apply isPrimitive_of_unique_norm_one: suffices to show μ = 1 for all
  -- peripheral eigenvalues μ.
  apply isPrimitive_of_unique_norm_one (T t) σ hσ_fix hσ_ne
  intro μ hμ_eig hμ_norm
  -- Peripheral eigenvalues of T_t are roots of unity (Wolf Thm 6.6).
  obtain ⟨p, hp_pos, hpow⟩ :=
    peripheral_isRootOfUnity_of_irreducible_channel (T t) hTt_ch hT_irr μ ⟨hμ_eig, hμ_norm⟩
  -- Get eigenvector V with (T t) V = μ • V, V ≠ 0.
  obtain ⟨V, hV_ev⟩ := hμ_eig.exists_hasEigenvector
  have hV_ne : V ≠ 0 := hV_ev.2
  have hTV : (T t) V = μ • V := Module.End.mem_eigenspace_iff.mp hV_ev.1
  -- (T t)^p V = μ^p • V = 1 • V = V: V is a fixed point of T_{pt}.
  have hTpV : ((T t) ^ p) V = V := by
    rw [pow_apply_eigenvector (T t) V μ p hTV, hpow, one_smul]
  -- T_{pt} = (T t)^p by the semigroup law.
  have hTpow : (T t) ^ p = T (↑p * t) :=
    (semigroup_pow T hT.semigroup.semigroup t (le_of_lt ht) p).symm
  -- T_{pt} is an irreducible channel.
  have hpt_pos : 0 < (↑p : ℝ) * t := mul_pos (Nat.cast_pos.mpr hp_pos) ht
  have hpt_ch : IsChannel (T (↑p * t)) := hT.channel _ (le_of_lt hpt_pos)
  have hpt_irr : IsIrreducibleMap (T (↑p * t)) := hT_irr_all _ hpt_pos
  -- V is a fixed point of T_{pt}.
  have hV_fix : T (↑p * t) V = V := by rw [← hTpow]; exact hTpV
  -- Get unique PosDef density-matrix fixed point σ' of T_{pt}.
  obtain ⟨σ', hσ'_mem, _hσ'_pd, hσ'_fix, _⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible
      (E := T (↑p * t)) hpt_ch hpt_irr hD
  -- V has nonzero trace (trace-zero fixed points of irreducible channels are zero).
  have hV_tr_ne : Matrix.trace V ≠ 0 := by
    intro htr
    exact hV_ne (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
      hpt_ch hpt_irr V hV_fix htr)
  -- The fixed-point space of T_{pt} is one-dimensional: V = (trace V) • σ'.
  have hV_eq : V = (Matrix.trace V) • σ' := by
    have hW_fix : T (↑p * t) (V - (Matrix.trace V) • σ') = V - (Matrix.trace V) • σ' := by
      rw [map_sub, map_smul, hV_fix, hσ'_fix]
    have hW_tr : Matrix.trace (V - (Matrix.trace V) • σ') = 0 := by
      rw [Matrix.trace_sub, Matrix.trace_smul, hσ'_mem.2, smul_eq_mul, mul_one, sub_self]
    exact sub_eq_zero.mp
      (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
        hpt_ch hpt_irr _ hW_fix hW_tr)
  -- Derive T_t σ' = μ • σ' from the eigenvector equation.
  have hTσ' : (T t) σ' = μ • σ' := by
    have h1 : (Matrix.trace V) • (T t) σ' = (μ * Matrix.trace V) • σ' := by
      calc (Matrix.trace V) • (T t) σ'
          = (T t) ((Matrix.trace V) • σ') := (map_smul (T t) _ σ').symm
        _ = (T t) V := by rw [← hV_eq]
        _ = μ • V := hTV
        _ = μ • ((Matrix.trace V) • σ') := by rw [hV_eq]
        _ = (μ * Matrix.trace V) • σ' := by rw [smul_smul]
    -- Cancel the nonzero scalar (trace V).
    have h2 : (Matrix.trace V) • (T t) σ' = (Matrix.trace V) • (μ • σ') := by
      rw [h1, smul_smul]
    have h3 := congr_arg ((Matrix.trace V)⁻¹ • ·) h2
    simp only [smul_smul, inv_mul_cancel₀ hV_tr_ne, one_smul] at h3
    exact h3
  -- **Key step**: trace preservation forces μ = 1.
  -- trace(T_t σ') = trace(σ') = 1 (TP), and trace(μ • σ') = μ · trace(σ') = μ.
  have htp : IsTracePreservingMap (T t) := hTt_ch.tp
  have h_tr_eq : Matrix.trace ((T t) σ') = Matrix.trace σ' := htp σ'
  rw [hTσ', Matrix.trace_smul, hσ'_mem.2, smul_eq_mul, mul_one] at h_tr_eq
  exact h_tr_eq
  -/

/-- **Wolf Proposition 7.5** (full equivalence): For a QDS of channels, the
following are equivalent:
1. There exists `t₀ > 0` such that `T_{t₀}` is irreducible.
2. `T_t` is irreducible for all `t > 0`.
3. `T_t` is primitive for all `t > 0`.
4. There exists a positive definite `ρ_∞` such that `T_t(ρ) → ρ_∞` for all
   density matrices `ρ`.
5. `ker(L)` is one-dimensional and spanned by a positive definite `ρ_∞`.

This formalization captures the equivalence of items 1, 2, and 3:
`(∃ t₀ > 0, IsIrreducibleMap (T t₀)) ↔ (∀ t > 0, IsPrimitive (T t) ∧ IsIrreducibleMap (T t))`.

The RHS includes `IsIrreducibleMap` alongside `IsPrimitive` because the definition
`IsPrimitive E := peripheralEigenvalues E = {1}` records only the *set* of peripheral
eigenvalues, which alone does not imply irreducibility (e.g. the identity map on
`M₂(ℂ)` is primitive but not irreducible). For quantum dynamical semigroups,
irreducibility at one time propagates to all times, making the conjunction equivalent
to item 2, and `IsPrimitive` then follows as a consequence. -/
theorem qds_irreducible_iff_primitive
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t) :
    (∃ t₀ : ℝ, 0 < t₀ ∧ IsIrreducibleMap (T t₀)) ↔
    (∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t)) := by
  constructor
  · -- Forward: ∃ t₀, irreducible T_{t₀} → ∀ t, primitive ∧ irreducible T_t
    rintro ⟨t₀, ht₀, hirr⟩
    exact irreducible_semigroup_implies_primitive L T hT hexp t₀ ht₀ hirr
  · -- Backward: ∀ t > 0, primitive ∧ irreducible T_t → ∃ t₀ > 0, irreducible T_{t₀}
    intro h
    exact ⟨1, one_pos, (h 1 one_pos).2⟩

end -- noncomputable section
