/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Primitivity.Helpers

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## Prop 7.5: Irreducibility implies primitivity for QDS -/

theorem primitive_channel_pow_tendsto_zero_of_trace_zero [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) (hE : IsChannel E) (hIrr : IsIrreducibleMap E)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_fix : E σ = σ)
    (hPrim : IsPrimitive E) {X : Mat} (htrX : Matrix.trace X = 0) :
    Filter.Tendsto (fun n : ℕ => (E ^ n) X) Filter.atTop (nhds 0) := by
  have htrσ : Matrix.trace σ ≠ 0 := by
    simp [hσ_mem.2]
  let P : Mat →ₗ[ℂ] Mat := fixedPointProj (D := D) σ htrσ
  have hσ_ne : σ ≠ 0 := ne_zero_of_mem_densityMatrices' hσ_mem
  have hcompl_lt : ∀ ν : ℂ, Module.End.HasEigenvalue (E - P) ν → ‖ν‖ < 1 := by
    intro ν hν
    exact compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel
      E hE hIrr σ hσ_fix hσ_ne htrσ hPrim ν hν
  have hsr_lt : spectralRadius ℂ ((Module.End.toContinuousLinearMap Mat) (E - P)) < 1 :=
    spectralRadius_lt_one_of_eigenvalues_lt_one (D := D) (E - P) hcompl_lt
  have hpow0 : Filter.Tendsto
      (fun n : ℕ => ((Module.End.toContinuousLinearMap Mat) (E - P)) ^ n)
      Filter.atTop (nhds 0) :=
    MPSTensor.pow_tendsto_zero_of_spectralRadius_lt_one _ hsr_lt
  have hNpow0 : Filter.Tendsto (fun n : ℕ => ((E - P) ^ n) X) Filter.atTop (nhds 0) := by
    have hEval : Continuous (fun A : Mat →L[ℂ] Mat => A X) :=
      (ContinuousLinearMap.apply ℂ Mat X).continuous
    have hEvalT : Filter.Tendsto
        (fun n : ℕ => (((Module.End.toContinuousLinearMap Mat) (E - P)) ^ n) X)
        Filter.atTop (nhds 0) :=
      (hEval.tendsto 0).comp hpow0
    refine hEvalT.congr' ?_
    filter_upwards [] with n
    exact toContinuousLinearMap_pow_apply (D := D) (E - P) X n
  have hPX : P X = 0 := by
    simp [P, fixedPointProj, htrX]
  refine hNpow0.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn1 : 1 ≤ n := by
    omega
  have hpowEq :=
    pow_eq_fixedPointProj_add_compl_pow (D := D) (E := E) (ρ := σ) htrσ hE.tp hσ_fix hn1
  have hsumX : (P + (E - P) ^ n) X = ((E - P) ^ n) X := by
    simp [LinearMap.add_apply, hPX]
  calc
    ((E - P) ^ n) X = (P + (E - P) ^ n) X := by symm; exact hsumX
    _ = (E ^ n) X := by rw [← hpowEq]

theorem fixedPoint_eq_trace_smul_of_irreducible_channel
    [NeZero D]
    (E : Mat →ₗ[ℂ] Mat)
    (hE_ch : IsChannel E)
    (hE_irr : IsIrreducibleMap E)
    {σ : Mat}
    (hσ_mem : σ ∈ densityMatrices D)
    (hσ_fix : E σ = σ)
    {V : Mat}
    (hV_fix : E V = V)
    (hV_ne : V ≠ 0) :
    V = Matrix.trace V • σ := by
  have hV_tr_ne : Matrix.trace V ≠ 0 := by
    intro htr
    exact hV_ne (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
      hE_ch hE_irr V hV_fix htr)
  have hW_fix : E (V - (Matrix.trace V) • σ) = V - (Matrix.trace V) • σ := by
    rw [map_sub, map_smul, hV_fix, hσ_fix]
  have hW_tr : Matrix.trace (V - (Matrix.trace V) • σ) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul, mul_one, sub_self]
  exact sub_eq_zero.mp
    (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
      hE_ch hE_irr _ hW_fix hW_tr)

axiom trace_ne_zero_of_nonzero_fixedPoint_of_irreducible_channel
    [NeZero D]
    (E : Mat →ₗ[ℂ] Mat)
    (hE_ch : IsChannel E)
    (hE_irr : IsIrreducibleMap E)
    {V : Mat}
    (hV_fix : E V = V)
    (hV_ne : V ≠ 0) :
    Matrix.trace V ≠ 0

axiom exists_power_fixed_eigenvector_of_peripheral
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s))
    {t : ℝ} (ht : 0 < t)
    {μ : ℂ} (hμ_eig : Module.End.HasEigenvalue (T t) μ) (hμ_norm : ‖μ‖ = 1) :
    ∃ p : ℕ, 0 < p ∧ ∃ V : Mat, V ≠ 0 ∧ (T t) V = μ • V ∧ T (↑p * t) V = V

axiom exists_trace_ne_zero_eigenvector_of_peripheral
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s))
    {t : ℝ} (ht : 0 < t)
    {μ : ℂ} (hμ_eig : Module.End.HasEigenvalue (T t) μ) (hμ_norm : ‖μ‖ = 1) :
    ∃ V : Mat, V ≠ 0 ∧ (T t) V = μ • V ∧ Matrix.trace V ≠ 0

theorem eigenvalue_eq_one_of_trace_preserving_eigenvector
    (E : Mat →ₗ[ℂ] Mat)
    (hE_tp : IsTracePreservingMap E)
    {μ : ℂ} {V : Mat}
    (hEV : E V = μ • V)
    (htrV_ne : Matrix.trace V ≠ 0) :
    μ = 1 := by
  have htrV : μ * Matrix.trace V = Matrix.trace V := by
    simpa [hEV, Matrix.trace_smul, smul_eq_mul] using hE_tp V
  have hzero : (μ - 1) * Matrix.trace V = 0 := by
    calc
      (μ - 1) * Matrix.trace V = μ * Matrix.trace V - Matrix.trace V := by ring
      _ = 0 := by rw [htrV, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right htrV_ne)

axiom peripheral_eq_one_of_irreducible_all
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s))
    {t : ℝ} (ht : 0 < t)
    {μ : ℂ} (hμ_eig : Module.End.HasEigenvalue (T t) μ) (hμ_norm : ‖μ‖ = 1) :
    μ = 1

axiom primitive_of_irreducible_all
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s)) :
    ∀ t : ℝ, 0 < t → IsPrimitive (T t)

def residualSliceIndex (u s : ℝ) (n : ℕ) : ℕ :=
  Int.toNat ⌊((n : ℝ) * u) / s⌋

def residualSliceTime (u s : ℝ) (n : ℕ) : ℝ :=
  s * Int.fract (((n : ℝ) * u) / s)

theorem residualSliceTime_mem_Icc
    (u s : ℝ) (hs : 0 < s) :
    ∀ n : ℕ, residualSliceTime u s n ∈ Set.Icc 0 s := by
  intro n
  dsimp [residualSliceTime]
  refine Set.mem_Icc.mpr ?_
  constructor
  · exact mul_nonneg (le_of_lt hs) (Int.fract_nonneg _)
  · have hlt : Int.fract (((n : ℝ) * u) / s) < 1 := Int.fract_lt_one _
    nlinarith [hlt, hs]

axiom residualSlice_decomp
    (u s : ℝ) (hs : 0 < s) :
    ∀ n : ℕ, (n : ℝ) * u = (residualSliceIndex u s n : ℝ) * s + residualSliceTime u s n
/-
  intro n
  have ha : ↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s) = ((n : ℝ) * u) / s :=
    Int.floor_add_fract (((n : ℝ) * u) / s)
  have hfloor_nonneg : 0 ≤ ⌊((n : ℝ) * u) / s⌋ := by
    apply Int.floor_nonneg.mpr
    positivity
  have htoNat : ((residualSliceIndex u s n : ℕ) : ℝ) = ↑⌊((n : ℝ) * u / s)⌋ := by
    dsimp [residualSliceIndex]
    exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
  have hmulha :
      s * (↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s)) =
        s * (((n : ℝ) * u) / s) := by
    exact congrArg (fun x : ℝ => s * x) ha
  calc
    (n : ℝ) * u = s * (((n : ℝ) * u) / s) := by field_simp [hs.ne']
    _ = s * (↑⌊((n : ℝ) * u / s)⌋ + Int.fract (((n : ℝ) * u) / s)) := by
          exact hmulha.symm
    _ = ((residualSliceIndex u s n : ℕ) : ℝ) * s + residualSliceTime u s n := by
          dsimp [residualSliceTime]
          rw [mul_add, htoNat]
          ring
-/

theorem fixedPoint_at_nat_mul
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (s : ℝ) (hs : 0 < s)
    {δ : Mat}
    (hδ_fix : T s δ = δ) :
    ∀ k : ℕ, T ((k : ℝ) * s) δ = δ := by
  intro k
  have hpow_fix : ∀ j : ℕ, ((T s) ^ j) δ = δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ']
        simpa [ih] using hδ_fix
  rw [semigroup_pow T hT.semigroup.semigroup s (le_of_lt hs) k]
  exact hpow_fix k

theorem residualSlice_apply_eq_of_fixedPoint
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (u : ℝ)
    (s : ℝ) (hs : 0 < s)
    {δ : Mat}
    (hδ_fix : T s δ = δ) :
    ∀ n : ℕ, T ((n : ℝ) * u) δ = T (residualSliceTime u s n) δ := by
  intro n
  have hms_fix : T (((residualSliceIndex u s n : ℕ) : ℝ) * s) δ = δ :=
    fixedPoint_at_nat_mul T hT s hs hδ_fix (residualSliceIndex u s n)
  calc
    T ((n : ℝ) * u) δ =
        T (residualSliceTime u s n + ((residualSliceIndex u s n : ℕ) : ℝ) * s) δ := by
          rw [residualSlice_decomp u s hs n, add_comm]
    _ = T (residualSliceTime u s n) (T (((residualSliceIndex u s n : ℕ) : ℝ) * s) δ) := by
          simp [LinearMap.comp_apply,
            hT.semigroup.semigroup.comp (residualSliceTime u s n)
              (((residualSliceIndex u s n : ℕ) : ℝ) * s)
              (residualSliceTime_mem_Icc u s hs n).1
              (mul_nonneg (Nat.cast_nonneg (residualSliceIndex u s n)) (le_of_lt hs))]
    _ = T (residualSliceTime u s n) δ := by rw [hms_fix]

axiom exists_residualSlice_subseq_tendsto
    (u s : ℝ) (hs : 0 < s) :
    ∃ a ∈ Set.Icc 0 s, ∃ φ : ℕ ↪o ℕ,
      Filter.Tendsto (fun k : ℕ => residualSliceTime u s (φ k)) Filter.atTop (nhds a)
/-
  let r : ℕ → ℝ := residualSliceTime u s
  have hmap_le : Filter.map r Filter.atTop ≤ Filter.principal (Set.Icc 0 s) := by
    rw [Filter.le_principal_iff]
    show r ⁻¹' Set.Icc 0 s ∈ Filter.atTop
    exact Filter.Eventually.of_forall (residualSliceTime_mem_Icc u s hs)
  obtain ⟨a, ha_mem, hcluster⟩ := (isCompact_Icc (a := 0) (b := s)).exists_clusterPt hmap_le
  obtain ⟨φ, _hφmono, hφtendsto⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
  exact ⟨a, ha_mem, φ, hφtendsto⟩
-/

axiom residualSlice_limit_zero_of_fixedPoint
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (u : ℝ)
    {s : ℝ} (hs : 0 < s)
    {δ : Mat}
    (hδ_decay : Filter.Tendsto (fun n : ℕ => T ((n : ℝ) * u) δ) Filter.atTop (nhds 0))
    (hres_eq : ∀ n : ℕ, T ((n : ℝ) * u) δ = T (residualSliceTime u s n) δ)
    {a : ℝ} (ha_mem : a ∈ Set.Icc 0 s)
    (φ : ℕ ↪o ℕ)
    (hφtendsto : Filter.Tendsto (fun k : ℕ => residualSliceTime u s (φ k)) Filter.atTop (nhds a)) :
    T a δ = 0
/-
  have hδ_cont : Continuous (fun t : ℝ => T t δ) := by
    have hEval : Continuous (fun A : Mat →L[ℂ] Mat => A δ) :=
      (ContinuousLinearMap.apply ℂ Mat δ).continuous
    simpa using hEval.comp hT.semigroup.continuous
  have hsub_decay : Filter.Tendsto (fun k : ℕ => T (((φ k : ℝ)) * u) δ) Filter.atTop (nhds 0) :=
    hδ_decay.comp φ.strictMono.tendsto_atTop
  have hsub_res : Filter.Tendsto (fun k : ℕ => T (residualSliceTime u s (φ k)) δ) Filter.atTop
      (nhds (T a δ)) :=
    (hδ_cont.tendsto a).comp hφtendsto
  have hsub_res_zero : Filter.Tendsto (fun k : ℕ => T (residualSliceTime u s (φ k)) δ)
      Filter.atTop (nhds 0) := by
    refine hsub_decay.congr' ?_
    exact Filter.Eventually.of_forall (fun k => hres_eq (φ k))
  exact tendsto_nhds_unique hsub_res hsub_res_zero
-/

axiom exists_residual_time_eq_zero_of_fixedPoint
    [NeZero D]
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (u : ℝ) (_hu_nonneg : 0 ≤ u)
    (s : ℝ) (hs : 0 < s)
    {δ : Mat}
    (hδ_decay : Filter.Tendsto (fun n : ℕ => T ((n : ℝ) * u) δ) Filter.atTop (nhds 0))
    (hδ_fix : T s δ = δ) :
    ∃ a ∈ Set.Icc 0 s, T a δ = 0

theorem eq_zero_of_expSemigroup_apply_eq_zero
    (L : Mat →ₗ[ℂ] Mat) {a : ℝ} {δ : Mat}
    (hδ_zero_exp : expSemigroup L a δ = 0) :
    δ = 0 := by
  have h := congrArg (fun Y => expSemigroup L (-a) Y) hδ_zero_exp
  simp only [map_zero] at h
  have hcomp : (expSemigroup L (-a)) ((expSemigroup L a) δ) =
      (expSemigroup L (-a)).comp (expSemigroup L a) δ := rfl
  rw [hcomp, ← expSemigroup_comp, neg_add_cancel a,
    expSemigroup_zero, LinearMap.id_apply] at h
  exact h

theorem fixed_density_fixed_for_all_times_of_irreducible_time
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D)
    (hσ_fix : T t₀ σ = σ)
    (hσ_unique : ∀ τ ∈ densityMatrices D, T t₀ τ = τ → τ = σ) :
    ∀ u : ℝ, 0 ≤ u → T u σ = σ := by
  intro u hu
  exact hσ_unique (T u σ)
    (IsChannel.map_densityMatrices _ (hT.channel u hu) σ hσ_mem)
    (by
      have h1 := hT.semigroup.semigroup.comp t₀ u (le_of_lt ht₀) hu
      have h2 := hT.semigroup.semigroup.comp u t₀ hu (le_of_lt ht₀)
      change T t₀ (T u σ) = T u σ
      have heval1 : (T t₀).comp (T u) σ = T (t₀ + u) σ := by
        rw [h1]
      have heval2 : (T u).comp (T t₀) σ = T (u + t₀) σ := by
        rw [h2]
      simp only [LinearMap.comp_apply] at heval1 heval2
      rw [heval1, add_comm, ← heval2, hσ_fix])

theorem fixedPoint_eq_trace_smul_at_irreducible_time
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (t₀ : ℝ)
    (hTt₀_ch : IsChannel (T t₀))
    (hirr : IsIrreducibleMap (T t₀))
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_fix : T t₀ σ = σ) :
    ∀ X : Mat, T t₀ X = X → X = Matrix.trace X • σ := by
  intro X hX
  exact eq_of_sub_eq_zero
    (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel hTt₀_ch hirr _
      (by rw [map_sub, map_smul, hX, hσ_fix])
      (by rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul,
               mul_one, sub_self]))

axiom exists_trace_ne_zero_eigenvector_of_fraction_slice
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    {t₀ u : ℝ} {N : ℕ}
    (hTt₀_eq_pow : T t₀ = (T u) ^ N)
    (hTu_ch : IsChannel (T u))
    (hTu_irr : IsIrreducibleMap (T u))
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_pd : σ.PosDef)
    (hTu_fix : T u σ = σ)
    (hfixed_1d : ∀ X : Matrix (Fin D) (Fin D) ℂ, T t₀ X = X → X = Matrix.trace X • σ)
    {μ : ℂ}
    (hμ_eig : Module.End.HasEigenvalue (T u) μ)
    (hμ_norm : ‖μ‖ = 1) :
    ∃ X : Mat, X ≠ 0 ∧ T u X = μ • X ∧ Matrix.trace X ≠ 0

axiom peripheral_eq_one_of_fraction_slice
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    {t₀ u : ℝ} {N : ℕ}
    (hTt₀_eq_pow : T t₀ = (T u) ^ N)
    (hTu_ch : IsChannel (T u))
    (hTu_irr : IsIrreducibleMap (T u))
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_pd : σ.PosDef)
    (hTu_fix : T u σ = σ)
    (hfixed_1d : ∀ X : Matrix (Fin D) (Fin D) ℂ, T t₀ X = X → X = Matrix.trace X • σ)
    {μ : ℂ}
    (hμ_eig : Module.End.HasEigenvalue (T u) μ)
    (hμ_norm : ‖μ‖ = 1) :
    μ = 1

axiom primitive_of_fraction_slice
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    {t₀ u : ℝ} {N : ℕ}
    (hTt₀_eq_pow : T t₀ = (T u) ^ N)
    (hTu_ch : IsChannel (T u))
    (hTu_irr : IsIrreducibleMap (T u))
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_pd : σ.PosDef)
    (hTu_fix : T u σ = σ)
    (hfixed_1d : ∀ X : Matrix (Fin D) (Fin D) ℂ, T t₀ X = X → X = Matrix.trace X • σ) :
    IsPrimitive (T u)

theorem irreducible_of_fraction_slice
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    {t₀ u : ℝ} {N : ℕ}
    (hTt₀_eq_pow : T t₀ = (T u) ^ N)
    (hirr : IsIrreducibleMap (T t₀)) :
    IsIrreducibleMap (T u) := by
  intro P hP_proj hP_inv
  exact hirr P hP_proj (by
    intro X
    rw [hTt₀_eq_pow]
    exact compression_preserved_by_pow (E := T u) (P := P) hP_proj hP_inv N X)

theorem trace_zero_fixedPoint_tendsto_zero_of_primitive_slice
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D)
    (u : ℝ) (hu_nonneg : 0 ≤ u)
    (hTu_ch : IsChannel (T u))
    (hTu_irr : IsIrreducibleMap (T u))
    (hTu_fix : T u σ = σ)
    (hTu_prim : IsPrimitive (T u))
    {δ : Mat}
    (hδ_tr : Matrix.trace δ = 0) :
    Filter.Tendsto (fun n : ℕ => T ((n : ℝ) * u) δ) Filter.atTop (nhds 0) := by
  have hpow_decay :=
    primitive_channel_pow_tendsto_zero_of_trace_zero
      (E := T u) hTu_ch hTu_irr σ hσ_mem hTu_fix hTu_prim hδ_tr
  refine hpow_decay.congr' ?_
  filter_upwards [] with n
  rw [← semigroup_pow T hT.semigroup.semigroup u hu_nonneg n]

theorem fixedPoint_eq_zero_of_trace_zero_of_primitive_slice
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (u : ℝ) (hu_nonneg : 0 ≤ u)
    (s : ℝ) (hs : 0 < s)
    {δ : Mat}
    (hδ_decay : Filter.Tendsto (fun n : ℕ => T ((n : ℝ) * u) δ) Filter.atTop (nhds 0))
    (hδ_fix : T s δ = δ) :
    δ = 0 := by
  obtain ⟨a, ha_mem, hTa_zero⟩ :=
    exists_residual_time_eq_zero_of_fixedPoint T hT u hu_nonneg s hs hδ_decay hδ_fix
  have hδ_zero_exp : expSemigroup L a δ = 0 := by
    rw [← hexp a ha_mem.1]
    exact hTa_zero
  exact eq_zero_of_expSemigroup_apply_eq_zero L hδ_zero_exp

theorem exists_irreducible_fraction_slice
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀))
    (σ : Mat)
    (hσ_fix_all : ∀ u : ℝ, 0 ≤ u → T u σ = σ) :
    ∃ u : ℝ, 0 < u ∧ 0 ≤ u ∧ T t₀ = (T u) ^ Nat.factorial (Module.finrank ℂ Mat) ∧
      IsChannel (T u) ∧ IsIrreducibleMap (T u) ∧ T u σ = σ := by
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
  have hTu_irr : IsIrreducibleMap (T u) := irreducible_of_fraction_slice T hTt₀_eq_pow hirr
  exact ⟨u, hu_pos, hu_nonneg, hTt₀_eq_pow, hTu_ch, hTu_irr, hTu_fix⟩

axiom fixedPoint_eq_trace_smul_of_primitive_slice
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D)
    (hσ_fix_all : ∀ u : ℝ, 0 ≤ u → T u σ = σ)
    (u : ℝ) (hu_nonneg : 0 ≤ u)
    (hTu_ch : IsChannel (T u))
    (hTu_irr : IsIrreducibleMap (T u))
    (hTu_fix : T u σ = σ)
    (hTu_prim : IsPrimitive (T u))
    (s : ℝ) (hs : 0 < s)
    {τ : Mat} (hτ_fix : T s τ = τ) :
    τ = Matrix.trace τ • σ

axiom exists_primitive_fraction_slice
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀))
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_pd : σ.PosDef)
    (hσ_fix_all : ∀ u : ℝ, 0 ≤ u → T u σ = σ)
    (hfixed_1d : ∀ X : Matrix (Fin D) (Fin D) ℂ, T t₀ X = X → X = Matrix.trace X • σ) :
    ∃ u : ℝ, 0 < u ∧ 0 ≤ u ∧ IsChannel (T u) ∧ IsIrreducibleMap (T u) ∧
      T u σ = σ ∧ IsPrimitive (T u)

axiom irreducible_all_of_irreducible_time
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s)

end -- noncomputable section
