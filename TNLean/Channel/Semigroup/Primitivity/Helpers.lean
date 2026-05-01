/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Primitivity.Basic

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal TNOperatorSpace
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

local instance : ContinuousSMul ℝ ℂ := TNOperatorSpace.complexContinuousSMulReal

local instance : ContinuousSMul ℝ Mat :=
  TNOperatorSpace.matrixContinuousSMulReal (n := Fin D)

local instance : IsScalarTower ℝ ℂ Mat :=
  TNOperatorSpace.matrixScalarTowerRealComplex (n := Fin D)

/-! ## Auxiliary lemmas for the primitivity proof -/

/-- Semigroup iteration: `T (n * t) = (T t) ^ n` for nonneg `t`. -/
theorem semigroup_pow
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hS : IsDynSemigroup T) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    T (↑n * t) = (T t) ^ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    change T 0 = LinearMap.id
    exact hS.zero
  | succ n ih =>
    have hnt : 0 ≤ (↑n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
    have hcast : (↑(n + 1) : ℝ) * t = ↑n * t + t := by push_cast; ring
    have hcomp := hS.comp (↑n * t) t hnt ht
    rw [hcast, hcomp, ih]
    exact (pow_succ (T t) n).symm

/-- Eigenvector equation for powers of a linear map: if `f v = μ • v` then
`(f ^ n) v = μ ^ n • v`. -/
theorem pow_apply_eigenvector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (v : V) (μ : ℂ) (n : ℕ) (hv : f v = μ • v) :
    (f ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp [pow_zero]
  | succ n ih =>
    have hstep : (f ^ (n + 1)) v = (f ^ n) (f v) := by
      change (f ^ n * f) v = (f ^ n) (f v)
      rfl
    rw [hstep, hv, map_smul, ih, smul_smul, pow_succ']

/-- A density matrix is nonzero. -/
lemma ne_zero_of_mem_densityMatrices' {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ ∈ densityMatrices D) : ρ ≠ 0 := by
  intro h; subst h
  simp [mem_densityMatrices, Matrix.trace_zero (Fin D) ℂ] at hρ

/-- If a compression is preserved by a linear map, then it is preserved by every power. -/
theorem compression_preserved_by_pow
    (E : Mat →ₗ[ℂ] Mat) (P : Mat) (hP : IsOrthogonalProjection P)
    (hInv : ∀ X : Mat, P * E (P * X * P) * P = E (P * X * P)) :
    ∀ n : ℕ, ∀ X : Mat, P * (E ^ n) (P * X * P) * P = (E ^ n) (P * X * P) := by
  intro n
  induction n with
  | zero =>
      intro X
      rw [pow_zero]
      calc
        P * (P * X * P) * P = ((P * P) * X) * (P * P) := by
          simp [Matrix.mul_assoc]
        _ = P * X * P := by
          simp [Matrix.mul_assoc, hP.2]
  | succ n ih =>
      intro X
      rw [pow_succ']
      change P * E ((E ^ n) (P * X * P)) * P = E ((E ^ n) (P * X * P))
      rw [← ih X]
      exact hInv ((E ^ n) (P * X * P))

/-- A genuine eigenvector of the generator stays an eigenvector for the whole semigroup. -/
theorem expSemigroup_apply_eigenvector
    (L : Mat →ₗ[ℂ] Mat) (X : Mat) (μ : ℂ)
    (hX : L X = μ • X) (t : ℝ) :
    expSemigroup L t X = Complex.exp ((t : ℂ) * μ) • X := by
  letI : IsScalarTower ℝ ℂ Mat := by infer_instance
  let c : ℝ → ℂ := fun u => Complex.exp (-((u : ℂ) * μ))
  let g : ℝ → Matrix (Fin D) (Fin D) ℂ := fun u => expSemigroup L u X
  let f : ℝ → Matrix (Fin D) (Fin D) ℂ := fun u => c u • g u
  have hsmul_deriv (u : ℝ) (hc : HasDerivAt c (-(c u * μ)) u)
      (hg : HasDerivAt g (μ • g u) u) :
      HasDerivAt f (c u • (μ • g u) + (-(c u * μ)) • g u) u := by
    have h :
        HasDerivAt (c • g) (c u • (μ • g u) + (-(c u * μ)) • g u) u :=
      @HasDerivAt.smul ℝ _ Mat _ _ g (μ • g u) u ℂ _ _ _ _
        (TNOperatorSpace.matrixScalarTowerRealComplex (n := Fin D)) c (-(c u * μ)) hc hg
    simpa [f, c, g] using h
  have hdiff : Differentiable ℝ f := by
    intro u
    have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * μ) ((1 : ℂ) * μ) u :=
      (Complex.ofRealCLM.hasDerivAt.mul_const μ)
    have hc : HasDerivAt c (-(c u * μ)) u := by
      dsimp [c]
      simpa using (Complex.hasDerivAt_exp (-((u : ℂ) * μ))).comp u hmul.neg
    have hg : HasDerivAt g (μ • g u) u := by
      dsimp [g]
      simpa [hX, smul_smul, mul_assoc] using hasDerivAt_expSemigroup_apply (D := D) L X u
    have hf := hsmul_deriv u hc hg
    simpa [f, c, g] using hf.differentiableAt
  have hderiv : ∀ u : ℝ, deriv f u = 0 := by
    intro u
    have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * μ) ((1 : ℂ) * μ) u :=
      (Complex.ofRealCLM.hasDerivAt.mul_const μ)
    have hc : HasDerivAt c (-(c u * μ)) u := by
      dsimp [c]
      simpa using (Complex.hasDerivAt_exp (-((u : ℂ) * μ))).comp u hmul.neg
    have hg : HasDerivAt g (μ • g u) u := by
      dsimp [g]
      simpa [hX, smul_smul, mul_assoc] using hasDerivAt_expSemigroup_apply (D := D) L X u
    have hf := hsmul_deriv u hc hg
    have hz : c u • (μ • g u) + (-(c u * μ)) • g u = 0 := by
      calc
        c u • (μ • g u) + (-(c u * μ)) • g u
            = (c u * μ) • g u + (-(c u * μ)) • g u := by
                simp [smul_smul]
        _ = 0 := by
              rw [neg_smul]
              exact add_neg_cancel ((c u * μ) • g u)
    simpa [hz, smul_smul, mul_assoc] using hf.deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv 0 t
  have hft0 : f 0 = X := by
    simp [f, c, g, expSemigroup_zero]
  have hfteq : f t = X := by
    calc
      f t = f 0 := by simpa using hconst.symm
      _ = X := hft0
  have hct_ne : c t ≠ 0 := by
    dsimp [c]
    exact Complex.exp_ne_zero _
  have hmain : c t • expSemigroup L t X = c t • (Complex.exp ((t : ℂ) * μ) • X) := by
    calc
      c t • expSemigroup L t X = f t := by rfl
      _ = X := hfteq
      _ = c t • (Complex.exp ((t : ℂ) * μ) • X) := by
        dsimp [c]
        rw [smul_smul]
        have : Complex.exp (-((t : ℂ) * μ)) * Complex.exp ((t : ℂ) * μ) = 1 := by
          rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
        rw [this, one_smul]
  have hcancel := congrArg ((c t)⁻¹ • ·) hmain
  simpa [c, smul_smul, inv_mul_cancel₀ hct_ne, one_smul,
    mul_comm, mul_left_comm, mul_assoc] using hcancel

/-- The peripheral spectrum of an irreducible finite-dimensional channel has cardinality at most
`dim(Mat)`.

This is proved by choosing one nonzero eigenvector for each peripheral eigenvalue and using the
linear independence of eigenvectors corresponding to distinct eigenvalues. -/
theorem peripheral_card_le_finrank [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) :
    (peripheralEigenvalues_finite E).toFinset.card ≤ Module.finrank ℂ Mat := by
  classical
  let hfin := peripheralEigenvalues_finite E
  letI : Fintype ↥(peripheralEigenvalues E) := Set.Finite.fintype hfin
  let xs : ↥(peripheralEigenvalues E) → Mat :=
    fun μ => Classical.choose (μ.2.1.exists_hasEigenvector)
  have hxs : ∀ μ : ↥(peripheralEigenvalues E), Module.End.HasEigenvector E (μ : ℂ) (xs μ) := by
    intro μ
    exact Classical.choose_spec (μ.2.1.exists_hasEigenvector)
  have hlin : LinearIndependent ℂ xs :=
    Module.End.eigenvectors_linearIndependent E (peripheralEigenvalues E) xs hxs
  rw [Set.Finite.card_toFinset hfin]
  simpa using LinearIndependent.fintype_card_le_finrank (R := ℂ) (M := Mat) hlin

/-- If peripheral powers are all again peripheral, then the order of a peripheral eigenvalue is
bounded by the dimension of the matrix space.

This is the finite-dimensional pigeonhole step used to force a common period at a divisor time.
The remaining input needed in the main proof is the closure of peripheral eigenvalues under powers
for the chosen irreducible time slice. -/
theorem bounded_root_of_peripheral_closed_powers [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) (μ : ℂ) (hμ : μ ∈ peripheralEigenvalues E)
    (hclosed : ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues E) :
    ∃ p : ℕ, 0 < p ∧ p ≤ Module.finrank ℂ Mat ∧ μ ^ p = 1 := by
  classical
  let N := Module.finrank ℂ Mat
  let hfin := peripheralEigenvalues_finite E
  letI : Fintype ↥(peripheralEigenvalues E) := Set.Finite.fintype hfin
  let f : Fin (N + 1) → ↥(peripheralEigenvalues E) :=
    fun n => ⟨μ ^ (n : ℕ), hclosed n⟩
  have hnotinj : ¬ Function.Injective f := by
    intro hf
    have hle1 : Fintype.card (Fin (N + 1)) ≤ Fintype.card ↥(peripheralEigenvalues E) :=
      Fintype.card_le_of_injective f hf
    have hle2 : Fintype.card ↥(peripheralEigenvalues E) ≤ N := by
      simpa [N] using peripheral_card_le_finrank E
    have : N + 1 ≤ N := by
      simpa [Fintype.card_fin] using le_trans hle1 hle2
    omega
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨a, b, hab, hne⟩ := hnotinj
  have hab' : μ ^ (a : ℕ) = μ ^ (b : ℕ) := congrArg Subtype.val hab
  have hab_ne : (a : ℕ) ≠ b := by
    intro h
    apply hne
    exact Fin.ext h
  rcases Nat.lt_or_gt_of_ne hab_ne with hlt | hgt
  · refine ⟨(b : ℕ) - (a : ℕ), Nat.sub_pos_of_lt hlt, ?_, ?_⟩
    · exact Nat.sub_le _ _ |>.trans (Nat.le_of_lt_succ b.2)
    · have hμ_ne : μ ≠ 0 := ne_zero_of_norm_eq_one hμ.2
      exact mul_left_cancel₀ (pow_ne_zero _ hμ_ne) (by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
        exact hab'.symm)
  · refine ⟨(a : ℕ) - (b : ℕ), Nat.sub_pos_of_lt hgt, ?_, ?_⟩
    · exact Nat.sub_le _ _ |>.trans (Nat.le_of_lt_succ a.2)
    · have hμ_ne : μ ≠ 0 := ne_zero_of_norm_eq_one hμ.2
      exact mul_left_cancel₀ (pow_ne_zero _ hμ_ne) (by
        rw [← pow_add, Nat.add_sub_cancel' hgt.le, mul_one]
        exact hab')

/-- Power-closure auxiliary lemma at an irreducible time slice.

After conjugating by the square root of a positive-definite fixed point, the
irreducible channel becomes unital with an adjoint fixed point, so Wolf's
peripheral-power closure theorem applies to the gauged Kraus family.

This is a purely channel-level lemma: its hypotheses mention one channel with a
positive-definite fixed point and do not use continuous-time propagation or
generator kernels. -/
theorem peripheral_powers_closed_of_irreducible_channel_with_fixed [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) (hE : IsChannel E) (hIrr : IsIrreducibleMap E)
    (σ : Mat) (hσ_pd : σ.PosDef) (hσ_fix : E σ = σ)
    {μ : ℂ} (hμ : μ ∈ peripheralEigenvalues E) :
    ∀ n : ℕ, μ ^ n ∈ peripheralEigenvalues E := by
  classical
  -- ── Step 1: Kraus representation ──
  obtain ⟨r, K, hK⟩ := hE.cp
  have hE_eq : E = MPSTensor.transferMap (d := r) (D := D) K :=
    LinearMap.ext fun X => by simpa [MPSTensor.transferMap_apply] using hK X
  have hK_tp : ∑ i : Fin r, (K i)ᴴ * K i = 1 :=
    kraus_sum_conjTranspose_mul_of_tp K E hK hE.tp
  -- ── Step 2: Square root S = CFC.sqrt σ ──
  let S : Mat := CFC.sqrt σ
  have hS_herm : Sᴴ = S := MPSTensor.conjTranspose_cfc_sqrt (D := D) σ
  have hS_sq : S * S = σ := MPSTensor.cfc_sqrt_mul_self_of_posDef (D := D) σ hσ_pd
  have hS_det : S.det ≠ 0 :=
    (MPSTensor.isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ_pd).ne_zero
  have hSmul : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S (Ne.isUnit hS_det)
  have hSinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S (Ne.isUnit hS_det)
  have hSinv_herm : (S⁻¹)ᴴ = S⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hS_herm]
  -- ── Step 3: Gauged operators L_i = S⁻¹ K_i S ──
  let L : Fin r → Mat := fun i => S⁻¹ * K i * S
  -- ── Step 4: L is unital (∑ L_i L_i† = 1) ──
  have hL_unital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) L := by
    change ∑ i : Fin r, L i * (L i)ᴴ = 1
    exact gauged_unital K S σ hS_det (by rw [hS_herm]; exact hS_sq)
      (by rw [← hE_eq]; exact hσ_fix)
  -- ── Step 5: Kraus.adjointMap L σ = σ ──
  have hL_adj : Kraus.adjointMap L σ = σ := by
    simp only [Kraus.adjointMap_apply, L]
    -- Rewrite conjTranspose of each L_i
    have hconj : ∀ i : Fin r, (S⁻¹ * K i * S)ᴴ = S * (K i)ᴴ * S⁻¹ := by
      intro i
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSinv_herm, hS_herm,
          Matrix.mul_assoc]
    simp_rw [hconj]
    -- S⁻¹ * σ * S⁻¹ = 1
    have hcancel : S⁻¹ * σ * S⁻¹ = 1 := by
      calc S⁻¹ * σ * S⁻¹ = S⁻¹ * (S * S) * S⁻¹ := by rw [hS_sq]
        _ = S⁻¹ * S * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hSinv, hSmul, Matrix.mul_one]
    -- Each term simplifies: S * (K i)ᴴ * S⁻¹ * σ * (S⁻¹ * K i * S)
    -- = S * ((K i)ᴴ * K i) * S
    have h_term_adj : ∀ i : Fin r,
        S * (K i)ᴴ * S⁻¹ * σ * (S⁻¹ * K i * S) = S * ((K i)ᴴ * K i) * S := by
      intro i
      calc
        S * (K i)ᴴ * S⁻¹ * σ * (S⁻¹ * K i * S)
            = S * ((K i)ᴴ * ((S⁻¹ * σ * S⁻¹) * (K i * S))) := by
                simp only [Matrix.mul_assoc]
        _ = S * ((K i)ᴴ * (1 * (K i * S))) := by rw [hcancel]
        _ = S * (((K i)ᴴ * K i) * S) := by simp [Matrix.mul_assoc]
        _ = S * ((K i)ᴴ * K i) * S := by simp only [Matrix.mul_assoc]
    simp_rw [h_term_adj]
    -- ∑ S * ((K i)ᴴ * K i) * S = S * (∑ (K i)ᴴ * K i) * S = σ
    rw [← Finset.sum_mul, ← Finset.mul_sum, hK_tp, Matrix.mul_one, hS_sq]
  -- ── Step 6: transferMap L X = S⁻¹ E(SXS) S⁻¹  (key identity) ──
  have h_term : ∀ (i : Fin r) (X : Mat),
      L i * X * (L i)ᴴ = S⁻¹ * (K i * (S * X * S) * (K i)ᴴ) * S⁻¹ := by
    intro i X
    change (S⁻¹ * K i * S) * X * (S⁻¹ * K i * S)ᴴ =
        S⁻¹ * (K i * (S * X * S) * (K i)ᴴ) * S⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSinv_herm, hS_herm]
    simp only [Matrix.mul_assoc]
  have hL_transfer : ∀ X, MPSTensor.transferMap (d := r) (D := D) L X =
      S⁻¹ * E (S * X * S) * S⁻¹ := by
    intro X
    simp only [MPSTensor.transferMap_apply]
    simp_rw [h_term _ X]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hE_eq, MPSTensor.transferMap_apply]
  -- ── Step 7: transferMap L is irreducible ──
  have hL_irr : IsIrreducibleMap (MPSTensor.transferMap (d := r) (D := D) L) := by
    suffices h : MPSTensor.transferMap (d := r) (D := D) L = similarityMap (D := D) S E by
      rw [h]; exact isIrreducibleMap_similarity (D := D) hS_det hIrr
    apply LinearMap.ext; intro X
    rw [hL_transfer X]
    change S⁻¹ * E (S * X * S) * S⁻¹ = S⁻¹ * E (S * X * Sᴴ) * (Sᴴ)⁻¹
    rw [hS_herm]
  -- Auxiliary lemma: sandwich cancellation lemmas
  have hSandwich : ∀ A : Mat, S * (S⁻¹ * A * S⁻¹) * S = A := by
    intro A
    calc S * (S⁻¹ * A * S⁻¹) * S
        = S * S⁻¹ * A * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hSmul, hSinv, Matrix.one_mul, Matrix.mul_one]
  have hSinvSandwich : ∀ A : Mat, S⁻¹ * (S * A * S) * S⁻¹ = A := by
    intro A
    calc S⁻¹ * (S * A * S) * S⁻¹
        = S⁻¹ * S * A * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hSinv, hSmul, Matrix.one_mul, Matrix.mul_one]
  -- ── Step 8: eigenvalue transfer (E → transferMap L) ──
  have heig_fwd : ∀ ν, Module.End.HasEigenvalue E ν →
      Module.End.HasEigenvalue (MPSTensor.transferMap (d := r) (D := D) L) ν := by
    intro ν hν
    obtain ⟨V, hV⟩ := hν.exists_hasEigenvector
    have hVne : V ≠ 0 := hV.2
    have hEV : E V = ν • V := Module.End.mem_eigenspace_iff.mp hV.1
    let W : Mat := S⁻¹ * V * S⁻¹
    have hWne : W ≠ 0 := by
      intro hW; apply hVne
      have hV_from_W : V = S * W * S := (hSandwich V).symm
      rw [hV_from_W, hW, mul_zero, zero_mul]
    have hLW : MPSTensor.transferMap (d := r) (D := D) L W = ν • W := by
      rw [hL_transfer, hSandwich V, hEV, mul_smul_comm, smul_mul_assoc]
    exact hasEigenvalue_of_eigenvector_eq _ ν W hLW hWne
  -- ── Step 9: eigenvalue transfer (transferMap L → E) ──
  have heig_bwd : ∀ ν, Module.End.HasEigenvalue (MPSTensor.transferMap (d := r) (D := D) L) ν →
      Module.End.HasEigenvalue E ν := by
    intro ν hν
    obtain ⟨W, hW⟩ := hν.exists_hasEigenvector
    have hWne : W ≠ 0 := hW.2
    have hLW : MPSTensor.transferMap (d := r) (D := D) L W = ν • W :=
      Module.End.mem_eigenspace_iff.mp hW.1
    let V : Mat := S * W * S
    have hVne : V ≠ 0 := by
      intro hV; apply hWne
      have hW_from_V : W = S⁻¹ * V * S⁻¹ := (hSinvSandwich W).symm
      rw [hW_from_V, hV, mul_zero, zero_mul]
    have hEV : E V = ν • V := by
      -- From hL_transfer W and hLW: S⁻¹ * E V * S⁻¹ = ν • W
      have h1 : S⁻¹ * E V * S⁻¹ = ν • W := by
        have := hL_transfer W; rw [hLW] at this; exact this.symm
      -- Sandwich with S to recover E V
      have h2 : E V = S * (ν • W) * S := by
        have := hSandwich (E V); rw [h1] at this; exact this.symm
      rw [h2, mul_smul_comm, smul_mul_assoc]
    exact hasEigenvalue_of_eigenvector_eq _ ν V hEV hVne
  -- ── Step 10: Apply power closure theorem and transfer back ──
  have hμ_L : μ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := r) (D := D) L) :=
    ⟨heig_fwd μ hμ.1, hμ.2⟩
  have hpow := MPSTensor.peripheralEigenvalues_pow_mem_of_irreducible_unital_of_adjoint_fixedPoint
    L hL_unital σ hσ_pd hL_adj hL_irr μ hμ_L
  intro n
  obtain ⟨hpow_eig, hpow_norm⟩ := hpow n
  exact ⟨heig_bwd (μ ^ n) hpow_eig, hpow_norm⟩

/-- Evaluation of powers after bundling an endomorphism as a continuous linear map. -/
theorem toContinuousLinearMap_pow_apply [NeZero D]
    (F : Mat →ₗ[ℂ] Mat) (X : Mat) (n : ℕ) :
    (((Module.End.toContinuousLinearMap Mat) F) ^ n) X = (F ^ n) X := by
  have hpowEq : ((Module.End.toContinuousLinearMap Mat) F) ^ n =
      (Module.End.toContinuousLinearMap Mat) (F ^ n) := by
    exact (map_pow (Module.End.toContinuousLinearMap Mat) F n).symm
  rw [hpowEq]
  rfl

/-- In finite dimensions, a strict modulus bound on every eigenvalue gives a spectral-radius gap. -/
theorem spectralRadius_lt_one_of_eigenvalues_lt_one [NeZero D]
    (F : Mat →ₗ[ℂ] Mat)
    (hF : ∀ ν : ℂ, Module.End.HasEigenvalue F ν → ‖ν‖ < 1) :
    spectralRadius ℂ ((Module.End.toContinuousLinearMap Mat) F) < 1 := by
  let Φ : (Mat →ₗ[ℂ] Mat) ≃ₐ[ℂ] (Mat →L[ℂ] Mat) := Module.End.toContinuousLinearMap Mat
  haveI : Nontrivial (Mat →L[ℂ] Mat) := ContinuousLinearMap.instNontrivialId
  let hFinite : FiniteDimensional ℂ (Mat →L[ℂ] Mat) :=
    (endEquiv (D := D)).toLinearEquiv.finiteDimensional
  have hF_nonempty : (spectrum ℂ (Φ F)).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (Φ F)
  have hcompact : IsCompact (spectrum ℂ (Φ F)) := by
    letI : FiniteDimensional ℂ (Mat →L[ℂ] Mat) := hFinite
    let hComplete : CompleteSpace (Mat →L[ℂ] Mat) := FiniteDimensional.complete ℂ (Mat →L[ℂ] Mat)
    exact @spectrum.isCompact ℂ (Mat →L[ℂ] Mat)
      inferInstance inferInstance inferInstance hComplete inferInstance (Φ F)
  obtain ⟨μ, hμ_spec, hμ_max⟩ :=
    hcompact.exists_isMaxOn hF_nonempty continuous_nnnorm.continuousOn
  have hμ_norm : (‖μ‖₊ : ENNReal) = spectralRadius ℂ (Φ F) := by
    exact le_antisymm (le_iSup₂ (α := ENNReal) μ hμ_spec) (iSup₂_le <| mod_cast hμ_max)
  have hμ_spec_end : μ ∈ spectrum ℂ F := by
    rw [AlgEquiv.spectrum_eq Φ] at hμ_spec
    exact hμ_spec
  have hμ_ev : Module.End.HasEigenvalue F μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  have hμ_lt : ‖μ‖ < 1 := hF μ hμ_ev
  rw [← hμ_norm]
  exact by
    exact_mod_cast hμ_lt

end -- noncomputable section
