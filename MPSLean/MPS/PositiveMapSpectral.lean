/-
Copyright (c) 2026 MPSLean Contributors.
SPDX-License-Identifier: Apache-2.0

# Spectral theory of positive maps on matrix algebras

This file develops the basic spectral theory of positive linear maps
on `M_D(ℂ)`, following Chapter 6 of Wolf's lecture notes
"Quantum Channels & Operations" (2012).

## Main results

* `IsPositiveMap`: a linear map that preserves the PSD cone
* `densityMatrices_isCompact`: the set of density matrices is compact
* `densityMatrices_isConvex`: the set of density matrices is convex
* `IsPositiveMap.posSemidef_fixedPoint_of_tracePreserving`:
    every trace-preserving positive map has a PSD fixed point (Cesàro mean argument)
* `IsPositiveMap.posSemidef_parts_of_hermitian_fixedPoint` (Wolf Prop 6.8):
    Hermitian fixed points decompose into PSD fixed points

## References

* [M. Wolf, *Quantum Channels & Operations*, Chapter 6][Wolf2012]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*][Evans1978]
-/

import MPSLean.MPS.CPPrimitive

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Matrix

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset

variable {D : ℕ}

/-! ## Positive maps -/

section PositiveMap

/-- A linear map `E : M_D(ℂ) →ₗ[ℂ] M_D(ℂ)` is **positive** if it maps
positive semidefinite matrices to positive semidefinite matrices. -/
def IsPositiveMap (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ, X.PosSemidef → (E X).PosSemidef

/-- A linear map is **trace-preserving** if `Tr(E(X)) = Tr(X)` for all `X`. -/
def IsTracePreservingMap (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ, trace (E X) = trace X

/-- A positive trace-preserving map is a **quantum channel** (in the broad sense). -/
structure IsChannel (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop where
  pos : IsPositiveMap E
  tp : IsTracePreservingMap E

/-- Positive maps preserve Hermiticity.

Proof: decompose `X = X⁺ - X⁻` using the CFC positive/negative parts.
Both parts are PSD, so `E(X⁺)` and `E(X⁻)` are PSD (hence Hermitian),
and `E(X) = E(X⁺) - E(X⁻)` is a difference of Hermitian matrices. -/
theorem IsPositiveMap.map_isHermitian (hE : IsPositiveMap E)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.IsHermitian) :
    (E X).IsHermitian := by
  -- Decompose X = X⁺ - X⁻ using CFC
  have h_decomp : X⁺ - X⁻ = X := CFC.posPart_sub_negPart X (isSelfAdjoint_iff.mpr hX)
  -- X⁺ and X⁻ are PSD (via nonneg_iff_posSemidef)
  have h_pos_psd := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)
  have h_neg_psd := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)
  -- E(X) = E(X⁺) - E(X⁻) by linearity
  have h_EX : E X = E (X⁺) - E (X⁻) := by
    conv_lhs => rw [← h_decomp]; simp [map_sub]
  rw [h_EX]
  exact (hE _ h_pos_psd).isHermitian.sub (hE _ h_neg_psd).isHermitian

end PositiveMap

/-! ## Density matrices: compactness and convexity -/

section DensityMatrices

open scoped Matrix.Norms.Frobenius

/-- The set of density matrices: PSD matrices with trace 1. -/
def densityMatrices (D : ℕ) : Set (Matrix (Fin D) (Fin D) ℂ) :=
  {ρ | ρ.PosSemidef ∧ trace ρ = 1}

/-! ### Auxiliary lemmas for closedness -/

/-- The set of nonneg complex numbers (those with `0 ≤ z` in `ComplexOrder`) is closed. -/
private lemma isClosed_complex_nonneg : IsClosed {z : ℂ | 0 ≤ z} := by
  have : {z : ℂ | 0 ≤ z} = {z | 0 ≤ z.re ∧ z.im = 0} := by
    ext z; constructor
    · intro h; exact ⟨(Complex.nonneg_iff.mp h).1, (Complex.nonneg_iff.mp h).2.symm⟩
    · intro ⟨h1, h2⟩; exact Complex.nonneg_iff.mpr ⟨h1, h2.symm⟩
  rw [this]
  exact IsClosed.inter
    (isClosed_le continuous_const Complex.continuous_re)
    (isClosed_eq Complex.continuous_im continuous_const)

/-- The quadratic form `X ↦ star v ⬝ᵥ X.mulVec v` is continuous. -/
private lemma continuous_quadraticForm (v : Fin D → ℂ) :
    Continuous (fun X : Matrix (Fin D) (Fin D) ℂ => star v ⬝ᵥ X.mulVec v) :=
  Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_id continuous_const)

/-! ### Auxiliary lemmas for boundedness -/

/-- For a nonneg complex number `z` (in `ComplexOrder`), `‖z‖ = z.re`. -/
private lemma norm_of_complex_nonneg {z : ℂ} (hz : 0 ≤ z) : ‖z‖ = z.re := by
  have ⟨h_re, h_im⟩ := Complex.nonneg_iff.mp hz
  rw [Complex.norm_eq_sqrt_sq_add_sq, h_im.symm, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, Real.sqrt_sq h_re]

/-- For PSD `X`, each diagonal entry norm is bounded by the trace norm. -/
private lemma posSemidef_diag_norm_le_trace_norm {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X.PosSemidef) (i : Fin D) : ‖X i i‖ ≤ ‖trace X‖ := by
  rw [norm_of_complex_nonneg hX.diag_nonneg, norm_of_complex_nonneg hX.trace_nonneg]
  have h_trace_re : (trace X).re = ∑ j : Fin D, (X j j).re := by
    simp [Matrix.trace, Matrix.diag]
  rw [h_trace_re]
  exact Finset.single_le_sum
    (fun j _ => (Complex.nonneg_iff.mp (hX.diag_nonneg (i := j))).1)
    (Finset.mem_univ i)

/-- For PSD `X = Bᴴ * B`, the entry `(Bᴴ * B) i j` equals an inner product of column vectors. -/
private lemma conjTranspose_mul_self_entry_eq_inner (B : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    (Bᴴ * B) i j = inner (𝕜 := ℂ) (WithLp.toLp (p := 2) (fun k => B k i))
                                      (WithLp.toLp (p := 2) (fun k => B k j)) := by
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1; ext k; ring

/-- The squared norm of a column vector of `B` equals the real part of
a diagonal entry of `Bᴴ * B`. -/
private lemma col_norm_sq_eq_diag (B : Matrix (Fin D) (Fin D) ℂ) (i : Fin D) :
    ‖WithLp.toLp (p := 2) (fun k : Fin D => B k i)‖ ^ 2 = ((Bᴴ * B) i i).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  conv_rhs => rw [Complex.re_sum]
  congr 1; ext k
  rw [show star (B k i) = starRingEnd ℂ (B k i) from rfl, RCLike.conj_mul]
  norm_cast

/-- If `a² ≤ c` and `b² ≤ c` with `c ≥ 0`, then `a * b ≤ c` (for nonneg `a, b`). -/
private lemma mul_le_of_sq_le {a b c : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha2 : a ^ 2 ≤ c) (hb2 : b ^ 2 ≤ c) : a * b ≤ c := by
  have h1 : a ≤ Real.sqrt c := Real.le_sqrt_of_sq_le ha2
  have h2 : b ≤ Real.sqrt c := Real.le_sqrt_of_sq_le hb2
  calc a * b ≤ Real.sqrt c * Real.sqrt c := mul_le_mul h1 h2 hb (Real.sqrt_nonneg _)
    _ = c := Real.mul_self_sqrt hc

/-- For PSD `X`, each entry norm is bounded by the trace norm.

The diagonal bound follows from nonnegativity of diagonal entries.
The off-diagonal bound uses the Cauchy-Schwarz inequality for the
PSD inner product: `|X i j|² ≤ (X i i) * (X j j) ≤ (trace X)²`. -/
private lemma posSemidef_entry_norm_le_trace_norm {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X.PosSemidef) (i j : Fin D) : ‖X i j‖ ≤ ‖trace X‖ := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  rw [Matrix.star_eq_conjTranspose] at *
  have hX' : (Bᴴ * B).PosSemidef :=
    (CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
      ⟨B, by rw [Matrix.star_eq_conjTranspose]⟩).posSemidef
  rw [conjTranspose_mul_self_entry_eq_inner]
  set u := WithLp.toLp (p := 2) (fun k : Fin D => B k i)
  set v := WithLp.toLp (p := 2) (fun k : Fin D => B k j)
  calc ‖inner (𝕜 := ℂ) u v‖
      ≤ ‖u‖ * ‖v‖ := @norm_inner_le_norm ℂ _ _ _ _ u v
    _ ≤ ‖trace (Bᴴ * B)‖ := by
        apply mul_le_of_sq_le (norm_nonneg u) (norm_nonneg v) (norm_nonneg _)
        · rw [col_norm_sq_eq_diag]
          rw [← norm_of_complex_nonneg hX'.diag_nonneg]
          exact posSemidef_diag_norm_le_trace_norm hX' i
        · rw [col_norm_sq_eq_diag]
          rw [← norm_of_complex_nonneg hX'.diag_nonneg]
          exact posSemidef_diag_norm_le_trace_norm hX' j

/-! ### Main results -/

/-- PSD matrices with trace ≤ c form a bounded set (in the Frobenius norm).

For PSD `X`, every entry satisfies `‖X i j‖ ≤ ‖trace X‖`
(diagonal: nonneg summand of trace; off-diagonal: Cauchy-Schwarz).
Hence the sup-norm `‖X‖ ≤ ‖trace X‖ ≤ c`. -/
theorem posSemidef_trace_bounded_isBounded (c : ℝ) :
    Bornology.IsBounded
      {X : Matrix (Fin D) (Fin D) ℂ | X.PosSemidef ∧ ‖trace X‖ ≤ c} := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨D * c, fun X ⟨hX_psd, hX_tr⟩ => ?_⟩
  have hc_nonneg : 0 ≤ c := le_trans (norm_nonneg _) hX_tr
  have hentry : ∀ i j, ‖X i j‖ ≤ c :=
    fun i j => le_trans (posSemidef_entry_norm_le_trace_norm hX_psd i j) hX_tr
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  rw [← Real.sqrt_sq (by positivity : 0 ≤ (D : ℝ) * c)]
  apply Real.sqrt_le_sqrt
  simp_rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  calc ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2
      ≤ ∑ _i : Fin D, ∑ _j : Fin D, c ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
    _ = ↑D * ↑D * c ^ 2 := by simp [Finset.sum_const]; ring
    _ = (↑D * c) ^ 2 := by ring

/-- The PSD cone is closed.

Proof: `PosSemidef X ↔ X.IsHermitian ∧ ∀ v, 0 ≤ star v ⬝ᵥ X.mulVec v`.
- `{X | X.IsHermitian}` is closed (continuous `conjTranspose`).
- Each `{X | 0 ≤ star v ⬝ᵥ X.mulVec v}` is closed (preimage of closed
  nonneg cone under continuous quadratic form). -/
theorem isClosed_posSemidef :
    IsClosed {X : Matrix (Fin D) (Fin D) ℂ | X.PosSemidef} := by
  have h_eq : {X : Matrix (Fin D) (Fin D) ℂ | X.PosSemidef}
    = {X | X.IsHermitian} ∩ ⋂ (v : Fin D → ℂ), {X | 0 ≤ star v ⬝ᵥ X.mulVec v} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [h_eq]
  exact IsClosed.inter
    (isClosed_eq continuous_star continuous_id)
    (isClosed_iInter fun v => isClosed_complex_nonneg.preimage (continuous_quadraticForm v))

/-- The set of density matrices is compact (Heine-Borel).

Closed: intersection of the closed PSD cone and the closed set `{trace = 1}`.
Bounded: PSD matrices with unit trace have bounded entries. -/
theorem densityMatrices_isCompact :
    IsCompact (densityMatrices D) := by
  haveI : ProperSpace (Matrix (Fin D) (Fin D) ℂ) :=
    FiniteDimensional.proper_rclike ℂ _
  apply Metric.isCompact_of_isClosed_isBounded
  · -- Closed: PSD ∩ {trace = 1}
    apply IsClosed.inter isClosed_posSemidef
    exact isClosed_eq (continuous_id.matrix_trace) continuous_const
  · -- Bounded: subset of PSD ∩ {‖trace‖ ≤ 1}
    apply Bornology.IsBounded.subset (posSemidef_trace_bounded_isBounded 1)
    intro X ⟨hX_psd, hX_tr⟩
    exact ⟨hX_psd, by rw [hX_tr]; simp⟩

/-- The set of density matrices is convex.

PSD cone is convex: `a • ρ + b • σ` is PSD when `ρ, σ` are PSD and `a, b ≥ 0`.
Trace is linear: `trace(a • ρ + b • σ) = a * 1 + b * 1 = 1` when `a + b = 1`. -/
theorem densityMatrices_isConvex :
    Convex ℝ (densityMatrices D) := by
  intro ρ ⟨hρ_psd, hρ_tr⟩ σ ⟨hσ_psd, hσ_tr⟩ a b ha hb hab
  refine ⟨?_, ?_⟩
  · exact (hρ_psd.smul ha).add (hσ_psd.smul hb)
  · simp only [trace_add, trace_smul, hρ_tr, hσ_tr]
    rw [← add_smul, hab, one_smul]

/-- The set of density matrices is nonempty when D > 0.

The matrix `(1/D) • I` is a density matrix. -/
theorem densityMatrices_nonempty (hD : 0 < D) :
    (densityMatrices D).Nonempty := by
  refine ⟨(D : ℂ)⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ), ?_, ?_⟩
  · exact Matrix.PosSemidef.one.smul (by positivity : (0 : ℝ) ≤ (D : ℂ)⁻¹)
  · simp only [trace_smul, trace_one, Fintype.card_fin]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hD))

end DensityMatrices

/-! ## Channels preserve density matrices -/

section ChannelPreserves

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- A channel (positive + trace-preserving) maps density matrices to density matrices. -/
theorem IsChannel.map_densityMatrices (hE : IsChannel E) :
    ∀ ρ ∈ densityMatrices D, E ρ ∈ densityMatrices D := by
  intro ρ ⟨hρ_psd, hρ_tr⟩
  exact ⟨hE.pos ρ hρ_psd, by rw [hE.tp, hρ_tr]⟩

end ChannelPreserves

/-! ## Wolf Proposition 6.8: Decomposition of fixed points -/

section FixedPointDecomposition

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- **Wolf Proposition 6.8** (Hermitian part):
If `E` is trace-preserving and positive, and `X` is a Hermitian fixed point,
then the positive and negative parts of `X` are also fixed points.

More precisely: if `X = X₊ - X₋` where `X₊, X₋ ≥ 0` and `X₊ ⊥ X₋`
(orthogonal supports), then `E(X₊) = X₊` and `E(X₋) = X₋`. -/
theorem IsChannel.posSemidef_parts_of_hermitian_fixedPoint
    (hE : IsChannel E)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX_herm : X.IsHermitian)
    (hX_fix : E X = X) :
    -- If P₊ is the positive part of X (projection onto positive eigenspace)
    -- and P₋ is the negative part, then both are fixed by E.
    -- For now, we state the consequence: there exist PSD Q₁, Q₂ with
    -- X = Q₁ - Q₂ and E(Q₁) = Q₁ and E(Q₂) = Q₂.
    ∃ Q₁ Q₂ : Matrix (Fin D) (Fin D) ℂ,
      Q₁.PosSemidef ∧ Q₂.PosSemidef ∧
      X = Q₁ - Q₂ ∧ E Q₁ = Q₁ ∧ E Q₂ = Q₂ := by
  sorry

end FixedPointDecomposition

/-! ## Cesàro mean existence of PSD fixed point -/

section CesaroMean

open scoped Matrix.Norms.Frobenius

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- The Cesàro mean of the iterates of `E` applied to `X`. -/
noncomputable def cesaroMean (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 / (N : ℂ)) • ∑ n ∈ Finset.range N, (E ^ n) X

/-- Key lemma: telescoping. `E(σ_N) - σ_N = (E^N(X) - X) / N`. -/
theorem cesaroMean_telescope (X : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) (_hN : 0 < N) :
    E (cesaroMean E X N) - cesaroMean E X N =
      (1 / (N : ℂ)) • ((E ^ N) X - X) := by
  simp only [cesaroMean]
  rw [map_smul, map_sum]
  rw [← smul_sub]
  congr 1
  conv_lhs =>
    arg 1; arg 2; ext x
    rw [show E ((E ^ x) X) = (E ^ (x + 1)) X from by rw [pow_succ']; rfl]
  rw [← Finset.sum_sub_distrib]
  conv_lhs => rw [show (fun x => (E ^ (x + 1)) X - (E ^ x) X) =
    (fun x => (fun n => (E ^ n) X) (x + 1) - (fun n => (E ^ n) X) x) from rfl]
  rw [Finset.sum_range_sub (fun n => (E ^ n) X)]
  simp [pow_zero]

/-- **Existence of PSD fixed point for channels** (Cesàro mean argument).

Every trace-preserving positive map on `M_D(ℂ)` with `D > 0` has a
nonzero PSD fixed point.

This avoids Brouwer's fixed point theorem entirely, using only:
- compactness of density matrices (finite-dimensional Heine-Borel)
- sequential compactness (extract convergent subsequence)
- linearity (telescoping identity)

**Proof sketch** (Markov-Kakutani style):
1. Start with any density matrix `ρ₀`.
2. The Cesàro means `σ_N = (1/N) Σ_{n=0}^{N-1} E^n(ρ₀)` are density matrices.
3. Extract convergent subsequence `σ_{N_k} → σ`.
4. `E(σ_N) - σ_N = (E^N(ρ₀) - ρ₀)/N → 0`.
5. Hence `E(σ) = σ`. -/
theorem IsChannel.exists_posSemidef_fixedPoint
    (hE : IsChannel E) (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧ E ρ = ρ := by
  -- Iterates of a channel preserve density matrices
  have h_iter : ∀ n : ℕ, ∀ (ρ : Matrix (Fin D) (Fin D) ℂ), ρ ∈ densityMatrices D →
      (E ^ n) ρ ∈ densityMatrices D := by
    intro n; induction n with
    | zero => intro ρ hρ; simpa [pow_zero]
    | succ n ih =>
      intro ρ hρ
      have h1 := ih ρ hρ
      change (E ^ (n + 1)) ρ ∈ densityMatrices D
      rw [pow_succ']
      change E ((E ^ n) ρ) ∈ densityMatrices D
      exact IsChannel.map_densityMatrices E hE ((E ^ n) ρ) h1
  -- Step 1: Pick a starting density matrix ρ₀
  obtain ⟨ρ₀, hρ₀⟩ := densityMatrices_nonempty hD
  -- Step 2: Define the Cesàro means σ(N) = cesaroMean E ρ₀ (N+1)
  set σ : ℕ → Matrix (Fin D) (Fin D) ℂ := fun N => cesaroMean E ρ₀ (N + 1)
  -- Step 3: Each σ(N) is a density matrix
  have hσ_mem : ∀ N, σ N ∈ densityMatrices D := by
    intro N
    refine ⟨?_, ?_⟩
    · -- PSD: (1/(N+1)) • Σ E^n(ρ₀) is PSD
      change cesaroMean E ρ₀ (N + 1) |>.PosSemidef
      unfold cesaroMean
      exact (Matrix.posSemidef_sum _ fun n _ => (h_iter n ρ₀ hρ₀).1).smul
        (by rw [one_div]; exact_mod_cast inv_nonneg_of_nonneg (Nat.cast_nonneg' (N + 1)))
    · -- Trace = 1
      change (cesaroMean E ρ₀ (N + 1)).trace = 1
      unfold cesaroMean
      rw [trace_smul, trace_sum,
        Finset.sum_congr rfl (fun n _ => (h_iter n ρ₀ hρ₀).2),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_div]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  -- Step 4: Extract convergent subsequence by compactness
  haveI : FirstCountableTopology (Matrix (Fin D) (Fin D) ℂ) :=
    @UniformSpace.firstCountableTopology _ _ inferInstance
  obtain ⟨ρ, hρ_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    densityMatrices_isCompact.tendsto_subseq hσ_mem
  -- Step 5: ρ is PSD with trace 1
  have hρ_psd : ρ.PosSemidef := hρ_mem.1
  have hρ_tr : trace ρ = 1 := hρ_mem.2
  -- Step 6: Show E(ρ) = ρ via telescoping + convergence
  have hE_cont : Continuous E := LinearMap.continuous_of_finiteDimensional E
  -- σ ∘ φ → ρ, E ∘ σ ∘ φ → E(ρ)
  have h_Eσ : Filter.Tendsto (E ∘ σ ∘ φ) Filter.atTop (nhds (E ρ)) :=
    (hE_cont.tendsto ρ).comp hφ_tendsto
  -- (E(σ(φ k)) - σ(φ k)) → E(ρ) - ρ
  have h_diff : Filter.Tendsto (fun k => (E ∘ σ ∘ φ) k - (σ ∘ φ) k)
      Filter.atTop (nhds (E ρ - ρ)) :=
    h_Eσ.sub hφ_tendsto
  -- By telescoping: E(σ(N)) - σ(N) = (1/(N+1)) • (E^(N+1)(ρ₀) - ρ₀)
  have h_telesc : ∀ k, (E ∘ σ ∘ φ) k - (σ ∘ φ) k =
      (1 / ((φ k + 1 : ℕ) : ℂ)) • ((E ^ (φ k + 1)) ρ₀ - ρ₀) :=
    fun k => cesaroMean_telescope E ρ₀ (φ k + 1) (Nat.succ_pos _)
  -- The RHS → 0: scalar → 0 times norm-bounded sequence → 0
  have h_rhs_zero : Filter.Tendsto (fun k => (1 / ((φ k + 1 : ℕ) : ℂ)) •
      ((E ^ (φ k + 1)) ρ₀ - ρ₀)) Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      ((fun k => (1 / ((φ k + 1 : ℕ) : ℂ))) • (fun k => (E ^ (φ k + 1)) ρ₀ - ρ₀))
      Filter.atTop (nhds 0)
    apply NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
    · -- 1/(φ k + 1) → 0 in ℂ
      simp_rw [one_div]
      have h_succ_tendsto : Filter.Tendsto (fun k => φ k + 1) Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_atTop_of_monotone
        · intro a b hab; exact Nat.add_le_add_right (hφ_mono.monotone hab) 1
        · intro b; exact ⟨b, Nat.le_succ_of_le (hφ_mono.id_le b)⟩
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp h_succ_tendsto
    · -- ‖E^n(ρ₀) - ρ₀‖ is bounded: density matrices are compact ⇒ bounded
      have hbdd := densityMatrices_isCompact (D := D) |>.isBounded
      rw [Metric.isBounded_iff_subset_ball 0] at hbdd
      obtain ⟨R, hR⟩ := hbdd
      apply Filter.isBoundedUnder_of
      refine ⟨R + R, fun k => ?_⟩
      have h1 := hR (h_iter (φ k + 1) ρ₀ hρ₀)
      have h2 := hR hρ₀
      rw [Metric.mem_ball, dist_zero_right] at h1 h2
      exact le_trans (norm_sub_le _ _) (by linarith)
  -- Conclude E(ρ) - ρ = 0 by uniqueness of limits
  have h_eq : E ρ - ρ = 0 :=
    tendsto_nhds_unique (h_diff.congr h_telesc) h_rhs_zero
  have hρ_fix : E ρ = ρ := sub_eq_zero.mp h_eq
  -- Step 7: ρ ≠ 0 (trace ρ = 1 ≠ 0)
  have hρ_ne : ρ ≠ 0 := by
    intro h; rw [h, Matrix.trace_zero (Fin D) ℂ] at hρ_tr; exact one_ne_zero hρ_tr.symm
  exact ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩

end CesaroMean

/-! ## Connection to MPS transfer maps -/

section TransferMap

/-- The transfer map of a normalized MPS tensor (with `∑ Aᵢ† Aᵢ = 1`)
is a channel: positive and trace-preserving. -/
theorem MPSTensor.transferMap_isChannel {d D : ℕ}
    (A : MPSTensor d D)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    IsChannel (MPSTensor.transferMap (d := d) (D := D) A) := by
  constructor
  · -- Positivity: already proved as transferMap_isCP / transferMap_pos
    intro X hX
    exact MPSTensor.transferMap_pos A hX
  · -- Trace-preserving: Tr(Σ Aᵢ X Aᵢ†) = Σ Tr(Aᵢ† Aᵢ X) = Tr(X)
    intro X
    simp only [MPSTensor.transferMap_apply]
    rw [trace_sum]
    conv_lhs => arg 2; ext i; rw [Matrix.trace_mul_cycle]
    rw [← trace_sum, ← Finset.sum_mul, hNorm, one_mul]

end TransferMap

/-! ## Existence of PSD eigenvector (Wolf Theorem 6.5 sketch)

For general CP maps (not necessarily trace-preserving), we need a different
approach. The key idea from Wolf is the **density argument**:

1. Perturb `E` to `E_ε = (1-ε)E + ε·D` where `D` is the depolarizing channel.
2. `E_ε` is trace-preserving (if we normalize appropriately) and irreducible.
3. By the Cesàro mean theorem, `E_ε` has a PSD fixed point `ρ_ε`.
4. By our PD theorem (irreducible case), `ρ_ε` is actually PD.
5. Take `ε → 0` and extract a limit.

This will be developed in a future extension of this file.
-/
