/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import QICLean.Algebra.PosSemidefSupport
import TNLean.Algebra.MatrixRealignment

/-!
# The nearest Kronecker product

For a bipartite square matrix `M` with realignment `R(M)`, the spectral projector
`P(M) = f(R(M) R(M)†)` cut off by a continuous ramp `f` (equal to `0` below `a`
and `1` above `b`) depends continuously on `M`. On the open set where the
spectrum of `R(M) R(M)†` misses the closed interval `[a, b]` and the trace of
`P(M)` lies in `(1/2, 3/2)`, `P(M)` is a rank-one orthogonal projector, and the
matrix `N(M)` with realignment `P(M) R(M)` is a Kronecker product of nonzero
factors. The map `N` is continuous, commutes with left multiplication by a
product `h ⊗ k` of unitaries, and fixes every product `x ⊗ y` of unitaries.

This is step 2 of the cross-section construction that replaces the slice theorem
of Montgomery and Yang in arXiv:1703.09188, proof of Corollary `coruvSF`,
lines 942--947; see `docs/paper-gaps/mpu_standard_form_path_cross_section.tex`.
The gap is the closed interval `[a, b]`, because the set of matrices whose
spectrum avoids an open interval is not open.

## Main declarations

* `Matrix.kroneckerProjector`: the spectral projector `P(M)`.
* `Matrix.nearestKronecker`: the nearest Kronecker product `N(M)`.
* `Matrix.kroneckerGapSet`: the open set on which `P(M)` has rank one.
* `Matrix.continuous_nearestKronecker`, `Matrix.isOpen_kroneckerGapSet`.
* `Matrix.nearestKronecker_kronecker_mul`: equivariance under `h ⊗ k`.
* `Matrix.exists_eq_kronecker_nearestKronecker`: on the gap set, `N(M)` is a
  Kronecker product of nonzero factors.
* `Matrix.nearestKronecker_kronecker_of_unitary`: `N(x ⊗ y) = x ⊗ y`.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-! ### The ramp function -/

/-- The continuous ramp equal to `0` on `(-∞, a]`, to `1` on `[b, ∞)`, and affine in
between.

Source: the cutoff function `f` of step 2 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def kroneckerRamp (a b : ℝ) (t : ℝ) : ℝ :=
  min 1 (max 0 ((t - a) / (b - a)))

theorem continuous_kroneckerRamp (a b : ℝ) : Continuous (kroneckerRamp a b) := by
  unfold kroneckerRamp
  fun_prop

theorem kroneckerRamp_of_le {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    kroneckerRamp a b t = 0 := by
  have : (t - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [kroneckerRamp, max_eq_left this]

theorem kroneckerRamp_of_ge {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    kroneckerRamp a b t = 1 := by
  have : 1 ≤ (t - a) / (b - a) := by rw [le_div_iff₀ (by linarith)]; linarith
  simp [kroneckerRamp, max_eq_right (zero_le_one.trans this), min_eq_left this]

/-- Off the closed interval `[a, b]` the ramp takes only the values `0` and `1`. -/
theorem kroneckerRamp_mul_self {a b t : ℝ} (hab : a < b) (ht : t ∉ Set.Icc a b) :
    kroneckerRamp a b t * kroneckerRamp a b t = kroneckerRamp a b t := by
  rcases le_or_gt t a with h | h
  · simp [kroneckerRamp_of_le hab h]
  · have : b ≤ t := by by_contra h'; exact ht ⟨h.le, (not_le.mp h').le⟩
    simp [kroneckerRamp_of_ge hab this]

/-! ### The spectral projector and the nearest Kronecker product -/

/-- The Gram matrix `R(M) R(M)†` of the realignment. -/
def realignGram (M : Matrix (m × n) (m × n) ℂ) : Matrix (m × m) (m × m) ℂ :=
  realign M * (realign M)ᴴ

omit [Fintype m] [DecidableEq m] in
theorem isSelfAdjoint_realignGram (M : Matrix (m × n) (m × n) ℂ) :
    IsSelfAdjoint (realignGram M) :=
  isHermitian_mul_conjTranspose_self _

omit [Fintype m] [DecidableEq m] in
theorem continuous_realignGram :
    Continuous (realignGram : Matrix (m × n) (m × n) ℂ → Matrix (m × m) (m × m) ℂ) :=
  continuous_realign.matrix_mul continuous_realign.matrix_conjTranspose

/-- The spectral projector `P(M) = f(R(M) R(M)†)` cut off by the ramp `f`.

Source: the projector `P(M)` of step 2 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def kroneckerProjector (a b : ℝ) (M : Matrix (m × n) (m × n) ℂ) :
    Matrix (m × m) (m × m) ℂ :=
  cfc (kroneckerRamp a b) (realignGram M)

/-- The nearest Kronecker product: the matrix whose realignment is `P(M) R(M)`.

Source: the map `N(M) = R⁻¹(P(M) R(M))` of step 2 of the cross-section
construction for arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def nearestKronecker (a b : ℝ) (M : Matrix (m × n) (m × n) ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  unrealign (kroneckerProjector a b M * realign M)

/-- The set where the spectrum of `R(M) R(M)†` misses the closed interval `[a, b]`
and the trace of `P(M)` lies in `(1/2, 3/2)`.

Source: the open set of step 2 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947, with the closed gap
recorded in `docs/paper-gaps/mpu_standard_form_path_cross_section.tex`. -/
def kroneckerGapSet (a b : ℝ) : Set (Matrix (m × n) (m × n) ℂ) :=
  {M | spectrum ℝ (realignGram M) ⊆ (Set.Icc a b)ᶜ ∧
    (kroneckerProjector a b M).trace.re ∈ Set.Ioo (1 / 2) (3 / 2)}

theorem isSelfAdjoint_kroneckerProjector (a b : ℝ) (M : Matrix (m × n) (m × n) ℂ) :
    IsSelfAdjoint (kroneckerProjector a b M) :=
  cfc_predicate _ _

theorem continuous_kroneckerProjector (a b : ℝ) :
    Continuous (kroneckerProjector a b : Matrix (m × n) (m × n) ℂ → _) :=
  Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ Filter.univ_mem continuous_realignGram
    (hf := (continuous_kroneckerRamp a b).continuousOn) (ha' := isSelfAdjoint_realignGram)

theorem continuous_nearestKronecker (a b : ℝ) :
    Continuous (nearestKronecker a b : Matrix (m × n) (m × n) ℂ → _) :=
  continuous_unrealign.comp ((continuous_kroneckerProjector a b).matrix_mul continuous_realign)

/-- The gap set is open: the spectrum is upper hemicontinuous, so avoiding the
compact interval `[a, b]` is an open condition, and the trace condition is the
preimage of an open interval under a continuous map. -/
theorem isOpen_kroneckerGapSet (a b : ℝ) :
    IsOpen (kroneckerGapSet a b : Set (Matrix (m × n) (m × n) ℂ)) := by
  have hI : IsOpen (Set.Ioo (1 / 2 : ℝ) (3 / 2)) := isOpen_Ioo
  change IsOpen ({M : Matrix (m × n) (m × n) ℂ | spectrum ℝ (realignGram M) ⊆ (Set.Icc a b)ᶜ} ∩
    ((fun M ↦ (kroneckerProjector a b M).trace.re) ⁻¹' Set.Ioo (1 / 2) (3 / 2)))
  refine IsOpen.inter ?_
    (hI.preimage (f := fun M : Matrix (m × n) (m × n) ℂ ↦ (kroneckerProjector a b M).trace.re) ?_)
  · have hspec := (upperHemicontinuous_iff_isOpen_preimage_Iic.mp
      (upperHemicontinuous_spectrum ℝ (Matrix (m × m) (m × m) ℂ))) _
      (isClosed_Icc (a := a) (b := b)).isOpen_compl
    exact hspec.preimage continuous_realignGram
  · exact Complex.continuous_re.comp (continuous_kroneckerProjector a b).matrix_trace

/-! ### Equivariance -/

section Equivariance

variable [DecidableEq n] (h : unitary (Matrix m m ℂ)) (k : unitary (Matrix n n ℂ))

/-- The unitary `h ⊗ 1` acting on the row index of the realignment. -/
private def rowUnitary : unitary (Matrix (m × m) (m × m) ℂ) :=
  ⟨(h : Matrix m m ℂ) ⊗ₖ (1 : Matrix m m ℂ), kronecker_mem_unitary h.2 (one_mem _)⟩

private theorem transpose_kronecker_one_mul_star :
    ((k : Matrix n n ℂ) ⊗ₖ (1 : Matrix n n ℂ))ᵀ *
      (((k : Matrix n n ℂ) ⊗ₖ (1 : Matrix n n ℂ))ᵀ)ᴴ = 1 := by
  have hu : ((k : Matrix n n ℂ) ⊗ₖ (1 : Matrix n n ℂ))ᵀ ∈ unitaryGroup (n × n) ℂ :=
    transpose_mem_unitaryGroup_iff.mpr (kronecker_mem_unitary k.2 (one_mem _))
  exact Unitary.mul_star_self_of_mem hu

private theorem realign_unitary_kronecker_mul (M : Matrix (m × n) (m × n) ℂ) :
    realign (((h : Matrix m m ℂ) ⊗ₖ (k : Matrix n n ℂ)) * M) =
      (rowUnitary h : Matrix (m × m) (m × m) ℂ) * realign M *
        ((k : Matrix n n ℂ) ⊗ₖ (1 : Matrix n n ℂ))ᵀ :=
  realign_kronecker_mul _ _ M

private theorem realignGram_unitary_kronecker_mul (M : Matrix (m × n) (m × n) ℂ) :
    realignGram (((h : Matrix m m ℂ) ⊗ₖ (k : Matrix n n ℂ)) * M) =
      Unitary.conjStarAlgAut ℝ _ (rowUnitary h) (realignGram M) := by
  rw [Unitary.conjStarAlgAut_apply, realignGram, realignGram,
    realign_unitary_kronecker_mul, conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose]
  calc _ = (rowUnitary h : Matrix (m × m) (m × m) ℂ) * realign M *
        ((((k : Matrix n n ℂ) ⊗ₖ (1 : Matrix n n ℂ))ᵀ *
          (((k : Matrix n n ℂ) ⊗ₖ (1 : Matrix n n ℂ))ᵀ)ᴴ)) *
        (realign M)ᴴ * (rowUnitary h : Matrix (m × m) (m × m) ℂ)ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [transpose_kronecker_one_mul_star, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

/-- **Equivariance of the projector.** Left multiplication by `h ⊗ k` conjugates
the projector by `h ⊗ 1`. -/
theorem kroneckerProjector_kronecker_mul (a b : ℝ) (M : Matrix (m × n) (m × n) ℂ) :
    kroneckerProjector a b (((h : Matrix m m ℂ) ⊗ₖ (k : Matrix n n ℂ)) * M) =
      Unitary.conjStarAlgAut ℝ _ (rowUnitary h) (kroneckerProjector a b M) := by
  have hφ : Continuous (Unitary.conjStarAlgAut ℝ _ (rowUnitary h)) := by
    have : ⇑(Unitary.conjStarAlgAut ℝ _ (rowUnitary h)) = fun x ↦
        (rowUnitary h : Matrix (m × m) (m × m) ℂ) * x *
          star (rowUnitary h : Matrix (m × m) (m × m) ℂ) :=
      funext (Unitary.conjStarAlgAut_apply _)
    rw [this]
    fun_prop
  rw [kroneckerProjector, kroneckerProjector, realignGram_unitary_kronecker_mul]
  exact (StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ _ (rowUnitary h)) _ _
    (hf := (continuous_kroneckerRamp a b).continuousOn)
    (hφ := hφ)
    (ha := isSelfAdjoint_realignGram M)
    (hφa := (isSelfAdjoint_realignGram M).map _)).symm

/-- **Equivariance of the nearest Kronecker product.** For unitaries `h` and `k`,
`N((h ⊗ k) M) = (h ⊗ k) N(M)`.

Source: the equivariance of `N` in step 2 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
theorem nearestKronecker_kronecker_mul (a b : ℝ) (M : Matrix (m × n) (m × n) ℂ) :
    nearestKronecker a b (((h : Matrix m m ℂ) ⊗ₖ (k : Matrix n n ℂ)) * M) =
      ((h : Matrix m m ℂ) ⊗ₖ (k : Matrix n n ℂ)) * nearestKronecker a b M := by
  have hstar : star (rowUnitary h : Matrix (m × m) (m × m) ℂ) *
      (rowUnitary h : Matrix (m × m) (m × m) ℂ) = 1 := Unitary.star_mul_self_of_mem (rowUnitary h).2
  rw [nearestKronecker, nearestKronecker, kroneckerProjector_kronecker_mul,
    Unitary.conjStarAlgAut_apply, realign_unitary_kronecker_mul]
  rw [← unrealign_realign (((h : Matrix m m ℂ) ⊗ₖ (k : Matrix n n ℂ)) * unrealign _),
    realign_kronecker_mul, realign_unrealign]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star _) _ (realign M * _), hstar, Matrix.one_mul]
  rfl

/-- The gap set is invariant under left multiplication by `h ⊗ k`. -/
theorem kronecker_mul_mem_kroneckerGapSet_iff (a b : ℝ) (M : Matrix (m × n) (m × n) ℂ) :
    ((h : Matrix m m ℂ) ⊗ₖ (k : Matrix n n ℂ)) * M ∈ kroneckerGapSet a b ↔
      M ∈ kroneckerGapSet a b := by
  simp only [kroneckerGapSet, Set.mem_ofPred_eq, realignGram_unitary_kronecker_mul,
    AlgEquiv.spectrum_eq, kroneckerProjector_kronecker_mul]
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.star_mul_self_of_mem (rowUnitary h).2, Matrix.one_mul]

end Equivariance

/-! ### The projector on the gap set -/

section GapSet

variable {a b : ℝ} {M : Matrix (m × n) (m × n) ℂ}

theorem kroneckerProjector_mul_self (hab : a < b) (hM : M ∈ kroneckerGapSet a b) :
    kroneckerProjector a b M * kroneckerProjector a b M = kroneckerProjector a b M := by
  have hc := (continuous_kroneckerRamp a b).continuousOn (s := spectrum ℝ (realignGram M))
  rw [kroneckerProjector, ← cfc_mul _ _ _ hc hc]
  exact cfc_congr fun t ht ↦ kroneckerRamp_mul_self hab (hM.1 ht)

theorem rank_kroneckerProjector (hab : a < b) (hM : M ∈ kroneckerGapSet a b) :
    (kroneckerProjector a b M).rank = 1 := by
  have hr := (isSelfAdjoint_kroneckerProjector a b M).isHermitian.rank_eq_trace_re_of_idem
    (kroneckerProjector_mul_self hab hM)
  obtain ⟨h1, h2⟩ := hM.2
  rw [← hr] at h1 h2
  have h2' : ((kroneckerProjector a b M).rank : ℝ) < 2 := by linarith
  have h1' : (0 : ℝ) < (kroneckerProjector a b M).rank := by linarith
  have : (kroneckerProjector a b M).rank < 2 := by exact_mod_cast h2'
  have : 0 < (kroneckerProjector a b M).rank := by exact_mod_cast h1'
  omega

private theorem eq_zero_of_rank_eq_zero {p q : Type*} [Finite p] [Fintype q]
    {X : Matrix p q ℂ} (h : X.rank = 0) : X = 0 := by
  have := Fintype.ofFinite p
  rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h
  ext i j
  have hcol : X.col j ∈ Submodule.span ℂ (Set.range X.col) := Submodule.subset_span ⟨j, rfl⟩
  rw [h, Submodule.mem_bot] at hcol
  exact congrFun hcol i

/-- On the gap set the product `P(M) R(M)` is nonzero: otherwise `P(M) R(M) R(M)†`
vanishes, so the ramp vanishes on the spectrum and `P(M) = 0`, contradicting the
trace condition. -/
theorem kroneckerProjector_mul_realign_ne_zero (ha : 0 < a) (hab : a < b)
    (hM : M ∈ kroneckerGapSet a b) :
    kroneckerProjector a b M * realign M ≠ 0 := by
  intro h0
  have hG := isSelfAdjoint_realignGram M
  have hc := (continuous_kroneckerRamp a b).continuousOn (s := spectrum ℝ (realignGram M))
  have hPG : cfc (fun t ↦ kroneckerRamp a b t * t) (realignGram M) = cfc (0 : ℝ → ℝ)
      (realignGram M) := by
    rw [cfc_zero, cfc_mul _ (fun t ↦ t) _ hc continuousOn_id, cfc_id' ℝ _ hG]
    change kroneckerProjector a b M * (realign M * (realign M)ᴴ) = 0
    rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]
  have hon := eqOn_of_cfc_eq_cfc hPG (hc.mul continuousOn_id) continuousOn_const hG
  have hP : kroneckerProjector a b M = 0 := by
    rw [kroneckerProjector, ← cfc_zero ℝ (realignGram M)]
    refine cfc_congr fun t ht ↦ ?_
    have h1 : kroneckerRamp a b t * t = 0 := hon ht
    rcases le_or_gt t a with hta | hta
    · exact kroneckerRamp_of_le hab hta
    · have hbt : b ≤ t := by by_contra h'; exact hM.1 ht ⟨hta.le, (not_le.mp h').le⟩
      rw [kroneckerRamp_of_ge hab hbt, one_mul] at h1
      linarith
  have := hM.2.1
  rw [hP, trace_zero, Complex.zero_re] at this
  norm_num at this

/-- **The nearest Kronecker product is a Kronecker product.** On the gap set,
`N(M) = A ⊗ B` for nonzero matrices `A` and `B`.

Source: step 2 of the cross-section construction for arXiv:1703.09188,
Corollary `coruvSF`, lines 942--947. -/
theorem exists_eq_kronecker_nearestKronecker (ha : 0 < a) (hab : a < b)
    (hM : M ∈ kroneckerGapSet a b) :
    ∃ (A : Matrix m m ℂ) (B : Matrix n n ℂ), A ≠ 0 ∧ B ≠ 0 ∧
      nearestKronecker a b M = A ⊗ₖ B := by
  rw [← rank_realign_eq_one_iff, nearestKronecker, realign_unrealign]
  refine le_antisymm ((rank_mul_le_left _ _).trans (rank_kroneckerProjector hab hM).le) ?_
  refine Nat.one_le_iff_ne_zero.mpr fun h0 ↦ ?_
  exact kroneckerProjector_mul_realign_ne_zero ha hab hM (eq_zero_of_rank_eq_zero h0)

end GapSet

/-! ### Unitary Kronecker products are fixed -/

section Fixed

variable [DecidableEq n] {a b : ℝ}

omit [Fintype m] [Fintype n] in
private theorem realign_one :
    realign (1 : Matrix (m × n) (m × n) ℂ) =
      vecMulVec (fun p : m × m ↦ (1 : Matrix m m ℂ) p.1 p.2)
        (fun p : n × n ↦ (1 : Matrix n n ℂ) p.1 p.2) := by
  rw [← one_kronecker_one, realign_kronecker]

private theorem dotProduct_vec_one_star {p : Type*} [Fintype p] [DecidableEq p] :
    (fun q : p × p ↦ (1 : Matrix p p ℂ) q.1 q.2) ⬝ᵥ
      star (fun q : p × p ↦ (1 : Matrix p p ℂ) q.1 q.2) = Fintype.card p := by
  simp only [dotProduct, Pi.star_apply, one_apply, Fintype.sum_prod_type]
  simp [apply_ite star]

private theorem star_vec_one {p : Type*} [DecidableEq p] :
    star (fun q : p × p ↦ (1 : Matrix p p ℂ) q.1 q.2) =
      (fun q : p × p ↦ (1 : Matrix p p ℂ) q.1 q.2) := by
  funext q
  simp [one_apply, apply_ite star]

omit [Fintype m] in
private theorem realignGram_one :
    realignGram (1 : Matrix (m × n) (m × n) ℂ) =
      ((Fintype.card n : ℂ)) • vecMulVec (fun p : m × m ↦ (1 : Matrix m m ℂ) p.1 p.2)
        (fun p : m × m ↦ (1 : Matrix m m ℂ) p.1 p.2) := by
  rw [realignGram, realign_one, conjTranspose_vecMulVec,
    vecMulVec_mul_vecMulVec, dotProduct_vec_one_star, star_vec_one, vecMulVec_smul]

/-- The realignment Gram matrix of the identity satisfies `G² = c G` with
`c = |m| |n|`. -/
private theorem realignGram_one_mul_self :
    realignGram (1 : Matrix (m × n) (m × n) ℂ) *
        realignGram (1 : Matrix (m × n) (m × n) ℂ) =
      ((Fintype.card m * Fintype.card n : ℝ)) • realignGram (1 : Matrix (m × n) (m × n) ℂ) := by
  have hv := dotProduct_vec_one_star (p := m)
  rw [star_vec_one] at hv
  rw [realignGram_one, smul_mul_smul_comm, vecMulVec_mul_vecMulVec, hv, vecMulVec_smul,
    smul_smul, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

private theorem realignGram_one_mul_realign :
    realignGram (1 : Matrix (m × n) (m × n) ℂ) * realign 1 =
      ((Fintype.card m * Fintype.card n : ℝ)) • realign (1 : Matrix (m × n) (m × n) ℂ) := by
  have hv := dotProduct_vec_one_star (p := m)
  rw [star_vec_one] at hv
  rw [realignGram_one, realign_one, Matrix.smul_mul, vecMulVec_mul_vecMulVec, hv, vecMulVec_smul,
    smul_smul, ← Complex.coe_smul]
  congr 1
  push_cast
  ring

/-- The spectrum of the realignment Gram matrix of the identity lies in `{0, |m| |n|}`. -/
private theorem spectrum_realignGram_one {t : ℝ}
    (ht : t ∈ spectrum ℝ (realignGram (1 : Matrix (m × n) (m × n) ℂ))) :
    t = 0 ∨ t = Fintype.card m * Fintype.card n := by
  have hG := isSelfAdjoint_realignGram (1 : Matrix (m × n) (m × n) ℂ)
  have h : cfc (fun t : ℝ ↦ t * t) (realignGram (1 : Matrix (m × n) (m × n) ℂ)) =
      cfc (fun t : ℝ ↦ (Fintype.card m * Fintype.card n : ℝ) * t)
        (realignGram (1 : Matrix (m × n) (m × n) ℂ)) := by
    rw [cfc_mul (fun t : ℝ ↦ t) (fun t : ℝ ↦ t) _ continuousOn_id continuousOn_id,
      cfc_id' ℝ _ hG, cfc_const_mul_id _ _ hG, realignGram_one_mul_self]
  have h' : t * t = (Fintype.card m * Fintype.card n : ℝ) * t :=
    eqOn_of_cfc_eq_cfc h (by fun_prop) (by fun_prop) hG ht
  have : t * (t - Fintype.card m * Fintype.card n) = 0 := by linear_combination h'
  rcases mul_eq_zero.mp this with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

variable (hapos : 0 < a) (hab : a < b) (hbc : b < Fintype.card m * Fintype.card n)
include hapos hab hbc

private theorem kroneckerProjector_one :
    kroneckerProjector a b (1 : Matrix (m × n) (m × n) ℂ) =
      ((Fintype.card m * Fintype.card n : ℝ))⁻¹ • realignGram (1 : Matrix (m × n) (m × n) ℂ) := by
  have hG := isSelfAdjoint_realignGram (1 : Matrix (m × n) (m × n) ℂ)
  have hc : (0 : ℝ) < Fintype.card m * Fintype.card n := by linarith
  rw [kroneckerProjector, ← cfc_const_mul_id _ _ hG]
  refine cfc_congr fun t ht ↦ ?_
  rcases spectrum_realignGram_one ht with rfl | rfl
  · simp [kroneckerRamp_of_le hab hapos.le]
  · rw [kroneckerRamp_of_ge hab hbc.le, inv_mul_cancel₀ hc.ne']

/-- The identity lies in the gap set when `0 < a < b < |m| |n|`. -/
theorem one_mem_kroneckerGapSet : (1 : Matrix (m × n) (m × n) ℂ) ∈ kroneckerGapSet a b := by
  have hc : (0 : ℝ) < Fintype.card m * Fintype.card n := by linarith
  refine ⟨fun t ht hmem ↦ ?_, ?_⟩
  · rcases spectrum_realignGram_one ht with rfl | rfl
    · exact (not_le.mpr hapos) hmem.1
    · exact (not_le.mpr hbc) hmem.2
  · have hv := dotProduct_vec_one_star (p := m)
    rw [star_vec_one] at hv
    rw [kroneckerProjector_one hapos hab hbc, realignGram_one, trace_smul, trace_smul,
      trace_vecMulVec, hv, smul_eq_mul, ← Complex.coe_smul, smul_eq_mul]
    have hne : ((Fintype.card m : ℂ) * Fintype.card n) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    rw [mul_comm (Fintype.card n : ℂ), inv_mul_cancel₀ hne, Complex.one_re]
    norm_num

/-- The nearest Kronecker product of the identity is the identity. -/
theorem nearestKronecker_one : nearestKronecker a b (1 : Matrix (m × n) (m × n) ℂ) = 1 := by
  have hc : (0 : ℝ) < Fintype.card m * Fintype.card n := by linarith
  rw [nearestKronecker, kroneckerProjector_one hapos hab hbc, Matrix.smul_mul,
    realignGram_one_mul_realign, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, unrealign_realign]

/-- **Unitary Kronecker products are fixed.** For unitaries `x` and `y`,
`N(x ⊗ y) = x ⊗ y`, provided `0 < a < b < |m| |n|`.

Source: step 2 of the cross-section construction for arXiv:1703.09188,
Corollary `coruvSF`, lines 942--947. -/
theorem nearestKronecker_kronecker_of_unitary (x : unitary (Matrix m m ℂ))
    (y : unitary (Matrix n n ℂ)) :
    nearestKronecker a b ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) =
      (x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ) := by
  have := nearestKronecker_kronecker_mul x y a b 1
  rwa [Matrix.mul_one, nearestKronecker_one hapos hab hbc, Matrix.mul_one] at this

/-- Products of unitaries lie in the gap set, provided `0 < a < b < |m| |n|`. -/
theorem kronecker_mem_kroneckerGapSet (x : unitary (Matrix m m ℂ))
    (y : unitary (Matrix n n ℂ)) :
    (x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ) ∈ kroneckerGapSet a b := by
  have := (kronecker_mul_mem_kroneckerGapSet_iff x y a b 1).mpr
    (one_mem_kroneckerGapSet hapos hab hbc)
  rwa [Matrix.mul_one] at this

end Fixed

end Matrix
