/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Uncle.UncleWallGram
import QICLean.Algebra.Matrix.MatrixTracePairing
import QICLean.Channel.KrausMap.KrausCPTP
import QICLean.Kraus.Wielandt.KrausRectangularComposition
import QICLean.Channel.Peripheral.Spectrum.UnitalKraus
import Mathlib.Logic.Equiv.Fin.Basic
import TNLean.MPS.ParentHamiltonian.Uncle.UnclePrimitiveTransfer
import TNLean.MPS.ParentHamiltonian.Uncle.UncleWallGramBounds
import QICLean.Analysis.TraceInequality.TraceMulBound
import QICLean.Analysis.Norm.OperatorNormConvergence
import QICLean.Channel.TraceNormNet

/-!
# The exact finite transfer contraction of a two-wall trial

A moving wall defines a rectangular Kraus map, with its actual wall words as
Kraus matrices. The squared norm of the five-segment trial is the real part
of the operator trace of the five corresponding transfer maps. No limiting
rank-one approximation, norm-growth estimate, or positivity assumption enters
this identity.

Source: arXiv:1210.6613, phiN-def and the norm calculation in the proof of
Lemma lowenergystates, lines 1196–1265.

It also contains the following results.

* `MPSTensor.uncleTwoWallTransfer_factorization_bound`,
  `MPSTensor.uncleTwoWallTrialSource_normalized_norm_sq_tendsto`: quantitative factorization of the
  two-wall transfer contraction.
* `MPSTensor.norm_uncleTwoWallTrial_one_wall_sq_le_mul`,
  `MPSTensor.norm_uncleTwoWallTrial_second_wall_sq_le_mul`: linear norm bounds for an actual trial
  with one pinned wall.
-/

section UncleTrialTransferNorm

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

/-- The actual moving-wall Gram map, with one Kraus matrix for each physical
word. Its value at the identity is the finite Gram matrix in the source norm
calculation; arXiv:1210.6613, proof of Lemma lowenergystates. -/
def uncleWallGramMap (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ) :
    Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ :=
  Matrix.rectangularKrausMap
    (fun σ : Cfg d n ↦ uncleDomainWallWord A B R (List.ofFn σ))

/-- The finite source Gram matrix is exactly the Gram map at the identity.
Source: arXiv:1210.6613, proof of Lemma lowenergystates. -/
@[simp] theorem uncleWallGramMap_one (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ) :
    uncleWallGramMap A B R n 1 = uncleWallGram A B R n := by
  simp [uncleWallGramMap, Matrix.rectangularKrausMap, uncleWallGram]

/-- The finite contraction of the five actual transfer maps. The two wall
maps are rectangular and act on the actual A/B bond spaces. Source:
arXiv:1210.6613, phiN-def and the norm calculation in Lemma lowenergystates. -/
def uncleTwoWallTransfer (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ :=
  (Kraus.mapLM A ^ p).comp ((uncleWallGramMap A B R r).comp
    ((Kraus.mapLM B ^ q).comp ((uncleWallGramMap B A L s).comp (Kraus.mapLM A ^ t))))

/-- The operator trace is exactly the sum of squared five-segment
coefficients, before identifying the product of configuration spaces with the
physical chain. Source: arXiv:1210.6613, the norm of phiN-def. -/
theorem trace_uncleTwoWallTransfer_eq_sum (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q s t) =
      ∑ u : Cfg d p, ∑ v : Cfg d r, ∑ w : Cfg d q,
        ∑ x : Cfg d s, ∑ y : Cfg d t,
          uncleTwoWallCoefficient A B R L (List.ofFn u) (List.ofFn v)
              (List.ofFn w) (List.ofFn x) (List.ofFn y) *
            star (uncleTwoWallCoefficient A B R L (List.ofFn u) (List.ofFn v)
              (List.ofFn w) (List.ofFn x) (List.ofFn y)) := by
  unfold uncleTwoWallTransfer uncleWallGramMap
  rw [← Matrix.rectangularKrausMap_evalWord_ofFn A p,
    ← Matrix.rectangularKrausMap_evalWord_ofFn B q,
    ← Matrix.rectangularKrausMap_evalWord_ofFn A t]
  simp only [Matrix.rectangularKrausMap_comp]
  rw [Matrix.linearMap_trace_rectangularKrausMap]
  simp only [Fintype.sum_prod_type, uncleTwoWallCoefficient, Matrix.mul_assoc]

/-- The two exterior A segments join under the operator trace. For the
source trial their common length N therefore becomes one separation of
length 2N. Source: arXiv:1210.6613, the cyclic contraction in the proof of
Lemma lowenergystates. -/
theorem trace_uncleTwoWallTransfer_join_exterior
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q s t) =
      LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L (p + t) r q s 0) := by
  let E := Kraus.mapLM A
  let M := (uncleWallGramMap A B R r).comp
    ((Kraus.mapLM B ^ q).comp (uncleWallGramMap B A L s))
  change LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) (E ^ p * (M * E ^ t)) =
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) (E ^ (p + t) * (M * E ^ 0))
  rw [pow_zero, mul_one, ← mul_assoc,
    LinearMap.trace_mul_comm (R := ℂ) (M := Matrix (Fin a) (Fin a) ℂ)
      (E ^ p * M) (E ^ t), ← mul_assoc, ← pow_add, Nat.add_comm t p]

/-- Canonical concatenation of five consecutive physical configuration segments.
Source: arXiv:1210.6613, the five intervals in phiN-def. -/
def uncleFiveConfigEquiv (p r q s t : ℕ) :
    Cfg d p × (Cfg d r × (Cfg d q × (Cfg d s × Cfg d t))) ≃
      Cfg d (p + r + q + s + t) := by
  let e₁ := (Equiv.prodAssoc (Cfg d p) (Cfg d r) (Cfg d q × (Cfg d s × Cfg d t))).symm
  let e₂ := (Fin.appendEquiv (α := Fin d) p r).prodCongr
    (Equiv.refl (Cfg d q × (Cfg d s × Cfg d t)))
  let e₃ := (Equiv.prodAssoc (Cfg d (p + r)) (Cfg d q) (Cfg d s × Cfg d t)).symm
  let e₄ := (Fin.appendEquiv (α := Fin d) (p + r) q).prodCongr (Equiv.refl (Cfg d s × Cfg d t))
  let e₅ := (Equiv.prodAssoc (Cfg d (p + r + q)) (Cfg d s) (Cfg d t)).symm
  let e₆ := (Fin.appendEquiv (α := Fin d) (p + r + q) s).prodCongr (Equiv.refl (Cfg d t))
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans
    (Fin.appendEquiv (α := Fin d) (p + r + q + s) t))))))

/-- The five-segment configuration equivalence is left-associated concatenation.
Source: arXiv:1210.6613, the physical word ordering in phiN-def. -/
theorem uncleFiveConfigEquiv_apply (p r q s t : ℕ)
    (z : Cfg d p × (Cfg d r × (Cfg d q × (Cfg d s × Cfg d t)))) :
    uncleFiveConfigEquiv p r q s t z =
      Fin.append (Fin.append (Fin.append (Fin.append z.1 z.2.1) z.2.2.1)
        z.2.2.2.1) z.2.2.2.2 := rfl

/-- The squared norm of the actual finite two-wall trial is the real
operator trace of its five actual transfer maps. This is a finite identity,
not an assumed large-separation factorization or norm-growth conclusion.
Source: arXiv:1210.6613, phiN-def and the norm computation in the proof of
Lemma lowenergystates, lines 1196–1265. -/
theorem norm_uncleTwoWallTrial_sq_eq_trace_transfer
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (p + r + q + s + t))).symm
        (uncleTwoWallTrial A B R L p r q s t)‖ ^ 2 =
      (LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q s t)).re := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ σ : Cfg d (p + r + q + s + t),
    ‖uncleTwoWallTrial A B R L p r q s t σ‖ ^ 2) = _
  rw [← (uncleFiveConfigEquiv (d := d) p r q s t).sum_comp
    (fun σ ↦ ‖uncleTwoWallTrial A B R L p r q s t σ‖ ^ 2)]
  simp only [Fintype.sum_prod_type, uncleFiveConfigEquiv_apply, uncleTwoWallTrial_append_apply]
  rw [trace_uncleTwoWallTransfer_eq_sum]
  change _ = Complex.reCLM _
  simp only [map_sum, Complex.reCLM_apply, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The actual source trial norm is the cyclic contraction with separation
lengths 2N in A and 2N−1 in B, and two moving intervals of N+1 sites.
No limiting factorization is supplied. Source: arXiv:1210.6613,
phiN-def and the norm calculation in Lemma lowenergystates. -/
theorem norm_uncleTwoWallTrialSource_sq_eq_trace_transfer
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) (hN : 0 < N) :
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)‖ ^ 2 =
      (LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0)).re := by
  rw [norm_uncleTwoWallTrialSource_eq A B R L N hN,
    norm_uncleTwoWallTrial_sq_eq_trace_transfer]
  exact congrArg Complex.re (by simpa only [two_mul] using
    trace_uncleTwoWallTransfer_join_exterior A B R L N (N + 1) (2 * N - 1) (N + 1) N)

/-- Replacing the two separated transfer powers by their actual canonical
rank-one trace contractions gives exactly the product of the two finite
one-wall weights. This identifies the leading term without assuming that
the transfer powers have already converged. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, lines 1230–1265. -/
theorem trace_uncleWallGram_rankOne_factorization
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (ρB : Matrix (Fin b) (Fin b) ℂ)
    (r s : ℕ) :
    let fA := (Matrix.traceLinearMap (Fin a) ℂ ℂ).comp
      (mulLeftLinearMap (n := Fin a) ℂ ρA)
    let fB := (Matrix.traceLinearMap (Fin b) ℂ ℂ).comp
      (mulLeftLinearMap (n := Fin b) ℂ ρB)
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        ((fA.smulRight 1).comp ((uncleWallGramMap A B R r).comp
          ((fB.smulRight 1).comp (uncleWallGramMap B A L s)))) =
      uncleWallGramWeight A B R ρA r * uncleWallGramWeight B A L ρB s := by
  dsimp only
  let fA := (Matrix.traceLinearMap (Fin a) ℂ ℂ).comp
    (mulLeftLinearMap (n := Fin a) ℂ ρA)
  let fB := (Matrix.traceLinearMap (Fin b) ℂ ℂ).comp
    (mulLeftLinearMap (n := Fin b) ℂ ρB)
  change LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
    ((fA.smulRight 1).comp ((uncleWallGramMap A B R r).comp
      ((fB.smulRight 1).comp (uncleWallGramMap B A L s)))) = _
  have hmap : (fA.smulRight 1).comp ((uncleWallGramMap A B R r).comp
        ((fB.smulRight 1).comp (uncleWallGramMap B A L s))) =
      (fB.comp (uncleWallGramMap B A L s)).smulRight
        (uncleWallGramWeight A B R ρA r • (1 : Matrix (Fin a) (Fin a) ℂ)) := by
    apply LinearMap.ext
    intro X
    simp [fA, fB, uncleWallGramWeight, LinearMap.smulRight_apply, map_smul,
      uncleWallGramMap_one, smul_smul, mul_comm]
  rw [hmap, LinearMap.trace_smulRight]
  simp only [LinearMap.comp_apply, map_smul, uncleWallGramMap_one]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- Every power of a unital transfer map contracts the matrix operator norm.
The trial-norm, factorization and overlap estimates of arXiv:1210.6613,
proof of Lemma lowenergystates, bound their pure transfer powers this way. -/
theorem norm_mapLM_pow_apply_le_of_mapLM_one (A : MPSTensor d a)
    (hA : Kraus.mapLM A 1 = 1) (n : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
    ‖((Kraus.mapLM A) ^ n) X‖ ≤ ‖X‖ := by
  have hCP : IsKrausCP (Kraus.mapLM A) := Kraus.isCPMap_mapLM A
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change ‖Kraus.mapLM A (((Kraus.mapLM A) ^ n) X)‖ ≤ ‖X‖
      exact (hCP.norm_apply_le_of_map_one_eq_one hA _).trans ih

end MPSTensor

end

end UncleTrialTransferNorm

section UncleNormFactorization

/-!
## Quantitative factorization of the two-wall transfer contraction

The exact finite transfer identity is approximated by the two
canonical rank-one contractions. Pure transfer powers converge by source
block injectivity and unital normalization, and the moving-wall
maps have linear bounds. This derives a geometric factorization error;
neither factorization nor norm growth is assumed:
\(|\operatorname{Tr}\mathcal T_N-\eta_R(N+1)\eta_L(N+1)|\le C(N+1)^2z^N\)
with \(0<z<1\), and hence \(\|\varphi_N\|^2/(N+1)^2\to\operatorname{Re}(\kappa_R\kappa_L)\)
for the limiting wall slopes \(\kappa_R,\kappa_L\).

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1230–1265.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Filter

namespace MPSTensor

variable {d a b : ℕ}

/-- Replacing the separated transfer powers by their canonical
contractions gives an error bounded by a quadratic length factor times a
geometric sequence. The leading term is the product of the two
finite wall Gram weights. Source: arXiv:1210.6613, proof of Lemma
lowenergystates, lines 1230–1265. -/
theorem uncleTwoWallTransfer_factorization_bound [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hIA : Kraus.IsInjective A) (hIB : Kraus.IsInjective B)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C z : ℝ, 0 < C ∧ 0 < z ∧ z < 1 ∧ ∀ N : ℕ, 0 < N →
      ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
          (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0) -
        uncleWallGramWeight A B R ρA (N + 1) * uncleWallGramWeight B A L ρB (N + 1)‖ ≤
        C * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N := by
  classical
  obtain ⟨cA, rA, hcA, hrA, hrA1, hdecA⟩ :=
    uncleTransfer_pow_sub_projection_bound A hIA hUA ρA htrA hFA
  obtain ⟨cB, rB, hcB, hrB, hrB1, hdecB⟩ :=
    uncleTransfer_pow_sub_projection_bound B hIB hUB ρB htrB hFB
  obtain ⟨cR, hcR, hwallR⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul A B R ρA hρA hFA hUB hAB
  obtain ⟨cL, hcL, hwallL⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul B A L ρB hρB hFB hUA hBA
  have hGR (n : ℕ) (X : Matrix (Fin b) (Fin b) ℂ) :
      ‖uncleWallGramMap A B R n X‖ ≤ cR * n * ‖X‖ := by
    simpa only [uncleWallGramMap] using hwallR n X
  have hGL (n : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleWallGramMap B A L n X‖ ≤ cL * n * ‖X‖ := by
    simpa only [uncleWallGramMap] using hwallL n X
  let PA := uncleDensityProjection ρA
  let PB := uncleDensityProjection ρB
  have hPA (X : Matrix (Fin a) (Fin a) ℂ) : ‖PA X‖ ≤ ‖X‖ := by
    change ‖Matrix.trace (ρA * X) • (1 : Matrix (Fin a) (Fin a) ℂ)‖ ≤ ‖X‖
    simpa only [norm_smul, norm_one, mul_one, htrA, Complex.one_re, one_mul] using
      hρA.posSemidef.norm_trace_mul_le X
  let T := fun N ↦ (Kraus.mapLM A ^ (2 * N)).comp ((uncleWallGramMap A B R (N + 1)).comp
    ((Kraus.mapLM B ^ (2 * N - 1)).comp (uncleWallGramMap B A L (N + 1))))
  let U := fun N ↦ PA.comp ((uncleWallGramMap A B R (N + 1)).comp
    (PB.comp (uncleWallGramMap B A L (N + 1))))
  let z := max rA rB
  have hz : 0 < z := lt_of_lt_of_le hrA (le_max_left _ _)
  have hz1 : z < 1 := max_lt hrA1 hrB1
  let K := cR * cL * (cA + cB)
  have hK : 0 < K := by dsimp [K]; positivity
  have hpoint (N : ℕ) (hN : 0 < N) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖(T N - U N) X‖ ≤ K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N * ‖X‖ := by
    let m : ℝ := ((N + 1 : ℕ) : ℝ)
    let Y := uncleWallGramMap B A L (N + 1) X
    let Z := uncleWallGramMap A B R (N + 1) (((Kraus.mapLM B) ^ (2 * N - 1)) Y)
    let W := uncleWallGramMap A B R (N + 1) (PB Y)
    have hY : ‖Y‖ ≤ cL * m * ‖X‖ := hGL (N + 1) X
    have hZ : ‖Z‖ ≤ cR * m * (cL * m * ‖X‖) := by
      calc
        ‖Z‖ ≤ cR * m * ‖((Kraus.mapLM B) ^ (2 * N - 1)) Y‖ := hGR (N + 1) _
        _ ≤ cR * m * ‖Y‖ := mul_le_mul_of_nonneg_left
          (norm_mapLM_pow_apply_le_of_mapLM_one B hUB _ _) (by positivity)
        _ ≤ cR * m * (cL * m * ‖X‖) := mul_le_mul_of_nonneg_left hY (by positivity)
    have hrateA : rA ^ (2 * N) ≤ z ^ N :=
      (pow_le_pow_left₀ hrA.le (show rA ≤ z from le_max_left _ _) (2 * N)).trans
        (pow_le_pow_of_le_one hz.le hz1.le (by omega))
    have hrateB : rB ^ (2 * N - 1) ≤ z ^ N :=
      (pow_le_pow_left₀ hrB.le (show rB ≤ z from le_max_right _ _) (2 * N - 1)).trans
        (pow_le_pow_of_le_one hz.le hz1.le (by omega))
    have hfirst : ‖((Kraus.mapLM A) ^ (2 * N)) Z - PA Z‖ ≤
        cA * z ^ N * (cR * m * (cL * m * ‖X‖)) :=
      (hdecA (2 * N) (by omega) Z).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hrateA hcA.le) hZ
          (norm_nonneg _) (by positivity))
    have hdiff : ‖((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y‖ ≤
        cB * z ^ N * (cL * m * ‖X‖) :=
      (hdecB (2 * N - 1) (by omega) Y).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hrateB hcB.le) hY
          (norm_nonneg _) (by positivity))
    have hsecond : ‖PA (uncleWallGramMap A B R (N + 1)
        (((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y))‖ ≤
        cR * m * (cB * z ^ N * (cL * m * ‖X‖)) :=
      (hPA _).trans ((hGR (N + 1) _).trans
        (mul_le_mul_of_nonneg_left hdiff (by positivity)))
    change ‖((Kraus.mapLM A) ^ (2 * N)) Z - PA W‖ ≤ _
    have hsub : ((Kraus.mapLM A) ^ (2 * N)) Z - PA W =
        (((Kraus.mapLM A) ^ (2 * N)) Z - PA Z) +
          PA (uncleWallGramMap A B R (N + 1)
            (((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y)) := by
      dsimp [Z, W]
      simp only [map_sub]
      abel
    rw [hsub]
    calc
      _ ≤ ‖((Kraus.mapLM A) ^ (2 * N)) Z - PA Z‖ +
          ‖PA (uncleWallGramMap A B R (N + 1)
            (((Kraus.mapLM B) ^ (2 * N - 1)) Y - PB Y))‖ := norm_add_le _ _
      _ ≤ cA * z ^ N * (cR * m * (cL * m * ‖X‖)) +
          cR * m * (cB * z ^ N * (cL * m * ‖X‖)) := add_le_add hfirst hsecond
      _ = K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N * ‖X‖ := by dsimp [K, m]; ring
  let V := Matrix (Fin a) (Fin a) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let : FiniteDimensional ℂ (V →L[ℂ] V) := Φ.toLinearEquiv.finiteDimensional
  let tr : (V →L[ℂ] V) →L[ℂ] ℂ :=
    ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap
  refine ⟨(‖tr‖ + 1) * K, z, by positivity, hz, hz1, fun N hN ↦ ?_⟩
  have hnorm : ‖Φ (T N - U N)‖ ≤ K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hpoint N hN)
  have hT : uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0 = T N := by
    rfl
  have hU : LinearMap.trace ℂ V (U N) =
      uncleWallGramWeight A B R ρA (N + 1) * uncleWallGramWeight B A L ρB (N + 1) :=
    trace_uncleWallGram_rankOne_factorization A B R L ρA ρB (N + 1) (N + 1)
  calc
    _ = ‖tr (Φ (T N - U N))‖ := by
      rw [hT, ← hU]
      change _ = ‖LinearMap.trace ℂ V (T N - U N)‖
      rw [map_sub]
    _ ≤ ‖tr‖ * ‖Φ (T N - U N)‖ := tr.le_opNorm _
    _ ≤ ‖tr‖ * (K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg tr)
    _ ≤ (‖tr‖ + 1) * (K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (‖tr‖ + 1) * K * ((N + 1 : ℕ) : ℝ) ^ 2 * z ^ N := by ring

/-- The squared norm of the source trial, divided by the squared
moving-window length, converges to the product of the limiting
wall coefficients. No positive-slope or norm-growth premise is required.
Source: arXiv:1210.6613, proof of Lemma lowenergystates. -/
theorem uncleTwoWallTrialSource_normalized_norm_sq_tendsto [NeZero a] [NeZero b]
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hIA : Kraus.IsInjective A) (hIB : Kraus.IsInjective B)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef) (htrA : Matrix.trace ρA = 1)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef) (htrB : Matrix.trace ρB = 1)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB)
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    Tendsto (fun N : ℕ ↦
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)‖ ^ 2 / ((N + 1 : ℕ) : ℝ) ^ 2) atTop
      (𝓝 ((uncleWallNormSlope A B R ρA * uncleWallNormSlope B A L ρB).re)) := by
  obtain ⟨C, z, _, hz, hz1, hbound⟩ := uncleTwoWallTransfer_factorization_bound
    A B R L hIA hIB hUA hUB ρA hρA htrA ρB hρB htrB hFA hFB hAB hBA
  let m := fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)
  let s := fun N : ℕ ↦
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
      (uncleTwoWallTrialSource A B R L N)‖ ^ 2
  let w := fun N : ℕ ↦
    (uncleWallGramWeight A B R ρA (N + 1) * uncleWallGramWeight B A L ρB (N + 1)).re /
      (m N) ^ 2
  let e := fun N : ℕ ↦ s N / (m N) ^ 2 - w N
  have habs : ∀ᶠ N : ℕ in atTop, |e N| ≤ C * z ^ N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hm : 0 < m N := by dsimp [m]; positivity
    dsimp only [e, w, s]
    rw [norm_uncleTwoWallTrialSource_sq_eq_trace_transfer A B R L N hN]
    rw [← sub_div, ← Complex.sub_re]
    calc
      _ = |(LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
          (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0) -
          uncleWallGramWeight A B R ρA (N + 1) *
            uncleWallGramWeight B A L ρB (N + 1)).re| / (m N) ^ 2 := by
              rw [abs_div, abs_of_nonneg (sq_nonneg (m N))]
      _ ≤ ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
          (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0) -
          uncleWallGramWeight A B R ρA (N + 1) *
            uncleWallGramWeight B A L ρB (N + 1)‖ / (m N) ^ 2 :=
              div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (sq_nonneg _)
      _ ≤ (C * (m N) ^ 2 * z ^ N) / (m N) ^ 2 :=
        div_le_div_of_nonneg_right (hbound N hN) (sq_nonneg _)
      _ = C * z ^ N := by
        rw [mul_right_comm C ((m N) ^ 2) (z ^ N),
          mul_div_cancel_right₀ _ (pow_ne_zero 2 (ne_of_gt hm))]
  have hgeom : Tendsto (fun N : ℕ ↦ C * z ^ N) atTop (𝓝 (0 : ℝ)) := by
    have hC : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
    simpa only [mul_zero] using hC.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hz.le hz1)
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using habs) hgeom
  have hR := (uncleWallGramWeight_normalized_tendsto A B R ρA hρA.isHermitian
    hFA hUB hAB).comp (tendsto_add_atTop_nat 1)
  have hL := (uncleWallGramWeight_normalized_tendsto B A L ρB hρB.isHermitian
    hFB hUA hBA).comp (tendsto_add_atTop_nat 1)
  have hw : Tendsto w atTop
      (𝓝 ((uncleWallNormSlope A B R ρA * uncleWallNormSlope B A L ρB).re)) := by
    have hprod := (Complex.continuous_re.tendsto _).comp (hR.mul hL)
    refine Tendsto.congr (fun N ↦ ?_) hprod
    dsimp only [w, m, Function.comp_apply]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, div_eq_mul_inv]
    ring
  change Tendsto (fun N : ℕ ↦ s N / (m N) ^ 2) atTop _
  simpa only [e, sub_add_cancel, zero_add] using he.add hw

end MPSTensor

end UncleNormFactorization

section UnclePinnedTrialNorm

/-!
## Linear norm bounds for an actual trial with one pinned wall

A one-site wall interval pins that wall. The other interval retains its
actual moving-wall Kraus map. Source unital diagonal transfers contract
matrix operator norms, while the actual moving-wall Gram bound is linear
in its length. The exact finite transfer trace therefore bounds the actual
pinned trial norm linearly, uniformly in all three padding lengths.

Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296.
No state-norm growth or endpoint-energy rate is supplied as a hypothesis.
-/

noncomputable section

open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace MPSTensor

variable {d a b : ℕ}

private theorem norm_linearMap_trace_le_entry_bound
    (T : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (C : ℝ) (hT : ∀ X, ‖T X‖ ≤ C * ‖X‖) :
    ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) T‖ ≤ (a : ℝ) ^ 2 * C := by
  rw [Matrix.linearMap_trace_eq_sum_apply_single]
  calc
    _ ≤ ∑ i : Fin a, ‖∑ j : Fin a, T (Matrix.single i j 1) i j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin a, ∑ j : Fin a, ‖T (Matrix.single i j 1) i j‖ :=
      Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
    _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖T (Matrix.single i j 1)‖ := Matrix.norm_apply_le_l2_opNorm _ i j
        _ ≤ C * ‖(Matrix.single i j 1 : Matrix (Fin a) (Fin a) ℂ)‖ := hT _
        _ = C := by rw [Matrix.l2_opNorm_single_one, mul_one]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- An actual one-site R interval and one moving L interval have a uniform
linear squared-norm bound, independently of every uniform padding length.
The stationary faithful density and mixed damping are the source normalized
block assumptions used for the actual L-wall Gram estimate.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem norm_uncleTwoWallTrial_one_wall_sq_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hB : Kraus.mapLM B 1 = 1)
    (ρ : Matrix (Fin b) (Fin b) ℂ) (hρ : ρ.PosDef)
    (hρB : Kraus.adjointMap B ρ = ρ)
    (hSpect : Kraus.mixedMapSpectralRadius B A < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q s t : ℕ,
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (p + 1 + q + s + t))).symm
          (uncleTwoWallTrial A B R L p 1 q s t)‖ ^ 2 ≤ C * s := by
  obtain ⟨C, hC, hL⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul B A L ρ hρ hρB hA hSpect
  let S := (Matrix.trace (uncleWallGram A B R 1)).re
  have hS : 0 ≤ S :=
    (Complex.nonneg_iff.mp (uncleWallGram_posSemidef A B R 1).trace_nonneg).1
  let K := S + 1
  have hK : 0 < K := by dsimp [K]; linarith
  have hR (X : Matrix (Fin b) (Fin b) ℂ) :
      ‖uncleWallGramMap A B R 1 X‖ ≤ K * ‖X‖ := by
    change ‖Matrix.rectangularKrausMap
      (fun σ : Cfg d 1 ↦ uncleDomainWallWord A B R (List.ofFn σ)) X‖ ≤ _
    exact (uncleWallGramMap_apply_l2_opNorm_le_trace A B R 1 X).trans
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg X))
  have hLbound (s : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleWallGramMap B A L s X‖ ≤ C * s * ‖X‖ := by
    exact hL s X
  have hTotal (p q s t : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleTwoWallTransfer A B R L p 1 q s t X‖ ≤ (K * C * s) * ‖X‖ := by
    change ‖((Kraus.mapLM A) ^ p)
      (uncleWallGramMap A B R 1 (((Kraus.mapLM B) ^ q)
        (uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X))))‖ ≤ _
    calc
      _ ≤ ‖uncleWallGramMap A B R 1 (((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X)))‖ :=
        norm_mapLM_pow_apply_le_of_mapLM_one A hA p _
      _ ≤ K * ‖((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X))‖ := hR _
      _ ≤ K * ‖uncleWallGramMap B A L s (((Kraus.mapLM A) ^ t) X)‖ :=
        mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one B hB q _) hK.le
      _ ≤ K * (C * s * ‖((Kraus.mapLM A) ^ t) X‖) :=
        mul_le_mul_of_nonneg_left (hLbound s _) hK.le
      _ ≤ K * (C * s * ‖X‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one A hA t X)
          (mul_nonneg hC.le (Nat.cast_nonneg s))) hK.le
      _ = _ := by ring
  let D := (a : ℝ) ^ 2 * K * C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun p q s t ↦ ?_⟩
  rw [norm_uncleTwoWallTrial_sq_eq_trace_transfer]
  calc
    _ ≤ ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p 1 q s t)‖ := Complex.re_le_norm _
    _ ≤ (a : ℝ) ^ 2 * (K * C * s) :=
      norm_linearMap_trace_le_entry_bound _ _ (hTotal p q s t)
    _ = ((a : ℝ) ^ 2 * K * C) * s := by ring
    _ ≤ D * s := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Nat.cast_nonneg s)

/-- The complementary actual trial with its second wall interval pinned
also has a uniform linear squared-norm bound in the first moving interval.
Source: arXiv:1210.6613, proof of Lemma lowenergystates, lines 1289–1296. -/
theorem norm_uncleTwoWallTrial_second_wall_sq_le_mul
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hA : Kraus.mapLM A 1 = 1) (hB : Kraus.mapLM B 1 = 1)
    (ρ : Matrix (Fin a) (Fin a) ℂ) (hρ : ρ.PosDef)
    (hρA : Kraus.adjointMap A ρ = ρ)
    (hSpect : Kraus.mixedMapSpectralRadius A B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ p r q t : ℕ,
      ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (p + r + q + 1 + t))).symm
          (uncleTwoWallTrial A B R L p r q 1 t)‖ ^ 2 ≤ C * r := by
  obtain ⟨C, hC, hR⟩ := uncleWallGramMap_apply_l2_opNorm_le_mul A B R ρ hρ hρA hB hSpect
  let S := (Matrix.trace (uncleWallGram B A L 1)).re
  have hS : 0 ≤ S :=
    (Complex.nonneg_iff.mp (uncleWallGram_posSemidef B A L 1).trace_nonneg).1
  let K := S + 1
  have hK : 0 < K := by dsimp [K]; linarith
  have hL (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleWallGramMap B A L 1 X‖ ≤ K * ‖X‖ := by
    exact (uncleWallGramMap_apply_l2_opNorm_le_trace B A L 1 X).trans
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg X))
  have hTotal (p r q t : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
      ‖uncleTwoWallTransfer A B R L p r q 1 t X‖ ≤ (C * K * r) * ‖X‖ := by
    change ‖((Kraus.mapLM A) ^ p)
      (uncleWallGramMap A B R r (((Kraus.mapLM B) ^ q)
        (uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X))))‖ ≤ _
    calc
      _ ≤ ‖uncleWallGramMap A B R r (((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X)))‖ :=
        norm_mapLM_pow_apply_le_of_mapLM_one A hA p _
      _ ≤ C * r * ‖((Kraus.mapLM B) ^ q)
          (uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X))‖ := hR r _
      _ ≤ C * r * ‖uncleWallGramMap B A L 1 (((Kraus.mapLM A) ^ t) X)‖ :=
        mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one B hB q _)
          (mul_nonneg hC.le (Nat.cast_nonneg r))
      _ ≤ C * r * (K * ‖((Kraus.mapLM A) ^ t) X‖) :=
        mul_le_mul_of_nonneg_left (hL _) (mul_nonneg hC.le (Nat.cast_nonneg r))
      _ ≤ C * r * (K * ‖X‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_mapLM_pow_apply_le_of_mapLM_one A hA t X) hK.le)
          (mul_nonneg hC.le (Nat.cast_nonneg r))
      _ = _ := by ring
  let D := (a : ℝ) ^ 2 * C * K + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun p r q t ↦ ?_⟩
  rw [norm_uncleTwoWallTrial_sq_eq_trace_transfer]
  calc
    _ ≤ ‖LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q 1 t)‖ := Complex.re_le_norm _
    _ ≤ (a : ℝ) ^ 2 * (C * K * r) :=
      norm_linearMap_trace_le_entry_bound _ _ (hTotal p r q t)
    _ = ((a : ℝ) ^ 2 * C * K) * r := by ring
    _ ≤ D * r := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Nat.cast_nonneg r)

end MPSTensor

end

end UnclePinnedTrialNorm
