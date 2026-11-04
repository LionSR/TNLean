/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SupportCoordinates

/-!
# Open-chain tensor parameters and bounded representations

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-! ### Finite parameter spaces for rational MPS approximation -/

namespace OBCChainTensor

/-- The finite index of all local tensor entries of one open-boundary chain with fixed
virtual dimensions. -/
abbrev ParameterIndex {D n : ℕ} (A : OBCChainTensor q D n) :=
  Σ p : Fin n,
    Fin q × Fin (A.bondDim p.castSucc) × Fin (A.bondDim p.succ)

/-- The finite complex parameter space of local tensor entries. -/
abbrev Parameters {D n : ℕ} (A : OBCChainTensor q D n) :=
  ParameterIndex A → ℂ

/-- A scalar and fixed-bond local tensor entries, all with rational real and imaginary
parts. -/
abbrev RationalParameters {D n : ℕ} (A : OBCChainTensor q D n) :=
  RationalComplex × (ParameterIndex A → RationalComplex)

/-- Forget the rationality certificates on a fixed-bond parameter point. -/
def rationalParametersVal {D n : ℕ} (A : OBCChainTensor q D n)
    (P : RationalParameters A) : ℂ × Parameters A :=
  Prod.map Subtype.val (Pi.map fun _ ↦ Subtype.val) P

/-- Rational fixed-bond parameter points are dense in the full complex parameter
space. -/
theorem denseRange_rationalParametersVal {D n : ℕ} (A : OBCChainTensor q D n) :
    DenseRange (rationalParametersVal A) := by
  have hpi : DenseRange
      (Pi.map fun _ : ParameterIndex A ↦ ((↑) : RationalComplex → ℂ)) :=
    DenseRange.piMap fun _ ↦ denseRange_rationalComplex_val
  have hprod := denseRange_rationalComplex_val.prodMap hpi
  exact hprod

/-- A uniformly bounded scalar and fixed-bond tensor parameter point has a
simultaneous dyadic approximation with one explicit coordinate-height bound. -/
theorem exists_dyadic_parameters_approximation {D n : ℕ}
    (A : OBCChainTensor q D n) {R : ℝ} {u t : ℕ}
    (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (P : ℂ × Parameters A) (hscalar : ‖P.1‖ ≤ R)
    (htensor : ∀ e, ‖P.2 e‖ ≤ R) :
    ∃ Q : ℂ × Parameters A,
      HasRationalComplexCoordinatesOfHeight (2 ^ (2 * u + 2 * t + 5)) Q.1 ∧
      (∀ e, HasRationalComplexCoordinatesOfHeight
        (2 ^ (2 * u + 2 * t + 5)) (Q.2 e)) ∧
      ‖P.1 - Q.1‖ ≤ (2 ^ t : ℝ)⁻¹ ∧
      ∀ e, ‖P.2 e - Q.2 e‖ ≤ (2 ^ t : ℝ)⁻¹ := by
  let f : Unit ⊕ ParameterIndex A → ℂ := fun e ↦
    match e with
    | Sum.inl _ => P.1
    | Sum.inr e => P.2 e
  have hf : ∀ e, ‖f e‖ ≤ R := by
    intro e
    cases e with
    | inl e => exact hscalar
    | inr e => exact htensor e
  obtain ⟨g, hgheight, hgclose⟩ :=
    exists_dyadic_rational_pi_approximation hR0 hR f hf
  let Q : ℂ × Parameters A := (g (Sum.inl ()), fun e ↦ g (Sum.inr e))
  refine ⟨Q, hgheight (Sum.inl ()), fun e ↦ hgheight (Sum.inr e), ?_, fun e ↦ ?_⟩
  · exact hgclose (Sum.inl ())
  · exact hgclose (Sum.inr e)

/-- Rebuild an open-boundary chain with the same virtual dimensions from its local
tensor-entry parameters. -/
def ofParameters {D n : ℕ} (A : OBCChainTensor q D n) (P : Parameters A) :
    OBCChainTensor q D n where
  bondDim := A.bondDim
  bondDim_le := A.bondDim_le
  left_dim := A.left_dim
  right_dim := A.right_dim
  tensor p i a c := P ⟨p, i, a, c⟩

/-- The local-entry parameters of an open-boundary chain. -/
def parameters {D n : ℕ} (A : OBCChainTensor q D n) : Parameters A :=
  fun e ↦ A.tensor e.1 e.2.1 e.2.2.1 e.2.2.2

@[simp]
theorem ofParameters_parameters {D n : ℕ} (A : OBCChainTensor q D n) :
    ofParameters A (parameters A) = A := by
  cases A
  rfl

/-- Entrywise perturbation of fixed-bond tensor parameters changes each contracted
physical coefficient by at most the number of virtual paths times the elementary
product perturbation bound. -/
theorem norm_coeff_ofParameters_sub_le_one {D n : ℕ}
    (A : OBCChainTensor q D n) (P Q : Parameters A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ e, ‖Q e‖ ≤ 1) (hclose : ∀ e, ‖P e - Q e‖ ≤ δ)
    (σ : Fin n → Fin q) :
    ‖(ofParameters A P).coeff σ - (ofParameters A Q).coeff σ‖ ≤
      Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ n - 1) := by
  classical
  unfold OBCChainTensor.coeff
  change ‖(∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩) -
    ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
        ((∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩) -
          ∏ p : Fin n, Q ⟨p, σ p, α p.castSucc, α p.succ⟩)‖ ≤
        ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
          ‖(∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩) -
            ∏ p : Fin n, Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _α : (p : Fin (n + 1)) → Fin (A.bondDim p),
          ((1 + δ) ^ n - 1) := by
      apply Finset.sum_le_sum
      intro α _hα
      simpa using norm_finset_prod_sub_prod_le_one Finset.univ
        (fun p : Fin n ↦ P ⟨p, σ p, α p.castSucc, α p.succ⟩)
        (fun p : Fin n ↦ Q ⟨p, σ p, α p.castSucc, α p.succ⟩)
        hδ (fun p _hp ↦ hQ ⟨p, σ p, α p.castSucc, α p.succ⟩)
        (fun p _hp ↦ hclose ⟨p, σ p, α p.castSucc, α p.succ⟩)
    _ = Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
          ((1 + δ) ^ n - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If reference tensor entries have norm at most one and the perturbed entries
are `δ`-close, then every perturbed contraction is bounded by the number of
virtual paths times `(1 + δ)^n`. -/
theorem norm_coeff_ofParameters_le_one_add {D n : ℕ}
    (A : OBCChainTensor q D n) (P Q : Parameters A) {δ : ℝ}
    (hQ : ∀ e, ‖Q e‖ ≤ 1) (hclose : ∀ e, ‖P e - Q e‖ ≤ δ)
    (σ : Fin n → Fin q) :
    ‖(ofParameters A P).coeff σ‖ ≤
      Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) * (1 + δ) ^ n := by
  classical
  unfold OBCChainTensor.coeff
  change ‖∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤ _
  calc
    ‖∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
        ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤
      ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
        ‖∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := norm_sum_le _ _
    _ ≤ ∑ _α : (p : Fin (n + 1)) → Fin (A.bondDim p), (1 + δ) ^ n := by
      apply Finset.sum_le_sum
      intro α _hα
      calc
        ‖∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ ≤
            ∏ p : Fin n, ‖P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := Finset.norm_prod_le _ _
        _ ≤ ∏ _p : Fin n, (1 + δ) := by
          apply Finset.prod_le_prod₀ (fun p _hp ↦ norm_nonneg _)
          intro p _hp
          calc
            ‖P ⟨p, σ p, α p.castSucc, α p.succ⟩‖ =
                ‖(P ⟨p, σ p, α p.castSucc, α p.succ⟩ -
                    Q ⟨p, σ p, α p.castSucc, α p.succ⟩) +
                  Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := by ring_nf
            _ ≤ ‖P ⟨p, σ p, α p.castSucc, α p.succ⟩ -
                    Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ +
                  ‖Q ⟨p, σ p, α p.castSucc, α p.succ⟩‖ := norm_add_le _ _
            _ ≤ δ + 1 := add_le_add (hclose _) (hQ _)
            _ = 1 + δ := by ring
        _ = (1 + δ) ^ n := by simp
    _ = Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) * (1 + δ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Simultaneously perturbing a unit-bounded scalar cap and unit-bounded tensor
entries changes each represented physical coefficient by the path count times
`(1 + δ)^(n+1) - 1`. -/
theorem norm_scalar_mul_coeff_ofParameters_sub_le_one {D n : ℕ}
    (A : OBCChainTensor q D n) (P Q : ℂ × Parameters A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQscalar : ‖Q.1‖ ≤ 1) (hQ : ∀ e, ‖Q.2 e‖ ≤ 1)
    (hscalarclose : ‖P.1 - Q.1‖ ≤ δ) (hclose : ∀ e, ‖P.2 e - Q.2 e‖ ≤ δ)
    (σ : Fin n → Fin q) :
    ‖P.1 * (ofParameters A P.2).coeff σ - Q.1 * (ofParameters A Q.2).coeff σ‖ ≤
      Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ (n + 1) - 1) := by
  have hcoeffP := norm_coeff_ofParameters_le_one_add A P.2 Q.2 hQ hclose σ
  have hcoeffdiff := norm_coeff_ofParameters_sub_le_one A P.2 Q.2 hδ hQ hclose σ
  have hpow : 0 ≤ (1 + δ) ^ n - 1 := by
    have : 1 ≤ (1 + δ) ^ n := one_le_pow₀ (by linarith)
    linarith
  calc
    ‖P.1 * (ofParameters A P.2).coeff σ - Q.1 * (ofParameters A Q.2).coeff σ‖ =
        ‖(P.1 - Q.1) * (ofParameters A P.2).coeff σ +
          Q.1 * ((ofParameters A P.2).coeff σ - (ofParameters A Q.2).coeff σ)‖ := by
      congr 1
      ring
    _ ≤ ‖P.1 - Q.1‖ * ‖(ofParameters A P.2).coeff σ‖ +
        ‖Q.1‖ * ‖(ofParameters A P.2).coeff σ - (ofParameters A Q.2).coeff σ‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ δ * (Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) * (1 + δ) ^ n) +
        1 * (Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
          ((1 + δ) ^ n - 1)) := by gcongr
    _ = Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ (n + 1) - 1) := by rw [pow_succ]; ring

/-- At a fixed physical configuration, contraction is continuous in all local tensor
entries. -/
theorem continuous_coeff_ofParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (σ : Fin n → Fin q) :
    Continuous (fun P : Parameters A ↦ (ofParameters A P).coeff σ) := by
  unfold OBCChainTensor.coeff
  change Continuous (fun P : Parameters A ↦
    ∑ α : (p : Fin (n + 1)) → Fin (A.bondDim p),
      ∏ p : Fin n, P ⟨p, σ p, α p.castSucc, α p.succ⟩)
  refine continuous_finsetSum
    (Finset.univ : Finset ((p : Fin (n + 1)) → Fin (A.bondDim p))) fun α _hα ↦ ?_
  refine continuous_finsetProd (Finset.univ : Finset (Fin n)) fun p _hp ↦ ?_
  exact continuous_apply _

/-- Contraction with an additional scalar is continuous in the scalar and all local
tensor entries. -/
theorem continuous_scalar_mul_coeff_ofParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (σ : Fin n → Fin q) :
    Continuous (fun P : ℂ × Parameters A ↦ P.1 * (ofParameters A P.2).coeff σ) :=
  continuous_fst.mul ((continuous_coeff_ofParameters A σ).comp continuous_snd)

/-- Contract scalar and local-tensor parameters to a vector on the first `n` sites.
The hypothesis `n ≤ L` identifies physical configurations with `Fin n` words. -/
noncomputable def vectorOfParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (hn : n ≤ L) (P : ℂ × Parameters A) : LeftBlockVector L q n :=
  WithLp.toLp 2 fun x ↦
    P.1 * (ofParameters A P.2).coeff ((leftConfigOfFinEquiv hn).symm x)

/-- A simultaneous `δ`-perturbation of unit-bounded fixed-bond parameters changes
the represented left-block vector by at most the number of physical configurations
times the virtual-path and product perturbation bounds. -/
theorem norm_vectorOfParameters_sub_le_one {D n : ℕ}
    (A : OBCChainTensor q D n) (hn : n ≤ L)
    (P Q : ℂ × Parameters A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQscalar : ‖Q.1‖ ≤ 1) (hQ : ∀ e, ‖Q.2 e‖ ≤ 1)
    (hscalarclose : ‖P.1 - Q.1‖ ≤ δ) (hclose : ∀ e, ‖P.2 e - Q.2 e‖ ≤ δ) :
    ‖vectorOfParameters (L := L) A hn P - vectorOfParameters (L := L) A hn Q‖ ≤
      (q ^ n : ℝ) * Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
        ((1 + δ) ^ (n + 1) - 1) := by
  let C : ℝ := Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) *
    ((1 + δ) ^ (n + 1) - 1)
  have hpow : 0 ≤ (1 + δ) ^ (n + 1) - 1 := by
    have : 1 ≤ (1 + δ) ^ (n + 1) := one_le_pow₀ (by linarith)
    linarith
  have hC : 0 ≤ C := mul_nonneg (by positivity) hpow
  have hbound := PiLp.norm_le_card_mul_of_forall_norm_le
    (vectorOfParameters (L := L) A hn P - vectorOfParameters (L := L) A hn Q)
    hC
    (fun x ↦ by
      change ‖P.1 * (ofParameters A P.2).coeff ((leftConfigOfFinEquiv hn).symm x) -
        Q.1 * (ofParameters A Q.2).coeff ((leftConfigOfFinEquiv hn).symm x)‖ ≤ C
      exact norm_scalar_mul_coeff_ofParameters_sub_le_one A P Q hδ hQscalar hQ
        hscalarclose hclose ((leftConfigOfFinEquiv hn).symm x))
  simpa only [C, Entropy.RegionConfig, Fintype.card_pi, Fintype.card_fin,
    Fintype.card_coe, card_leftBlock, min_eq_right hn, Finset.prod_const, Finset.card_univ,
    Nat.cast_mul, Nat.cast_pow, mul_assoc] using hbound

/-- Finite open-boundary tensor contraction is continuous as a map into the complete
Euclidean left-block vector, not merely coordinatewise. -/
theorem continuous_vectorOfParameters {D n : ℕ} (A : OBCChainTensor q D n)
    (hn : n ≤ L) :
    Continuous (vectorOfParameters (L := L) A hn) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro x
  exact continuous_scalar_mul_coeff_ofParameters A ((leftConfigOfFinEquiv hn).symm x)

/-- On fixed virtual spaces, rational scalar and local-tensor entries approximate the
contracted left-block vector arbitrarily well. -/
theorem exists_rational_parameters_close {D n : ℕ} (A : OBCChainTensor q D n)
    (hn : n ≤ L) (P : ℂ × Parameters A) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℂ × Parameters A,
      HasRationalComplexCoordinates Q.1 ∧
      (∀ e, HasRationalComplexCoordinates (Q.2 e)) ∧
      ‖vectorOfParameters (L := L) A hn P - vectorOfParameters (L := L) A hn Q‖ < ε := by
  have hpre :
      vectorOfParameters (L := L) A hn ⁻¹'
          Metric.ball (vectorOfParameters (L := L) A hn P) ε ∈ nhds P :=
    (continuous_vectorOfParameters A hn).continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds _ hε)
  obtain ⟨R, hR⟩ := (denseRange_rationalParametersVal A).mem_nhds hpre
  let Q : ℂ × Parameters A := rationalParametersVal A R
  refine ⟨Q, R.1.2, fun e ↦ (R.2 e).2, ?_⟩
  have hdist :
      dist (vectorOfParameters (L := L) A hn Q)
        (vectorOfParameters (L := L) A hn P) < ε := by
    simpa [Q] using hR
  rw [dist_comm] at hdist
  simpa [dist_eq_norm] using hdist

end OBCChainTensor

/-- Evaluating the scalar and local-entry parameters of an explicit left-open MPS
representation recovers its represented vector. -/
theorem LeftOpenMPSRepresentation.vectorOfParameters_eq {b k : ℕ}
    {v : LeftBlockVector L q k} (R : LeftOpenMPSRepresentation b v) (hk : k ≤ L) :
    OBCChainTensor.vectorOfParameters (L := L) R.tensor hk
      (R.scalar, OBCChainTensor.parameters R.tensor) = v := by
  ext x
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  change R.scalar * R.tensor.coeff y = v x
  calc
    R.scalar * R.tensor.coeff y = v (leftConfigOfFin y) := (R.coeff_eq y).symm
    _ = v x := congrArg v ((leftConfigOfFinEquiv hk).apply_symm_apply x)

/-- A normalized positive-length left-open MPS has an equivalent representation
with scalar cap one and every local tensor entry of norm at most one, without
increasing any virtual bond dimension. -/
theorem LeftOpenMPSRepresentation.exists_unitBounded_of_norm_eq_one
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (R : LeftOpenMPSRepresentation b v) (hk : n + 1 ≤ L) (hv : ‖v‖ = 1) :
    ∃ R' : LeftOpenMPSRepresentation b v,
      R'.scalar = 1 ∧ ∀ p i a c, ‖R'.tensor.tensor p i a c‖ ≤ 1 := by
  let B := R.tensor.smulSite (0 : Fin (n + 1)) R.scalar
  have hBcoeff : B.coeff = fun x ↦ v (leftConfigOfFin x) := by
    funext x
    change (R.tensor.smulSite (0 : Fin (n + 1)) R.scalar).coeff x = _
    rw [congrFun (OBCChainTensor.coeff_smulSite
      R.tensor (0 : Fin (n + 1)) R.scalar) x]
    change R.scalar * R.tensor.coeff x = v (leftConfigOfFin x)
    exact (R.coeff_eq x).symm
  have hBnorm : star B.coeff ⬝ᵥ B.coeff = 1 := by
    let w : EuclideanSpace ℂ (Fin (n + 1) → Fin q) := WithLp.toLp 2 B.coeff
    have hw : ‖w‖ = 1 := by
      have hiso := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (leftConfigOfFinEquiv hk).symm).norm_map v
      have hw_eq : w =
          LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (leftConfigOfFinEquiv hk).symm v := by
        ext x
        change B.coeff x = v (leftConfigOfFin x)
        exact congrFun hBcoeff x
      rw [hw_eq, hiso, hv]
    calc
      star B.coeff ⬝ᵥ B.coeff = B.coeff ⬝ᵥ star B.coeff := dotProduct_comm _ _
      _ = inner ℂ w w := by
        simpa only [w, WithLp.ofLp_toLp] using
          (EuclideanSpace.inner_eq_star_dotProduct w w).symm
      _ = (‖w‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K w
      _ = 1 := by rw [hw]; norm_num
  obtain ⟨B', hcoeff, hbond, hiso⟩ := B.exists_isometric_coeff_eq_of_norm hBnorm
  let R' : LeftOpenMPSRepresentation b v :=
    { tensor := B'
      scalar := 1
      internal_bondDim_le := fun k hk0 hkn ↦
        (hbond k).trans (R.internal_bondDim_le k hk0 hkn)
      coeff_eq := fun x ↦ by
        rw [one_mul]
        calc
          v (leftConfigOfFin x) = B.coeff x := (congrFun hBcoeff x).symm
          _ = B'.coeff x := (congrFun hcoeff x).symm }
  refine ⟨R', rfl, ?_⟩
  intro p i a c
  exact norm_apply_le_one_of_sum_conjTranspose_mul_eq_one
    (fun i ↦ B'.tensor p i) (hiso p) i a c

/-- A positive-length left-open MPS in the unit ball has a representation with
unit-bounded scalar cap and local tensor entries on the original bond spaces. -/
theorem LeftOpenMPSRepresentation.exists_unitBounded_of_norm_le_one
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (R : LeftOpenMPSRepresentation b v) (hk : n + 1 ≤ L) (hv : ‖v‖ ≤ 1) :
    ∃ R' : LeftOpenMPSRepresentation b v,
      ‖R'.scalar‖ ≤ 1 ∧ ∀ p i a c, ‖R'.tensor.tensor p i a c‖ ≤ 1 := by
  by_cases hvzero : v = 0
  · let R' : LeftOpenMPSRepresentation b v :=
      { tensor := OBCChainTensor.ofParameters R.tensor (fun _ ↦ 0)
        scalar := 0
        internal_bondDim_le := R.internal_bondDim_le
        coeff_eq := fun x ↦ by simp [hvzero] }
    exact ⟨R', by simp [R'], by intros; simp [R', OBCChainTensor.ofParameters]⟩
  · let w := (‖v‖ : ℂ)⁻¹ • v
    have hw : ‖w‖ = 1 := by
      simp [w, norm_smul, norm_inv, Complex.norm_real,
        norm_ne_zero_iff.mpr hvzero]
    let Rw : LeftOpenMPSRepresentation b w := R.smul (‖v‖ : ℂ)⁻¹
    obtain ⟨Rw', hcap, hentry⟩ := Rw.exists_unitBounded_of_norm_eq_one hk hw
    have hscale : (‖v‖ : ℂ) • w = v := by
      calc
        (‖v‖ : ℂ) • w = ((‖v‖ : ℂ) * (‖v‖ : ℂ)⁻¹) • v :=
          smul_smul (‖v‖ : ℂ) (‖v‖ : ℂ)⁻¹ v
        _ = v := by
          rw [mul_inv_cancel₀, one_smul]
          exact_mod_cast norm_ne_zero_iff.mpr hvzero
    let R' : LeftOpenMPSRepresentation b v :=
      { tensor := Rw'.tensor
        scalar := (‖v‖ : ℂ) * Rw'.scalar
        internal_bondDim_le := Rw'.internal_bondDim_le
        coeff_eq := fun x ↦ by
          calc
            v (leftConfigOfFin x) = ((‖v‖ : ℂ) • w) (leftConfigOfFin x) := by rw [hscale]
            _ = (‖v‖ : ℂ) * (Rw'.scalar * Rw'.tensor.coeff x) := by
              change (‖v‖ : ℂ) * w (leftConfigOfFin x) = _
              rw [Rw'.coeff_eq]
            _ = _ := (mul_assoc _ _ _).symm }
    refine ⟨R', ?_, hentry⟩
    simpa [R', hcap, Complex.norm_real, abs_of_nonneg (norm_nonneg v)] using hv

end TNLean.MPS.AreaLaw
