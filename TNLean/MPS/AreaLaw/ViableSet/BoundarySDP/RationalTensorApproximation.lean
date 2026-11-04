/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.TensorParameters

/-!
# Quantitative rational approximation of open-chain tensors

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Explicit left-open MPS data whose scalar and every local tensor entry have rational
real and imaginary parts.  This is the arithmetic information about retained vectors
that is not contained in `IsLeftOpenMPS`. -/
structure RationalLeftOpenMPSRepresentation (b : ℕ) {k : ℕ}
    (v : LeftBlockVector L q k) where
  tensor : OBCChainTensor q (max 1 (max 1 b)) k
  scalar : ℂ
  internal_bondDim_le : ∀ p, 0 < p.val → p.val < k → tensor.bondDim p ≤ max 1 b
  coeff_eq : ∀ x, v (leftConfigOfFin x) = scalar * tensor.coeff x
  scalar_rational : HasRationalComplexCoordinates scalar
  tensor_rational : ∀ p i a c,
    HasRationalComplexCoordinates (tensor.tensor p i a c)

namespace RationalLeftOpenMPSRepresentation

/-- Evaluating the canonical scalar and local-entry parameters of a rational MPS
representation recovers its represented left-block vector. -/
theorem vectorOfParameters_eq {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) (hk : k ≤ L) :
    OBCChainTensor.vectorOfParameters (L := L) R.tensor hk
      (R.scalar, OBCChainTensor.parameters R.tensor) = v := by
  ext x
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  change R.scalar * R.tensor.coeff y = v x
  calc
    R.scalar * R.tensor.coeff y = v (leftConfigOfFin y) := (R.coeff_eq y).symm
    _ = v x := congrArg v ((leftConfigOfFinEquiv hk).apply_symm_apply x)

/-- Forgetting rationality retains the explicit left-open MPS representation. -/
def representation {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) : LeftOpenMPSRepresentation b v where
  tensor := R.tensor
  scalar := R.scalar
  internal_bondDim_le := R.internal_bondDim_le
  coeff_eq := R.coeff_eq

/-- Rational scalar and local-entry parameters on fixed virtual spaces give an explicit
rational left-open MPS representation. -/
noncomputable def ofParameters {b k : ℕ} {v : LeftBlockVector L q k}
    (R : LeftOpenMPSRepresentation b v) (hk : k ≤ L)
    (P : ℂ × OBCChainTensor.Parameters R.tensor)
    (hscalar : HasRationalComplexCoordinates P.1)
    (htensor : ∀ e, HasRationalComplexCoordinates (P.2 e)) :
    RationalLeftOpenMPSRepresentation b
      (OBCChainTensor.vectorOfParameters (L := L) R.tensor hk P) where
  tensor := OBCChainTensor.ofParameters R.tensor P.2
  scalar := P.1
  internal_bondDim_le := R.internal_bondDim_le
  coeff_eq := by
    intro x
    change P.1 * (OBCChainTensor.ofParameters R.tensor P.2).coeff
      ((leftConfigOfFinEquiv hk).symm (leftConfigOfFin x)) =
        P.1 * (OBCChainTensor.ofParameters R.tensor P.2).coeff x
    have hx : (leftConfigOfFinEquiv (q := q) hk).symm (leftConfigOfFin x) = x :=
      (leftConfigOfFinEquiv hk).symm_apply_apply x
    rw [hx]
  scalar_rational := hscalar
  tensor_rational := by
    intro p i a c
    exact htensor ⟨p, i, a, c⟩

/-- Appending one site preserves rationality of every local tensor entry. -/
theorem tensor_snoc_rational {D n : ℕ} (A : OBCChainTensor q D n) (f : Fin q → ℂ)
    (hA : ∀ p i a c, HasRationalComplexCoordinates (A.tensor p i a c))
    (hf : ∀ i, HasRationalComplexCoordinates (f i)) :
    ∀ p i a c, HasRationalComplexCoordinates ((A.snoc f).tensor p i a c) := by
  intro p
  refine Fin.lastCases ?_ (fun p' ↦ ?_) p
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_last]
    change HasRationalComplexCoordinates (f i)
    exact hf i
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_castSucc]
    change HasRationalComplexCoordinates (A.tensor p' i _ _)
    exact hA p' i _ _

/-- Every physical coefficient represented by rational open-chain tensor data is a
Gaussian rational complex number. -/
theorem coordinate_rational {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinates (v x) := by
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  have hxy : leftConfigOfFin y = x := (leftConfigOfFinEquiv hk).apply_symm_apply x
  rw [← hxy]
  rw [R.coeff_eq]
  apply R.scalar_rational.mul
  unfold OBCChainTensor.coeff
  apply HasRationalComplexCoordinates.fintype_sum
  intro path
  apply HasRationalComplexCoordinates.fintype_prod
  intro p
  exact R.tensor_rational p
    (y p)
    (path p.castSucc) (path p.succ)

/-- Forgetting arithmetic information recovers the mathematical MPS predicate. -/
theorem isLeftOpenMPS {b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentation b v) : IsLeftOpenMPS b v :=
  R.representation.isLeftOpenMPS

/-- Appending a computational-basis site preserves rational open-chain tensor data. -/
noncomputable def extendSite {i b : ℕ} (hi0 : 0 < i) (hiL : i ≤ L)
    {v : LeftBlockVector L q (i - 1)}
    (R : RationalLeftOpenMPSRepresentation b v) (k : Fin q) :
    RationalLeftOpenMPSRepresentation b (AreaLaw.extendSite i k v) := by
  cases i with
  | zero => omega
  | succ n =>
      simp only [Nat.succ_sub_one] at v R ⊢
      let f : Fin q → ℂ := fun y ↦ if y = k then 1 else 0
      let rep := R.representation.snoc
        (lt_of_lt_of_le Nat.one_pos (le_max_left 1 b)) f
      refine
        { tensor := R.tensor.snoc f
          scalar := R.scalar
          internal_bondDim_le := rep.internal_bondDim_le
          coeff_eq := fun x ↦ ?_
          scalar_rational := R.scalar_rational
          tensor_rational := tensor_snoc_rational R.tensor f R.tensor_rational (fun y ↦ ?_) }
      · have heq : (fun x ↦ AreaLaw.extendSite (n + 1) k v (leftConfigOfFin x)) =
            (fun x ↦ v (leftConfigOfFin (Fin.init x)) * f (x (Fin.last n))) := by
          funext y
          rw [extendSite_apply hi0 hiL, mul_ite, mul_one, mul_zero]
          rfl
        rw [congrFun heq x]
        exact rep.coeff_eq x
      · dsimp only [f]
        split_ifs
        · exact HasRationalComplexCoordinates.one
        · exact HasRationalComplexCoordinates.zero

end RationalLeftOpenMPSRepresentation

/-- Every left-open matrix product state admits arbitrarily accurate rational tensor
data on the same virtual spaces, and hence with the same bond bound. -/
theorem IsLeftOpenMPS.exists_rational_approximation {b k : ℕ}
    {v : LeftBlockVector L q k} (hv : IsLeftOpenMPS b v) (hk : k ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : LeftBlockVector L q k,
      Nonempty (RationalLeftOpenMPSRepresentation b w) ∧ ‖v - w‖ ≤ ε := by
  obtain ⟨R⟩ := (isLeftOpenMPS_iff_nonempty_representation b v).mp hv
  let P : ℂ × OBCChainTensor.Parameters R.tensor :=
    (R.scalar, OBCChainTensor.parameters R.tensor)
  obtain ⟨Q, hQscalar, hQtensor, hclose⟩ :=
    OBCChainTensor.exists_rational_parameters_close R.tensor hk P hε
  let w := OBCChainTensor.vectorOfParameters (L := L) R.tensor hk Q
  refine ⟨w, ⟨RationalLeftOpenMPSRepresentation.ofParameters R hk Q hQscalar hQtensor⟩, ?_⟩
  rw [← R.vectorOfParameters_eq hk]
  exact le_of_lt hclose

/-- The number of dependent virtual paths of an open chain of length `n` and bond
budget `D` is at most `D^(n+1)`. -/
theorem OBCChainTensor.virtualPath_card_le {D n : ℕ} (A : OBCChainTensor q D n) :
    Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)) ≤ D ^ (n + 1) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    ∏ p : Fin (n + 1), A.bondDim p ≤ ∏ _p : Fin (n + 1), D := by
      exact Finset.prod_le_prod fun p _hp ↦ A.bondDim_le p
    _ = D ^ (n + 1) := by simp

/-- Rational open-chain tensor data with one common coordinate-height bound. -/
structure RationalLeftOpenMPSRepresentationOfHeight (H b : ℕ) {k : ℕ}
    (v : LeftBlockVector L q k) where
  data : RationalLeftOpenMPSRepresentation b v
  scalar_height : HasRationalComplexCoordinatesOfHeight H data.scalar
  tensor_height : ∀ p i a c,
    HasRationalComplexCoordinatesOfHeight H (data.tensor.tensor p i a c)

namespace RationalLeftOpenMPSRepresentationOfHeight

/-- Height-bounded scalar and local-entry parameters on fixed virtual spaces give a
height-bounded rational left-open MPS representation. -/
noncomputable def ofParameters {H b k : ℕ} {v : LeftBlockVector L q k}
    (R : LeftOpenMPSRepresentation b v) (hk : k ≤ L)
    (P : ℂ × OBCChainTensor.Parameters R.tensor)
    (hscalar : HasRationalComplexCoordinatesOfHeight H P.1)
    (htensor : ∀ e, HasRationalComplexCoordinatesOfHeight H (P.2 e)) :
    RationalLeftOpenMPSRepresentationOfHeight H b
      (OBCChainTensor.vectorOfParameters (L := L) R.tensor hk P) where
  data := RationalLeftOpenMPSRepresentation.ofParameters R hk P hscalar.forget
    (fun e ↦ (htensor e).forget)
  scalar_height := hscalar
  tensor_height := by
    intro p i a c
    exact htensor ⟨p, i, a, c⟩

end RationalLeftOpenMPSRepresentationOfHeight

/-- A positive-length left-open MPS in the unit ball admits a dyadic rational
approximation of the same bond bound, with explicit common parameter height and
an explicit full-vector error bound. -/
theorem IsLeftOpenMPS.exists_dyadic_rational_approximation_of_norm_le_one
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (hv : IsLeftOpenMPS b v) (hk : n + 1 ≤ L) (hvnorm : ‖v‖ ≤ 1) (t : ℕ) :
    ∃ w : LeftBlockVector L q (n + 1),
      Nonempty (RationalLeftOpenMPSRepresentationOfHeight
        (2 ^ (2 * t + 5)) b w) ∧
      ‖v - w‖ ≤ (q ^ (n + 1) : ℝ) *
        (max 1 (max 1 b) : ℝ) ^ (n + 2) *
          ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) := by
  obtain ⟨R⟩ := (isLeftOpenMPS_iff_nonempty_representation b v).mp hv
  obtain ⟨R', hR'scalar, hR'tensor⟩ :=
    R.exists_unitBounded_of_norm_le_one hk hvnorm
  let P₀ : ℂ × OBCChainTensor.Parameters R'.tensor :=
    (R'.scalar, OBCChainTensor.parameters R'.tensor)
  have hP₀scalar : ‖P₀.1‖ ≤ (1 : ℝ) := hR'scalar
  have hP₀tensor : ∀ e, ‖P₀.2 e‖ ≤ (1 : ℝ) := by
    intro e
    exact hR'tensor e.1 e.2.1 e.2.2.1 e.2.2.2
  obtain ⟨P, hPscalar, hPtensor, hPscalarClose, hPtensorClose⟩ :=
    OBCChainTensor.exists_dyadic_parameters_approximation R'.tensor
      (u := 0) (t := t) zero_le_one (by norm_num) P₀ hP₀scalar hP₀tensor
  let w := OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P
  have hscalarClose : ‖P.1 - P₀.1‖ ≤ (2 ^ t : ℝ)⁻¹ := by
    simpa only [norm_sub_rev] using hPscalarClose
  have htensorClose : ∀ e, ‖P.2 e - P₀.2 e‖ ≤ (2 ^ t : ℝ)⁻¹ := by
    intro e
    simpa only [norm_sub_rev] using hPtensorClose e
  have hδ : 0 ≤ (2 ^ t : ℝ)⁻¹ := by positivity
  have herr := OBCChainTensor.norm_vectorOfParameters_sub_le_one R'.tensor hk P P₀
    hδ hP₀scalar hP₀tensor hscalarClose htensorClose
  have hfactor : 0 ≤ (q ^ (n + 1) : ℝ) *
      ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) := by
    have hone : 1 ≤ (1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) :=
      one_le_pow₀ (by linarith)
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hone)
  refine ⟨w, ⟨?_⟩, ?_⟩
  · simpa [w] using
      RationalLeftOpenMPSRepresentationOfHeight.ofParameters R' hk P hPscalar hPtensor
  · have hpath := OBCChainTensor.virtualPath_card_le R'.tensor
    have hscaled := mul_le_mul_of_nonneg_left (show
      (Fintype.card ((p : Fin (n + 1 + 1)) → Fin (R'.tensor.bondDim p)) : ℝ) ≤
        (max 1 (max 1 b) : ℝ) ^ (n + 2) by exact_mod_cast hpath) hfactor
    have hfinal := herr.trans (by
      calc
        (q ^ (n + 1) : ℝ) *
            Fintype.card ((p : Fin (n + 1 + 1)) → Fin (R'.tensor.bondDim p)) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) =
            ((q ^ (n + 1) : ℝ) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1)) *
                Fintype.card ((p : Fin (n + 1 + 1)) → Fin (R'.tensor.bondDim p)) := by ring
        _ ≤ ((q ^ (n + 1) : ℝ) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1)) *
                (max 1 (max 1 b) : ℝ) ^ (n + 2) := hscaled
        _ = (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
              ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) := by ring)
    calc
      ‖v - w‖ =
          ‖OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P₀ -
            OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P‖ := by
              rw [R'.vectorOfParameters_eq hk]
      _ = ‖OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P -
            OBCChainTensor.vectorOfParameters (L := L) R'.tensor hk P₀‖ := norm_sub_rev _ _
      _ ≤ _ := hfinal

/-- The explicit dyadic approximation bound specialized to normalized states. -/
theorem IsLeftOpenMPS.exists_dyadic_rational_approximation_of_norm_eq_one
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (hv : IsLeftOpenMPS b v) (hk : n + 1 ≤ L) (hvnorm : ‖v‖ = 1) (t : ℕ) :
    ∃ w : LeftBlockVector L q (n + 1),
      Nonempty (RationalLeftOpenMPSRepresentationOfHeight
        (2 ^ (2 * t + 5)) b w) ∧
      ‖v - w‖ ≤ (q ^ (n + 1) : ℝ) *
        (max 1 (max 1 b) : ℝ) ^ (n + 2) *
          ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) :=
  hv.exists_dyadic_rational_approximation_of_norm_le_one hk hvnorm.le t

/-- On the unit interval, the power error is at most the mesh size times the
degree and a fixed power of two. -/
theorem one_add_pow_sub_one_le_mul_two_pow {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (r : ℕ) :
    (1 + δ) ^ r - 1 ≤ δ * r * 2 ^ (r - 1) := by
  have h := abs_pow_sub_pow_le (a := (1 + δ)) (b := (1 : ℝ)) (n := r)
  have hmax : max |1 + δ| |(1 : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 + δ), abs_of_nonneg zero_le_one]
    exact max_le (by linarith) (by norm_num)
  calc
    (1 + δ) ^ r - 1 ≤ |(1 + δ) ^ r - 1| := le_abs_self _
    _ ≤ δ * r * max |1 + δ| |(1 : ℝ)| ^ (r - 1) := by
      simpa only [one_pow, add_sub_cancel_left, abs_of_nonneg hδ] using h
    _ ≤ δ * r * 2 ^ (r - 1) := by gcongr

/-- The ceiling binary logarithm chooses a dyadic mesh meeting a prescribed
positive error after multiplication by a fixed contraction bound. -/
theorem mul_inv_two_pow_clog_natCeil_le {K ε : ℝ} (hε : 0 < ε) :
    K * (2 ^ Nat.clog 2 ⌈K / ε⌉₊ : ℝ)⁻¹ ≤ ε := by
  have hceil : K / ε ≤ (⌈K / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hpow : (⌈K / ε⌉₊ : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 ⌈K / ε⌉₊ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈K / ε⌉₊
  apply (mul_inv_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ Nat.clog 2 ⌈K / ε⌉₊)).mpr
  have h := (div_le_iff₀ hε).mp (hceil.trans hpow)
  nlinarith

/-- A positive-length left-open MPS in the unit ball can be rounded to any positive
vector error with an explicit dyadic precision. The precision exponent is the
ceiling binary logarithm of the contraction bound divided by the target error. -/
theorem IsLeftOpenMPS.exists_dyadic_rational_approximation_at_error_of_norm_le_one
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (hv : IsLeftOpenMPS b v) (hk : n + 1 ≤ L) (hvnorm : ‖v‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
      (n + 2) * 2 ^ (n + 1)
    let t := Nat.clog 2 ⌈K / ε⌉₊
    ∃ w : LeftBlockVector L q (n + 1),
      Nonempty (RationalLeftOpenMPSRepresentationOfHeight (2 ^ (2 * t + 5)) b w) ∧
      ‖v - w‖ ≤ ε := by
  dsimp only
  let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
    (n + 2) * 2 ^ (n + 1)
  let t := Nat.clog 2 ⌈K / ε⌉₊
  obtain ⟨w, hw, herr⟩ := hv.exists_dyadic_rational_approximation_of_norm_le_one hk hvnorm t
  refine ⟨w, hw, herr.trans ?_⟩
  have hδ : 0 ≤ (2 ^ t : ℝ)⁻¹ := by positivity
  have hδone : (2 ^ t : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hpower := one_add_pow_sub_one_le_mul_two_pow hδ hδone (n + 2)
  calc
    (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
        ((1 + (2 ^ t : ℝ)⁻¹) ^ (n + 2) - 1) ≤
        (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
          ((2 ^ t : ℝ)⁻¹ * (n + 2) * 2 ^ (n + 1)) := by
            exact mul_le_mul_of_nonneg_left (by simpa using hpower) (by positivity)
    _ = K * (2 ^ t : ℝ)⁻¹ := by dsimp [K]; ring
    _ ≤ ε := mul_inv_two_pow_clog_natCeil_le hε

/-- The explicit arbitrary-error dyadic approximation specialized to normalized states. -/
theorem IsLeftOpenMPS.exists_dyadic_rational_approximation_at_error
    {b n : ℕ} {v : LeftBlockVector L q (n + 1)}
    (hv : IsLeftOpenMPS b v) (hk : n + 1 ≤ L) (hvnorm : ‖v‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
      (n + 2) * 2 ^ (n + 1)
    let t := Nat.clog 2 ⌈K / ε⌉₊
    ∃ w : LeftBlockVector L q (n + 1),
      Nonempty (RationalLeftOpenMPSRepresentationOfHeight (2 ^ (2 * t + 5)) b w) ∧
      ‖v - w‖ ≤ ε :=
  hv.exists_dyadic_rational_approximation_at_error_of_norm_le_one hk hvnorm.le hε

/-- A finite family in the unit ball admits a simultaneous rational approximation
with one parameter-height bound, without increasing its cardinality or bond bound.
The family is chosen before any ground vector or viability witness is supplied. -/
theorem exists_rational_leftFamily_approximation_of_norm_le_one
    {b n : ℕ} (S : Finset (LeftBlockVector L q (n + 1))) (hk : n + 1 ≤ L)
    (hMPS : ∀ v ∈ S, IsLeftOpenMPS b v) (hnorm : ∀ v ∈ S, ‖v‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 b) : ℝ) ^ (n + 2) *
      (n + 2) * 2 ^ (n + 1)
    let t := Nat.clog 2 ⌈K / ε⌉₊
    ∃ T : Finset (LeftBlockVector L q (n + 1)),
      T.card ≤ S.card ∧
      (∀ w ∈ T, Nonempty
        (RationalLeftOpenMPSRepresentationOfHeight (2 ^ (2 * t + 5)) b w)) ∧
      ∀ v ∈ S, ∃ w ∈ T, ‖v - w‖ ≤ ε := by
  classical
  dsimp only
  choose w hrep hclose using fun v : S ↦
    (hMPS v.1 v.2).exists_dyadic_rational_approximation_at_error_of_norm_le_one
      hk (hnorm v.1 v.2) hε
  let T := Finset.univ.image w
  refine ⟨T, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro v hv
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hv
    exact hrep s
  · intro v hv
    exact ⟨w ⟨v, hv⟩, Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩,
      hclose ⟨v, hv⟩⟩

/-- Contracting a height-bounded rational open chain gives an explicit height bound.
The outer exponent is the number of dependent virtual paths, while `productHeight`
accounts for the product of the `n` local tensor entries along each path. -/
theorem OBCChainTensor.coeff_height {D n H : ℕ} (A : OBCChainTensor q D n)
    (hA : ∀ p i a c,
      HasRationalComplexCoordinatesOfHeight H (A.tensor p i a c))
    (σ : Fin n → Fin q) :
    HasRationalComplexCoordinatesOfHeight
      ((2 * HasRationalComplexCoordinatesOfHeight.productHeight H n) ^
        Fintype.card ((p : Fin (n + 1)) → Fin (A.bondDim p)))
      (A.coeff σ) := by
  rw [OBCChainTensor.coeff]
  apply HasRationalComplexCoordinatesOfHeight.finset_sum
  intro α _hα
  simpa using HasRationalComplexCoordinatesOfHeight.finset_prod
    (s := Finset.univ) (fun p _hp ↦ hA p (σ p) (α p.castSucc) (α p.succ))

namespace RationalLeftOpenMPSRepresentationOfHeight

/-- Uniform physical-coordinate height bound obtained from a local height `H`, a bond
budget `b`, and a chain length `k`. -/
def coordinateHeightBound (H b k : ℕ) : ℕ :=
  let HP := HasRationalComplexCoordinatesOfHeight.productHeight H k
  let HC := (2 * HP) ^ ((max 1 (max 1 b)) ^ (k + 1))
  2 * (H * HC) * (H * HC)

/-- Every physical coefficient represented by height-bounded rational open-chain data
has an explicit coordinate-height bound. -/
theorem coordinate_height {H b k : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    let HC :=
      (2 * HasRationalComplexCoordinatesOfHeight.productHeight H k) ^
        Fintype.card ((p : Fin (k + 1)) → Fin (R.data.tensor.bondDim p))
    HasRationalComplexCoordinatesOfHeight (2 * (H * HC) * (H * HC)) (v x) := by
  dsimp only
  let y := (leftConfigOfFinEquiv (q := q) hk).symm x
  have hxy : leftConfigOfFin y = x := (leftConfigOfFinEquiv hk).apply_symm_apply x
  rw [← hxy, R.data.coeff_eq]
  exact R.scalar_height.mul
    (OBCChainTensor.coeff_height R.data.tensor R.tensor_height y)

/-- The preceding coefficient bound depends only on the advertised local height, bond
budget, and chain length, rather than on the varying internal bond dimensions. -/
theorem coordinate_height_le {H b k : ℕ} (hH : 0 < H)
    {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight (coordinateHeightBound H b k) (v x) := by
  let HP := HasRationalComplexCoordinatesOfHeight.productHeight H k
  let HC := (2 * HP) ^
    Fintype.card ((p : Fin (k + 1)) → Fin (R.data.tensor.bondDim p))
  have hx : HasRationalComplexCoordinatesOfHeight (2 * (H * HC) * (H * HC)) (v x) :=
    R.coordinate_height hk x
  apply hx.mono
  dsimp only [coordinateHeightBound, HC, HP]
  have hbase : 0 < 2 * HasRationalComplexCoordinatesOfHeight.productHeight H k := by
    exact Nat.mul_pos (by omega)
      (HasRationalComplexCoordinatesOfHeight.productHeight_pos hH k)
  have hpow := Nat.pow_le_pow_right hbase
    (OBCChainTensor.virtualPath_card_le R.data.tensor)
  have hterm := Nat.mul_le_mul_left H hpow
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul hterm hterm)

/-- Height-one rational tensor data for the scalar basis vector at the empty cut. -/
noncomputable def emptyLeftVector (L q : ℕ) :
    RationalLeftOpenMPSRepresentationOfHeight 1 1 (AreaLaw.emptyLeftVector L q) := by
  let A : OBCChainTensor q 1 0 :=
    { bondDim := fun _ ↦ 1
      bondDim_le := fun _ ↦ le_rfl
      left_dim := rfl
      right_dim := rfl
      tensor := fun p ↦ p.elim0 }
  let R : RationalLeftOpenMPSRepresentation 1 (AreaLaw.emptyLeftVector L q) :=
    { tensor := A
      scalar := 1
      internal_bondDim_le := fun p hp hp' ↦ by omega
      coeff_eq := fun x ↦ by simp [AreaLaw.emptyLeftVector, A]
      scalar_rational := HasRationalComplexCoordinates.one
      tensor_rational := fun p ↦ p.elim0 }
  exact
    { data := R
      scalar_height := HasRationalComplexCoordinatesOfHeight.one
      tensor_height := fun p ↦ p.elim0 }

/-- Appending one site whose entries have height at most `H` preserves the same tensor
entry height bound. -/
theorem tensor_snoc_height {D n H : ℕ} (A : OBCChainTensor q D n) (f : Fin q → ℂ)
    (hA : ∀ p i a c, HasRationalComplexCoordinatesOfHeight H (A.tensor p i a c))
    (hf : ∀ i, HasRationalComplexCoordinatesOfHeight H (f i)) :
    ∀ p i a c, HasRationalComplexCoordinatesOfHeight H ((A.snoc f).tensor p i a c) := by
  intro p
  refine Fin.lastCases ?_ (fun p' ↦ ?_) p
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_last]
    change HasRationalComplexCoordinatesOfHeight H (f i)
    exact hf i
  · intro i a c
    simp only [OBCChainTensor.snoc, Fin.lastCases_castSucc]
    change HasRationalComplexCoordinatesOfHeight H (A.tensor p' i _ _)
    exact hA p' i _ _

/-- Computational-basis extension preserves a common height bound `H ≥ 1`. -/
noncomputable def extendSite {H i b : ℕ} (hH : 1 ≤ H) (hi0 : 0 < i) (hiL : i ≤ L)
    {v : LeftBlockVector L q (i - 1)}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (k : Fin q) :
    RationalLeftOpenMPSRepresentationOfHeight H b (AreaLaw.extendSite i k v) := by
  cases i with
  | zero => omega
  | succ n =>
      simp only [Nat.succ_sub_one] at v R ⊢
      let f : Fin q → ℂ := fun y ↦ if y = k then 1 else 0
      let data := R.data.extendSite hi0 hiL k
      refine ⟨data, ?_, ?_⟩
      · change HasRationalComplexCoordinatesOfHeight H R.data.scalar
        exact R.scalar_height
      · change ∀ p i a c,
          HasRationalComplexCoordinatesOfHeight H ((R.data.tensor.snoc f).tensor p i a c)
        apply tensor_snoc_height R.data.tensor f R.tensor_height
        intro y
        dsimp only [f]
        split_ifs
        · exact HasRationalComplexCoordinatesOfHeight.one.mono hH
        · exact HasRationalComplexCoordinatesOfHeight.zero.mono hH

end RationalLeftOpenMPSRepresentationOfHeight

end TNLean.MPS.AreaLaw
