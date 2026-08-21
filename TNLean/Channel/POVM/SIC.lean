/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RankOneSandwich
import TNLean.Algebra.SICPOVMBound
import TNLean.Algebra.PerronFrobenius.RankOne
import TNLean.Channel.KrausMap
import TNLean.Channel.POVM

/-!
# Symmetric informationally complete measurements

This file distinguishes the three normalizations associated with a symmetric
informationally complete measurement: the rank-one projectors \(P_i\), the POVM
effects \(P_i/d\), and the Kraus operators \(P_i/\sqrt d\). It proves the
diagonal representation of arbitrary matrices and the corresponding quantum
channel identity.

## References

* Wolf, *Quantum Channels & Operations*, Chapter 2, equations (2.33)--(2.34);
  `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 825--859
-/

open scoped Matrix ComplexOrder BigOperators

/-- A symmetric informationally complete family in dimension \(d\), expressed
in terms of its unscaled rank-one projectors \(P_i\). Thus
\(\sum_i P_i=d\,1\) and distinct projectors have overlap \(1/(d+1)\).

Source: Wolf, *Quantum Channels & Operations*, Chapter 2;
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 825--840. -/
structure SICPOVM (d : ℕ) where
  /-- The matrix dimension is positive. -/
  dim_pos : 0 < d
  /-- The \(d^2\) unscaled rank-one projectors. -/
  projector : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ
  /-- Every member is a rank-one orthogonal projection. -/
  rank_one : ∀ i, IsRankOneOrthogonalProjection (projector i)
  /-- The projectors form a tight frame with frame operator \(d\,1\). -/
  sum_projector : ∑ i, projector i = (d : ℂ) • 1
  /-- Distinct projectors have Hilbert--Schmidt overlap \(1/(d+1)\). -/
  overlap : ∀ i j, i ≠ j →
    (projector i * projector j).trace = ((((d : ℝ) + 1)⁻¹ : ℝ) : ℂ)

namespace SICPOVM

variable {d : ℕ} (S : SICPOVM d)

/-- Every SIC projector is positive semidefinite. -/
theorem projector_posSemidef (i : Fin (d ^ 2)) :
    (S.projector i).PosSemidef :=
  isOrthogonalProjection_posSemidef (S.rank_one i).1

/-- Every SIC projector is idempotent. -/
theorem projector_mul_self (i : Fin (d ^ 2)) :
    S.projector i * S.projector i = S.projector i :=
  (S.rank_one i).1.2

/-- Every SIC projector has trace one. -/
theorem projector_trace (i : Fin (d ^ 2)) :
    (S.projector i).trace = 1 := by
  have hre := (S.rank_one i).1.1.rank_eq_trace_re_of_idem (S.projector_mul_self i)
  rw [(S.rank_one i).2] at hre
  have him := (Complex.nonneg_iff.mp (S.projector_posSemidef i).trace_nonneg).2
  apply Complex.ext
  · norm_num at hre ⊢
    exact hre.symm
  · simpa using him.symm

/-- Every SIC projector has unit Hilbert--Schmidt purity. -/
theorem projector_purity (i : Fin (d ^ 2)) :
    ((S.projector i) ^ 2).trace = 1 := by
  rw [pow_two, S.projector_mul_self, S.projector_trace]

/-- The POVM effect associated with a SIC projector is \(P_i/d\). -/
noncomputable def effect (i : Fin (d ^ 2)) : Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℝ)⁻¹) • S.projector i

/-- Every SIC effect is positive semidefinite. -/
theorem effect_posSemidef (i : Fin (d ^ 2)) :
    (S.effect i).PosSemidef :=
  (S.projector_posSemidef i).smul (by positivity)

/-- The scaled effects \(P_i/d\) form a POVM. -/
noncomputable def toPOVM : POVM d (d ^ 2) where
  ops := S.effect
  posSemidef := S.effect_posSemidef
  sum_eq_one := by
    rw [show ∑ i, S.effect i = ((d : ℝ)⁻¹) • ∑ i, S.projector i by
      simp only [effect, Finset.smul_sum]]
    rw [S.sum_projector]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
      rw [mul_one, ← Complex.coe_smul, smul_eq_mul]
      rw [Complex.ofReal_inv]
      push_cast
      rw [inv_mul_cancel₀]
      exact_mod_cast S.dim_pos.ne'
    · simp [Matrix.smul_apply, hij]

/-- The Kraus operator associated with a SIC projector is \(P_i/\sqrt d\). -/
noncomputable def kraus (i : Fin (d ^ 2)) : Matrix (Fin d) (Fin d) ℂ :=
  ((Real.sqrt d)⁻¹ : ℝ) • S.projector i

/-- SIC Kraus operators are Hermitian. -/
theorem kraus_conjTranspose (i : Fin (d ^ 2)) :
    (S.kraus i)ᴴ = S.kraus i := by
  simp [kraus, Matrix.conjTranspose_smul, (S.rank_one i).1.1.eq]

/-- The unscaled projectors of a SIC measurement are linearly independent. -/
theorem linearIndependent_projector : LinearIndependent ℂ S.projector := by
  by_cases hd1 : d = 1
  · subst d
    simpa using Matrix.singleton_linearIndependent_of_trace_sq_eq_one
      S.projector (S.projector_purity 0)
  · have hdpos := S.dim_pos
    have hd2 : 2 ≤ d := by omega
    have hn2 : 2 ≤ d ^ 2 := by nlinarith
    have hdn : d ≤ d ^ 2 := by nlinarith [S.dim_pos]
    have heq := (Matrix.sicPOVM_offDiag_overlap_sq_eq_iff
      S.projector hn2 S.dim_pos hdn S.projector_posSemidef S.projector_purity).mpr
      (by
        refine ⟨S.rank_one, ?_, ?_⟩
        · rw [S.sum_projector]
          ext i j
          by_cases hij : i = j
          · subst j
            simp only [Nat.cast_pow, Matrix.smul_apply, Matrix.one_apply_eq,
              smul_eq_mul]
            field_simp
            push_cast
            norm_num
          · simp [Matrix.smul_apply, hij]
        · intro i j hij
          rw [S.overlap i j hij]
          simp only [Complex.ofReal_re, Nat.cast_pow]
          have hdR : (0 : ℝ) < d := by exact_mod_cast S.dim_pos
          have hd2R : (2 : ℝ) ≤ d := by exact_mod_cast hd2
          rw [show (d : ℝ) ^ 2 - d = d * (d - 1) by ring,
            show (d : ℝ) ^ 2 - 1 = (d - 1) * (d + 1) by ring]
          field_simp [hdR.ne', show (d : ℝ) - 1 ≠ 0 by nlinarith [hd2R],
            show (d : ℝ) + 1 ≠ 0 by positivity])
    exact Matrix.sicPOVM_linearIndependent_of_overlap_bound_eq
      S.projector hn2 hd2 hdn S.projector_posSemidef S.projector_purity heq

/-- The SIC projectors span the full matrix algebra. -/
theorem span_projector_eq_top :
    Submodule.span ℂ (Set.range S.projector) = ⊤ := by
  apply S.linearIndependent_projector.span_eq_top_of_card_eq_finrank'
  simp [Module.finrank_matrix, pow_two]

/-- The frame operator of the unscaled SIC projectors is
\(X\mapsto\sum_i\operatorname{tr}(P_iX)P_i\). -/
noncomputable def frameMap :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, ((Matrix.traceLinearMap (Fin d) ℂ ℂ).comp
    (LinearMap.mulLeft ℂ (S.projector i))).smulRight (S.projector i)

@[simp]
theorem frameMap_apply (X : Matrix (Fin d) (Fin d) ℂ) :
    S.frameMap X = ∑ i, (S.projector i * X).trace • S.projector i := by
  simp [frameMap, Matrix.traceLinearMap_apply]

private theorem sum_erase_projector (j : Fin (d ^ 2)) :
    ∑ i ∈ (Finset.univ : Finset (Fin (d ^ 2))).erase j, S.projector i =
      (d : ℂ) • 1 - S.projector j := by
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin (d ^ 2)))
    S.projector (Finset.mem_univ j)
  rw [S.sum_projector] at hsplit
  apply eq_sub_of_add_eq
  simpa [add_comm] using hsplit

private theorem frameMap_projector (j : Fin (d ^ 2)) :
    S.frameMap (S.projector j) =
      ((d : ℂ) / ((d : ℂ) + 1)) • (S.projector j + 1) := by
  rw [S.frameMap_apply]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin (d ^ 2)))
    (fun i ↦ (S.projector i * S.projector j).trace • S.projector i)
    (Finset.mem_univ j)]
  rw [show (S.projector j * S.projector j).trace = 1 by
    simpa [pow_two] using S.projector_purity j, one_smul]
  have hoff :
      ∑ i ∈ (Finset.univ : Finset (Fin (d ^ 2))).erase j,
          (S.projector i * S.projector j).trace • S.projector i =
        ((((d : ℝ) + 1)⁻¹ : ℝ) : ℂ) •
          ∑ i ∈ (Finset.univ : Finset (Fin (d ^ 2))).erase j, S.projector i := by
    calc
      _ = ∑ i ∈ (Finset.univ : Finset (Fin (d ^ 2))).erase j,
          ((((d : ℝ) + 1)⁻¹ : ℝ) : ℂ) • S.projector i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [S.overlap i j (Finset.ne_of_mem_erase hi)]
      _ = _ := by rw [Finset.smul_sum]
  rw [hoff, S.sum_erase_projector]
  simp only [smul_sub, smul_smul, smul_add]
  rw [Complex.ofReal_inv]
  push_cast
  have hdp1 : (d : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by positivity : (d : ℝ) + 1 ≠ 0)
  have hcoeffP : (1 : ℂ) - ((d : ℂ) + 1)⁻¹ =
      (d : ℂ) / ((d : ℂ) + 1) := by
    field_simp [hdp1]
    ring
  have hcoeffI : ((d : ℂ) + 1)⁻¹ * d =
      (d : ℂ) / ((d : ℂ) + 1) := by
    field_simp [hdp1]
  calc
    S.projector j +
          ((((d : ℂ) + 1)⁻¹ * d) • 1 - ((d : ℂ) + 1)⁻¹ • S.projector j) =
        ((1 : ℂ) - ((d : ℂ) + 1)⁻¹) • S.projector j +
          (((d : ℂ) + 1)⁻¹ * d) • 1 := by module
    _ = ((d : ℂ) / ((d : ℂ) + 1)) • S.projector j +
        ((d : ℂ) / ((d : ℂ) + 1)) • 1 := by
      rw [hcoeffP, hcoeffI]

/-- The frame operator of a SIC family is the sum of the identity map and the
trace-to-identity map, with coefficient \(d/(d+1)\). -/
theorem frameMap_eq (X : Matrix (Fin d) (Fin d) ℂ) :
    S.frameMap X = ((d : ℂ) / ((d : ℂ) + 1)) • (X + X.trace • 1) := by
  let T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    ((d : ℂ) / ((d : ℂ) + 1)) •
      (LinearMap.id + (Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight 1)
  have hmaps : S.frameMap = T := by
    apply LinearMap.ext_on_range (v := S.projector) S.span_projector_eq_top
    intro j
    simp only [T, LinearMap.add_apply, LinearMap.id_coe, id_eq,
      LinearMap.smulRight_apply, LinearMap.smul_apply,
      Matrix.traceLinearMap_apply, S.projector_trace, one_smul]
    exact S.frameMap_projector j
  have hX := congrArg (fun F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ ↦ F X) hmaps
  simpa only [T, LinearMap.add_apply, LinearMap.id_coe, id_eq,
    LinearMap.smulRight_apply, LinearMap.smul_apply,
    Matrix.traceLinearMap_apply] using hX

/-- **SIC diagonal representation** (Wolf equation (2.33)). Every matrix is
reconstructed from its trace pairings with the unscaled SIC projectors.

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, equation (2.33);
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 839--848. -/
theorem diagonalRepresentation (X : Matrix (Fin d) (Fin d) ℂ) :
    X = (d : ℂ)⁻¹ •
      ∑ i, ((((d : ℂ) + 1) * (S.projector i * X).trace - X.trace) •
        S.projector i) := by
  symm
  calc
    (d : ℂ)⁻¹ •
          ∑ i, ((((d : ℂ) + 1) * (S.projector i * X).trace - X.trace) •
            S.projector i) =
        (d : ℂ)⁻¹ • (((d : ℂ) + 1) • S.frameMap X -
          X.trace • ∑ i, S.projector i) := by
      congr 1
      simp_rw [sub_smul, mul_smul]
      rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
        ← S.frameMap_apply]
    _ = X := by
      rw [S.frameMap_eq, S.sum_projector]
      simp only [smul_sub, smul_add, smul_smul]
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast S.dim_pos.ne'
      have hdp1 : (d : ℂ) + 1 ≠ 0 := by
        exact_mod_cast (by positivity : (d : ℝ) + 1 ≠ 0)
      field_simp [hdC, hdp1]
      module

/-- Sandwiching by a SIC projector multiplies that projector by the
corresponding trace pairing. -/
theorem projector_mul_mul_projector (i : Fin (d ^ 2))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    S.projector i * X * S.projector i =
      (X * S.projector i).trace • S.projector i := by
  obtain ⟨u, v, huv⟩ := Matrix.hasRankOneFactorization_of_mul_self_eq_self
    (S.projector_mul_self i) (S.projector_trace i)
  rw [huv]
  exact Matrix.vecMulVec_mul_mul_vecMulVec_eq_trace_smul u v X

/-- **SIC Kraus-channel identity** (Wolf equation (2.34)). The Kraus action
associated with the operators \(P_i/\sqrt d\) is the depolarizing channel
\(X\mapsto (X+\operatorname{tr}(X)1)/(d+1)\).

Source: Wolf, *Quantum Channels & Operations*, Chapter 2, equation (2.34);
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 850--859. -/
theorem krausChannel_identity (X : Matrix (Fin d) (Fin d) ℂ) :
    (d : ℂ)⁻¹ • ∑ i, S.projector i * X * S.projector i =
      ((d : ℂ) + 1)⁻¹ • (X.trace • 1 + X) := by
  have hsum : ∑ i, S.projector i * X * S.projector i = S.frameMap X := by
    rw [S.frameMap_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [S.projector_mul_mul_projector]
    rw [Matrix.trace_mul_comm]
  rw [hsum, S.frameMap_eq]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast S.dim_pos.ne'
  have hdp1 : (d : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by positivity : (d : ℝ) + 1 ≠ 0)
  simp only [smul_smul]
  field_simp [hdC, hdp1]
  module

/-- Each SIC Kraus summand is the corresponding projector sandwich divided by
the dimension. -/
theorem kraus_mul_mul_conjTranspose (i : Fin (d ^ 2))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    S.kraus i * X * (S.kraus i)ᴴ =
      (d : ℂ)⁻¹ • (S.projector i * X * S.projector i) := by
  rw [S.kraus_conjTranspose]
  simp only [kraus, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hscale : (Real.sqrt d)⁻¹ * (Real.sqrt d)⁻¹ = ((d : ℝ)⁻¹) := by
    have hsqrt0 : Real.sqrt d ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast S.dim_pos))
    field_simp [hsqrt0, show (d : ℝ) ≠ 0 by exact_mod_cast S.dim_pos.ne']
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]
  rw [hscale, ← Complex.coe_smul, Complex.ofReal_inv]
  push_cast
  norm_num

/-- The Kraus map defined by the operators \(P_i/\sqrt d\) has Wolf's closed
form from equation (2.34). -/
theorem krausMap_eq (X : Matrix (Fin d) (Fin d) ℂ) :
    Kraus.mapLM S.kraus X =
      ((d : ℂ) + 1)⁻¹ • (X.trace • 1 + X) := by
  rw [Kraus.mapLM_apply, Kraus.map_apply]
  simp_rw [S.kraus_mul_mul_conjTranspose]
  rw [← Finset.smul_sum]
  exact S.krausChannel_identity X

/-- The SIC Kraus operators satisfy the trace-preserving normalization. -/
theorem kraus_isTP : Kraus.IsTP S.kraus := by
  rw [Kraus.IsTP]
  calc
    ∑ i, (S.kraus i)ᴴ * S.kraus i =
        ∑ i, S.kraus i * (1 : Matrix (Fin d) (Fin d) ℂ) * (S.kraus i)ᴴ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [S.kraus_conjTranspose, Matrix.mul_one]
    _ = ∑ i, (d : ℂ)⁻¹ •
        (S.projector i * (1 : Matrix (Fin d) (Fin d) ℂ) * S.projector i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact S.kraus_mul_mul_conjTranspose i 1
    _ = (d : ℂ)⁻¹ • ∑ i, S.projector i := by
      simp_rw [Matrix.mul_one, S.projector_mul_self]
      rw [Finset.smul_sum]
    _ = 1 := by
      rw [S.sum_projector]
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one]
        rw [inv_mul_cancel₀]
        exact_mod_cast S.dim_pos.ne'
      · simp [Matrix.smul_apply, hij]

/-- The finite Kraus family \(P_i/\sqrt d\) defines a quantum channel. -/
theorem isChannel_krausMap : IsChannel (Kraus.mapLM S.kraus) :=
  Kraus.isChannel_mapLM S.kraus S.kraus_isTP

end SICPOVM
