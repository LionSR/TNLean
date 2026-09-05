/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLT
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# AKLT two-site parent Hamiltonian

The AKLT tensor becomes injective only after blocking two sites, so the general
uniqueness theorem for parent Hamiltonians of normal tensors covers the
three-site parent Hamiltonian and larger. The review remarks that this
locality bound is not tight: the two-site parent Hamiltonian already has a
unique ground state, which "can be seen e.g. by checking by hand that
\(\mathcal G_{1,2}\cap\mathcal G_{2,3}=\mathcal G_{1,2,3}\)"
(arXiv:2011.12127, line 2095).

This file carries out that hand check. With
\(A^0 = c\,\sigma^z\), \(A^1 = b\,\sigma^+\), \(A^2 = -b\,\sigma^-\),
\(c = 1/\sqrt3\), \(b = \sqrt2/\sqrt3\), the two-site local ground space is
\[
  \mathcal G_2(A) = \{v : v_{11} = v_{22} = 0,\ v_{01} + v_{10} = 0,\
    v_{02} + v_{20} = 0,\ 2 v_{00} + v_{12} + v_{21} = 0\},
\]
the four-dimensional space spanned by the spin-\(0\) and spin-\(1\) vectors of
two spin-\(1\) particles. A three-site vector whose two restrictions lie in
\(\mathcal G_2(A)\) is then shown, coordinate by coordinate, to be
\(\Gamma_3(X)\) for an explicit boundary matrix \(X\) read off from four of its
coefficients. The periodic two-site parent Hamiltonian on \(N \ge 3\) sites
therefore has the same ground space as the three-site one, which the general
theorem identifies with the span of the AKLT state.

## Main results

* The two-site local ground space is cut out by the five linear constraints
  above.
* The intersection property
  \((\mathcal G_{1,2}\otimes\mathcal H_3)\cap(\mathcal H_1\otimes\mathcal G_{2,3})
  = \mathcal G_{1,2,3}\) of arXiv:2011.12127, line 2095.
* The periodic two-site parent Hamiltonian on \(N\ge3\) sites has the AKLT
  state as its unique ground state.

## References

* Cirac--Pérez-García--Schuch--Verstraete 2021, arXiv:2011.12127, line 2095
  (the remark) and lines 2372--2396 (the tensor).
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ### The two scalars of the AKLT tensor -/

/-- The scalar \(c = 1/\sqrt3\) multiplying \(\sigma^z\) in the AKLT tensor. -/
private noncomputable def akltCoeffZ : ℂ := ↑(1 / Real.sqrt 3)

/-- The scalar \(b = \sqrt2/\sqrt3\) multiplying \(\sigma^{\pm}\) in the AKLT
tensor. -/
private noncomputable def akltCoeffPM : ℂ := ↑(Real.sqrt 2 / Real.sqrt 3)

private lemma akltTensor_zero' : akltTensor 0 = akltCoeffZ • !![1, 0; 0, -1] := rfl

private lemma akltTensor_one' : akltTensor 1 = akltCoeffPM • !![0, 1; 0, 0] := rfl

private lemma akltTensor_two' : akltTensor 2 = -akltCoeffPM • !![0, 0; 1, 0] := rfl

private lemma akltCoeffZ_ne_zero : akltCoeffZ ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

private lemma akltCoeffPM_ne_zero : akltCoeffPM ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

/-- The relation \(b^2 = 2c^2\) between the two AKLT scalars. -/
private lemma akltCoeffPM_mul_self :
    akltCoeffPM * akltCoeffPM = 2 * (akltCoeffZ * akltCoeffZ) := by
  simp only [akltCoeffPM, akltCoeffZ, ← Complex.ofReal_mul]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm, div_mul_div_comm, Real.mul_self_sqrt (by norm_num),
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-! ### The two-site local ground space -/

private lemma aklt_groundSpaceMap_two_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 3) :
    groundSpaceMap akltTensor 2 X ![a, b] =
      Matrix.trace (akltTensor a * (akltTensor b * X)) := by
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

private lemma cfg_two_eq (σ : Fin 2 → Fin 3) : σ = ![σ 0, σ 1] := by
  ext k
  fin_cases k <;> rfl

/-- The two-site local ground space of the AKLT tensor is cut out by five linear
constraints: with \(A^0 = c\,\sigma^z\), \(A^1 = b\,\sigma^+\),
\(A^2 = -b\,\sigma^-\), the products \(A^{a}A^{b}\) are
\(A^0A^0 = c^2 1\), \(A^0A^1 = -A^1A^0 = cb\,\ketbra01\),
\(A^0A^2 = -A^2A^0 = cb\,\ketbra10\), \(A^1A^2 = -b^2\ketbra00\),
\(A^2A^1 = -b^2\ketbra11\), and \(A^1A^1 = A^2A^2 = 0\), so
\(\Gamma_2(X)\) has coordinates \(c^2(X_{00}+X_{11})\), \(cbX_{10}\), \(cbX_{01}\),
\(-cbX_{10}\), \(0\), \(-b^2X_{00}\), \(-cbX_{01}\), \(-b^2X_{11}\), \(0\), and
\(b^2 = 2c^2\). This is the hand computation behind arXiv:2011.12127, line 2095. -/
theorem mem_aklt_groundSpace_two_iff (v : NSiteSpace 3 2) :
    v ∈ groundSpace akltTensor 2 ↔
      v ![1, 1] = 0 ∧ v ![2, 2] = 0 ∧ v ![0, 1] + v ![1, 0] = 0 ∧
        v ![0, 2] + v ![2, 0] = 0 ∧ 2 * v ![0, 0] + v ![1, 2] + v ![2, 1] = 0 := by
  constructor
  · rintro ⟨X, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [aklt_groundSpaceMap_two_apply, akltTensor_zero', akltTensor_one',
        akltTensor_two', Fin.isValue, Matrix.trace_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one, neg_mul, mul_neg,
        neg_neg, neg_zero]
    all_goals
      first
        | linear_combination
        | linear_combination (-(X 0 0 + X 1 1)) * akltCoeffPM_mul_self
  · rintro ⟨h11, h22, h01, h02, h00⟩
    have hb := akltCoeffPM_mul_self
    set c := akltCoeffZ
    set b := akltCoeffPM
    have hK : c * c * (b * b) ≠ 0 :=
      mul_ne_zero (mul_ne_zero akltCoeffZ_ne_zero akltCoeffZ_ne_zero)
        (mul_ne_zero akltCoeffPM_ne_zero akltCoeffPM_ne_zero)
    let X : Matrix (Fin 2) (Fin 2) ℂ :=
      !![-(c * c * v ![1, 2]), c * b * v ![0, 2]; c * b * v ![0, 1], -(c * c * v ![2, 1])]
    have key : groundSpaceMap akltTensor 2 X = (c * c * (b * b)) • v := by
      ext σ
      rw [cfg_two_eq σ]
      generalize σ 0 = a
      generalize σ 1 = a'
      fin_cases a <;> fin_cases a' <;>
        simp only [X, aklt_groundSpaceMap_two_apply, akltTensor_zero', akltTensor_one',
        akltTensor_two', Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
        Pi.smul_apply, mul_zero, zero_mul, add_zero, zero_add, mul_one,
        neg_mul, mul_neg, neg_neg, neg_zero]
      · linear_combination (-(c * c * (c * c))) * h00 - (v ![0, 0] * c * c) * hb
      · linear_combination
      · linear_combination
      · linear_combination (-(c * c * (b * b))) * h01
      · linear_combination (-(c * c * (b * b))) * h11
      · linear_combination
      · linear_combination (-(c * c * (b * b))) * h02
      · linear_combination
      · linear_combination (-(c * c * (b * b))) * h22
    refine ⟨(c * c * (b * b))⁻¹ • X, ?_⟩
    rw [map_smul, key, smul_smul, inv_mul_cancel₀ hK, one_smul]

/-! ### The three-site intersection property -/

private lemma cfg_three_eq (σ : Fin 3 → Fin 3) : σ = ![σ 0, σ 1, σ 2] := by
  ext k
  fin_cases k <;> rfl

private lemma fin_snoc_two (a b j : Fin 3) :
    (Fin.snoc ![a, b] j : Fin 3 → Fin 3) = ![a, b, j] := by
  ext k
  fin_cases k <;> rfl

/-- The five constraints on a right restriction \(\psi(i,\cdot,\cdot)\). -/
private lemma aklt_right_constraints (ψ : NSiteSpace 3 3) (i : Fin 3)
    (h : restrictFirst ψ i ∈ groundSpace akltTensor 2) :
    ψ ![i, 1, 1] = 0 ∧ ψ ![i, 2, 2] = 0 ∧ ψ ![i, 0, 1] + ψ ![i, 1, 0] = 0 ∧
      ψ ![i, 0, 2] + ψ ![i, 2, 0] = 0 ∧ 2 * ψ ![i, 0, 0] + ψ ![i, 1, 2] + ψ ![i, 2, 1] = 0 :=
  (mem_aklt_groundSpace_two_iff _).1 h

/-- The five constraints on a left restriction \(\psi(\cdot,\cdot,k)\). -/
private lemma aklt_left_constraints (ψ : NSiteSpace 3 3) (k : Fin 3)
    (h : restrictLast ψ k ∈ groundSpace akltTensor 2) :
    ψ ![1, 1, k] = 0 ∧ ψ ![2, 2, k] = 0 ∧ ψ ![0, 1, k] + ψ ![1, 0, k] = 0 ∧
      ψ ![0, 2, k] + ψ ![2, 0, k] = 0 ∧ 2 * ψ ![0, 0, k] + ψ ![1, 2, k] + ψ ![2, 1, k] = 0 := by
  have := (mem_aklt_groundSpace_two_iff _).1 h
  simpa only [restrictLast_apply, fin_snoc_two] using this

private lemma aklt_groundSpaceMap_three_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (a b c : Fin 3) :
    groundSpaceMap akltTensor 3 X ![a, b, c] =
      Matrix.trace (akltTensor a * (akltTensor b * (akltTensor c * X))) := by
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

/-- **The AKLT hand check** of arXiv:2011.12127, line 2095: a three-site vector
whose restrictions to sites \(\{1,2\}\) and \(\{2,3\}\) lie in the two-site
local ground space lies in the three-site local ground space. The boundary
matrix is read off from four coefficients,
\[
  c^2b^2\,\psi = \Gamma_3
  \begin{pmatrix} c\,\psi_{102} & -b\,\psi_{002} \\ b\,\psi_{001} & c\,\psi_{210}\end{pmatrix},
\]
and the remaining coordinates are matched using the five constraints on each of
the six restrictions together with \(b^2 = 2c^2\). -/
theorem aklt_mem_groundSpace_three_of_inLeftGround_of_inRightGround
    {ψ : NSiteSpace 3 3} (hLeft : InLeftGround akltTensor 2 ψ)
    (hRight : InRightGround akltTensor 2 ψ) :
    ψ ∈ groundSpace akltTensor 3 := by
  have R1 : ∀ i : Fin 3, ψ ![i, 1, 1] = 0 := fun i => (aklt_right_constraints ψ i (hRight i)).1
  have R2 : ∀ i : Fin 3, ψ ![i, 2, 2] = 0 := fun i => (aklt_right_constraints ψ i (hRight i)).2.1
  have R3 : ∀ i : Fin 3, ψ ![i, 0, 1] + ψ ![i, 1, 0] = 0 :=
    fun i => (aklt_right_constraints ψ i (hRight i)).2.2.1
  have R4 : ∀ i : Fin 3, ψ ![i, 0, 2] + ψ ![i, 2, 0] = 0 :=
    fun i => (aklt_right_constraints ψ i (hRight i)).2.2.2.1
  have R5 : ∀ i : Fin 3, 2 * ψ ![i, 0, 0] + ψ ![i, 1, 2] + ψ ![i, 2, 1] = 0 :=
    fun i => (aklt_right_constraints ψ i (hRight i)).2.2.2.2
  have L1 : ∀ k : Fin 3, ψ ![1, 1, k] = 0 := fun k => (aklt_left_constraints ψ k (hLeft k)).1
  have L2 : ∀ k : Fin 3, ψ ![2, 2, k] = 0 := fun k => (aklt_left_constraints ψ k (hLeft k)).2.1
  have L3 : ∀ k : Fin 3, ψ ![0, 1, k] + ψ ![1, 0, k] = 0 :=
    fun k => (aklt_left_constraints ψ k (hLeft k)).2.2.1
  have L4 : ∀ k : Fin 3, ψ ![0, 2, k] + ψ ![2, 0, k] = 0 :=
    fun k => (aklt_left_constraints ψ k (hLeft k)).2.2.2.1
  have L5 : ∀ k : Fin 3, 2 * ψ ![0, 0, k] + ψ ![1, 2, k] + ψ ![2, 1, k] = 0 :=
    fun k => (aklt_left_constraints ψ k (hLeft k)).2.2.2.2
  have hb := akltCoeffPM_mul_self
  set c := akltCoeffZ
  set b := akltCoeffPM
  have hK : c * c * (b * b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero akltCoeffZ_ne_zero akltCoeffZ_ne_zero)
      (mul_ne_zero akltCoeffPM_ne_zero akltCoeffPM_ne_zero)
  let X : Matrix (Fin 2) (Fin 2) ℂ :=
    !![c * ψ ![1, 0, 2], -(b * ψ ![0, 0, 2]); b * ψ ![0, 0, 1], c * ψ ![2, 1, 0]]
  have key : groundSpaceMap akltTensor 3 X = (c * c * (b * b)) • ψ := by
    ext σ
    rw [cfg_three_eq σ]
    generalize σ 0 = a
    generalize σ 1 = a'
    generalize σ 2 = a''
    fin_cases a <;> fin_cases a' <;> fin_cases a'' <;>
      simp only [X, aklt_groundSpaceMap_three_apply, akltTensor_zero', akltTensor_one',
      akltTensor_two', Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
      Pi.smul_apply, mul_zero, zero_mul, add_zero, zero_add, mul_one,
      neg_mul, mul_neg, neg_neg, neg_zero]
    · linear_combination (-(c * c * c * c)) * L5 0 + (c * c * c * c) * R4 1
        - (c * c * ψ ![0, 0, 0]) * hb
    · linear_combination
    · linear_combination
    · linear_combination (-(c * c * (b * b))) * R3 0
    · linear_combination (-(c * c * (b * b))) * R1 0
    · linear_combination (-(c * c * (b * b))) * L3 2
    · linear_combination (-(c * c * (b * b))) * R4 0
    · linear_combination (-(c * c * (b * b))) * (R5 0 - L5 0 - L3 2 + R4 1)
    · linear_combination (-(c * c * (b * b))) * R2 0
    · linear_combination (-(c * c * (b * b))) * (L3 0 - R3 0)
    · linear_combination (-(c * c * (b * b))) * (R3 1 - L1 0)
    · linear_combination
    · linear_combination (-(c * c * (b * b))) * L1 0
    · linear_combination (-(c * c * (b * b))) * R1 1
    · linear_combination (-(c * c * (b * b))) * L1 2
    · linear_combination (-(c * c * (b * b))) * R4 1
    · linear_combination (-(c * c * (b * b))) * (R5 1 - L1 2 - 2 * L3 0 + 2 * R3 0)
        - (b * b * ψ ![0, 0, 1]) * hb
    · linear_combination (-(c * c * (b * b))) * R2 1
    · linear_combination (-(c * c * (b * b))) * (L4 0 - R4 0)
    · linear_combination (-(c * c * (b * b))) * R3 2
    · linear_combination (-(c * c * (b * b))) * (R4 2 - L2 0)
    · linear_combination
    · linear_combination (-(c * c * (b * b))) * R1 2
    · linear_combination (-(c * c * (b * b))) * (R5 2 - L2 1 - 2 * L4 0 + 2 * R4 0)
        - (b * b * ψ ![0, 0, 2]) * hb
    · linear_combination (-(c * c * (b * b))) * L2 0
    · linear_combination (-(c * c * (b * b))) * L2 1
    · linear_combination (-(c * c * (b * b))) * R2 2
  refine ⟨(c * c * (b * b))⁻¹ • X, ?_⟩
  rw [map_smul, key, smul_smul, inv_mul_cancel₀ hK, one_smul]

/-- The intersection property
\[
  (\mathcal G_{1,2}\otimes\mathcal H_3)\cap(\mathcal H_1\otimes\mathcal G_{2,3})
  = \mathcal G_{1,2,3}
\]
for the AKLT tensor, arXiv:2011.12127, line 2095. The inclusion \(\supseteq\)
is the general restriction property of local ground spaces; the inclusion
\(\subseteq\) is the hand check above. -/
theorem aklt_groundSpace_intersection_two :
    (⨅ b : Fin 3, (groundSpace akltTensor 2).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin 3, (groundSpace akltTensor 2).comap (restrictFirstₗ a)) =
      groundSpace akltTensor 3 := by
  ext ψ
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · rintro ⟨hLeft, hRight⟩
    exact aklt_mem_groundSpace_three_of_inLeftGround_of_inRightGround hLeft hRight
  · intro hψ
    exact ⟨groundSpace_inLeftGround akltTensor 2 hψ, groundSpace_inRightGround akltTensor 2 hψ⟩

/-! ### The periodic two-site parent Hamiltonian -/

/-- Every vector satisfying the cyclic two-site AKLT constraints satisfies the
cyclic three-site constraints: each cyclic three-site window restricts on
both sides to cyclic two-site windows, and the hand check of the three-site
intersection property applies. -/
theorem aklt_chainGroundSpace_two_le_chainGroundSpace_three {N : ℕ} (hN : 3 ≤ N) :
    chainGroundSpace akltTensor 2 N ≤ chainGroundSpace akltTensor 3 N := by
  have hNpos : 0 < N := by omega
  intro ψ hψ
  rw [chainGroundSpace, dite_eq_left ⟨hNpos, by omega⟩] at hψ
  rw [chainGroundSpace, dite_eq_left ⟨hNpos, hN⟩]
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ ⊢
  intro i τ
  apply aklt_mem_groundSpace_three_of_inLeftGround_of_inRightGround
  · intro j
    rw [cyclicRestrictₗ_restrictLast]
    exact hψ i _
  · intro j
    rw [cyclicRestrictₗ_restrictFirst hNpos hN]
    exact hψ _ _

/-- **Unique ground state of the two-site AKLT parent Hamiltonian**
(arXiv:2011.12127, line 2095). On a periodic chain of \(N\ge3\) sites, the
common kernel of the cyclic two-site AKLT constraints is spanned by the AKLT
state:
\[
  \mathcal G_{N,2}(A_{\mathrm{AKLT}}) = \mathbb C\,V^{(N)}(A_{\mathrm{AKLT}}).
\]
The two-site chain space lies in the three-site chain space by the hand
check, and the three-site chain space is the span of the AKLT state by the
general theorem for normal tensors (\(L_0 = 2 < 3\)). The finite-size
condition \(N \ge 3\) is the one under which the general theorem applies; on
two periodic sites the two-site space is \(\mathcal G_2(A)\) itself. -/
theorem aklt_chainGroundSpace_two_eq_mpvSubmodule {N : ℕ} (hN : 3 ≤ N) :
    chainGroundSpace akltTensor 2 N = mpvSubmodule akltTensor N := by
  apply le_antisymm
  · refine (aklt_chainGroundSpace_two_le_chainGroundSpace_three hN).trans ?_
    rw [chainGroundSpace_eq_mpvSubmodule_normal aklt_isNormal aklt_isNBlkInjective_two
      (by norm_num) (by omega) (by norm_num) hN (by omega)]
  · intro ψ hψ
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hψ
    obtain ⟨a, rfl⟩ := hψ
    exact Submodule.smul_mem _ a (mpv_mem_chainGroundSpace akltTensor 2 N (by omega) (by omega))

/-- The two-site AKLT parent Hamiltonian on a periodic chain of \(N\ge3\) sites
has a unique ground state, arXiv:2011.12127, line 2095. -/
theorem aklt_parentHamiltonian_two_unique_gs {N : ℕ} (hN : 3 ≤ N) :
    HasUniqueGroundState (chainGroundSpace akltTensor 2 N) := by
  rw [HasUniqueGroundState, aklt_chainGroundSpace_two_eq_mpvSubmodule hN]
  have hmpv := mpv_ne_zero_of_isNBlkInjective aklt_isNBlkInjective_two (by norm_num)
    (show 2 + 1 ≤ N by omega)
  change Module.finrank ℂ (ℂ ∙ (mpv akltTensor : NSiteSpace 3 N)) = 1
  exact finrank_span_singleton (K := ℂ) hmpv

end MPSTensor
