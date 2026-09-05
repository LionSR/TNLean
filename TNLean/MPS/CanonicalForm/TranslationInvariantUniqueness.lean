/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Blocking
import QICLean.Kraus.CPPrimitive
import QICLean.Kraus.IrreducibleAction
import TNLean.MPS.CanonicalForm.FixedLengthIntertwiner
import TNLean.MPS.CanonicalForm.PGVWC07CanonicalForm
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.SharedInfra.Scaling

/-!
# Uniqueness of the translation-invariant canonical form at a fixed ring length

This file formalizes the corrected form of the uniqueness theorem for the
translation-invariant canonical form of Pérez-García, Verstraete, Wolf, and
Cirac (PGVWC07, arXiv:quant-ph/0608197, Theorem 7, MPSarchive.tex lines
1002-1015), starting from the fixed-length intertwiner of the module on the
fixed-length intertwiner and carrying out the unitarity argument of the
printed proof (lines 1097-1108).

## The printed theorem and its correction

The printed theorem takes a translation-invariant canonical \(D\)-MPS
\(\lvert\psi\rangle=\sum\operatorname{tr}(B_{i_1}\cdots B_{i_N})\lvert i_1\cdots i_N\rangle\)
on a ring of \(N\) sites such that condition C1 holds at some length \(L_0\),
the open-boundary canonical representation of \(\lvert\psi\rangle\) is unique,
and \(N>2L_0+D^4\). For any further translation-invariant canonical \(D\)-MPS
representation \(C\) of the same state it claims a unitary \(U\) with
\(B_i=UC_iU^\dagger\) for every \(i\).

The exact conjugacy claim is false on a finite ring: multiplying every matrix
\(C_i\) by a nontrivial \(N\)th root of unity preserves the represented
length-\(N\) state, while unitary conjugation acts trivially already for
\(d=D=1\). The counterexample and the corrected conclusion are recorded in
the paper-gap notes docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex
and docs/paper-gaps/pgvwc07_ti_uniqueness_scope.tex. The corrected conclusion
provides a unitary \(U\) and a scalar \(\xi\) with \(\lvert\xi\rvert=1\),
\(\xi^N=1\), and \(B_i=\xi UC_iU^\dagger\) for every \(i\).

## The proof route

The module on the fixed-length intertwiner supplies, from condition C1 and
the equality of the two length-\(N\) states, a nonzero matrix \(R\) and a
scalar \(x\neq0\) with \(RC_i=x^{-1}B_iR\) (lines 1063-1095). Condition C1
makes \(R\) invertible (lines 1105-1108) and both transfer maps irreducible,
so the unitary-gauge theorem for left-canonical irreducible tensors, applied
to the conjugate-transposed families, gives the unitary \(U\) and
\(\lvert x\rvert=1\); the printed proof derives these from the dual fixed
point \(\Lambda\) and the single-block property (lines 1097-1108).

Both representations are taken in the block form of Theorem 4 (lines
742-763), packaged in the module on the PGVWC07 canonical form. Condition C1
leaves \(B\) with one block, the first assertion of the proposition on
condition C1 (lines 911-919), and the invertible intertwiner transports
block injectivity to \(C\), which therefore has one block as well; the
printed proof treats only this single-block case, since it uses
\(\sum_iC_iC_i^\dagger=1\) at line 1104.

## Main declarations

* MPSTensor.isUnit_of_intertwines_of_isNBlkInjective,
  MPSTensor.exists_unitaryConj_of_intertwines_of_isNBlkInjective - the
  invertibility of the intertwiner, the unitary gauge, and the unit phase.
* MPSTensor.pgvwc07_uniqueness_of_unital,
  MPSTensor.pgvwc07_uniqueness_of_weighted - the corrected theorem for two
  single blocks, with unit weights and with the block weights of Theorem 4.
* MPSTensor.pgvwc07_uniqueness_of_canonical_form - the corrected uniqueness
  theorem for two canonical representations in the block form of Theorem 4,
  with the unitary \(U\) and the \(N\)th-root phase \(\xi\).
* MPSTensor.pgvwc07_uniqueness_of_canonical_form_rephased - exact unitary
  conjugacy after the explicit rephasing \(\widehat C_i:=\xi C_i\), which
  represents the same length-\(N\) state.
* MPSTensor.pgvwc07_uniqueness_of_canonical_form_unitGaugePhaseEquiv - the
  same conclusion as a unit-modulus gauge-phase equivalence.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-! ## Invertibility of the intertwiner -/

/-- A nonzero matrix `R` with `R C_i = x⁻¹ B_i R` for a block-injective family
`B` is invertible: its range is invariant under every `B_i`, hence under every
word of `B`, and block injectivity leaves no nontrivial invariant subspace.
This is the use of the single-block property of `B` in the proof of Theorem 7
of PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex lines 1105-1108), which the
source attributes to the proposition on condition C1. -/
theorem isUnit_of_intertwines_of_isNBlkInjective [NeZero D] {B C : MPSTensor d D}
    {L : ℕ} (hB : Kraus.IsNBlkInjective B L) {R : Matrix (Fin D) (Fin D) ℂ} {x : ℂ}
    (hR : R ≠ 0) (hx : x ≠ 0) (hrel : ∀ i, R * C i = x⁻¹ • (B i * R)) :
    IsUnit R := by
  classical
  have hInj : Kraus.IsInjective (Kraus.blockTensor B L) :=
    (Kraus.isNBlkInjective_iff_blockTensor_isInjective B L).mp hB
  have hAct : Matrix.IsIrreducibleAction (Kraus.blockTensor B L) :=
    Kraus.isIrreducibleAction_of_isIrreducibleFamily _
      (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
        (Kraus.injective_implies_irreducibleCP _ hInj))
  let Wr : Submodule ℂ (Fin D → ℂ) := LinearMap.range (Matrix.toLin' R)
  have hBR : ∀ i, B i * R = x • (R * C i) := by
    intro i
    rw [hrel i, smul_smul, mul_inv_cancel₀ hx, one_smul]
  have hword : ∀ w : List (Fin d), ∀ v ∈ Wr, (Kraus.evalWord B w).mulVec v ∈ Wr := by
    intro w
    induction w with
    | nil => intro v hv; simpa using hv
    | cons i w ih =>
      intro v hv
      rw [Kraus.evalWord_cons, ← Matrix.mulVec_mulVec]
      obtain ⟨u, hu⟩ := ih v hv
      rw [← hu]
      refine ⟨x • (C i).mulVec u, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hBR i,
        Matrix.smul_mulVec]
  have hinv : Matrix.IsInvariantSubmodule (Kraus.blockTensor B L) Wr :=
    fun I v hv => hword _ v hv
  rcases hAct Wr hinv with hbot | htop
  · exfalso
    apply hR
    have : Matrix.toLin' R = 0 := LinearMap.range_eq_bot.mp hbot
    exact Matrix.toLin'.injective (by simpa using this)
  · rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨u, hu⟩ := (LinearMap.range_eq_top.mp htop) v
    exact ⟨u, by simpa using hu⟩

/-! ## The unitary gauge and the unit phase -/

/-- **The unitary gauge and the unit-modulus phase**, PGVWC07
(arXiv:quant-ph/0608197, Theorem 7, MPSarchive.tex lines 1097-1108). Let `B`
and `C` be unital, `∑ B_i B_i† = 1` and `∑ C_i C_i† = 1`, let `B` satisfy
condition C1 at length `L₀`, and let `R ≠ 0` and `x ≠ 0` satisfy
`R C_i = x⁻¹ B_i R` for every `i`. Then `|x| = 1` and there is a unitary `U`
with `B_i = x U C_i U†` for every `i`.

Condition C1 makes `R` invertible and both transfer maps irreducible, so the
conjugate-transposed families are left-canonical irreducible tensors related
by the gauge `(R†)⁻¹` and the scalar `conj x`; the fixed-point argument of
lines 1097-1108 is then the unitary-gauge theorem
`exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible`. The
printed proof uses the dual fixed point `Λ` of `B` for `|x| = 1` and the
single-block property of `B` for `R R† = 1`; here both are consequences of
condition C1 through the Perron--Frobenius theory of irreducible maps. -/
theorem exists_unitaryConj_of_intertwines_of_isNBlkInjective {B C : MPSTensor d D} {L₀ : ℕ}
    (hB_unital : ∑ i, B i * (B i)ᴴ = 1)
    (hC_unital : ∑ i, C i * (C i)ᴴ = 1)
    (hC1 : Kraus.IsNBlkInjective B L₀)
    {R : Matrix (Fin D) (Fin D) ℂ} {x : ℂ}
    (hR : R ≠ 0) (hx : x ≠ 0) (hrel : ∀ i, R * C i = x⁻¹ • (B i * R)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ, ‖x‖ = 1 ∧
      ∀ i, B i = x • ((U : Matrix (Fin D) (Fin D) ℂ) * C i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  have : NeZero D := ⟨fun hD => hR (by subst hD; exact Subsingleton.elim R 0)⟩
  have hRunit : IsUnit R := isUnit_of_intertwines_of_isNBlkInjective hC1 hR hx hrel
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRunit
  -- `B_i = x R C_i R⁻¹`.
  have hBR : ∀ i, B i * R = x • (R * C i) := by
    intro i
    rw [hrel i, smul_smul, mul_inv_cancel₀ hx, one_smul]
  have hBconj : ∀ i, B i = x • (R * C i * R⁻¹) := by
    intro i
    rw [← smul_mul_assoc, ← hBR i, Matrix.mul_assoc, Matrix.mul_nonsing_inv R hRdet,
      Matrix.mul_one]
  -- Pass to the conjugate-transposed families, which are left-canonical.
  let Ba : MPSTensor d D := fun i => (B i)ᴴ
  let Ca : MPSTensor d D := fun i => (C i)ᴴ
  have hBa_left : IsLeftCanonical Ba := by
    change ∑ i, (Ba i)ᴴ * Ba i = 1
    simpa [Ba] using hB_unital
  have hCa_left : IsLeftCanonical Ca := by
    change ∑ i, (Ca i)ᴴ * Ca i = 1
    simpa [Ca] using hC_unital
  -- Irreducibility of `B` and `C` from condition C1.
  have hBact : Matrix.IsIrreducibleAction B := by
    have hInj : Kraus.IsInjective (Kraus.blockTensor B L₀) :=
      (Kraus.isNBlkInjective_iff_blockTensor_isInjective B L₀).mp hC1
    have hAct : Matrix.IsIrreducibleAction (Kraus.blockTensor B L₀) :=
      Kraus.isIrreducibleAction_of_isIrreducibleFamily _
        (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
          (Kraus.injective_implies_irreducibleCP _ hInj))
    intro Wr hinv
    refine hAct Wr fun I v hv => ?_
    change (Kraus.evalWord B (Kraus.wordOfBlock d L₀ I)).mulVec v ∈ Wr
    generalize Kraus.wordOfBlock d L₀ I = w
    induction w with
    | nil => simpa using hv
    | cons i w ih =>
      rw [Kraus.evalWord_cons, ← Matrix.mulVec_mulVec]
      exact hinv i _ ih
  have hCact : Matrix.IsIrreducibleAction C := by
    intro Wr hinv
    -- The image of `Wr` under `R` is `B`-invariant.
    have hmap : Matrix.IsInvariantSubmodule B (Wr.map (Matrix.toLin' R)) := by
      intro i v hv
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨x • (C i).mulVec u, Wr.smul_mem x (hinv i u hu), ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hBR i,
        Matrix.smul_mulVec]
    have hRinj : Function.Injective R.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hRunit
    rcases hBact _ hmap with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' : Matrix.toLin' R v ∈ Wr.map (Matrix.toLin' R) := Submodule.mem_map_of_mem hv
      rw [hbot, Submodule.mem_bot, Matrix.toLin'_apply] at hv'
      exact hRinj (by rw [hv', Matrix.mulVec_zero])
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hv' : Matrix.toLin' R v ∈ Wr.map (Matrix.toLin' R) := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hv'
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at huv
      rwa [← hRinj huv]
  have hBa_irr : Kraus.IsIrreducibleFamily Ba :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.isIrreducibleMap_mapLM_conjTranspose B
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B
          (Kraus.isIrreducibleFamily_of_isIrreducibleAction B hBact)))
  have hCa_irr : Kraus.IsIrreducibleFamily Ca :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.isIrreducibleMap_mapLM_conjTranspose C
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily C
          (Kraus.isIrreducibleFamily_of_isIrreducibleAction C hCact)))
  -- The gauge relation for the conjugate-transposed families: `B_i† = conj x (R†)⁻¹ C_i† R†`.
  have hRH : IsUnit (Rᴴ)⁻¹ := by
    rw [Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact hRdet.star
  let X : GL (Fin D) ℂ := hRH.unit
  have hX : (X : Matrix (Fin D) (Fin D) ℂ) = (Rᴴ)⁻¹ := rfl
  have hXinv : ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = Rᴴ := by
    rw [Matrix.coe_units_inv, hX, Matrix.nonsing_inv_nonsing_inv]
    rw [Matrix.det_conjTranspose]
    exact hRdet.star
  have hBa_gauge : ∀ i, Ba i = (starRingEnd ℂ x) •
      ((X : Matrix (Fin D) (Fin D) ℂ) * Ca i *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro i
    rw [hXinv, hX]
    simp only [Ba, Ca, hBconj i, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rfl
  have hxbar : starRingEnd ℂ x ≠ 0 := by simpa using hx
  obtain ⟨U, hU_norm, hU⟩ :=
    exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible X (starRingEnd ℂ x)
      hxbar hBa_gauge hCa_left hBa_left hCa_irr hBa_irr
  -- Return to the original families: `B_i = x U C_i U†`.
  have hBconjU : ∀ i, B i = x • ((U : Matrix (Fin D) (Fin D) ℂ) * C i *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
    intro i
    have := congrArg Matrix.conjTranspose (hU i)
    simp only [Ba, Ca, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Complex.star_def, Complex.conj_conj, Matrix.mul_assoc] at this
    rw [this, Matrix.mul_assoc]
  exact ⟨U, by simpa using hU_norm, hBconjU⟩

/-- The length-`N` coefficients of two tensors related by a unitary gauge and a
scalar `x` differ by the factor `x^N`: `B_i = x U C_i U†` gives
`⟨σ|ψ_B⟩ = x^N ⟨σ|ψ_C⟩`. This is the homogeneity used for the root-of-unity
correction in docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex. -/
theorem mpv_eq_pow_mul_mpv_of_unitaryConj {B C : MPSTensor d D} {x : ℂ} (hx : x ≠ 0)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hconj : ∀ i, B i = x • ((U : Matrix (Fin D) (Fin D) ℂ) * C i *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv B σ = x ^ N * mpv C σ := by
  have hUU : (U : Matrix (Fin D) (Fin D) ℂ) * star (U : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hUunit : IsUnit (U : Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hUU)
  have hgauge : GaugeEquiv C (fun i => x⁻¹ • B i) := by
    refine ⟨hUunit.unit, fun i => ?_⟩
    change x⁻¹ • B i = _
    rw [hconj i, smul_smul, inv_mul_cancel₀ hx, one_smul, Matrix.coe_units_inv,
      IsUnit.unit_spec, Matrix.inv_eq_right_inv hUU, Matrix.star_eq_conjTranspose]
  have := hgauge.sameMPV N σ
  rw [mpv_smul] at this
  rw [this, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul]

/-! ## Scalar rescalings -/

/-- Nonzero scalar multiplication preserves injectivity at a fixed blocking
length: every word of the scaled tensor is the word of the original tensor
times a nonzero power of the scalar. This converts condition C1 for the
weighted representation `λ B` of Theorem 4 into condition C1 for its block
`B` (PGVWC07, arXiv:quant-ph/0608197, MPSarchive.tex lines 742-763). -/
theorem isNBlkInjective_smul {A : MPSTensor d D} {N : ℕ} (z : ℂ) (hz : z ≠ 0)
    (hA : Kraus.IsNBlkInjective A N) :
    Kraus.IsNBlkInjective (fun i => z • A i) N := by
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan, eq_top_iff] at hA ⊢
  intro X hXtop
  clear hXtop
  have hX : X ∈ Submodule.span ℂ
      (Set.range fun σ : Fin N → Fin d => Kraus.evalWord A (List.ofFn σ)) :=
    hA (Submodule.mem_top : X ∈ (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)))
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨σ, rfl⟩ := hX
      change Kraus.evalWord A (List.ofFn σ) ∈ _
      rw [← inv_smul_smul₀ (pow_ne_zero N hz) (Kraus.evalWord A (List.ofFn σ))]
      apply Submodule.smul_mem
      have hscaled : Kraus.evalWord (fun i => z • A i) (List.ofFn σ) ∈
          Submodule.span ℂ (Set.range fun τ : Fin N → Fin d =>
            Kraus.evalWord (fun i => z • A i) (List.ofFn τ)) :=
        Submodule.subset_span (Set.mem_range_self σ)
      simpa only [Kraus.evalWord_smul, List.length_ofFn] using hscaled
  | zero => exact Submodule.zero_mem _
  | add X Y _ _ hX hY => exact Submodule.add_mem _ hX hY
  | smul z X _ hX => exact Submodule.smul_mem _ z hX

/-- Scaling a family by a scalar `c` scales the sum `∑_i A_i A_i†` by `conj c * c`. -/
theorem sum_smul_mul_conjTranspose_smul (A : MPSTensor d D) (c : ℂ) :
    ∑ i, (c • A i) * (c • A i)ᴴ = (star c * c) • ∑ i, A i * (A i)ᴴ := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Finset.smul_sum]

/-- A weighted block `λ A` of the canonical form of PGVWC07 (arXiv:quant-ph/0608197,
Theorem 4, MPSarchive.tex lines 742-763), with `∑_i (λ A_i)(λ A_i)† = λ² 1`, has
the unital block `A = λ⁻¹ (λ A)`. -/
theorem sum_inv_smul_mul_conjTranspose_eq_one {A : MPSTensor d D} {lam : ℝ} (hlam : 0 < lam)
    (hA : ∑ i, A i * (A i)ᴴ = ((lam : ℂ) ^ 2) • 1) :
    ∑ i, ((lam : ℂ)⁻¹ • A i) * ((lam : ℂ)⁻¹ • A i)ᴴ = 1 := by
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hstar : star ((lam : ℂ)⁻¹) = (lam : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [sum_smul_mul_conjTranspose_smul, hA, smul_smul, hstar,
    show (lam : ℂ)⁻¹ * (lam : ℂ)⁻¹ * (lam : ℂ) ^ 2 = 1 by field_simp, one_smul]

/-! ## The corrected uniqueness theorem for a single block -/

/-- **Uniqueness for unital single blocks.** PGVWC07 (arXiv:quant-ph/0608197,
Theorem 7, MPSarchive.tex lines 1002-1015) in the case treated by its printed
proof, which uses `∑_i C_i C_i† = 1` at line 1104: two unital families
`∑_i B_i B_i† = 1` and `∑_i C_i C_i† = 1`, condition C1 for `B` at length `L₀`
(lines 907-908), the size condition `N > 2 L₀ + D⁴` (hypothesis (iii)), and
equality of the two nonzero length-`N` states. The conclusion is corrected as
recorded in docs/paper-gaps/pgvwc07_ti_uniqueness_scope.tex: there are a
unitary `U` and a scalar `ξ` with `|ξ| = 1`, `ξ^N = 1`, and `B_i = ξ U C_i U†`
for every `i`.

The printed hypothesis (ii), uniqueness of the open-boundary canonical
representation, is not consumed: the intertwiner chain of lines 1080-1086 is
obtained from the cut vectors and condition C1 alone
(`exists_intertwiner_of_fixedLength_mpv_eq`), which is the square case of the
freedom theorem invoked there. Condition C1 also supplies the invertibility of
`R` (lines 1105-1108) and, through irreducibility of the transfer maps, the
fixed-point argument of lines 1097-1108 in the form of
`exists_unitaryConj_of_intertwines_of_isNBlkInjective`. The root-of-unity
property `ξ^N = 1` follows from the equality of the two nonzero length-`N`
states. -/
theorem pgvwc07_uniqueness_of_unital {B C : MPSTensor d D} {L₀ N : ℕ}
    (hB_unital : ∑ i, B i * (B i)ᴴ = 1)
    (hC_unital : ∑ i, C i * (C i)ᴴ = 1)
    (hC1 : Kraus.IsNBlkInjective B L₀)
    (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv B σ = mpv C σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv B σ ≠ 0) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ξ : ℂ), ‖ξ‖ = 1 ∧ ξ ^ N = 1 ∧
      ∀ i, B i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * C i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hnonzero
  -- The nonzero intertwiner `R` with `R C_i = x⁻¹ B_i R` (lines 1063-1095).
  have : NeZero D := ⟨fun hD => hσ₀ (by subst hD; simp [mpv, coeff, Matrix.trace])⟩
  obtain ⟨R, x, hR, hx, hrel⟩ :=
    exists_intertwiner_of_fixedLength_mpv_eq hB_unital hC1 hN.le hstate
  -- The unitary gauge and the unit phase (lines 1097-1108).
  obtain ⟨U, hx_norm, hBconjU⟩ :=
    exists_unitaryConj_of_intertwines_of_isNBlkInjective hB_unital hC_unital hC1 hR hx hrel
  -- The root-of-unity property from the equality of the nonzero length-`N` states.
  have hxN : x ^ N = 1 := by
    have h := mpv_eq_pow_mul_mpv_of_unitaryConj hx U hBconjU σ₀
    rw [hstate σ₀] at h
    have hC0 : mpv C σ₀ ≠ 0 := by rwa [hstate σ₀] at hσ₀
    exact (mul_eq_right₀ hC0).mp h.symm
  exact ⟨U, x, hx_norm, hxN, hBconjU⟩

/-- **Uniqueness for weighted single blocks.** PGVWC07 (arXiv:quant-ph/0608197,
Theorem 7, MPSarchive.tex lines 1002-1015) for two single-block canonical
representations `λ_B B¹` and `λ_C C¹` of Theorem 4 (lines 742-763), written
through the identities `∑_i B_i B_i† = λ_B² 1` and `∑_i C_i C_i† = λ_C² 1`
with `0 < λ_B, λ_C`: for two such representations of the same nonzero
length-`N` state, with condition C1 for `B` at length `L₀` and
`N > 2 L₀ + D⁴`, the weights agree and there are a unitary `U` and a scalar
`ξ` with `|ξ| = 1`, `ξ^N = 1`, and `B_i = ξ U C_i U†` for every `i`.

The printed proof takes both weights equal to one; the intertwiner of
lines 1063-1095 is obtained for the pair `λ_B⁻¹ B`, `λ_B⁻¹ C`, which represents
the same state, and the fixed-point argument of lines 1097-1108 is applied to
the unital blocks `λ_B⁻¹ B` and `λ_C⁻¹ C`. The weights then agree because the
resulting phase `x λ_C / λ_B` has modulus one while `x^N = 1`. -/
theorem pgvwc07_uniqueness_of_weighted {B C : MPSTensor d D} {L₀ N : ℕ} {lamB lamC : ℝ}
    (hlamB : 0 < lamB) (hlamC : 0 < lamC)
    (hB_sum : ∑ i, B i * (B i)ᴴ = ((lamB : ℂ) ^ 2) • 1)
    (hC_sum : ∑ i, C i * (C i)ᴴ = ((lamC : ℂ) ^ 2) • 1)
    (hC1 : Kraus.IsNBlkInjective B L₀)
    (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv B σ = mpv C σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv B σ ≠ 0) :
    lamB = lamC ∧ ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ξ : ℂ), ‖ξ‖ = 1 ∧ ξ ^ N = 1 ∧
      ∀ i, B i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * C i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hnonzero
  have : NeZero D := ⟨fun hD => hσ₀ (by subst hD; simp [mpv, coeff, Matrix.trace])⟩
  have hlamB0 : (lamB : ℂ) ≠ 0 := by exact_mod_cast hlamB.ne'
  have hlamC0 : (lamC : ℂ) ≠ 0 := by exact_mod_cast hlamC.ne'
  -- The unital blocks and the common rescaling of the pair.
  set B₁ : MPSTensor d D := fun i => (lamB : ℂ)⁻¹ • B i with hB₁
  set C₁ : MPSTensor d D := fun i => (lamB : ℂ)⁻¹ • C i with hC₁
  set C₂ : MPSTensor d D := fun i => (lamC : ℂ)⁻¹ • C i with hC₂
  have hB₁_unital : ∑ i, B₁ i * (B₁ i)ᴴ = 1 := sum_inv_smul_mul_conjTranspose_eq_one hlamB hB_sum
  have hC₂_unital : ∑ i, C₂ i * (C₂ i)ᴴ = 1 := sum_inv_smul_mul_conjTranspose_eq_one hlamC hC_sum
  have hC1₁ : Kraus.IsNBlkInjective B₁ L₀ := isNBlkInjective_smul _ (inv_ne_zero hlamB0) hC1
  have hstate₁ : ∀ σ : Fin N → Fin d, mpv B₁ σ = mpv C₁ σ := by
    intro σ
    simp only [hB₁, hC₁, mpv_smul, hstate σ]
  -- The intertwiner for the rescaled pair (lines 1063-1095).
  obtain ⟨R, x, hR, hx, hrel⟩ :=
    exists_intertwiner_of_fixedLength_mpv_eq hB₁_unital hC1₁ hN.le hstate₁
  -- The same intertwiner relates the unital blocks with the phase `x λ_C / λ_B`.
  set y : ℂ := x * (lamC : ℂ) / (lamB : ℂ) with hy
  have hy0 : y ≠ 0 := by
    rw [hy]
    exact div_ne_zero (mul_ne_zero hx hlamC0) hlamB0
  have hrel₂ : ∀ i, R * C₂ i = y⁻¹ • (B₁ i * R) := by
    intro i
    have h := hrel i
    simp only [hC₁, Matrix.mul_smul] at h
    have hRC : R * C i = (lamB : ℂ) • (x⁻¹ • (B₁ i * R)) := by
      rw [← h, smul_smul, mul_inv_cancel₀ hlamB0, one_smul]
    simp only [hC₂, Matrix.mul_smul]
    rw [hRC, smul_smul, smul_smul, hy]
    congr 1
    field_simp
  -- The unitary gauge and the unit phase (lines 1097-1108).
  obtain ⟨U, hy_norm, hconj₁⟩ :=
    exists_unitaryConj_of_intertwines_of_isNBlkInjective hB₁_unital hC₂_unital hC1₁ hR hy0 hrel₂
  have hconj : ∀ i, B i = x • ((U : Matrix (Fin D) (Fin D) ℂ) * C i *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
    intro i
    have h := hconj₁ i
    simp only [hB₁, hC₂, Matrix.mul_smul, Matrix.smul_mul, smul_smul] at h
    have hB : B i = (lamB : ℂ) • ((lamB : ℂ)⁻¹ • B i) := by
      rw [smul_smul, mul_inv_cancel₀ hlamB0, one_smul]
    rw [hB, h, smul_smul, hy]
    congr 1
    field_simp
  -- The root-of-unity property and the equality of the weights.
  have hxN : x ^ N = 1 := by
    have h := mpv_eq_pow_mul_mpv_of_unitaryConj hx U hconj σ₀
    rw [hstate σ₀] at h
    have hC0 : mpv C σ₀ ≠ 0 := by rwa [hstate σ₀] at hσ₀
    exact (mul_eq_right₀ hC0).mp h.symm
  have hx_norm : ‖x‖ = 1 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hxN
    simp only [norm_pow, norm_one] at h
    have hN0 : N ≠ 0 := by
      have : 0 < D ^ 4 := pow_pos (NeZero.pos D) 4
      omega
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN0).mp h
  have hweights : lamB = lamC := by
    rw [hy, norm_div, norm_mul, hx_norm, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hlamC.le, Real.norm_of_nonneg hlamB.le,
      div_eq_one_iff_eq hlamB.ne'] at hy_norm
    exact hy_norm.symm
  exact ⟨hweights, U, x, hx_norm, hxN, hconj⟩

/-! ## The corrected uniqueness theorem -/

/-- **Uniqueness of the translation-invariant canonical form, corrected
form.** PGVWC07 (arXiv:quant-ph/0608197, Theorem 7, MPSarchive.tex lines
1002-1015), with the conclusion corrected as recorded in
docs/paper-gaps/pgvwc07_ti_uniqueness_scope.tex.

Let `B` and `C` be translation-invariant canonical `D`-MPS representations in
the sense of Theorem 4 (lines 742-763), each a weighted direct sum of blocks
satisfying the three canonical conditions. Assume condition C1 for `B` at
length `L₀` (lines 907-908), the size condition `N > 2 L₀ + D⁴` (hypothesis
(iii)), and that `B` and `C` represent the same nonzero length-`N` state. Then
there are a unitary `U` and a scalar `ξ` with `|ξ| = 1`, `ξ^N = 1`, and
`B_i = ξ U C_i U†` for every `i`.

Condition C1 leaves `B` with a single block, the first assertion of the
proposition on condition C1 (lines 911-919). The intertwiner of lines
1063-1095 for the rescaled pair `λ_B⁻¹ B`, `λ_B⁻¹ C` is invertible by
condition C1 (lines 1105-1108), so `C` is conjugate to a scalar multiple of
`B` and satisfies condition C1 as well; hence `C` has a single block too, and
the weighted single-block theorem applies. The printed hypothesis (ii),
uniqueness of the open-boundary canonical representation, is not consumed,
as explained at `pgvwc07_uniqueness_of_unital`. -/
theorem pgvwc07_uniqueness_of_canonical_form {B C : MPSTensor d D} {L₀ N : ℕ}
    (hB : IsPGVWC07CanonicalForm B) (hC : IsPGVWC07CanonicalForm C)
    (hC1 : Kraus.IsNBlkInjective B L₀)
    (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv B σ = mpv C σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv B σ ≠ 0) :
    ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ξ : ℂ), ‖ξ‖ = 1 ∧ ξ ^ N = 1 ∧
      ∀ i, B i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * C i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hnonzero
  have : NeZero D := ⟨fun hD => hσ₀ (by subst hD; simp [mpv, coeff, Matrix.trace])⟩
  obtain ⟨hB⟩ := hB
  obtain ⟨hC⟩ := hC
  -- `B` has a single block (lines 911-919).
  obtain ⟨lamB, hlamB, -, hB_sum⟩ :=
    hB.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hlamB0 : (lamB : ℂ) ≠ 0 := by exact_mod_cast hlamB.ne'
  -- The invertible intertwiner of the rescaled pair makes `C` block injective.
  set B₁ : MPSTensor d D := fun i => (lamB : ℂ)⁻¹ • B i with hB₁
  set C₁ : MPSTensor d D := fun i => (lamB : ℂ)⁻¹ • C i with hC₁
  have hB₁_unital : ∑ i, B₁ i * (B₁ i)ᴴ = 1 := sum_inv_smul_mul_conjTranspose_eq_one hlamB hB_sum
  have hC1₁ : Kraus.IsNBlkInjective B₁ L₀ := isNBlkInjective_smul _ (inv_ne_zero hlamB0) hC1
  have hstate₁ : ∀ σ : Fin N → Fin d, mpv B₁ σ = mpv C₁ σ := by
    intro σ
    simp only [hB₁, hC₁, mpv_smul, hstate σ]
  obtain ⟨R, x, hR, hx, hrel⟩ :=
    exists_intertwiner_of_fixedLength_mpv_eq hB₁_unital hC1₁ hN.le hstate₁
  have hRunit : IsUnit R := isUnit_of_intertwines_of_isNBlkInjective hC1₁ hR hx hrel
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRunit
  have hgauge : GaugeEquiv B₁ (fun i => x • C₁ i) := by
    refine ⟨hRunit.unit⁻¹, fun i => ?_⟩
    have hBR : B₁ i * R = x • (R * C₁ i) := by
      rw [hrel i, smul_smul, mul_inv_cancel₀ hx, one_smul]
    rw [inv_inv, Matrix.coe_units_inv, IsUnit.unit_spec, Matrix.mul_assoc, hBR, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul R hRdet, Matrix.one_mul]
  have hC1_C : Kraus.IsNBlkInjective C L₀ := by
    have h := isNBlkInjective_smul (x⁻¹ * (lamB : ℂ)) (mul_ne_zero (inv_ne_zero hx) hlamB0)
      (isNBlkInjective_of_gaugeEquiv hC1₁ hgauge)
    convert h using 2
    funext i
    simp only [hC₁, smul_smul]
    rw [show x⁻¹ * (lamB : ℂ) * (x * (lamB : ℂ)⁻¹) = 1 by field_simp, one_smul]
  -- `C` has a single block as well, and the weighted single-block theorem applies.
  obtain ⟨lamC, hlamC, -, hC_sum⟩ :=
    hC.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1_C
  exact (pgvwc07_uniqueness_of_weighted hlamB hlamC hB_sum hC_sum hC1 hN hstate ⟨σ₀, hσ₀⟩).2

/-- **Exact unitary conjugacy after rephasing.** With the data of
`pgvwc07_uniqueness_of_canonical_form`, the rephased representation
`ξ C_i` is exactly unitarily conjugate to `B` and represents the same
length-`N` state, because `ξ^N = 1`. This is the corrected form of the
conclusion `B_i = U C_i U†` printed in PGVWC07 (arXiv:quant-ph/0608197,
Theorem 7, MPSarchive.tex lines 1011-1013), as recorded in
docs/paper-gaps/pgvwc07_ti_uniqueness_scope.tex. -/
theorem pgvwc07_uniqueness_of_canonical_form_rephased {B C : MPSTensor d D} {L₀ N : ℕ}
    (hB : IsPGVWC07CanonicalForm B) (hC : IsPGVWC07CanonicalForm C)
    (hC1 : Kraus.IsNBlkInjective B L₀)
    (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv B σ = mpv C σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv B σ ≠ 0) :
    ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ ξ ^ N = 1 ∧
      (∀ σ : Fin N → Fin d, mpv (fun i => ξ • C i) σ = mpv C σ) ∧
      ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
        ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * (ξ • C i) *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨U, ξ, hξ, hξN, hconj⟩ :=
    pgvwc07_uniqueness_of_canonical_form hB hC hC1 hN hstate hnonzero
  refine ⟨ξ, hξ, hξN, fun σ => ?_, U, fun i => ?_⟩
  · rw [mpv_smul, hξN, one_mul]
  · rw [hconj i]
    simp

/-- The corrected uniqueness theorem as a unit-modulus gauge-phase
equivalence: the unitary `U` is the gauge and the `N`th root of unity `ξ` is
the phase. -/
theorem pgvwc07_uniqueness_of_canonical_form_unitGaugePhaseEquiv {B C : MPSTensor d D}
    {L₀ N : ℕ}
    (hB : IsPGVWC07CanonicalForm B) (hC : IsPGVWC07CanonicalForm C)
    (hC1 : Kraus.IsNBlkInjective B L₀)
    (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv B σ = mpv C σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv B σ ≠ 0) :
    UnitGaugePhaseEquiv C B := by
  obtain ⟨U, ξ, hξ, -, hconj⟩ :=
    pgvwc07_uniqueness_of_canonical_form hB hC hC1 hN hstate hnonzero
  have hUU : (U : Matrix (Fin D) (Fin D) ℂ) * star (U : Matrix (Fin D) (Fin D) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hUunit : IsUnit (U : Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hUU)
  refine ⟨hUunit.unit, ξ, ?_, fun i => ?_⟩
  · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
    norm_num
  · rw [hconj i, Matrix.coe_units_inv, IsUnit.unit_spec, Matrix.inv_eq_right_inv hUU,
      Matrix.star_eq_conjTranspose]

end MPSTensor
