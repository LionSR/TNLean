/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CornerSkolemNoether
import TNLean.Channel.PositiveConditionalExpectationDirectSum
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.Periodic.Overlap.SelfOverlapSetup
import TNLean.MPS.Periodic.SectorContraction

/-!
# Periodic sector-match contraction foundations

This module collects the common blocking inverses, ambient corner gauges, and
cyclic-list identities used in the full-cycle contraction.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module

namespace MPSTensor

variable {d D : ℕ}

/-- Common `Ω_u` right inverses for the sector blocks.

This is the Lean form of the normality input in arXiv:1708.00029, Appendix A,
lines 1026--1040, equations `eq:Fu` and `eq:Omegauprop`: after choosing one
common positive word length, every sector block has a right inverse for the
linear span of its length-`L` word products. -/
lemma exists_common_sectorDecompositionMaps_of_isNormal_leftCanonical
    {m : ℕ} {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPSTensor d (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hNondeg : ∀ k, dim k ≠ 0)
    (hNormal : ∀ k, IsNormal (blocks k)) :
    ∃ L : ℕ, 0 < L ∧
      ∃ Ω : (k : Fin m) →
          Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ] ((Fin L → Fin d) → ℂ),
        ∀ (k : Fin m) (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          ∑ σ : Fin L → Fin d,
            (Ω k X σ) • evalWord (blocks k) (List.ofFn σ) = X := by
  obtain ⟨L, hL_pos, hL⟩ :=
    exists_common_isNBlkInjective_of_isNormal_leftCanonical
      blocks hBlocks_lc hNondeg hNormal
  refine ⟨L, hL_pos, fun k => blockDecompositionMap (hL k), ?_⟩
  intro k X
  exact blockDecompositionMap_sum (hL k) X

/-- Nonzero scalar multiplication preserves injectivity at a fixed blocking length.

This is used when normalizing the matched sector tensors in arXiv:1708.00029,
Appendix A, lines 985--1002. -/
private lemma isNBlkInjective_smul_of_ne
    {e n N : ℕ} (C : MPSTensor e n) (z : ℂ) (hz : z ≠ 0)
    (hC : IsNBlkInjective C N) :
    IsNBlkInjective (fun i => z • C i) N := by
  rw [IsNBlkInjective, eq_top_iff] at hC ⊢
  intro X hXtop
  clear hXtop
  have hX : X ∈ Submodule.span ℂ
      (Set.range fun σ : Fin N → Fin e => evalWord C (List.ofFn σ)) :=
    hC (Submodule.mem_top : X ∈ (⊤ : Submodule ℂ (MatrixAlg n)))
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨σ, rfl⟩ := hX
      change evalWord C (List.ofFn σ) ∈ _
      rw [← inv_smul_smul₀ (pow_ne_zero N hz)
        (evalWord C (List.ofFn σ))]
      apply Submodule.smul_mem
      have hscaled : evalWord (fun i => z • C i) (List.ofFn σ) ∈
          Submodule.span ℂ (Set.range fun τ : Fin N → Fin e =>
            evalWord (fun i => z • C i) (List.ofFn τ)) :=
        Submodule.subset_span (Set.mem_range_self σ)
      simpa only [evalWord_smul, List.length_ofFn] using hscaled
  | zero => exact Submodule.zero_mem _
  | add X Y _ _ hX hY => exact Submodule.add_mem _ hX hY
  | smul z X _ hX => exact Submodule.smul_mem _ z hX

/-- Nonzero scalar multiplication preserves algebraic normality.

This is used when normalizing the matched sector tensors in arXiv:1708.00029,
Appendix A, lines 985--1002. -/
private lemma isNormal_smul_of_ne
    {e n : ℕ} (C : MPSTensor e n) (z : ℂ) (hz : z ≠ 0)
    (hC : IsNormal C) :
    IsNormal (fun i => z • C i) := by
  obtain ⟨N, hN, hC⟩ := hC
  exact ⟨N, hN, isNBlkInjective_smul_of_ne C z hz hC⟩

/-- A matched pair of compressed sectors has an ambient corner implementation.

This is equation `eq:blockedABprop` in ambient form, hence the input to
`eq:BCmprop`, in arXiv:1708.00029, Appendix A, lines 985--1024. -/
lemma exists_ambient_corner_gauge_of_gaugePhase
    {e nA nB : ℕ} [NeZero nA]
    (CA : MPSTensor e nA) (CB : MPSTensor e nB)
    (hdim : nA = nB)
    (P Q : MatrixAlg D)
    (φP : MatrixAlg nA ≃ₗ[ℂ] cornerSubmodule P)
    (φQ : MatrixAlg nB ≃ₗ[ℂ] cornerSubmodule Q)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hφP_mul : ∀ X Y : MatrixAlg nA,
      (φP (X * Y)).1 = (φP X).1 * (φP Y).1)
    (hφQ_mul : ∀ X Y : MatrixAlg nB,
      (φQ (X * Y)).1 = (φQ X).1 * (φQ Y).1)
    (hφP_star : ∀ X : MatrixAlg nA, (φP Xᴴ).1 = (φP X).1ᴴ)
    (hφQ_star : ∀ X : MatrixAlg nB, (φQ Xᴴ).1 = (φQ X).1ᴴ)
    (hCA_lc : IsLeftCanonical CA) (hCB_lc : IsLeftCanonical CB)
    (hCA_normal : IsNormal CA)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg (MPSTensor e) hdim) CA) CB) :
    ∃ (U : MatrixAlg D) (c : ℂ),
      U = P * U * Q ∧
      Uᴴ * U = Q ∧
      U * Uᴴ = P ∧
      ‖c‖ = 1 ∧
      ∀ i : Fin e, (φP (CA i)).1 =
        c • (U * (φQ (CB i)).1 * Uᴴ) := by
  classical
  subst nB
  simp only [cast_eq] at hMatch
  obtain ⟨X, z, hz, hCB⟩ := hMatch
  let CB' : MPSTensor e nA := fun i => z⁻¹ • CB i
  have hGauge : GaugeEquiv CA CB' := by
    refine ⟨X, fun i => ?_⟩
    simp only [CB', hCB i, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have hCB'_normal : IsNormal CB' :=
    isNormal_of_gaugeEquiv hCA_normal hGauge
  have hCB_eq : CB = fun i => z • CB' i := by
    funext i
    simp [CB', hz]
  have hCB_normal : IsNormal CB := by
    rw [hCB_eq]
    exact isNormal_smul_of_ne CB' z hz hCB'_normal
  have hCA_irr : IsIrreducibleTensor CA :=
    (isNormalTensor_of_isNormal_leftCanonical CA hCA_normal hCA_lc).no_invariant_proj
  have hCB_irr : IsIrreducibleTensor CB :=
    (isNormalTensor_of_isNormal_leftCanonical CB hCB_normal hCB_lc).no_invariant_proj
  obtain ⟨W, c₀, hc₀, hW⟩ :=
    exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible
      (show GaugePhaseEquiv CA CB from ⟨X, z, hz, hCB⟩)
      hCA_lc hCB_lc hCA_irr hCB_irr
  let g : MatrixAlg nA ≃ₗ[ℂ] MatrixAlg nA :=
    Matrix.unitaryReindexLinearEquiv (Equiv.refl (Fin nA)) W W.prop
  let f : cornerSubmodule Q ≃ₗ[ℂ] cornerSubmodule P :=
    φQ.symm.trans (g.trans φP)
  let mulQ (A B : cornerSubmodule Q) : cornerSubmodule Q :=
    ⟨A.1 * B.1, by
      have hQA : Q * A.1 = A.1 := by
        calc
          Q * A.1 = Q * (Q * A.1 * Q) := by rw [A.2]
          _ = (Q * Q) * A.1 * Q := by simp only [Matrix.mul_assoc]
          _ = A.1 := by rw [hQ.2, A.2]
      have hBQ : B.1 * Q = B.1 := by
        calc
          B.1 * Q = (Q * B.1 * Q) * Q := by rw [B.2]
          _ = Q * B.1 * (Q * Q) := by simp only [Matrix.mul_assoc]
          _ = B.1 := by rw [hQ.2, B.2]
      calc
        Q * (A.1 * B.1) * Q = (Q * A.1) * (B.1 * Q) := by
          simp only [Matrix.mul_assoc]
        _ = A.1 * B.1 := by rw [hQA, hBQ]⟩
  have hφQ_symm_mul (A B : cornerSubmodule Q) :
      φQ.symm (mulQ A B) = φQ.symm A * φQ.symm B := by
    apply φQ.injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply, hφQ_mul,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hf_mul (A B : cornerSubmodule Q) :
      (f (mulQ A B)).1 = (f A).1 * (f B).1 := by
    simp only [f, LinearEquiv.trans_apply]
    rw [hφQ_symm_mul, show g (φQ.symm A * φQ.symm B) =
      g (φQ.symm A) * g (φQ.symm B) by
        exact Matrix.unitaryReindexLinearEquiv_mul
          (Equiv.refl (Fin nA)) W W.prop (φQ.symm A) (φQ.symm B)]
    exact hφP_mul _ _
  let starQ (A : cornerSubmodule Q) : cornerSubmodule Q :=
    ⟨A.1ᴴ, by
      change Q * A.1ᴴ * Q = A.1ᴴ
      rw [Matrix.mul_assoc]
      simpa only [Matrix.conjTranspose_mul, hQ.1.eq,
        Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose A.2⟩
  have hφQ_symm_star (A : cornerSubmodule Q) :
      φQ.symm (starQ A) = (φQ.symm A)ᴴ := by
    apply φQ.injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply, hφQ_star, LinearEquiv.apply_symm_apply]
  have hf_star (A : cornerSubmodule Q) :
      (f (starQ A)).1 = (f A).1ᴴ := by
    simp only [f, LinearEquiv.trans_apply]
    rw [hφQ_symm_star, show g ((φQ.symm A)ᴴ) = (g (φQ.symm A))ᴴ by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.unitaryReindexLinearEquiv_star
          (Equiv.refl (Fin nA)) W W.prop (φQ.symm A)]
    exact hφP_star _
  obtain ⟨U, hU_corner, hU_star_U, hU_U_star, hU_transport⟩ :=
    exists_partial_isometry_implementing_corner_linearEquiv P Q hP hQ f
      (by
        intro A B
        simpa only [mulQ] using hf_mul A B)
      (by
        intro A
        simpa only [starQ] using hf_star A)
  have hW_star_W : (W : MatrixAlg nA)ᴴ * (W : MatrixAlg nA) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self W
  have hgCB (i : Fin e) : g (CB i) = c₀ • CA i := by
    simp only [g, hW i, Matrix.unitaryReindexLinearEquiv_apply, Equiv.refl_symm,
      Matrix.reindex_refl_refl, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      hW_star_W, Matrix.mul_one]
    rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc,
      hW_star_W, Matrix.one_mul]
  have htransport (i : Fin e) :
      c₀ • (φP (CA i)).1 = U * (φQ (CB i)).1 * Uᴴ := by
    calc
      c₀ • (φP (CA i)).1 = (φP (c₀ • CA i)).1 := by
        rw [map_smul]
        rfl
      _ = (f (φQ (CB i))).1 := by
        simp only [f, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hgCB]
      _ = U * (φQ (CB i)).1 * Uᴴ := hU_transport (φQ (CB i))
  have hc₀_ne : c₀ ≠ 0 := Complex.ne_zero_of_norm_eq_one hc₀
  refine ⟨U, c₀⁻¹, hU_corner, hU_star_U, hU_U_star, ?_, ?_⟩
  · simp [norm_inv, hc₀]
  · intro i
    rw [← htransport i, smul_smul, inv_mul_cancel₀ hc₀_ne, one_smul]

/-- A cyclic corner product is supported on the right by its final corner.

This is the support identity used in the concatenation in arXiv:1708.00029,
Appendix A, lines 1041--1056. -/
lemma cornerProd_mul_finalCorner
    {m : ℕ} [NeZero m]
    (Q : Fin m → MatrixAlg D) (B : MPSTensor d D)
    (hQ : ∀ v, IsOrthogonalProjection (Q v))
    (hQ_shift : ∀ (v : Fin m) (i : Fin d), Q v * B i = B i * Q (v + 1))
    (v : Fin m) (w : List (Fin d)) :
    cornerProd Q B v w * Q (v + w.length • (1 : Fin m)) =
      cornerProd Q B v w := by
  rw [cornerProd_eq_conj_evalWord Q B hQ hQ_shift]
  simp only [Matrix.mul_assoc, (hQ (v + w.length • (1 : Fin m))).2]

/-- Repeated ambient blocked-sector equations concatenate through the corner
partial isometries.

This is the cancellation of adjacent \(U_v^\dagger U_v=Q_v\) factors in
arXiv:1708.00029, Appendix A, lines 1041--1056. -/
lemma cornerProd_blockMatch_partial_isometry_pow
    {m : ℕ} [NeZero m]
    (P Q : Fin m → MatrixAlg D) (A B : MPSTensor d D)
    (q : Fin m) (U : Fin m → MatrixAlg D) (c : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hQ : ∀ v, IsOrthogonalProjection (Q v))
    (hQ_shift : ∀ (v : Fin m) (i : Fin d), Q v * B i = B i * Q (v + 1))
    (hU_star_U : ∀ u, (U u)ᴴ * U u = Q (u + q))
    (hBC : ∀ (u : Fin m) (w : List (Fin d)), w.length = m →
      cornerProd P A u w =
        c u • (U u * cornerProd Q B (u + q) w * (U u)ᴴ))
    (u : Fin m) (k : ℕ) :
    ∀ W : List (Fin d), W.length = (k + 1) * m →
      cornerProd P A u W =
        (c u) ^ (k + 1) •
          (U u * cornerProd Q B (u + q) W * (U u)ᴴ) := by
  induction k with
  | zero =>
      intro W hW
      rw [zero_add, one_mul] at hW
      simpa using hBC u W hW
  | succ k ih =>
      intro W hW
      set block := W.take m with hblock_def
      set rest := W.drop m with hrest_def
      have hWlen : m ≤ W.length := by rw [hW]; nlinarith [Nat.zero_le k]
      have hblock_len : block.length = m := by
        rw [hblock_def, List.length_take, Nat.min_eq_left hWlen]
      have hrest_len : rest.length = (k + 1) * m := by
        rw [hrest_def, List.length_drop, hW]
        ring_nf
        omega
      have hWeq : W = block ++ rest := (List.take_append_drop m W).symm
      have hshift_block : block.length • (1 : Fin m) = 0 := by
        rw [hblock_len]
        exact nsmul_card_one_fin
      rw [hWeq, cornerProd_append P A hP u block rest,
        hshift_block, add_zero, hBC u block hblock_len, ih rest hrest_len,
        smul_mul_smul_comm, ← pow_succ']
      congr 1
      rw [cornerProd_append Q B hQ (u + q) block rest,
        hshift_block, add_zero]
      have hblock_right :
          cornerProd Q B (u + q) block * Q (u + q) =
            cornerProd Q B (u + q) block := by
        simpa only [hshift_block, add_zero] using
          cornerProd_mul_finalCorner Q B hQ hQ_shift (u + q) block
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U u)ᴴ (U u), hU_star_U,
        ← Matrix.mul_assoc (cornerProd Q B (u + q) block) (Q (u + q)),
        hblock_right]

/-- The first `n` entries encountered by moving cyclically from `u`.

This orders the concatenated factors in arXiv:1708.00029, Appendix A,
lines 1041--1056. -/
def cyclicList {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α) :
    Fin m → ℕ → List α
  | _, 0 => []
  | u, n + 1 => f u :: cyclicList f (u + 1) n

/-- A cyclic list is a list generated by the corresponding finite function.

This is the indexing identity used for the concatenation in arXiv:1708.00029,
Appendix A, lines 1041--1056. -/
private lemma cyclicList_eq_ofFn
    {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α) (u : Fin m) (n : ℕ) :
    cyclicList f u n =
      List.ofFn (fun j : Fin n => f (u + j.1 • (1 : Fin m))) := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
      rw [cyclicList, List.ofFn_succ, ih]
      congr 1
      · simp
      · congr 1
        funext j
        congr 1
        rw [show (j.succ).1 = j.1 + 1 from rfl, add_nsmul, one_nsmul]
        abel

/-- One complete cyclic list starting at zero is the standard finite list. -/
lemma cyclicList_zero_card_eq_ofFn
    {m : ℕ} [NeZero m] {α : Type*} (f : Fin m → α) :
    cyclicList f 0 m = List.ofFn f := by
  rw [cyclicList_eq_ofFn]
  congr 1
  funext j
  congr 1
  rw [zero_add]
  have hnsmul : ∀ (n : ℕ) (hn : n < m),
      n • (1 : Fin m) = ⟨n, hn⟩ := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        rw [succ_nsmul, ih (Nat.lt_of_succ_lt hn)]
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (by omega : 1 < m)]
        exact Nat.mod_eq_of_lt hn
  exact hnsmul j.1 j.2

end MPSTensor
