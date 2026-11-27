/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixAlgebra.SkolemNoetherUnitary
import QICLean.Channel.Positive.PositiveConditionalExpectationDirectSum
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalityChain
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.Tensor.Words.OneSidedInverse
import TNLean.MPS.Tensor.Words.ScaledNormality
import TNLean.MPS.Transfer.Irreducible.UnitaryGauge
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.PeriodicSectorDecomposition
import TNLean.MPS.CanonicalForm.Periodic.Overlap.SectorContraction
import QICLean.Algebra.Kronecker.PiTensorProductPhase

/-!
# Periodic sector-match contraction foundations

This module collects the common blocking inverses, ambient corner gauges, and
cyclic-list identities used in the full-cycle contraction.

It also contains the following results.

* `MPSTensor.piTensorProduct_eq_smul_of_corner_cyclic_products`: cyclic trace separation for
  periodic sector matches.
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder InnerProductSpace TensorProduct
open Filter Matrix Module

namespace MPSTensor

section SectorMatch

variable {α : Type*} [Fintype α] {D : ℕ}

/-- Common `Ω_u` right inverses for the sector blocks.

This is the Lean form of the normality input in arXiv:1708.00029, Appendix A,
lines 1026--1040, equations `eq:Fu` and `eq:Omegauprop`: after choosing one
common positive word length, every sector block has a right inverse for the
linear span of its length-`L` word products. -/
lemma exists_common_sectorDecompositionMaps_of_isNormal_leftCanonical
    {m : ℕ} {dim : Fin m → ℕ}
    (blocks : (k : Fin m) → MPTensor α (Fin (dim k)))
    (hBlocks_lc :
      ∀ k, ∑ i : α, (blocks k i)ᴴ * blocks k i = 1)
    (hNondeg : ∀ k, dim k ≠ 0)
    (hNormal : ∀ k, Kraus.IsNormal (blocks k)) :
    ∃ L : ℕ, 0 < L ∧
      ∃ Ω : (k : Fin m) →
          Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ] ((Fin L → α) → ℂ),
        ∀ (k : Fin m) (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
          ∑ σ : Fin L → α,
            (Ω k X σ) • Kraus.evalWord (blocks k) (List.ofFn σ) = X := by
  obtain ⟨L, hL_pos, hL⟩ :=
    exists_common_isNBlkInjective_of_isNormal_leftCanonical
      blocks hBlocks_lc hNondeg hNormal
  refine ⟨L, hL_pos, fun k => Kraus.blockDecompositionMap (hL k), ?_⟩
  intro k X
  exact Kraus.blockDecompositionMap_sum (hL k) X

/-- A matched pair of compressed sectors has an ambient corner implementation.

This is equation `eq:blockedABprop` in ambient form, hence the input to
`eq:BCmprop`, in arXiv:1708.00029, Appendix A, lines 985--1024. -/
lemma exists_ambient_corner_gauge_of_gaugePhase
    {β : Type*} [Fintype β] {nA nB : ℕ} [NeZero nA]
    (CA : MPTensor β (Fin nA)) (CB : MPTensor β (Fin nB))
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
    (hCA_normal : Kraus.IsNormal CA)
    (hMatch : GaugePhaseEquiv
      (cast (congr_arg (fun n ↦ MPTensor β (Fin n)) hdim) CA) CB) :
    ∃ (U : MatrixAlg D) (c : ℂ),
      U = P * U * Q ∧
      Uᴴ * U = Q ∧
      U * Uᴴ = P ∧
      ‖c‖ = 1 ∧
      ∀ i : β, (φP (CA i)).1 =
        c • (U * (φQ (CB i)).1 * Uᴴ) := by
  classical
  subst nB
  simp only [cast_eq] at hMatch
  obtain ⟨X, z, hz, hCB⟩ := hMatch
  let CB' : MPTensor β (Fin nA) := fun i => z⁻¹ • CB i
  have hGauge : GaugeEquiv CA CB' := by
    refine ⟨X, fun i => ?_⟩
    simp only [CB', hCB i, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have hCB'_normal : Kraus.IsNormal CB' :=
    isNormal_of_gaugeEquiv hCA_normal hGauge
  have hCB_eq : CB = fun i => z • CB' i := by
    funext i
    simp [CB', hz]
  have hCB_normal : Kraus.IsNormal CB := by
    rw [hCB_eq]
    exact (isNormal_smul_iff hz CB').2 hCB'_normal
  have hCA_irr : Kraus.IsIrreducibleFamily CA :=
    (isNormalTensor_of_isNormal_leftCanonical CA hCA_normal hCA_lc).no_invariant_proj
  have hCB_irr : Kraus.IsIrreducibleFamily CB :=
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
  have hgCB (i : β) : g (CB i) = c₀ • CA i := by
    simp only [g, hW i, Matrix.unitaryReindexLinearEquiv_apply, Equiv.refl_symm,
      Matrix.reindex_refl_refl, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      hW_star_W, Matrix.mul_one]
    rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc,
      hW_star_W, Matrix.one_mul]
  have htransport (i : β) :
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
    (Q : Fin m → MatrixAlg D) (B : MPTensor α (Fin D))
    (hQ : ∀ v, IsOrthogonalProjection (Q v))
    (hQ_shift : ∀ (v : Fin m) (i : α), Q v * B i = B i * Q (v + 1))
    (v : Fin m) (w : List α) :
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
    (P Q : Fin m → MatrixAlg D) (A B : MPTensor α (Fin D))
    (q : Fin m) (U : Fin m → MatrixAlg D) (c : Fin m → ℂ)
    (hP : ∀ u, IsOrthogonalProjection (P u))
    (hQ : ∀ v, IsOrthogonalProjection (Q v))
    (hQ_shift : ∀ (v : Fin m) (i : α), Q v * B i = B i * Q (v + 1))
    (hU_star_U : ∀ u, (U u)ᴴ * U u = Q (u + q))
    (hBC : ∀ (u : Fin m) (w : List α), w.length = m →
      cornerProd P A u w =
        c u • (U u * cornerProd Q B (u + q) w * (U u)ᴴ))
    (u : Fin m) (k : ℕ) :
    ∀ W : List α, W.length = (k + 1) * m →
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

end SectorMatch

section SectorMatchCyclicTrace

/-!
## Cyclic trace separation for periodic sector matches

This module separates full-cycle corner products by matrix units and tensor
trace pairings.
-/

variable {α : Type*} [Fintype α] {D : ℕ}

/-- Matrix units separate a cyclic product into its individual matrix
coefficients.

This is the coordinate form of applying the tensor of the inverses in
arXiv:1708.00029, Appendix A, lines 1048--1067. -/
private lemma cyclic_matrix_single_chain_apply
    {m : ℕ} [NeZero m] {D : ℕ}
    (M : Fin m → MatrixAlg D) (p : Fin m → Fin D × Fin D)
    (u : Fin m) (n : ℕ) (r s : Fin D) :
    ((cyclicList
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))
        u (n + 1)).prod : MatrixAlg D) r s =
      if s = (p (u + (n + 1) • (1 : Fin m))).1 then
        M u r (p u).2 *
          (cyclicList (fun k => M k (p k).1 (p k).2) (u + 1) n).prod
      else 0 := by
  induction n generalizing u r with
  | zero =>
    simp only [cyclicList, List.prod_cons, List.prod_nil, mul_one]
    norm_num
    by_cases hs : s = (p (u + 1)).1
    · subst s
      simp
    · rw [ite_eq_right hs,
        Matrix.mul_single_apply_of_ne (1 : ℂ) (p u).2 (p (u + 1)).1 r
          s hs]
  | succ n ih =>
    simp only [cyclicList, List.prod_cons]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    rw [Finset.sum_eq_single (p u).2]
    · simp only [Matrix.single_mul_apply_same, one_mul]
      change M u r (p u).2 *
          ((cyclicList
            (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))
            (u + 1) (n + 1)).prod : MatrixAlg D) (p (u + 1)).1 s = _
      rw [ih]
      have hindex :
          u + 1 + (n + 1) • (1 : Fin m) =
            u + (n + 1 + 1) • (1 : Fin m) := by
        have hsmul :
            (1 + (n + 1)) • (1 : Fin m) =
              1 + (n + 1) • (1 : Fin m) := by
          calc
            (1 + (n + 1)) • (1 : Fin m) =
                1 • (1 : Fin m) + (n + 1) • (1 : Fin m) :=
              add_nsmul (1 : Fin m) 1 (n + 1)
            _ = 1 + (n + 1) • (1 : Fin m) := by rw [one_nsmul]
        rw [show n + 1 + 1 = 1 + (n + 1) by omega, hsmul, add_assoc]
      rw [hindex]
      split_ifs with hs
      · rfl
      · rw [mul_zero]
    · intro a _ ha
      rw [Matrix.single_mul_apply_of_ne (1 : ℂ) (p u).2
        (p (u + 1)).1 a s ha]
      rw [mul_zero]
    · simp

/-- A projection supporting the first factor supports a nonempty cyclic
product on the left. -/
private lemma cyclic_prod_left
    {m : ℕ} [NeZero m]
    (P R : Fin m → MatrixAlg D)
    (hR_left : ∀ k, P k * R k = R k)
    (u : Fin m) (n : ℕ) :
    P u * (cyclicList R u (n + 1)).prod =
      (cyclicList R u (n + 1)).prod := by
  simp only [cyclicList, List.prod_cons, ← Matrix.mul_assoc, hR_left]

/-- Inserting the next-sector projection after every factor leaves only the
final projection at the end of a cyclic product. -/
private lemma cyclic_prod_insert_right_projection
    {m : ℕ} [NeZero m]
    (P R : Fin m → MatrixAlg D)
    (hR_left : ∀ k, P k * R k = R k)
    (u : Fin m) (n : ℕ) :
    (cyclicList (fun k => R k * P (k + 1)) u (n + 1)).prod =
      (cyclicList R u (n + 1)).prod *
        P (u + (n + 1) • (1 : Fin m)) := by
  induction n generalizing u with
  | zero => simp [cyclicList]
  | succ n ih =>
    change
      (R u * P (u + 1)) *
          (cyclicList (fun k => R k * P (k + 1)) (u + 1) (n + 1)).prod =
        R u * (cyclicList R (u + 1) (n + 1)).prod *
          P (u + (n + 1 + 1) • (1 : Fin m))
    rw [ih (u + 1)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P (u + 1)) (cyclicList R (u + 1) (n + 1)).prod,
      cyclic_prod_left P R hR_left (u + 1) n]
    congr 2
    have hindex :
        u + (n + 1 + 1) • (1 : Fin m) =
          u + 1 + (n + 1) • (1 : Fin m) := by
      rw [add_nsmul, one_nsmul]
      abel
    rw [hindex]

/-- Compressing every inserted matrix to the intervening corner does not
change the cyclic trace pairing.

This is the open-index interpretation of the corner inverse in
arXiv:1708.00029, Appendix A, lines 1048--1067. -/
private lemma trace_prod_corner_compression
    {m : ℕ} [NeZero m]
    (P M X : Fin m → MatrixAlg D)
    (hM_left : ∀ k, P k * M k = M k)
    (hM_right : ∀ k, M k * P (k + 1) = M k) :
    Matrix.trace
        (List.ofFn (fun k => M k * (P (k + 1) * X k * P (k + 1)))).prod =
      Matrix.trace (List.ofFn (fun k => M k * X k)).prod := by
  let R : Fin m → MatrixAlg D := fun k => M k * X k
  have hR_left : ∀ k, P k * R k = R k := by
    intro k
    simp only [R, ← Matrix.mul_assoc, hM_left]
  have hterm : ∀ k, M k * (P (k + 1) * X k * P (k + 1)) =
      R k * P (k + 1) := by
    intro k
    change M k * (P (k + 1) * X k * P (k + 1)) =
      (M k * X k) * P (k + 1)
    rw [Matrix.mul_assoc (P (k + 1))]
    rw [← Matrix.mul_assoc, hM_right]
    rw [Matrix.mul_assoc]
  have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
  have hprod :=
    cyclic_prod_insert_right_projection P R hR_left 0 m.pred
  rw [hm, nsmul_card_one_fin, zero_add] at hprod
  rw [cyclicList_zero_card_eq_ofFn, cyclicList_zero_card_eq_ofFn] at hprod
  have hcompressed :
      (List.ofFn (fun k => M k * (P (k + 1) * X k * P (k + 1)))).prod =
        (List.ofFn R).prod * P 0 := by
    calc
      (List.ofFn (fun k => M k * (P (k + 1) * X k * P (k + 1)))).prod =
          (List.ofFn (fun k => R k * P (k + 1))).prod := by
            apply congrArg List.prod
            apply List.ofFn_inj.mpr
            funext k
            exact hterm k
      _ = (List.ofFn R).prod * P 0 := hprod
  rw [hcompressed, Matrix.trace_mul_comm]
  rw [← cyclicList_zero_card_eq_ofFn]
  have hleft := cyclic_prod_left P R hR_left 0 m.pred
  rw [hm] at hleft
  simpa only [cyclicList_zero_card_eq_ofFn, R] using congrArg Matrix.trace hleft

/-- The cyclic trace against linked matrix units is the product of the selected
matrix coefficients. -/
private lemma trace_cyclic_matrix_single_chain
    {m : ℕ} [NeZero m] {D : ℕ}
    (M : Fin m → MatrixAlg D) (p : Fin m → Fin D × Fin D) :
    Matrix.trace
        (List.ofFn
          (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod =
      ∏ k, M k (p k).1 (p k).2 := by
  let f : Fin m → ℂ := fun k => M k (p k).1 (p k).2
  have hm : m.pred + 1 = m := Nat.succ_pred_eq_of_pos (NeZero.pos m)
  have hdiag : ∀ r : Fin D,
      (List.ofFn
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod r r =
        if r = (p 0).1 then ∏ k, f k else 0 := by
    intro r
    have hchain :=
      cyclic_matrix_single_chain_apply M p 0 m.pred r r
    rw [hm, nsmul_card_one_fin, zero_add] at hchain
    rw [cyclicList_zero_card_eq_ofFn] at hchain
    by_cases hr : r = (p 0).1
    · subst r
      rw [ite_eq_left rfl] at hchain ⊢
      rw [hchain]
      calc
        M 0 (p 0).1 (p 0).2 *
            (cyclicList f (0 + 1) m.pred).prod =
            (cyclicList f 0 m).prod := by
              have hcycle :
                  cyclicList f 0 m =
                    f 0 :: cyclicList f (0 + 1) m.pred := by
                calc
                  cyclicList f 0 m = cyclicList f 0 (m.pred + 1) :=
                    congrArg _ hm.symm
                  _ = _ := rfl
              rw [hcycle, List.prod_cons]
        _ = (List.ofFn f).prod := by rw [cyclicList_zero_card_eq_ofFn]
        _ = ∏ k, f k := List.prod_ofFn
    · rw [ite_eq_right hr] at hchain ⊢
      exact hchain
  rw [Matrix.trace, Finset.sum_eq_single (p 0).1]
  · change
      (List.ofFn
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod
          (p 0).1 (p 0).1 = _
    rw [hdiag, ite_eq_left rfl]
  · intro r _ hr
    change
      (List.ofFn
        (fun k => M k * Matrix.single (p k).2 (p (k + 1)).1 (1 : ℂ))).prod
          r r = 0
    rw [hdiag, ite_eq_right hr]
  · simp

/-- A cyclic product identity tested on all matrices in the intervening
corners determines the corresponding product-tensor identity.

This is `eq:resultprop` in arXiv:1708.00029, Appendix A, lines 1063--1067,
with the open virtual indices read through the corner trace pairing. -/
lemma piTensorProduct_eq_smul_of_corner_cyclic_products
    {m : ℕ} [NeZero m] {D : ℕ}
    (P : Fin m → MatrixAlg D)
    (A B : Fin m → MatrixAlg D) (z : ℂ)
    (hP : ∀ k, IsOrthogonalProjection (P k))
    (hA_left : ∀ k, P k * A k = A k)
    (hA_right : ∀ k, A k * P (k + 1) = A k)
    (hB_left : ∀ k, P k * B k = B k)
    (hB_right : ∀ k, B k * P (k + 1) = B k)
    (h : ∀ X : Fin m → MatrixAlg D,
      (∀ k, P (k + 1) * X k * P (k + 1) = X k) →
      (List.ofFn (fun k => A k * X k)).prod =
        z • (List.ofFn (fun k => B k * X k)).prod) :
    (⨂ₜ[ℂ] k : Fin m, A k) = z • (⨂ₜ[ℂ] k : Fin m, B k) := by
  classical
  let b : (k : Fin m) → Basis (Fin D × Fin D) ℂ (MatrixAlg D) :=
    fun _ => Matrix.stdBasis ℂ (Fin D) (Fin D)
  apply (Basis.piTensorProduct b).repr.injective
  ext p
  simp only [Basis.piTensorProduct_repr_tprod_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  let X : Fin m → MatrixAlg D :=
    fun k => Matrix.single (p k).2 (p (k + 1)).1 1
  let Xc : Fin m → MatrixAlg D :=
    fun k => P (k + 1) * X k * P (k + 1)
  have hXc : ∀ k, P (k + 1) * Xc k * P (k + 1) = Xc k := by
    intro k
    simp only [Xc, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, (hP (k + 1)).2]
  have htrace := congrArg Matrix.trace (h Xc hXc)
  have htrace' :
      Matrix.trace (List.ofFn (fun k => A k * Xc k)).prod =
        z * Matrix.trace (List.ofFn (fun k => B k * Xc k)).prod := by
    rw [Matrix.trace_smul] at htrace
    simpa only [smul_eq_mul] using htrace
  rw [trace_prod_corner_compression P A X hA_left hA_right,
    trace_prod_corner_compression P B X hB_left hB_right,
    trace_cyclic_matrix_single_chain A p,
    trace_cyclic_matrix_single_chain B p] at htrace'
  simpa [b, Matrix.stdBasis] using htrace'

end SectorMatchCyclicTrace

end MPSTensor
