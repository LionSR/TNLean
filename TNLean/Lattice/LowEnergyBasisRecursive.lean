/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisRefinement
import TNLean.Lattice.LowEnergyBasisSpectralSplit
import TNLean.Lattice.LowEnergyDecayKernel

/-!
# Recursive construction of a uniform low-energy basis

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, chooses successive
spectral splittings to control the off-diagonal parts of local ground-space compressions.
The induction below stops on scalar subspaces and uses complementary orthogonal subspaces
at every nontrivial split. Its constants depend on the ground-space dimension and the
original commutator decay, rather than on inverse gaps of compressed operators.

**Local fix (compression cross terms):** each refinement retains the two products through
the complementary subspace. The resulting graph decay rate is `γ / 2^n`, with the explicit
dimension-dependent coefficient below. The printed quantitative dependence is replaced by
this corrected constant; see `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.
-/

namespace TNLean.Lattice

open scoped InnerProductSpace

/-- A uniform upper bound for the commutator coefficient at depth `t` in a spectral
refinement of total dimension at most `N`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708, with compression cross terms retained. -/
noncomputable def recursiveCommutatorCoeff (N : ℕ) (C : ℝ) (t : ℕ) : ℝ :=
  C * (1 + 2 * (N : ℝ) ^ 3) ^ t

/-- One coefficient dominating all cross-block errors in the recursive basis construction.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable def recursiveBasisCoeff (N : ℕ) (C : ℝ) : ℝ :=
  Real.sqrt ((N : ℝ) ^ 3 * C * (1 + 2 * (N : ℝ) ^ 3) ^ N)

theorem recursiveCommutatorCoeff_nonneg (N t : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ recursiveCommutatorCoeff N C t := by
  unfold recursiveCommutatorCoeff
  positivity

theorem recursiveBasisCoeff_nonneg (N : ℕ) (C : ℝ) : 0 ≤ recursiveBasisCoeff N C :=
  Real.sqrt_nonneg _

/-- The dimension-dependent coefficient bounds the cross-block coefficient at every
allowed depth. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem sqrt_recursiveCommutatorCoeff_le {m N t : ℕ} (hm : m ≤ N) (ht : t ≤ N)
    {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt ((m : ℝ) ^ 3 * recursiveCommutatorCoeff N C t) ≤ recursiveBasisCoeff N C := by
  apply Real.sqrt_le_sqrt
  unfold recursiveCommutatorCoeff
  have hbase : (1 : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 3 :=
    le_add_of_nonneg_right (by positivity)
  have hpow := pow_le_pow_right₀ hbase ht
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hm3 : (m : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmR _
  calc (m : ℝ) ^ 3 * (C * (1 + 2 * (N : ℝ) ^ 3) ^ t)
      = ((m : ℝ) ^ 3 * C) * (1 + 2 * (N : ℝ) ^ 3) ^ t := by ring
    _ ≤ ((N : ℝ) ^ 3 * C) * (1 + 2 * (N : ℝ) ^ 3) ^ N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm3 hC) hpow (by positivity) (by positivity)
    _ = _ := rfl

/-- Retaining both cross terms advances the commutator coefficient by one depth.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem recursiveCommutatorCoeff_step {m N t : ℕ} (hm : m ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    recursiveCommutatorCoeff N C t +
      2 * (Real.sqrt ((m : ℝ) ^ 3 * recursiveCommutatorCoeff N C t)) ^ 2 ≤
        recursiveCommutatorCoeff N C (t + 1) := by
  have hCt := recursiveCommutatorCoeff_nonneg N t hC
  rw [Real.sq_sqrt (mul_nonneg (by positivity) hCt)]
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hm3 : (m : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmR _
  calc _ = (1 + 2 * (m : ℝ) ^ 3) * recursiveCommutatorCoeff N C t := by ring
    _ ≤ (1 + 2 * (N : ℝ) ^ 3) * recursiveCommutatorCoeff N C t := by gcongr
    _ = _ := by simp only [recursiveCommutatorCoeff, pow_succ]; ring

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The finite-rank induction constructing the basis. The total dimension budget bounds
both the recursion depth and the number of selected original terms. Scalar terminal
subspaces need not have dimension one. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_uniform_kernel_aux {κ : Type*} [Finite κ]
    (k : κ → κ → ℝ) (hk0 : ∀ i j, 0 ≤ k i j) (hk1 : ∀ i j, k i j ≤ 1)
    (hksymm : ∀ i j, k i j = k j i) (hktri : ∀ i j l, k i j * k j l ≤ k i l)
    (N : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ (m : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E], Module.finrank ℂ E = m →
      ∀ t : ℕ, t + m ≤ N → ∀ B : κ → E →L[ℂ] E,
        (∀ i, IsSelfAdjoint (B i)) →
        (∀ i j, ‖B i * B j - B j * B i‖ ≤ recursiveCommutatorCoeff N C t * sqrtKernel k t i j) →
        ∃ (b : OrthonormalBasis (Fin m) ℂ E) (s : List κ), s.length ≤ m - 1 ∧
          ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤
            recursiveBasisCoeff N C * listKernelSum (sqrtKernel k N) s i := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ _ hdim t ht B hB hcomm
    by_cases hm : m ≤ 1
    · let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hdim)
      refine ⟨b, [], by simp, fun i a c hac => ?_⟩
      exact False.elim (hac (Fin.ext (by omega)))
    have hmN : m ≤ N := by omega
    have htN : t ≤ N := by omega
    have hdim' : Module.finrank ℂ E = (m - 1) + 1 := by omega
    have hm' : (m - 1) + 1 = m := by omega
    let Ct := recursiveCommutatorCoeff N C t
    let D := Real.sqrt ((m : ℝ) ^ 3 * Ct)
    have hCt : 0 ≤ Ct := recursiveCommutatorCoeff_nonneg N t hC
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDmax : D ≤ recursiveBasisCoeff N C := sqrt_recursiveCommutatorCoeff_le hmN htN hC
    have hstep : Ct + 2 * D ^ 2 ≤ recursiveCommutatorCoeff N C (t + 1) :=
      recursiveCommutatorCoeff_step hmN hC
    let f := sqrtKernel k t
    have hf0 := sqrtKernel_nonneg hk0 t
    have hf1 := sqrtKernel_le_one hk1 t
    have hfsymm := sqrtKernel_symm hksymm t
    have hftri := sqrtKernel_mul_le hk0 hktri t
    rcases exists_family_spectral_split B hB (by omega : 0 < m - 1) hdim' hCt f hf0
      hfsymm hcomm with hscalar | ⟨P, j, hP, hPn, hQn, hP0, hP1, hcross⟩
    · let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hdim)
      refine ⟨b, [], by simp, fun i a c hac => ?_⟩
      obtain ⟨r, hr⟩ := hscalar i
      simp only [hr, smul_apply, one_apply_eq_self, inner_smul_right,
        b.inner_eq_zero hac, mul_zero, norm_zero, listKernelSum_nil]
      exact le_rfl
    · obtain ⟨K, _, hPK⟩ := isStarProjection_iff_eq_starProjection.mp hP
      subst P
      let : InnerProductSpace ℂ K := K.innerProductSpace
      let : InnerProductSpace ℂ Kᗮ := Kᗮ.innerProductSpace
      let : CompleteSpace K := FiniteDimensional.complete ℂ K
      let : CompleteSpace Kᗮ := FiniteDimensional.complete ℂ Kᗮ
      have hK0 : K ≠ ⊥ := by
        intro h
        exact hP0 (by simp [h])
      have hK1 : K ≠ ⊤ := by
        intro h
        apply hP1
        ext x
        exact K.starProjection_eq_self_iff.mpr (by rw [h]; trivial)
      let p := Module.finrank ℂ K
      let q := Module.finrank ℂ Kᗮ
      have hp : 0 < p := by
        let : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK0
        exact Module.finrank_pos
      have hq : 0 < q := by
        have hq0 : Kᗮ ≠ ⊥ := fun h => hK1 (K.orthogonal_eq_bot_iff.mp h)
        let : Nontrivial Kᗮ := Submodule.nontrivial_iff_ne_bot.mpr hq0
        exact Module.finrank_pos
      have hpq : p + q = m := K.finrank_add_finrank_orthogonal.trans hdim
      have hpp : p < m := by omega
      have hqq : q < m := by omega
      have hc0 (i : κ) : ‖K.starProjection * B i * (1 - K.starProjection)‖ ≤
          D * Real.sqrt (f i j) := by simpa only [hm'] using (hcross i).1
      have hc1 (i : κ) : ‖(1 - K.starProjection) * B i * K.starProjection‖ ≤
          D * Real.sqrt (f i j) := by simpa only [hm'] using (hcross i).2
      have hPP : K.starProjection * K.starProjection = K.starProjection :=
        hP.isIdempotentElem.eq
      have hQQ : (1 - K.starProjection) * (1 - K.starProjection) = 1 - K.starProjection := by
        noncomm_ring [hPP]
      have hcommL (i l : κ) :
          ‖subspaceCompression K (B i) * subspaceCompression K (B l) -
            subspaceCompression K (B l) * subspaceCompression K (B i)‖ ≤
            recursiveCommutatorCoeff N C (t + 1) * sqrtKernel k (t + 1) i l := by
        rw [norm_subspaceCompression_commutator]
        exact (norm_commutator_compression_le_kernel K.starProjection hPP hPn B hCt hD
          f hf0 hf1 hfsymm hftri j hcomm hc0 hc1 i l).trans
            (mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _))
      have hcommR (i l : κ) :
          ‖subspaceCompression Kᗮ (B i) * subspaceCompression Kᗮ (B l) -
            subspaceCompression Kᗮ (B l) * subspaceCompression Kᗮ (B i)‖ ≤
            recursiveCommutatorCoeff N C (t + 1) * sqrtKernel k (t + 1) i l := by
        rw [norm_subspaceCompression_commutator, K.starProjection_orthogonal']
        have hcQ0 (i : κ) : ‖(1 - K.starProjection) * B i * (1 - (1 - K.starProjection))‖ ≤
            D * Real.sqrt (f i j) := by simpa only [sub_sub_cancel] using hc1 i
        have hcQ1 (i : κ) : ‖(1 - (1 - K.starProjection)) * B i * (1 - K.starProjection)‖ ≤
            D * Real.sqrt (f i j) := by simpa only [sub_sub_cancel] using hc0 i
        exact (norm_commutator_compression_le_kernel (1 - K.starProjection) hQQ hQn B hCt hD
          f hf0 hf1 hfsymm hftri j hcomm hcQ0 hcQ1 i l).trans
            (mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _))
      obtain ⟨u, sL, hsL, hu⟩ := ih p hpp K rfl (t + 1) (by omega)
        (fun i => subspaceCompression K (B i))
        (fun i => isSelfAdjoint_subspaceCompression K (B i) (hB i)) hcommL
      obtain ⟨v, sR, hsR, hv⟩ := ih q hqq Kᗮ rfl (t + 1) (by omega)
        (fun i => subspaceCompression Kᗮ (B i))
        (fun i => isSelfAdjoint_subspaceCompression Kᗮ (B i) (hB i)) hcommR
      obtain ⟨b, hl, hr⟩ := exists_orthonormalBasis_orthogonal_sum K u v
      let e : Fin p ⊕ Fin q ≃ Fin m := Fintype.equivFinOfCardEq (by
        simpa only [Fintype.card_sum, Fintype.card_fin] using hpq)
      refine ⟨b.reindex e, j :: (sL ++ sR), ?_, fun i a c hac => ?_⟩
      · simp only [List.length_cons, List.length_append]
        omega
      · have hnew : ‖K.starProjection * B i * Kᗮ.starProjection‖ ≤
            recursiveBasisCoeff N C * sqrtKernel k N i j := by
          rw [K.starProjection_orthogonal']
          exact (hc0 i).trans (mul_le_mul hDmax
            (sqrtKernel_mono hk0 hk1 i j (by omega : t + 1 ≤ N))
            (Real.sqrt_nonneg _) (recursiveBasisCoeff_nonneg N C))
        have h := norm_inner_le_of_orthogonal_sum K u v b hl hr (B i) (hB i).isSymmetric
          (mul_nonneg (recursiveBasisCoeff_nonneg N C)
            (listKernelSum_nonneg (sqrtKernel_nonneg hk0 N) sL i))
          (mul_nonneg (recursiveBasisCoeff_nonneg N C)
            (listKernelSum_nonneg (sqrtKernel_nonneg hk0 N) sR i))
          (mul_nonneg (recursiveBasisCoeff_nonneg N C) (sqrtKernel_nonneg hk0 N i j))
          (hu i) (hv i) hnew (fun heq => hac (e.symm.injective heq))
        simpa only [OrthonormalBasis.reindex_apply, listKernelSum_cons, listKernelSum_append,
          mul_add, add_comm, add_left_comm, add_assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- A finite Hermitian family admits an actual orthonormal basis with uniform
matrix-element decay from at most `n-1` original anchors. No spectral denominators or
supplied separation assumptions occur. The conclusion retains the cross terms through
successive square roots of the decay kernel. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_uniform_kernel {κ E : Type*} [Finite κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (B : κ → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i)) (k : κ → κ → ℝ)
    (hk0 : ∀ i j, 0 ≤ k i j) (hk1 : ∀ i j, k i j ≤ 1)
    (hksymm : ∀ i j, k i j = k j i) (hktri : ∀ i j l, k i j * k j l ≤ k i l)
    {C : ℝ} (hC : 0 ≤ C) (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * k i j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (s : List κ),
      s.length ≤ Module.finrank ℂ E - 1 ∧
      ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤ recursiveBasisCoeff (Module.finrank ℂ E) C *
        listKernelSum (sqrtKernel k (Module.finrank ℂ E)) s i := by
  exact exists_orthonormalBasis_uniform_kernel_aux k hk0 hk1 hksymm hktri
    (Module.finrank ℂ E) hC (Module.finrank ℂ E) E rfl 0 (by omega) B hB
    (by simpa only [recursiveCommutatorCoeff, pow_zero, mul_one, sqrtKernel_zero] using hcomm)

end TNLean.Lattice
