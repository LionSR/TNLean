/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.PhysicalFilterFamily
import TNLean.MPS.AreaLaw.ViableSet.CutDecomposition
import TNLean.MPS.AreaLaw.ViableSet.ErrorReduction

/-!
# Error reduction by a finite family of physical Gaussian filters

For a positive nearest-neighbour chain, collect the left factors of all the finite
Gaussian approximants over an energy mesh. The collected factors are named before the
input family: applying every one of them to every member of a half-viable input family
`S` gives the family `{A u : A ∈ F, u ∈ S}`, which is viable at precision `c / L`. The
factors are chosen before either the ground energy or the ground vector is supplied, and
the output has explicit cardinality and MPS bond bounds.

The proof uses the actual physical filter construction of Huang,
arXiv:1406.6355v6, Section 5.4, Lemmas 18--19, followed by the deterministic
error-reduction argument of LVV, arXiv:1307.5143v1, `algo53.tex`, Claim
`c:errorreduction`, lines 580--592. It does not assume a supplied approximate
projection, a supplied family of suitable factors, or knowledge of the ground energy.
The polynomial quantitative scope is the conservative one stated in
`docs/paper-gaps/lvv13_runtime_ground_energy.tex`.
-/

open Matrix
open scoped InnerProductSpace Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The left factors of finitely many operators form one bounded finite collection.
LVV13, algo53.tex, decomposition e:decomp and Claim c:errorreduction, lines 584--591. -/
theorem exists_finite_left_filter_factors {L q i M R : ℕ} (hi : i ≤ L)
    (Q : Fin M → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hQ : ∀ j k, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) (Q j)) ≤ R) :
    ∃ F : Finset (LeftBlockMatrix L q i), F.card ≤ M * R ∧
      (∀ A ∈ F, ∀ k, 0 < k → k < i → operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
          (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ R) ∧
      ∀ j, ∃ (N : ℕ) (A : Fin N → LeftBlockMatrix L q i)
        (B : Fin N → RightBlockMatrix L q i),
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) (Q j) =
          ∑ k, A k ⊗ₖ B k ∧ ∀ k, A k ∈ F := by
  classical
  choose N A B hN hdecomp hA using fun j ↦
    exists_cutDecomposition_of_operatorSchmidtRank_le hi (Q j) (hQ j)
  let F := Finset.univ.biUnion fun j : Fin M ↦ Finset.univ.image (A j)
  have hmem (j : Fin M) (k : Fin (N j)) : A j k ∈ F :=
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
  refine ⟨F, ?_, ?_, fun j ↦ ⟨N j, A j, B j, hdecomp j, hmem j⟩⟩
  · calc
      F.card ≤ ∑ j : Fin M, (Finset.univ.image (A j)).card := Finset.card_biUnion_le
      _ ≤ ∑ j : Fin M, N j := Finset.sum_le_sum fun j _ ↦
        (Finset.card_image_le).trans_eq (by simp)
      _ ≤ ∑ _ : Fin M, R := Finset.sum_le_sum fun j _ ↦ hN j
      _ = M * R := by simp
  · intro X hX
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hX
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hj
    exact hA j k

/-- **The left filter factors of the Gaussian error reduction.** A finite family `F` of left
factors, chosen from the chain terms, the gap, the precision and the cut before every ground
pair and before every input family, with at most `M R` members of operator-Schmidt rank at
most `R` at every internal left cut. Applying every member of `F` to every member of a
half-viable input family gives a `c / L`-viable family `{A u : A ∈ F, u ∈ S}`.
Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19, composed with the deterministic
LVV error-reduction step, `algo53.tex`, Claim `c:errorreduction`, lines 580--592. -/
theorem exists_positive_chain_error_reduction_factors {L q i : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) (hL : 1 ≤ L) (hi : i ≤ L) :
    ∃ F : Finset (LeftBlockMatrix L q i),
      F.card ≤ huangEnergyCount c Delta L * huangFilterRankBound q c Delta L ∧
      (∀ A ∈ F, ∀ k, 0 < k → k < i → operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
          (A.submatrix leftConfigOfFin leftConfigOfFin)) ≤ huangFilterRankBound q c Delta L) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)), ‖Γ‖ = 1 →
        (∑ j, h j) *ᵥ WithLp.ofLp Γ = (E₀ : ℂ) • WithLp.ofLp Γ →
        ((∑ j, h j) - (E₀ : ℂ) • 1 - (Delta : ℂ) •
          (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef →
        ∀ S : Finset (LeftBlockVector L q i),
          IsViable Γ (1 / 2) (S : Set (LeftBlockVector L q i)) →
          IsViable Γ (c / L) (errorReductionSet F id S : Set (LeftBlockVector L q i)) := by
  classical
  obtain ⟨Q, hQrank, hgood⟩ :=
    exists_positive_chain_ground_filter_family hq h hs h0 h1 hc hDelta
  obtain ⟨F, hFcard, hFrank, hFdecomp⟩ := exists_finite_left_filter_factors hi Q hQrank
  refine ⟨F, hFcard, hFrank, ?_⟩
  intro E₀ Γ hΓ hHΓ hgap S hviable
  obtain ⟨j, a, ha, -, herror⟩ := hgood E₀ Γ hΓ hHΓ hgap
  obtain ⟨N, A, B, hdecomp, hmem⟩ := hFdecomp j
  have ha0 : 0 < a := by linarith
  have hdecomp' : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) (Q j) =
      ∑ k ∈ (Finset.univ : Finset (Fin N)), A k ⊗ₖ B k := by
    simpa using hdecomp
  have hsmall := huangFilterEta_amplitude_budget hc L ha
  have hout := hviable.errorReduction_of_norm_sub_smul_groundProjection_le
    hΓ hdecomp' ha0 herror hsmall
  have hη := (huangFilterEta_bounds hc L).1
  have hloss : 4 * (4 * huangFilterEta c L) / a ≤ c / L := by
    calc
      _ ≤ 32 * huangFilterEta c L := by
        apply (div_le_iff₀ ha0).mpr
        nlinarith
      _ ≤ c / L := huangFilterEta_length_budget hc hL
  obtain ⟨v, hv1, hvΓ, hvS⟩ := hout
  refine ⟨v, hv1, by linarith, ?_⟩
  have hsubset : (errorReductionSet Finset.univ A S : Set (LeftBlockVector L q i)) ⊆
      errorReductionSet F id S := by
    intro w hw
    obtain ⟨k, -, t, ht, rfl⟩ := Finset.mem_image₂.mp hw
    exact Finset.mem_image₂.mpr ⟨A k, hmem k, t, ht, rfl⟩
  intro z
  exact Submodule.span_mono hsubset (hvS z)

/-- Every member of the error-reduced family `{A j u : j ∈ J, u ∈ S}` is a matrix product
state of bond dimension at most `D * max 1 b` when every factor `A j`, `j ∈ J`, has
operator-Schmidt rank at most `D` at every internal left cut and every member of `S` has
bond bound `b`. LVV13, `algo53.tex`, Claim `c:errorreduction`, line 591. -/
theorem isLeftOpenMPS_of_mem_errorReductionSet {L q i : ℕ} {ι : Type*} (hi : i ≤ L)
    {D b : ℕ} {J : Finset ι} {A : ι → LeftBlockMatrix L q i}
    (hA : ∀ j ∈ J, ∀ k, 0 < k → k < i → operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D)
    {S : Finset (LeftBlockVector L q i)} (hS : ∀ v ∈ S, IsLeftOpenMPS b v)
    {v : LeftBlockVector L q i} (hv : v ∈ errorReductionSet J A S) :
    IsLeftOpenMPS (D * max 1 b) v := by
  classical
  obtain ⟨j, hj, t, ht, rfl⟩ := Finset.mem_image₂.mp hv
  exact IsLeftOpenMPS.toEuclideanLin hi (hS t ht) (A j) (hA j hj)

/-- A finite error-reduced set chosen from the physical chain before every ground pair:
the existence form of `exists_positive_chain_error_reduction_factors`, with the output
`{A u : A ∈ F, u ∈ S}` left unnamed. Huang, arXiv:1406.6355v6, Section 5.4,
Lemmas 18--19, composed with the deterministic LVV error-reduction step. -/
theorem exists_positive_chain_error_reduced_set {L q i s b : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
      (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    {c Delta : ℝ} (hc : 0 < c) (hDelta : 0 < Delta) (hL : 1 ≤ L) (hi : i ≤ L)
    (S : Finset (LeftBlockVector L q i)) (hcard : S.card ≤ s)
    (hSmps : ∀ v ∈ S, IsLeftOpenMPS b v) :
    ∃ T : Finset (LeftBlockVector L q i),
      T.card ≤ huangEnergyCount c Delta L * huangFilterRankBound q c Delta L * s ∧
      (∀ v ∈ T, IsLeftOpenMPS (huangFilterRankBound q c Delta L * max 1 b) v) ∧
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)), ‖Γ‖ = 1 →
        (∑ j, h j) *ᵥ WithLp.ofLp Γ = (E₀ : ℂ) • WithLp.ofLp Γ →
        ((∑ j, h j) - (E₀ : ℂ) • 1 - (Delta : ℂ) •
          (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef →
        IsViable Γ (1 / 2) (S : Set (LeftBlockVector L q i)) →
        IsViable Γ (c / L) (T : Set (LeftBlockVector L q i)) := by
  obtain ⟨F, hFcard, hFrank, hgood⟩ :=
    exists_positive_chain_error_reduction_factors hq h hs h0 h1 hc hDelta hL hi
  exact ⟨errorReductionSet F id S,
    (card_errorReductionSet_le F id S).trans (Nat.mul_le_mul hFcard hcard),
    fun v hv ↦ isLeftOpenMPS_of_mem_errorReductionSet hi hFrank hSmps hv,
    fun E₀ Γ hΓ hHΓ hgap hviable ↦ hgood E₀ Γ hΓ hHΓ hgap S hviable⟩

end TNLean.MPS.AreaLaw
