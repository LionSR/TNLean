/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ConstantRankCut
import TNLean.MPS.AreaLaw.ViableSet.Gluing
import QICLean.Channel.TrimmedWitness

/-!
# The trimmed witness at a cut of the chain

Fix the cut after `k` sites. Let `H = H_L + H_R + K` with `H_L` supported on the first `k`
sites, `H_R` on the others and `0 ≤ K ≤ 1`, and `H ≥ E₀`. Let `ψ` be a unit vector of energy at
most `E₀ + δ` whose left factor lies in the range of a matrix `P_V` on the first `k` sites,
`P_V C = C` for its cut matrix `C`, and let some unit vector of rank at most `D` across the cut
overlap `ψ` by at least `1 - η`, with `2η < 1`. Trimming `ψ` across the cut to its `D` largest
Schmidt terms and normalizing gives a unit vector `w` of rank at most `D` across the cut, with
energy at most `E₀ + (δ + 2√(2η))/(1 - 2η)` and left factor still in the range of `P_V`.
Moreover `w = (1 ⊗ W) x` in the cut coordinates of `TNLean.MPS.AreaLaw.gluingCut` for an
isometry `W` from a bond `ℂ^m`, `m ≤ D`, into the sites right of the cut, and a left state `x`
whose left factor is again in the range of `P_V`. This is the input of Lemma `l:leading` on the
chain (`TNLean.MPS.AreaLaw.exists_leading_eigenvector_chain`).

This is Lemma `l:within` of Landau, Vazirani and Vidick on the chain. With `P_V` the projection
onto the span of a viable set `S`, the condition `P_V C = C` says that the left Schmidt vectors
of `ψ` lie in `Span(S)`.

**Local fix (energy after trimming):** the energy bound is the corrected one,
`E₀ + (δ + 2√(2η))/(1 - 2η)`; the printed `ε₀ + 6√c_ε` is not established by the printed
argument. Documented in the QICLean note
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_energy.pdf>.

## Main results

* `TNLean.MPS.AreaLaw.exists_trimmed_witness_chain`: Lemma `l:within` on the chain.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: Lemma
  `l:within`, lines 509–515.
-/

open Matrix
open scoped Matrix Kronecker ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- **Lemma `l:within` on the chain** (arXiv:1307.5143v1, `algo53.tex`, lines 509–515), with
the corrected energy bound. Let `H = H_L + H_R + K` with `H_L` supported on the first `k`
sites, `H_R` on the others, `0 ≤ K ≤ 1` and `H ≥ E₀`. Let `ψ` be a unit vector with
`Re ⟨ψ, H ψ⟩ ≤ E₀ + δ` and `P_V C = C` for its cut matrix `C`, and let a unit vector `u` of rank
at most `D` across the cut satisfy `|⟨u, ψ⟩| ≥ 1 - η` with `2η < 1`. Then there are a unit
vector `w` of rank at most `D` across the cut, with
`Re ⟨w, H w⟩ ≤ E₀ + (δ + 2√(2η))/(1 - 2η)` and `P_V C_w = C_w`, an isometry `W` from `ℂ^m`,
`m ≤ D`, into the sites right of the cut, and `x` with `w = (1 ⊗ W) x` in the coordinates of
`gluingCut L q k`, whose left factor is in the range of `P_V`. -/
theorem exists_trimmed_witness_chain {k : ℕ}
    {H HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hsplit : H = HL + HR + K)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hHR : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HR (leftBlock L k)ᶜ)
    (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef) {E₀ δ : ℝ}
    (hH0 : (H - (E₀ : ℂ) • 1).PosSemidef) {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : ‖ψ‖ = 1) (hE : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re ≤ E₀ + δ) {D : ℕ}
    {u : EuclideanSpace ℂ (Fin L → Fin q)} (hu : ‖u‖ = 1) (huD : (cutMatrix u k).rank ≤ D)
    {η : ℝ} (hη : 1 - η ≤ ‖⟪u, ψ⟫_ℂ‖) (hη2 : 2 * η < 1) {PV : LeftBlockMatrix L q k}
    (hPV : PV * cutMatrix ψ k = cutMatrix ψ k) :
    ∃ (w : EuclideanSpace ℂ (Fin L → Fin q)) (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
      (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ),
      ‖w‖ = 1 ∧ (cutMatrix w k).rank ≤ D ∧
      (⟪w, toEuclideanLin H w⟫_ℂ).re ≤ E₀ + (δ + 2 * √(2 * η)) / (1 - 2 * η) ∧
      PV * cutMatrix w k = cutMatrix w k ∧ Wᴴ * W = 1 ∧ m ≤ D ∧
      WithLp.ofLp w ∘ (gluingCut L q k).symm =
        ((1 : Matrix (CutLeft L q k × CutSite L q k) (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ
          x ∧
      (reindex (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
          (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1))) PV ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x := by
  classical
  rcases isEmpty_or_nonempty (Fin L → Fin q) with hσ | ⟨⟨σ⟩⟩
  · exfalso
    have h0 : ψ = 0 := Subsingleton.elim _ _
    simp [h0] at hψ
  set e := Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)
  set ψc := Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ
  set uc := Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) u
  -- The Hamiltonian in the cut coordinates.
  have hL := hHL.cutOperator_eq_kronecker_one (B := leftBlock L k) subset_rfl (e σ).2
  have hR := hHR.cutOperator_eq_one_kronecker (B := leftBlock L k) disjoint_compl_left (e σ).1
  obtain ⟨A, A', hHc⟩ : ∃ (A : LeftBlockMatrix L q k)
      (A' : Matrix (CutRight L q k) (CutRight L q k) ℂ),
      Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) H =
        A ⊗ₖ (1 : Matrix (CutRight L q k) (CutRight L q k) ℂ) +
          (1 : LeftBlockMatrix L q k) ⊗ₖ A' +
          Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K :=
    ⟨fun x x' ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) HL
        (x, (e σ).2) (x', (e σ).2),
      fun y y' ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) HR
        ((e σ).1, y) ((e σ).1, y'),
      by rw [hsplit, cutOperator_add, cutOperator_add, ← hL, ← hR]⟩
  have hK1c : (1 - Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K).PosSemidef := by
    have : (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
        (1 - K)).PosSemidef := hK1.submatrix _
    have h1 : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) (1 - K) =
        1 - Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K := by
      ext a b
      simp [one_apply]
    rwa [h1] at this
  have hHc0 : (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) H -
      (E₀ : ℂ) • 1).PosSemidef := by
    rw [← cutOperator_sub_smul_one]
    exact hH0.submatrix _
  have hEc := hE
  rw [← Entropy.inner_cutOperator (leftBlock L k)] at hEc
  have hψc : ‖ψc‖ = 1 := by rw [Entropy.norm_cutVector, hψ]
  have huc : ‖uc‖ = 1 := by rw [Entropy.norm_cutVector, hu]
  have hucD : HasSchmidtRankLE D (WithLp.ofLp uc) := huD
  have hη' : 1 - η ≤ ‖⟪uc, ψc⟫_ℂ‖ := by rw [inner_cutVector]; exact hη
  have hPVc : leftApply PV ψc = ψc := by
    change toEuclid (PV * cutMatrix ψ k) = toEuclid (cutMatrix ψ k)
    rw [hPV]
  obtain ⟨wc, m, W, xc, hwc1, hwcD, hwcE, hwcPV, hW, hmD, hwx, hxPV⟩ :=
    IsTrimmingProjection.exists_trimmed_witness hHc hHc0 (hK0.submatrix _) hK1c hψc hEc huc
      hucD hη' hη2 hPVc
  -- Back to the chain.
  set w : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2 (WithLp.ofLp wc ∘ e)
  have hwcw : Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) w = wc := by
    ext x
    simp [w, e]
  have hcm : cutMatrix w k = schmidtCoeffMatrix (WithLp.ofLp wc) := by
    rw [cutMatrix, hwcw]
  set Ssplit :=
    Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (L := L) (Nat.sub_le k 1))
  refine ⟨w, m, W, fun p ↦ WithLp.ofLp xc (Ssplit.symm p.1, p.2), ?_, ?_, ?_, ?_, hW, hmD, ?_, ?_⟩
  · rw [← Entropy.norm_cutVector (leftBlock L k), hwcw, hwc1]
  · rw [hcm]; exact hwcD
  · rw [← Entropy.inner_cutOperator (leftBlock L k), hwcw]; exact hwcE
  · rw [hcm]
    have h := congrArg (fun v ↦ schmidtCoeffMatrix (WithLp.ofLp v)) hwcPV
    simpa only [schmidtCoeffMatrix_ofLp_leftApply] using h
  · funext ⟨p, z⟩
    have h := congrFun hwx (Ssplit.symm p, z)
    have hg : (gluingCut L q k).symm (p, z) = e.symm (Ssplit.symm p, z) := by
      rw [gluingCut, Entropy.threeCutEquiv_eq_trans]
      rfl
    simp only [Function.comp_apply, hg, w, Equiv.apply_symm_apply]
    rw [h]
    simp [mulVec, dotProduct, Fintype.sum_prod_type, one_apply]
  · have h := congrArg (fun v ↦ schmidtCoeffMatrix (WithLp.ofLp v)) hxPV
    simp only [schmidtCoeffMatrix_ofLp_leftApply] at h
    funext ⟨p, j⟩
    have hpj := congrFun (congrFun h (Ssplit.symm p)) j
    simp only [schmidtCoeffMatrix_apply, mul_apply] at hpj
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
      reindex_apply, submatrix_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [← hpj, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv Ssplit.symm _ _ fun _ ↦ rfl

end TNLean.MPS.AreaLaw
