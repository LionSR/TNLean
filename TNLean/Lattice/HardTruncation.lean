/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.EuclideanEigenvectorBasis
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.RelativeLowEnergyCloseness
import TNLean.Algebra.WeightedLowRestriction
import TNLean.Lattice.BoundedDegreeImaginaryTime
import TNLean.Lattice.DisjointRegionalGround

/-!
# Hard truncation of a region of a bounded-interaction lattice Hamiltonian

Positive contractions `h i` act on sets `D i` of an arbitrary finite site set,
with `|D i| ≤ k` and every site in at most `g` of the sets. For a region `Λ`,
the terms inside `Λ` form `H_in`, those disjoint from `Λ` form `H_out`, and the
`b` remaining terms, which cross the boundary, form `Y`. Clipping `H_in` at
`e_in + t`, where `e_in` is its actual ground energy, gives `F`.

For `η > 0` and `t ≥ η + 3 b + 1` both restricted errors of `H - F`, on the
low-energy spaces of `H` and of `F` within `η` of the ground energy of `H`, are
at most `ξ = 4 g k (b + 1) exp(-(t - η - 3 b - 1) / (2 g k))`. The ordered
eigenvalues below that window shift by at most `ξ`, the ground energy by at most
`ξ`, and the low-energy spaces are close in both directions after the
window-count enlargement. No regional minimum, eigenbasis, spectral gap or
residual is an input, and arbitrary ground degeneracy is allowed.

Source: Arad, Kuwahara and Landau, arXiv:1406.3898, Definition `def:Ht`,
`low70.tex`, lines 684–697, and Theorem `thm:lowspec`, lines 719–748, quoted as
Theorem 2.6 by ALVV, arXiv:1602.08828v2, Definition 4.3, Proposition 4.4 and
Lemma 4.5, `local_alg_arxiv_v2.tex`, lines 873–968.

**Local fix (cutoff, constants and window count):** the cutoff is the explicit
sufficient `t ≥ η + 3 b + 1` rather than the printed unrestricted `t > η`, the
decay rate is `1 / (2 g k)` with the displayed prefactor rather than the printed
constants, and the relative enlargement includes the actual ceiling window count
and ground shift. For nearest-neighbour chains `b ≤ 2` and the cutoff is
`η + 7`, as in `TNLean.MPS.AreaLaw.ALVV.HardTruncation`. See
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf and
`docs/audits/2026-11-15_lattice_hard_truncation.md`.
-/

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

noncomputable section

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The last canonically ordered eigenvalue is the minimum eigenvalue. -/
theorem eigenvalues₀_last_eq_minEigenvalue [Nonempty n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) :
    let jmin : Fin (Fintype.card n) :=
      ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩
    hM.eigenvalues₀ jmin = minEigenvalue hM := by
  intro jmin
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  apply le_antisymm
  · obtain ⟨i, hi⟩ := minEigenvalue_achieved hM
    have hle : e.symm i ≤ jmin := by
      change (e.symm i).val ≤ Fintype.card n - 1
      omega
    have h := hM.eigenvalues₀_antitone hle
    change hM.eigenvalues₀ (e.symm i) = minEigenvalue hM at hi
    exact h.trans_eq hi
  · simpa only [IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
      minEigenvalue_le hM (e jmin)

/-- The closed spectral span of the reindexed eigenvector basis is that of the
canonically ordered one. -/
theorem spectralSpanLE_eigenvectorBasis_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    Submodule.spectralSpanLE hM.eigenvectorBasis hM.eigenvalues c =
      Submodule.spectralSpanLE
        ((isSymmetric_toEuclideanLin_iff.mpr hM).eigenvectorBasis finrank_euclideanSpace)
        hM.eigenvalues₀ c := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  unfold Submodule.spectralSpanLE
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e.symm i, hi, ?_⟩
    simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply, e]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e i, ?_, ?_⟩
    · have hi' : hM.eigenvalues₀ i ≤ c := hi
      simpa [IsHermitian.eigenvalues, e] using hi'
    · simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply,
        e, Equiv.symm_apply_apply]

end Matrix.IsHermitian

namespace TNLean.Lattice

open QuantumCircuit

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] {q : ℕ}

omit [DecidableEq ι] [Fintype I] in
private theorem sum_posSemidef_le_card (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) (s : Finset I) :
    (∑ i ∈ s, h i).PosSemidef ∧ ∑ i ∈ s, h i ≤ (s.card : ℝ) • 1 := by
  refine ⟨nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i), ?_⟩
  calc
    ∑ i ∈ s, h i ≤ s.card • (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) :=
      Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ h1 i
    _ = (s.card : ℝ) • 1 := (Nat.cast_smul_eq_nsmul ℝ _ _).symm

private theorem residual_coefficient_le {κ b E η t : ℝ} (hκ : 0 < κ) (hb : 0 ≤ b)
    (hE : E ≤ b) :
    (Real.exp (-(1 / (2 * κ)) * (t - (η + 3 * b + 1)) - 1) / (1 / (2 * κ))) *
        ((2 * b) / ((η + 3 * b + 1) - (E + η) - 2 * b)) ≤
      4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) := by
  have hd : 1 ≤ (η + 3 * b + 1) - (E + η) - 2 * b := by linarith
  have hq : (2 * b) / ((η + 3 * b + 1) - (E + η) - 2 * b) ≤ 2 * (b + 1) := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have hexp : -(1 / (2 * κ)) * (t - (η + 3 * b + 1)) - 1 =
      -(t - (η + 3 * b + 1)) / (2 * κ) + (-1) := by
    field_simp
    ring
  have h1 : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hX : 0 < Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) := Real.exp_pos _
  calc
    _ ≤ (Real.exp (-(1 / (2 * κ)) * (t - (η + 3 * b + 1)) - 1) / (1 / (2 * κ))) *
        (2 * (b + 1)) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) *
        Real.exp (-1) := by
      rw [hexp, Real.exp_add]
      field_simp
      ring
    _ ≤ 4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) * 1 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _

/-- Actual hard truncation of one region of a bounded-support, bounded-degree
lattice Hamiltonian of positive contractions, with both restricted errors.
The regional minima, the common regional ground vector and the ground vectors
of the original and clipped operators are constructed; no residual, minimum,
eigenbasis or gap is an input. Both operators carry the same scalar shift.

Source: AKL14, arXiv:1406.3898, `def:Ht`, lines 684–697, and `thm:lowspec`,
lines 719–748, as Proposition 4.4(1) of ALVV, arXiv:1602.08828v2, lines 894–921,
with the explicit sufficient cutoff and constants recorded in the module's
local-fix marker. -/
theorem exists_region_hard_truncation_residuals {k g : ℕ}
    (hq : 0 < q) (hk0 : 0 < k) (hg0 : 0 < g)
    (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ) (D : I → Finset ι)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : ι ↦ q) (h i) (D i))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (hk : ∀ i, (D i).card ≤ k) (hg : ∀ x, (Finset.univ.filter fun i ↦ x ∈ D i).card ≤ g)
    (Λ : Finset ι) :
    let Iin := Finset.univ.filter fun i ↦ D i ⊆ Λ
    let Iout := Finset.univ.filter fun i ↦ ¬D i ⊆ Λ ∧ Disjoint (D i) Λ
    let Ib := Finset.univ.filter fun i ↦ ¬D i ⊆ Λ ∧ ¬Disjoint (D i) Λ
    let Hin := ∑ i ∈ Iin, h i
    let Hout := ∑ i ∈ Iout, h i
    let Y := ∑ i ∈ Ib, h i
    let b : ℝ := Ib.card
    let κ : ℝ := ((g * k : ℕ) : ℝ)
    ∃ (ein eout : ℝ) (x z : (ι → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ Hin *ᵥ x = (ein : ℂ) • x ∧ Hout *ᵥ x = (eout : ℂ) • x ∧
      (Hin - (ein : ℂ) • 1).PosSemidef ∧ (Hout - (eout : ℂ) • 1).PosSemidef ∧
      0 ≤ ein ∧ 0 ≤ eout ∧
      let H := (∑ i, h i) - ((ein + eout : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ b ∧
      ∀ η t : ℝ, 0 < η → η + 3 * b + 1 ≤ t →
        let F := energyTruncation Hin (ein + t) + Hout + Y - ((ein + eout : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian) (E' : ℝ) (z' : (ι → Fin q) → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ)).PosSemidef ∧
          0 ≤ E' ∧ E' ≤ b ∧
          let ξ : ℝ := (4 : ℝ) * κ * (b + (1 : ℝ)) *
            Real.exp (-(t - (η + (3 : ℝ) * b + (1 : ℝ))) / ((2 : ℝ) * κ))
          ‖((toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE
              ((isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
                finrank_euclideanSpace) hH.eigenvalues₀ (E + η))‖ ≤ ξ ∧
          ‖((toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE
              ((isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
                finrank_euclideanSpace) hF.eigenvalues₀ (E + η))‖ ≤ ξ := by
  intro Iin Iout Ib Hin Hout Y b κ
  classical
  have sum_supported_of_subset (s : Finset I) (R : Finset ι) (hR : ∀ i ∈ s, D i ⊆ R) :
      Entropy.IsSupportedOn (n := fun _ : ι ↦ q) (∑ i ∈ s, h i) R := by
    show _ ∈ ManyBody.supportedOperators _ _
    exact sum_mem fun i hi ↦
      ManyBody.supportedOperators_mono (by exact_mod_cast hR i hi)
        (hs i)
  let A : Fin 2 → Matrix (ι → Fin q) (ι → Fin q) ℂ := ![Hin, Hout]
  let R : Fin 2 → Finset ι := ![Λ, Λᶜ]
  let c : Fin 2 → ℕ := ![Iin.card, Iout.card]
  have hR : Pairwise fun i j ↦ Disjoint (R i) (R j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [R, disjoint_compl_right, disjoint_compl_left]
  have hsA (j : Fin 2) : Entropy.IsSupportedOn (n := fun _ : ι ↦ q) (A j) (R j) := by
    fin_cases j
    · exact sum_supported_of_subset Iin Λ fun i hi ↦ (Finset.mem_filter.mp hi).2
    · refine sum_supported_of_subset Iout Λᶜ fun i hi ↦ ?_
      exact Finset.subset_compl_iff_disjoint_right.mpr (Finset.mem_filter.mp hi).2.2
  have hA (j : Fin 2) : (A j).PosSemidef ∧ A j ≤ (c j : ℝ) • 1 := by
    fin_cases j
    · exact sum_posSemidef_le_card h h0 h1 Iin
    · exact sum_posSemidef_le_card h h0 h1 Iout
  obtain ⟨hY, hYC⟩ := sum_posSemidef_le_card h h0 h1 Ib
  have hsum : (∑ i, h i) = (∑ j, A j) + Y := by
    rw [Fin.sum_univ_two]
    change (∑ i, h i) = Hin + Hout + Y
    simp only [Hin, Hout, Y, Iin, Iout, Ib]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ D i ⊆ Λ),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun i ↦ ¬D i ⊆ Λ)
        (fun i ↦ Disjoint (D i) Λ), Finset.filter_filter, Finset.filter_filter, add_assoc]
  obtain ⟨e, x, hx, hxe, he, hclip⟩ :=
    Matrix.exists_disjoint_regional_clipping_structure hq R A c hR hsA
      (fun j ↦ (hA j).1) (fun j ↦ (hA j).2) Y Ib.card hY hYC
  let B (t : ℝ) (T : Finset (Fin 2)) :=
    (∑ j, ((if j ∈ T then cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
      (e j : ℂ) • 1)) + Y
  let H := (∑ i, h i) - ((e 0 + e 1 : ℝ) : ℂ) • 1
  have hcenter (t : ℝ) : B t ∅ = H := by
    simp only [B, H, Finset.notMem_empty, ite_false, Finset.sum_sub_distrib, hsum,
      Fin.sum_univ_two]
    push_cast
    rw [add_smul]
    abel
  obtain ⟨hX0, _hx0, _hc0, _ho0, _hcap0, _hnorm0,
      E, z, hz, hHz, hE, hE0, hEJ⟩ := hclip 0 le_rfl ∅
  have hHpos : H.PosSemidef := by
    rw [← hcenter 0]
    exact hX0.add hY
  have hHz' : H *ᵥ z = (E : ℂ) • z := by
    rw [← hcenter 0]
    exact hHz
  have hE' : (H - (E : ℂ) • 1).PosSemidef := by
    rw [← hcenter 0]
    exact hE
  refine ⟨e 0, e 1, x, z, E, hx, hxe 0, hxe 1, he 0, he 1,
    (hA 0).1.nonneg_of_normalized_eigenvector (e 0) x (hxe 0) hx,
    (hA 1).1.nonneg_of_normalized_eigenvector (e 1) x (hxe 1) hx,
    hz, hHz', hE', hE0, hEJ, ?_⟩
  intro η t hη ht F
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := by linarith
  have hmiddle : B t {0} = F := by
    simp only [B, Fin.sum_univ_two, Finset.mem_singleton, Fin.isValue, ite_true,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
    dsimp only [F, energyTruncation]
    push_cast
    rw [add_smul]
    simp only [A, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    abel
  have hdiff : H - F = Hin - energyTruncation Hin (e 0 + t) := by
    dsimp only [H, F]
    rw [hsum, Fin.sum_univ_two]
    change Hin + Hout + Y - _ - (energyTruncation Hin (e 0 + t) + Hout + Y - _) = _
    abel
  have hFH : F ≤ H := Matrix.le_iff.mpr (by
    rw [hdiff]
    exact Matrix.le_iff.mp ((hA 0).1.isHermitian.energyTruncation_le (e 0 + t)))
  obtain ⟨hX1, _hx1, _hc1, _ho1, _hcap1, _hnorm1,
      E', z', hz', hFz₀, hE'₀, hE'0, hE'J⟩ := hclip t ht0 {0}
  have hFz' : F *ᵥ z' = (E' : ℂ) • z' := by
    rw [← hmiddle]
    exact hFz₀
  have hE'' : (F - (E' : ℂ) • 1).PosSemidef := by
    rw [← hmiddle]
    exact hE'₀
  have hFpos : F.PosSemidef := by
    rw [← hmiddle]
    exact hX1.add hY
  let hH := hHpos.isHermitian
  let hF := hFpos.isHermitian
  refine ⟨hH, hF, E', z', hFH, hz', hFz', hE'', hE'0, hE'J, ?_⟩
  have hκ : 0 < κ := Nat.cast_pos.mpr (Nat.mul_pos hg0 hk0)
  let s : ℝ := 1 / (2 * κ)
  have hs0 : 0 < s := by positivity
  have hsκ : 2 * κ * s ≤ 1 := by
    simp only [s]
    field_simp
    exact le_rfl
  let u : ℝ := η + 3 * b + 1
  have hconj : ‖NormedSpace.exp (s • (A 0 - (e 0 + u) • (1 : Matrix (ι → Fin q)
      (ι → Fin q) ℂ))) * Y * NormedSpace.exp (-(s • (A 0 - (e 0 + u) •
        (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ))))‖ ≤ 2 * b := by
    have hgin (y : ι) : (Iin.filter fun i ↦ y ∈ D i).card ≤ g :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans
        (hg y)
    have hc := norm_exp_conjugation_shift_sum_le (s := Iin) (J := Ib) h D hk0 hg0
      (fun i _ ↦ hs i) (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) (fun i _ ↦ hk i) hgin
      ((e 0 + u : ℝ) : ℂ) s hs0.le hsκ
    simp only [Complex.coe_smul] at hc
    exact hc
  have hgap : 2 * b < u - (E + η) := by simp only [u]; linarith
  have hres (M : Matrix (ι → Fin q) (ι → Fin q) ℂ) (hM : M.IsHermitian)
      (T : Finset (Fin 2)) (hBM : B t T = M) :
      ‖((toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) H -
          (toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) F).domRestrict
        (Submodule.spectralSpanLE hM.eigenvectorBasis hM.eigenvalues (E + η))‖ ≤
          4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) := by
    have hEigen (v : ι → Fin q) : (toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) (B t T)
        (hM.eigenvectorBasis v) = (hM.eigenvalues v : ℂ) • hM.eigenvectorBasis v := by
      rw [hBM]
      exact hM.toEuclideanCLM_eigenvectorBasis v
    have hsingle := Matrix.norm_partially_clipped_truncation_low_le A
      (fun j ↦ (hA j).1.isHermitian)
      (fun i j hij ↦ by
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact ManyBody.commute_of_mem_supportedOperators_of_disjoint (hsA 0) (hsA 1) (hR hij)
        · exact ManyBody.commute_of_mem_supportedOperators_of_disjoint (hsA 1) (hsA 0) (hR hij)
        · exact absurd rfl hij)
      e (fun j ↦ Matrix.le_iff.mpr (he j)) T 0 Y u (E + η) s t (2 * b) hs0
      (by simp only [u]; linarith) ht hM.eigenvectorBasis hM.eigenvalues hEigen hconj hgap
    rw [← map_sub, hdiff]
    exact hsingle.trans (residual_coefficient_le hκ hb0 hEJ)
  constructor
  · rw [← hH.spectralSpanLE_eigenvectorBasis_eq (E + η)]
    exact hres H hH ∅ (hcenter t)
  · rw [← hF.spectralSpanLE_eigenvectorBasis_eq (E + η)]
    exact hres F hF {0} hmiddle

/-- Actual hard truncation of one region of a bounded-support, bounded-degree
lattice Hamiltonian of positive contractions: ordered energy comparison, ground
energy displacement and both relative-ground-energy spectral-space comparisons.
No residual, regional minimum, eigenbasis or spectral gap is an input, and the
ground spaces may be degenerate. The displayed spaces belong to the actual
operators with their common derived scalar shift.

Source: AKL14, arXiv:1406.3898, `thm:lowspec`, lines 719–748, as Proposition 4.4
and Lemma 4.5 of ALVV, arXiv:1602.08828v2, lines 894–968, with the explicit
sufficient cutoff, constants and ceiling window count recorded in the module's
local-fix marker. -/
theorem exists_region_hard_truncation_spectral_comparison {k g : ℕ}
    (hq : 0 < q) (hk0 : 0 < k) (hg0 : 0 < g)
    (h : I → Matrix (ι → Fin q) (ι → Fin q) ℂ) (D : I → Finset ι)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : ι ↦ q) (h i) (D i))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (hk : ∀ i, (D i).card ≤ k) (hg : ∀ x, (Finset.univ.filter fun i ↦ x ∈ D i).card ≤ g)
    (Λ : Finset ι) :
    let Iin := Finset.univ.filter fun i ↦ D i ⊆ Λ
    let Iout := Finset.univ.filter fun i ↦ ¬D i ⊆ Λ ∧ Disjoint (D i) Λ
    let Ib := Finset.univ.filter fun i ↦ ¬D i ⊆ Λ ∧ ¬Disjoint (D i) Λ
    let Hin := ∑ i ∈ Iin, h i
    let Hout := ∑ i ∈ Iout, h i
    let Y := ∑ i ∈ Ib, h i
    let b : ℝ := Ib.card
    let κ : ℝ := ((g * k : ℕ) : ℝ)
    ∃ (ein eout : ℝ) (x z : (ι → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ Hin *ᵥ x = (ein : ℂ) • x ∧ Hout *ᵥ x = (eout : ℂ) • x ∧
      (Hin - (ein : ℂ) • 1).PosSemidef ∧ (Hout - (eout : ℂ) • 1).PosSemidef ∧
      0 ≤ ein ∧ 0 ≤ eout ∧
      let H := (∑ i, h i) - ((ein + eout : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ b ∧
      ∀ η t : ℝ, 0 < η → η + 3 * b + 1 ≤ t →
        let F := energyTruncation Hin (ein + t) + Hout + Y - ((ein + eout : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian) (E' : ℝ) (z' : (ι → Fin q) → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ)).PosSemidef ∧
          0 ≤ E' ∧ E' ≤ b ∧
          let ξ : ℝ := (4 : ℝ) * κ * (b + (1 : ℝ)) *
            Real.exp (-(t - (η + (3 : ℝ) * b + (1 : ℝ))) / ((2 : ℝ) * κ))
          let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
            finrank_euclideanSpace
          let bF := (isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
            finrank_euclideanSpace
          ‖((toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η))‖ ≤ ξ ∧
          ‖((toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := ι → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η))‖ ≤ ξ ∧
          (∀ i : Fin (Fintype.card (ι → Fin q)), hF.eigenvalues₀ i ≤ E + η →
            hF.eigenvalues₀ i ≤ hH.eigenvalues₀ i ∧
              hH.eigenvalues₀ i ≤ hF.eigenvalues₀ i + ξ) ∧
          E' ≤ E ∧ E ≤ E' + ξ ∧
          ∀ δ : ℝ, 0 < δ →
            let η' : ℝ := η + ξ + (2 : ℝ) * ξ * Real.sqrt ((⌈η / ((2 : ℝ) * ξ)⌉₊ : ℝ) / δ)
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η'))
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η)) ∧
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η'))
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η)) := by
  intro Iin Iout Ib Hin Hout Y b κ
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨ein, eout, x, z, E, hx, hxin, hxout, hein, heout, hein0, heout0,
      hz, hHz, hElow, hE0, hEb, hclip⟩ :=
    exists_region_hard_truncation_residuals hq hk0 hg0 h D hs h0 h1 hk hg Λ
  refine ⟨ein, eout, x, z, E, hx, hxin, hxout, hein, heout, hein0, heout0,
    hz, hHz, hElow, hE0, hEb, ?_⟩
  intro η t hη ht F
  obtain ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'b, hresH, hresF⟩ :=
    hclip η t hη ht
  let ξ : ℝ := (4 : ℝ) * κ * (b + (1 : ℝ)) *
    Real.exp (-(t - (η + (3 : ℝ) * b + (1 : ℝ))) / ((2 : ℝ) * κ))
  have hκ : 0 < κ := Nat.cast_pos.mpr (Nat.mul_pos hg0 hk0)
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hξ : 0 < ξ := by dsimp only [ξ]; positivity
  let jmin : Fin (Fintype.card (ι → Fin q)) :=
    ⟨Fintype.card (ι → Fin q) - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩
  have hminH : minEigenvalue hH = E := by
    simpa using hH.minEigenvalue_eq_add_of_centered_ground 0 E z hz
      (by simpa using hHz) (by simpa using hElow)
  have hminF : minEigenvalue hF = E' := by
    simpa using hF.minEigenvalue_eq_add_of_centered_ground 0 E' z' hz'
      (by simpa using hFz') (by simpa using hE'low)
  have hlastH : hH.eigenvalues₀ jmin = E :=
    hH.eigenvalues₀_last_eq_minEigenvalue.trans hminH
  have hlastF : hF.eigenvalues₀ jmin = E' :=
    hF.eigenvalues₀_last_eq_minEigenvalue.trans hminF
  have hresult (δ : ℝ) (hδ : 0 < δ) := by
    have h := hH.groundEnergy_compare_and_isCloseTo_spectralSpanLE_of_norm_domRestrict_le
      hF hFH η ξ δ hη hξ hδ
    dsimp only at h
    rw [hlastH, hlastF] at h
    exact h hresH hresF
  obtain ⟨hgroundLower, hgroundUpper, _hcloseH, _hcloseF⟩ := hresult 1 zero_lt_one
  refine ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'b,
    hresH, hresF, ?_, hgroundLower, hgroundUpper, ?_⟩
  · intro i hi
    exact ⟨hF.eigenvalues₀_mono hH hFH i,
      hH.eigenvalues₀_le_add_of_norm_domRestrict_low_le hF (E + η) ξ hresF i hi⟩
  · intro δ hδ
    exact ⟨(hresult δ hδ).2.2.1, (hresult δ hδ).2.2.2⟩

end TNLean.Lattice
