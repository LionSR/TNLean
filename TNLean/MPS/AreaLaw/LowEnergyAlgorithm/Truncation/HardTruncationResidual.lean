/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Eigenvalue.HermitianExtremalEigenvalues
import QICLean.ManyBody.Hamiltonian.DisjointRegionalGround
import QICLean.Algebra.Combinatorics.FinSum
import QICLean.ManyBody.Hamiltonian.Chain.RegionalTruncation
import QICLean.Spectral.Filter.EnergyTruncation
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Analysis.Projection.ProjectedPositiveEnergy
import QICLean.Analysis.Subspace.ViableSubspace
import QICLean.Spectral.LowEnergy.RelativeLowEnergyCloseness

/-!
# Actual residuals for one regional hard truncation

Original positive-contraction nearest-neighbour bonds determine three disjoint
regional sums and their genuine minimum energies. Only the middle regional sum
is clipped. Both actual restricted errors, on the original and clipped closed
low-energy spaces, are derived from those bonds at `t ≥ η + 7`.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3 and Proposition 4.4(1),
`local_alg_arxiv_v2.tex`, lines 873–921.

**Local fix (cutoff):** The proof uses the explicit sufficient cutoff `t ≥ η + 7`;
the printed unrestricted truncated-side claim under merely `t > η` is not asserted.
The companion source note is
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
Its pending cutoff revision, the separate source counterexample and the
acceptance gates for the physical prerequisites are recorded in
`docs/audits/2026-10-29_single_region_hard_truncation.md`.

## Regional excitation energy on the full original ground space

For an interval of a nearest-neighbour chain, the regional Hamiltonian,
centered at its actual minimum, has energy at most two on every unit
vector of the full original ground space. Only the two crossing bonds
contribute to this budget. Its norm is bounded by the chain length.
Projection into a candidate with loss at most `1 / (100 * (L + 1))`
keeps the regional energy below three and supplies a nonzero candidate
vector with this Rayleigh bound.

This is an auxiliary for ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1631–1632, and the energy-estimation argument in the proof of
`t:alg1`, lines 1805–1806. No gap or simple-ground-space assumption is used.

It also contains the following results.

* `TNLean.MPS.AreaLaw.ALVV.exists_single_region_hard_truncation_spectral_comparison`: physical hard
  truncation: ordered energies and relative low-energy spaces.
-/

section HardTruncationResidual

section

open ManyBody (interval)

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ManyBody.BondInteraction (five_region_original_bond_data)

noncomputable section

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
private theorem three_region_data {L q l r : ℕ} (hlr : l ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 4 → ℕ := ![0, l, r, L]
    let R := fun j : Fin 3 ↦ interval L (k j.castSucc) (k j.succ)
    let I := fun j : Fin 3 ↦ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A := ManyBody.BondInteraction.threeRegionHamiltonians l r Φ
    let J := Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
    let Y := ∑ i ∈ J, Φ.term i
    Monotone k ∧ (Pairwise fun i j ↦ Disjoint (R i) (R j)) ∧
      (∀ j, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (A j) (R j)) ∧
      (∀ j, (A j).PosSemidef ∧ A j ≤ ((I j).card : ℝ) • 1) ∧
      Y.PosSemidef ∧ Y ≤ (J.card : ℝ) • 1 ∧ J.card ≤ 2 ∧
      Φ.hamiltonian = (∑ j, A j) + Y := by
  intro k R I A J Y
  let k5 : Fin 6 → ℕ := ![0, l, l, r, r, L]
  let R5 := fun j : Fin 5 ↦ interval L (k5 j.castSucc) (k5 j.succ)
  let I5 := fun j : Fin 5 ↦ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k5 j.castSucc ≤ i.val ∧ i.val + 1 < k5 j.succ)
  let A5 := fun j : Fin 5 ↦ ∑ i ∈ I5 j, Φ.term i
  let f := fun j : Fin 3 ↦ (⟨2 * j.val, by omega⟩ : Fin 5)
  obtain ⟨_hk5, hR5, hs5, hA5, hY, hYC, _hJ4, hsum5⟩ :=
    five_region_original_bond_data L q l l r r le_rfl hlr le_rfl hrL Φ h0 h1
  have hR (j : Fin 3) : R j = R5 (f j) := by fin_cases j <;> rfl
  have hI (j : Fin 3) : I j = I5 (f j) := by fin_cases j <;> rfl
  have hA (j : Fin 3) : A j = A5 (f j) := by fin_cases j <;> rfl
  have hJ5 : Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, l, r, r} : Finset ℕ)) = J := by
    ext i
    simp [J]
  have hJ : J.card ≤ 2 := by
    have hc := Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
      (s := J) (t := {l, r}) (fun _ hi ↦ (Finset.mem_filter.mp hi).2) (by
        intro i _ j _ hij
        apply Fin.ext
        change i.val + 1 = j.val + 1 at hij
        omega)
    exact hc.trans (by simpa using Finset.card_insert_le l ({r} : Finset ℕ))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hJ, ?_⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [k] <;> omega
  · intro i j hij
    have hne : f i ≠ f j := by
      intro heq
      apply hij
      apply Fin.ext
      have hv := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val at hv
      omega
    rw [hR i, hR j]
    exact hR5 hne
  · intro j
    rw [hA j, hR j]
    exact hs5 (f j)
  · intro j
    rw [hA j, hI j]
    exact hA5 (f j)
  · simpa only [hJ5] using hY
  · simpa only [hJ5] using hYC
  · have hcontra (c m : ℕ) : (c ≤ m ∧ m + 1 < c) ↔ False := ⟨fun h ↦ by omega, False.elim⟩
    have hsum := hsum5
    rw [Fin.sum_univ_five] at hsum
    simp only [A, ManyBody.BondInteraction.threeRegionHamiltonians, Fin.sum_univ_three, J, Y]
    simp only [Fin.isValue, Fin.castSucc_zero, cons_val_zero, zero_le, Fin.succ_zero_eq_one,
      cons_val_one, true_and, Fin.castSucc_one, Fin.succ_one_eq_two, cons_val, hcontra,
      Finset.filter_false, Finset.sum_empty, add_zero, Fin.reduceCastSucc, Fin.reduceSucc,
      add_assoc, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.mem_insert,
      true_or] at hsum ⊢
    convert hsum using 6 <;> rfl

private theorem residual_coefficient_le {c E η t : ℝ} (hc : c ≤ 2) (hE : E ≤ 2) :
    (Real.exp (-(1 / 8) * (t - (η + 7)) - 1) / (1 / 8)) *
        ((2 * c) / ((η + 7) - (E + η) - 2 * c)) ≤
      32 * Real.exp (-(t - η) / 8) := by
  have hd : 1 ≤ (η + 7) - (E + η) - 2 * c := by linarith
  have hq : (2 * c) / ((η + 7) - (E + η) - 2 * c) ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < (η + 7) - (E + η) - 2 * c)).mpr
    linarith
  have hexp : -(1 / 8 : ℝ) * (t - (η + 7)) - 1 =
      -(t - η) / 8 + (-1 / 8) := by ring
  calc
    _ ≤ (Real.exp (-(1 / 8) * (t - (η + 7)) - 1) / (1 / 8)) * 4 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 32 * Real.exp (-(t - η) / 8) * Real.exp (-1 / 8) := by
      rw [hexp, Real.exp_add]
      ring
    _ ≤ 32 * Real.exp (-(t - η) / 8) * 1 := by
      gcongr
      exact Real.exp_le_one_iff.mpr (by norm_num)
    _ = _ := mul_one _

open Classical in
/-- Actual single-middle-region hard truncation from the original chain, with both
restricted errors at the same original-ground-energy cutoff. Regional minima and
the original and clipped ground vectors are constructed. The sufficient cutoff
is `t ≥ η+7`; no clipped gap, perturbation bound or decomposition is assumed.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3 and Proposition 4.4(1),
lines 873–921, with the explicit sufficient cutoff and pending companion-note
revision recorded in `docs/audits/2026-10-29_single_region_hard_truncation.md`.
Empty regions and coincident or endpoint cuts are included. -/
theorem exists_single_region_hard_truncation_residuals {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, ManyBody.BondInteraction.threeRegionHamiltonians l r Φ j *ᵥ x =
        (e j : ℂ) • x) ∧
      (∀ j, (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ j - (e j : ℂ) • 1).PosSemidef) ∧
        (∀ j, 0 ≤ e j) ∧
      let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 2 ∧
      ∀ η t : ℝ, 0 < η → η + 7 ≤ t →
        let F :=
          energyTruncation (ManyBody.BondInteraction.threeRegionHamiltonians
            l r Φ 1) (e 1 + t) + ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 0 +
            ManyBody.BondInteraction.threeRegionHamiltonians
              l r Φ 2 + (∑ i ∈ Finset.univ.filter
            (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), Φ.term i) -
          (((∑ j, e j) : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian)
          (E' : ℝ) (z' : (Fin L → Fin q) → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • 1).PosSemidef ∧ 0 ≤ E' ∧ E' ≤ 2 ∧
          ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE
              ((isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
                finrank_euclideanSpace) hH.eigenvalues₀ (E + η))‖ ≤
              32 * Real.exp (-(t - η) / 8) ∧
          ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE
              ((isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
                finrank_euclideanSpace) hF.eigenvalues₀ (E + η))‖ ≤
              32 * Real.exp (-(t - η) / 8) := by
  set A := ManyBody.BondInteraction.threeRegionHamiltonians l r Φ with hAdef
  set J := Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
    with hJdef
  set Y := ∑ i ∈ J, Φ.term i with hYdef
  let k : Fin 4 → ℕ := ![0, l, r, L]
  let R := fun j : Fin 3 ↦ interval L (k j.castSucc) (k j.succ)
  let I := fun j : Fin 3 ↦ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
  obtain ⟨hk, hR, hsA, hA, hY, hYC, hJ, hsum⟩ :
      Monotone k ∧ (Pairwise fun i j ↦ Disjoint (R i) (R j)) ∧
        (∀ j, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (A j) (R j)) ∧
        (∀ j, (A j).PosSemidef ∧ A j ≤ ((I j).card : ℝ) • 1) ∧
        Y.PosSemidef ∧ Y ≤ (J.card : ℝ) • 1 ∧ J.card ≤ 2 ∧
        Φ.hamiltonian = (∑ j, A j) + Y :=
    three_region_data hlr hrL Φ h0 h1
  have : NeZero q := ⟨hq.ne'⟩
  obtain ⟨e, x, hx, hxe, he, hclip⟩ :=
    ManyBody.exists_disjoint_regional_clipping_structure (X := fun _ ↦ Fin q) R A
      (fun j ↦ (I j).card)
      hR hsA (fun j ↦ (hA j).1) (fun j ↦ (hA j).2) Y J.card hY hYC
  let B (t : ℝ) (T : Finset (Fin 3)) :=
    (∑ j, ((if j ∈ T then energyTruncation (A j) (e j + t) else A j) -
      (e j : ℂ) • 1)) + Y
  let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
  have hcenter (t : ℝ) : B t ∅ = H := by
    simp only [B, H, Finset.notMem_empty, ite_false, Finset.sum_sub_distrib, hsum]
    push_cast
    rw [Finset.sum_smul]
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
  refine ⟨e, x, z, E, hx, hxe, he,
    fun j ↦ (hA j).1.nonneg_of_normalized_eigenvector (e j) x (hxe j) hx,
    hz, hHz', hE', hE0, hEJ.trans (by exact_mod_cast hJ), ?_⟩
  intro η t hη ht F
  have ht0 : 0 ≤ t := by linarith
  have hmiddle : B t {1} = F := by
    simp only [B, Fin.sum_univ_three, Finset.mem_singleton, Fin.reduceEq, ite_true,
      ite_false]
    dsimp only [F]
    rw [Fin.sum_univ_three]
    push_cast
    rw [add_smul, add_smul]
    abel
  have hdiff : H - F = A 1 - energyTruncation (A 1) (e 1 + t) := by
    dsimp only [H, F]
    rw [hsum, Fin.sum_univ_three]
    abel
  have hFH : F ≤ H := Matrix.le_iff.mpr (by
    rw [hdiff]
    exact Matrix.le_iff.mp ((hA 1).1.isHermitian.energyTruncation_le (e 1 + t)))
  obtain ⟨hX1, _hx1, _hc1, _ho1, _hcap1, _hnorm1,
      E', z', hz', hFz', hE', hE'0, hE'J⟩ := hclip t ht0 {1}
  have hFpos : F.PosSemidef := by
    rw [← hmiddle]
    exact hX1.add hY
  let hH := hHpos.isHermitian
  let hF := hFpos.isHermitian
  refine ⟨hH, hF, E', z', hFH, hz', ?_, ?_, hE'0,
    hE'J.trans (by exact_mod_cast hJ), ?_⟩
  · rw [← hmiddle]
    exact hFz'
  · rw [← hmiddle]
    exact hE'
  · have heorder (j : Fin 3) : (e j : ℂ) • 1 ≤ A j := Matrix.le_iff.mpr (he j)
    have hJreal : (J.card : ℝ) ≤ 2 := by exact_mod_cast hJ
    have hE2 : E ≤ 2 := hEJ.trans (by exact_mod_cast hJ)
    have hgap : 2 * (J.card : ℝ) < (η + 7) - (E + η) := by linarith
    have hres (M : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (hM : M.IsHermitian)
        (T : Finset (Fin 3)) (hBM : B t T = M) :
        ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
            (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) F).domRestrict
          (Submodule.spectralSpanLE hM.eigenvectorBasis hM.eigenvalues (E + η))‖ ≤
            32 * Real.exp (-(t - η) / 8) := by
      have hEigen (v : Fin L → Fin q) : (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) (B t T)
          (hM.eigenvectorBasis v) = (hM.eigenvalues v : ℂ) • hM.eigenvectorBasis v := by
        rw [hBM]
        exact hM.toEuclideanCLM_eigenvectorBasis v
      have hsingle :=
        ManyBody.BondInteraction.norm_consecutive_regional_truncation_low_le k hk Φ h0 h1
        e T 1 J (η + 7) (E + η) (1 / 8) t (by norm_num) (by norm_num)
        (by linarith) ht hM.eigenvectorBasis hM.eigenvalues heorder hEigen hgap
      have hsingle' := hsingle.trans (residual_coefficient_le hJreal hE2)
      rw [← map_sub, hdiff]
      exact hsingle'
    constructor
    · rw [← hH.spectralSpanLE_eigenvectorBasis_eq (E + η)]
      exact hres H hH ∅ (hcenter t)
    · rw [← hF.spectralSpanLE_eigenvectorBasis_eq (E + η)]
      exact hres F hF {1} hmiddle

end TNLean.MPS.AreaLaw.ALVV
end

end

section

open ManyBody (interval)

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The actual regional minimum gives a positive regional excitation
operator whose energy on the original full ground space is at most two.
Its norm is at most the chain length. A sufficiently close candidate
contains a nonzero vector with regional excitation energy at most three,
and the same bound holds on the entire projected ground space.
All regional and ground-space data
are constructed from the original bonds. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632. -/
theorem exists_regional_ground_energy_bound {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let A := ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 1
    ∃ (e : ℝ) (x : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (e : ℂ) • x ∧
      let C := A - (e : ℂ) • 1
      C.PosSemidef ∧ ‖C‖ ≤ (L : ℝ) ∧
        (∀ g ∈ G, (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C g) g).re ≤
          2 * ‖g‖ ^ 2) ∧
        ∀ (δ : ℝ) (U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))),
          0 ≤ δ → δ ≤ 1 / (100 * ((L : ℝ) + 1)) → Submodule.IsCloseTo δ U G →
          (∀ v ∈ G.map U.starProjection.toLinearMap,
            (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C v) v).re ≤
              3 * ‖v‖ ^ 2) ∧
          ∃ v ∈ U, v ≠ 0 ∧
            (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C v) v).re ≤
              3 * ‖v‖ ^ 2 := by
  intro config H hH G A
  let : Nonempty (Fin L → Fin q) := config
  obtain ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hE, hE0, hE2, _htruncation⟩ :=
    ALVV.exists_single_region_hard_truncation_residuals hq hlr hrL Φ h0 h1
  clear _htruncation
  refine ⟨e 1, x, hx, hxe 1, ?_⟩
  intro C
  have hC : C.PosSemidef := he 1
  let I := Finset.univ.filter (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r)
  have hAeq : A = ∑ i ∈ I, Φ.term i := rfl
  have hcard : I.card ≤ L := by
    calc
      I.card ≤ Fintype.card (Fin (L - 1)) := Finset.card_le_univ I
      _ = L - 1 := Fintype.card_fin _
      _ ≤ L := Nat.sub_le _ _
  have hcapA : A ≤ (L : ℝ) • 1 := by
    calc
      A = ∑ i ∈ I, Φ.term i := hAeq
      _ ≤ (I.card : ℝ) • 1 :=
        (sum_posSemidef_and_le_card_of_positive_unit_terms I Φ.term
          (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)).2
      _ ≤ (L : ℝ) • 1 := smul_le_smul_of_nonneg_right (by exact_mod_cast hcard) zero_le_one
  have hcapC : C ≤ (L : ℝ) • 1 := by
    refine (sub_le_self A ?_).trans hcapA
    rw [Complex.coe_smul]
    exact smul_nonneg (he0 1) zero_le_one
  have hnorm : ‖C‖ ≤ (L : ℝ) :=
    (CStarAlgebra.norm_le_iff_le_algebraMap C (by positivity) hC.nonneg).mpr
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hcapC)
  let S := ∑ j, e j
  have hmin : minEigenvalue hH = E + S :=
    hH.minEigenvalue_eq_add_of_centered_ground S E z hz hHz hE
  let Y := ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), Φ.term i
  have hrest :
      ((ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 0 - (e 0 : ℂ) • 1) +
        (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 2 - (e 2 : ℂ) • 1) +
        Y).PosSemidef :=
    ((he 0).add (he 2)).add (posSemidef_sum _ (fun i _ ↦ (h0 i).posSemidef))
  have hsplit : H - (S : ℂ) • 1 - C =
      (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 0 - (e 0 : ℂ) • 1) +
        (ManyBody.BondInteraction.threeRegionHamiltonians l r Φ 2 - (e 2 : ℂ) • 1) + Y := by
    dsimp only [H, S, C, A, Y]
    rw [ManyBody.BondInteraction.hamiltonian_eq_sum_threeRegionHamiltonians_add_crossings hlr Φ]
    simp only [Fin.sum_univ_three, Complex.ofReal_add, add_smul]
    abel
  have hpos : (H - (S : ℂ) • 1 - C).PosSemidef := by rw [hsplit]; exact hrest
  have hbase : ∀ g ∈ G,
      (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C g) g).re ≤
        2 * ‖g‖ ^ 2 := by
    intro g hg
    have hraw := Submodule.re_inner_apply_le_of_mem_spectralSpanLE
      hH.eigenvectorBasis hH.eigenvalues
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H).toLinearMap
      (fun j ↦ hH.toEuclideanCLM_eigenvectorBasis j) (minEigenvalue hH) hg
    have hquadratic := hpos.isPositive_toEuclideanCLM.re_inner_nonneg_left g
    simp only [map_sub, map_smul, map_one, _root_.sub_apply,
      _root_.smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, RCLike.re_to_complex, Complex.conj_ofReal,
      Complex.re_ofReal_mul] at hquadratic
    have hself : (inner ℂ g g).re = ‖g‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) g
    rw [hself] at hquadratic
    have hrawLeft : (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H g) g).re ≤
        minEigenvalue hH * ‖g‖ ^ 2 := by
      calc
        _ = (inner ℂ g (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H g)).re :=
          inner_re_symm (𝕜 := ℂ) _ _
        _ ≤ _ := hraw
    rw [hmin] at hrawLeft
    nlinarith only [hquadratic, hrawLeft, mul_le_mul_of_nonneg_right hE2 (sq_nonneg ‖g‖)]
  refine ⟨hC, hnorm, hbase, ?_⟩
  intro δ U hδ0 hsmall hclose
  have hfinal : ∀ v ∈ G.map U.starProjection.toLinearMap,
      (inner ℂ (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C v) v).re ≤
        3 * ‖v‖ ^ 2 :=
    hclose.map_starProjection_energy_le_three hδ0
      (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) C) hC.isPositive_toEuclideanCLM
      hbase hnorm hsmall
  refine ⟨hfinal, ?_⟩
  have hδ1 : δ < 1 :=
    (Real.projected_positive_energy_le_three (by positivity : (0 : ℝ) ≤ L) hδ0 hsmall).1
  obtain ⟨g0, hg0, hg0norm⟩ : ∃ g0 ∈ G, ‖g0‖ = 1 := by
    obtain ⟨j, hj⟩ := minEigenvalue_achieved hH
    exact ⟨hH.eigenvectorBasis j, Submodule.subset_span ⟨j, hj.le, rfl⟩,
      hH.eigenvectorBasis.norm_eq_one j⟩
  have hvnz : U.starProjection g0 ≠ 0 :=
    hclose.starProjection_ne_zero hδ1 hg0 (norm_ne_zero_iff.mp (hg0norm.trans_ne one_ne_zero))
  exact ⟨U.starProjection g0, U.starProjection_apply_mem g0, hvnz,
    hfinal _ (Submodule.mem_map_of_mem hg0)⟩

end TNLean.MPS.AreaLaw

end

end HardTruncationResidual

section HardTruncation

/-!
## Physical hard truncation: ordered energies and relative low-energy spaces

Original positive-contraction nearest-neighbour bonds determine the middle
regional clipping and both physical restricted errors. These errors give ordered
eigenvalue comparison, actual ground-energy displacement, and closeness in both
directions relative to each operator's own actual ground energy. The matrices
use the same derived sum of regional minima as a scalar shift.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3, Proposition 4.4 and Lemma 4.5,
`local_alg_arxiv_v2.tex`, lines 873–968.

**Local fix (cutoff and window count):** The physical cutoff is the explicit
sufficient `t ≥ η + 7`, rather than the printed unrestricted `t > η`. The
relative enlargement includes the actual ceiling window count and ground shift.
See https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf
and the pending revision and prerequisite gates recorded in
`docs/audits/2026-10-29_physical_hard_truncation_capstone.md`.
-/

open ManyBody (interval)

open Matrix
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.MPS.AreaLaw.ALVV

open Classical in
/-- Actual single-region hard truncation with both physical residuals, ordered
energy comparison and two relative-ground-energy spectral-space comparisons.

Source: ALVV, arXiv:1602.08828v2, Definition 4.3, Proposition 4.4 and Lemma 4.5,
lines 873–968, with the explicit sufficient cutoff and ceiling window count
recorded in the module's companion-note reference. No residual, regional
minimum, eigenbasis or spectral gap is an input. The displayed spectral spaces
belong to the actual operators with their common derived scalar shift. -/
theorem exists_single_region_hard_truncation_spectral_comparison {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let A := ManyBody.BondInteraction.threeRegionHamiltonians l r Φ
    let J := Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
    let Y := ∑ i ∈ J, Φ.term i
    ∃ (e : Fin 3 → ℝ) (x z : (Fin L → Fin q) → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
      (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧ (∀ j, 0 ≤ e j) ∧
      let H := Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ 2 ∧
      ∀ η t : ℝ, 0 < η → η + 7 ≤ t →
        let F := energyTruncation (A 1) (e 1 + t) + A 0 + A 2 + Y -
          (((∑ j, e j) : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian)
          (E' : ℝ) (z' : (Fin L → Fin q) → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • 1).PosSemidef ∧ 0 ≤ E' ∧ E' ≤ 2 ∧
          let ξ := 32 * Real.exp (-(t - η) / 8)
          let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
            finrank_euclideanSpace
          let bF := (isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
            finrank_euclideanSpace
          ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η))‖ ≤
              ξ ∧
          ‖((toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η))‖ ≤
              ξ ∧
          (∀ i : Fin (Fintype.card (Fin L → Fin q)), hF.eigenvalues₀ i ≤ E + η →
            hF.eigenvalues₀ i ≤ hH.eigenvalues₀ i ∧
              hH.eigenvalues₀ i ≤ hF.eigenvalues₀ i + ξ) ∧
          E' ≤ E ∧ E ≤ E' + ξ ∧
          ∀ δ : ℝ, 0 < δ →
            let η' := η + ξ + 2 * ξ * Real.sqrt ((⌈η / (2 * ξ)⌉₊ : ℝ) / δ)
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η'))
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η)) ∧
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η'))
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η)) := by
  intro A J Y
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hElow, hE0, hE2, hclip⟩ :=
    exists_single_region_hard_truncation_residuals hq hlr hrL Φ h0 h1
  refine ⟨e, x, z, E, hx, hxe, he, he0, hz, hHz, hElow, hE0, hE2, ?_⟩
  intro η t hη ht F
  obtain ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'2, hresH, hresF⟩ :=
    hclip η t hη ht
  let ξ := 32 * Real.exp (-(t - η) / 8)
  have hξ : 0 < ξ := by dsimp only [ξ]; positivity
  let jmin : Fin (Fintype.card (Fin L → Fin q)) :=
    ⟨Fintype.card (Fin L → Fin q) - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩
  have hminH : minEigenvalue hH = E := by
    simpa using hH.minEigenvalue_eq_add_of_centered_ground 0 E z hz
      (by simpa using hHz) (by simpa using hElow)
  have hminF : minEigenvalue hF = E' := by
    simpa using hF.minEigenvalue_eq_add_of_centered_ground 0 E' z' hz'
      (by simpa using hFz') (by simpa using hE'low)
  have hlastH : hH.eigenvalues₀ jmin = E := hH.eigenvalues₀_last_eq_minEigenvalue.trans hminH
  have hlastF : hF.eigenvalues₀ jmin = E' := hF.eigenvalues₀_last_eq_minEigenvalue.trans hminF
  have hcompare (δ : ℝ) (hδ : 0 < δ) :=
    hH.groundEnergy_compare_and_isCloseTo_spectralSpanLE_of_norm_domRestrict_le
      hF hFH η ξ δ hη hξ hδ
  have hresult (δ : ℝ) (hδ : 0 < δ) := by
    have h := hcompare δ hδ
    dsimp only at h
    rw [hlastH, hlastF] at h
    exact h hresH hresF
  obtain ⟨hgroundLower, hgroundUpper, _hcloseH, _hcloseF⟩ := hresult 1 zero_lt_one
  refine ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'2,
    hresH, hresF, ?_, hgroundLower, hgroundUpper, ?_⟩
  · intro i hi
    exact ⟨hF.eigenvalues₀_mono hH hFH i,
      hH.eigenvalues₀_le_add_of_norm_domRestrict_low_le hF (E + η) ξ hresF i hi⟩
  · intro δ hδ
    exact ⟨(hresult δ hδ).2.2.1, (hresult δ hδ).2.2.2⟩

end TNLean.MPS.AreaLaw.ALVV

end

end HardTruncation
