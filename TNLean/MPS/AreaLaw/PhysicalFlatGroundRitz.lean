/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalFilterIteration
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import QICLean.Analysis.RitzCompression
import QICLean.Analysis.ViableSubspaceDimension

/-!
# Exact Ritz extraction from the same root in the flat case

Under a spectral gap implication, absence of an excited spectral value makes
all eigenvalues equal to the ground energy. The original ground space is the
whole space. A candidate approximating it with error below one is therefore
that same whole space, not an independently chosen approximation.

Zero rounds of the literal filter-and-trim operation retain the given root.
Its actual full-rank Ritz space is exact, and every vector has MPS bond at
most the ground multiplicity, hence at most the supplied dimension bound.
The raw filter is not applied; it may vanish for a scalar Hamiltonian.

This is the flat-case auxiliary for a gap-implication-only formulation of
ALVV, arXiv:1602.08828v2, final extraction in Figure `fig:algo1`, lines
1641–1643 and 1814–1817. The source's nonflat `(DG)` assumption is not
replaced by an extra excited-value hypothesis in such a formulation.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A given root close to the full ground space is retained exactly when
there is no excited spectral value. Zero literal refinement rounds and the
actual same-root Ritz extraction give zero error and bond at most the ground
multiplicity or the supplied count. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1641–1643 and 1814–1817. -/
theorem flat_ground_same_root_ritz_exact {L q count : ℕ}
    {H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (hH : H.IsHermitian)
    (mu gamma delta : ℝ) (hgamma : 0 < gamma) (hmu : mu ∈ spectrum ℝ H)
    (hgap : ∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z)
    (hflat : ¬ ∃ nu ∈ spectrum ℝ H, mu < nu)
    (S0 : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)))
    (hcount : Module.finrank ℂ S0 ≤ count) :
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    let r := Module.finrank ℂ G
    let Kraw := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (1 - ‖H‖⁻¹ • H)
    Submodule.IsCloseTo delta (nativeFullIntervalSpace L q S0) G → delta < 1 →
    ∀ xi : ℝ,
    let S := fullIntervalFilterTrimIterate L q Kraw xi S0 0
    let W := nativeFullIntervalSpace L q S
    let R := W.ritzSubspace (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
    G = ⊤ ∧ S0 = ⊤ ∧ S = S0 ∧ W = G ∧ R = W ∧
      Module.finrank ℂ R = r ∧
      Submodule.IsCloseTo 0 G R ∧ Submodule.IsCloseTo 0 R G ∧ r ≤ count ∧
      ∀ v ∈ R, IsOpenMPS L q r (fun x ↦ v x) ∧
        IsOpenMPS L q count (fun x ↦ v x) := by
  classical
  intro G r Kraw hclose hdelta xi S W R
  have heig (i) : hH.eigenvalues i = mu := by
    rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with hi | hi
    · exact hi
    · exact False.elim (hflat ⟨_, hH.eigenvalues_mem_spectrum_real i,
        by linarith only [hi, hgamma]⟩)
  have hGtop : G = ⊤ := by
    apply top_unique
    intro v _
    apply (Submodule.mem_spectralSpanLE_iff _ _ _ _).mpr
    intro i hi
    simp only [heig i, lt_self_iff_false] at hi
  have hWtop : W = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_le le_top
    have hdim := hclose.finrank_le hdelta
    change Module.finrank ℂ G ≤ Module.finrank ℂ W at hdim
    rw [hGtop] at hdim
    exact hdim
  have hWG : W = G := hWtop.trans hGtop.symm
  have hS0top : S0 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      Module.finrank ℂ S0 = Module.finrank ℂ W :=
        ((fullIntervalEquiv L q).toLinearEquiv.finrank_map_eq S0).symm
      _ = Module.finrank ℂ (EuclideanSpace ℂ (Fin L → Fin q)) := by rw [hWtop]; simp
      _ = Module.finrank ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)) :=
        (fullIntervalEquiv L q).toLinearEquiv.finrank_eq.symm
  have hdimW : Module.finrank ℂ W = r := by rw [hWG]
  have hRle : R ≤ W := W.ritzSubspace_le
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r
  have hdimR : Module.finrank ℂ R = r := W.finrank_ritzSubspace
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) r hdimW.ge
  have hRW : R = W := Submodule.eq_of_le_of_finrank_eq hRle (hdimR.trans hdimW.symm)
  have hGR : Submodule.IsCloseTo 0 G R := by
    rw [hRW, hWG]
    exact Submodule.isCloseTo_of_le (by norm_num) le_rfl
  have hRG : Submodule.IsCloseTo 0 R G := by
    rw [hRW, hWG]
    exact Submodule.isCloseTo_of_le (by norm_num) le_rfl
  have hrCount : r ≤ count := by
    calc
      r = Module.finrank ℂ W := hdimW.symm
      _ = Module.finrank ℂ S0 := (fullIntervalEquiv L q).toLinearEquiv.finrank_map_eq S0
      _ ≤ count := hcount
  refine ⟨hGtop, hS0top, rfl, hWG, hRW, hdimR, hGR, hRG, hrCount, ?_⟩
  have hconfig : Nonempty (Fin L → Fin q) := by
    by_contra hempty
    have : IsEmpty (Fin L → Fin q) := not_nonempty_iff.mp hempty
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hmu
  let config : Fin L → Fin q := Classical.choice hconfig
  intro v _
  have hv : IsOpenMPS L q r (fun x ↦ v x) := by
    apply (isOpenMPS_iff_internal_cutMatrix_rank_le v).mpr
    intro k hk0 hkL
    have hq : 1 ≤ q := by
      have hvalue := (config ⟨0, by omega⟩).isLt
      omega
    calc
      (cutMatrix v k).rank ≤
          Fintype.card ((w : {w : Fin L // w ∈ leftBlock L k}) → Fin q) :=
        Matrix.rank_le_card_height _
      _ = q ^ Fintype.card {w : Fin L // w ∈ leftBlock L k} := by simp
      _ ≤ q ^ L := Nat.pow_le_pow_right hq (by
        simpa using Fintype.card_subtype_le (fun w : Fin L ↦ w ∈ leftBlock L k))
      _ = r := by
        change q ^ L = Module.finrank ℂ G
        rw [hGtop]
        simp
  exact ⟨hv, hv.mono hrCount⟩

end TNLean.MPS.AreaLaw
