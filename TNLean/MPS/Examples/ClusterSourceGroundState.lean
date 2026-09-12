/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ClusterParentHamiltonian
import TNLean.Algebra.ListProduct
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.SharedInfra.Scaling

/-!
# Ground state of the source cluster tensor

The matrices displayed for the one-dimensional cluster state in
Pérez-García--Verstraete--Wolf--Cirac, arXiv:quant-ph/0608197, local TeX lines
374--387, use the opposite stabilizer sign from `clusterTensor`. This module
transports the established cluster-state results through the explicit virtual
gauge and the physical action of `Z` on every site. It also proves the bottom
eigenspace and energy bound for the corresponding stabilizer sum by the same
sum-of-squares argument.

## Main statements

* `clusterSource_mpv_eq_globalZ` and `clusterSource_mpv_ne_zero` identify the
  source MPV with the globally `Z`-rotated cluster MPV and prove nonvanishing.
* `clusterSource_iInf_eigenspace_eq_mpvSubmodule` and
  `clusterSource_stabilizer_unique_gs` identify the common `-1` stabilizer
  eigenspace and prove its uniqueness.
* `clusterSource_hamiltonian_eigenspace_eq_mpvSubmodule` and
  `clusterSource_energy_lower_bound` identify the bottom eigenspace of the
  stabilizer sum and prove its energy lower bound.

## References

* Pérez-García--Verstraete--Wolf--Cirac 2007, arXiv:quant-ph/0608197, local
  TeX lines 374--387.
-/

open scoped BigOperators Matrix ComplexConjugate

namespace MPSTensor

noncomputable section

/-- A virtual gauge relating the source and cluster tensors. -/
private def G : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 1, 1]

/-- The inverse of `G`. -/
private def Ginv : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; -1 / 2, 1 / 2]

private lemma gauge_inv : G * Ginv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [G, Ginv, Matrix.mul_apply, Fin.sum_univ_two]

private lemma inv_gauge : Ginv * G = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [G, Ginv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The pointwise gauge and physical-sign identity for the two tensors. -/
private lemma source_tensor_relation (t : Fin 2) :
    (↑(1 / Real.sqrt 2) : ℂ) • clusterSourceTensor t =
      (-1 : ℂ) ^ t.val • (G * clusterTensor t * Ginv) := by
  fin_cases t <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [G, Ginv, clusterSourceTensor, clusterTensor] <;> ring

/-- The global sign picked up by applying `Z` at every site. -/
private def paritySign {N : ℕ} (s : Fin N → Fin 2) : ℂ :=
  ∏ i : Fin N, (-1 : ℂ) ^ (s i).val

/-- The coefficient-space action of on-site `Z` at every site. -/
private def globalZ {N : ℕ} : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N where
  toFun v s := paritySign s * v s
  map_add' v w := by
    ext s
    simp only [mul_add, Pi.add_apply]
  map_smul' c v := by
    ext s
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

@[simp] private lemma globalZ_apply {N : ℕ} (v : NSiteSpace 2 N) (s : Fin N → Fin 2) :
    globalZ v s = paritySign s * v s := rfl

/-- The invertible virtual gauge relating the source and cluster tensors. -/
private def Gunit : GL (Fin 2) ℂ where
  val := G
  inv := Ginv
  val_inv := gauge_inv
  inv_val := inv_gauge

@[simp] private lemma Gunit_val : (Gunit : Matrix (Fin 2) (Fin 2) ℂ) = G := rfl

@[simp] private lemma Gunit_inv_val :
    ((Gunit⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Ginv := rfl

/-- The global on-site `Z` action multiplies every cluster coefficient by its parity sign. -/
private lemma mpv_signedCluster {N : ℕ} (s : Fin N → Fin 2) :
    mpv (fun t : Fin 2 => (-1 : ℂ) ^ t.val • clusterTensor t) s =
      paritySign s * mpv clusterTensor s := by
  simp only [mpv, coeff, evalWord_ofFn_eq_prod]
  rw [List.prod_ofFn_smul, Matrix.trace_smul]
  rfl

/-- The normalized source tensor is gauge-equivalent to the physically
`Z`-rotated cluster tensor. -/
private lemma scaledSource_gauge_rotatedCluster :
    GaugeEquiv (fun t : Fin 2 => (-1 : ℂ) ^ t.val • clusterTensor t)
      (fun t : Fin 2 => (↑(1 / Real.sqrt 2) : ℂ) • clusterSourceTensor t) := by
  refine ⟨Gunit, fun t => ?_⟩
  change (↑(1 / Real.sqrt 2) : ℂ) • clusterSourceTensor t =
    G * (((-1 : ℂ) ^ t.val) • clusterTensor t) * Ginv
  rw [source_tensor_relation]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The source MPV is `sqrt(2)^N` times the global on-site `Z` transform of the
normalized library cluster MPV.

See arXiv:quant-ph/0608197, local TeX lines 374--387. -/
theorem clusterSource_mpv_eq_globalZ {N : ℕ} (_hN : 3 ≤ N) (s : Fin N → Fin 2) :
    mpv clusterSourceTensor s = (↑(Real.sqrt 2) : ℂ) ^ N *
      (∏ i, (-1 : ℂ) ^ (s i).val) * mpv clusterTensor s := by
  have hsqrtR : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hgauge := scaledSource_gauge_rotatedCluster.sameMPV N s
  rw [mpv_smul, mpv_signedCluster] at hgauge
  change _ = (↑(Real.sqrt 2) : ℂ) ^ N * paritySign s * mpv clusterTensor s
  calc
    mpv clusterSourceTensor s =
        (↑(Real.sqrt 2) : ℂ) ^ N *
          ((↑(1 / Real.sqrt 2) : ℂ) ^ N * mpv clusterSourceTensor s) := by
            rw [← mul_assoc, ← mul_pow]
            simp [hsqrtR]
    _ = (↑(Real.sqrt 2) : ℂ) ^ N *
          (paritySign s * mpv clusterTensor s) := by rw [hgauge]
    _ = _ := by ring

/-- Bundled vector form of `clusterSource_mpv_eq_globalZ`. -/
private lemma source_mpv_vector_relation {N : ℕ} (hN : 3 ≤ N) :
    (mpv clusterSourceTensor : NSiteSpace 2 N) =
      (↑(Real.sqrt 2) : ℂ) ^ N • globalZ (mpv clusterTensor) := by
  funext s
  simp only [Pi.smul_apply, smul_eq_mul, globalZ_apply]
  simpa only [paritySign, mul_assoc] using clusterSource_mpv_eq_globalZ hN s

/-- Flipping the qubit at `j`. -/
private def flipConfig {N : ℕ} (j : Fin N) (s : Fin N → Fin 2) : Fin N → Fin 2 :=
  Function.update s j (s j + 1)

private lemma flipConfig_involutive {N : ℕ} (j : Fin N) :
    Function.Involutive (flipConfig j) := by
  intro s
  funext k
  by_cases hkj : k = j
  · subst k
    simp only [flipConfig, Function.update_self]
    generalize s j = x
    fin_cases x <;> rfl
  · simp [flipConfig, hkj]

private lemma flipConfig_bijective {N : ℕ} (j : Fin N) :
    Function.Bijective (flipConfig j) :=
  (flipConfig_involutive j).bijective

private lemma paritySign_ne_zero {N : ℕ} (s : Fin N → Fin 2) :
    paritySign s ≠ 0 := by
  simp only [paritySign]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (by norm_num)

private lemma paritySign_sq {N : ℕ} (s : Fin N → Fin 2) :
    paritySign s * paritySign s = 1 := by
  simp only [paritySign, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  generalize s i = x
  fin_cases x <;> norm_num

private lemma paritySign_flip {N : ℕ} (j : Fin N) (s : Fin N → Fin 2) :
    paritySign (flipConfig j s) = -paritySign s := by
  simp only [paritySign]
  rw [Fintype.prod_eq_prod_compl_mul j, Fintype.prod_eq_prod_compl_mul j]
  have hcompl :
      (∏ i ∈ {j}ᶜ, (-1 : ℂ) ^ ((flipConfig j s i).val)) =
        ∏ i ∈ {j}ᶜ, (-1 : ℂ) ^ ((s i).val) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := by simpa using hi
    simp [flipConfig, hij]
  rw [hcompl]
  have hsite :
      (-1 : ℂ) ^ ((flipConfig j s j).val) = -((-1 : ℂ) ^ ((s j).val)) := by
    simp only [flipConfig, Function.update_self]
    generalize s j = x
    fin_cases x
    · norm_num
    · norm_num [Fin.add_def]
  rw [hsite]
  ring

private lemma globalZ_involutive {N : ℕ} :
    Function.Involutive (fun v : NSiteSpace 2 N => globalZ v) := by
  intro v
  ext s
  simp only [globalZ_apply]
  rw [← mul_assoc, paritySign_sq]
  simp

private lemma globalZ_injective {N : ℕ} :
    Function.Injective (fun v : NSiteSpace 2 N => globalZ v) :=
  globalZ_involutive.injective

/-- Applying on-site `Z` at every site anticommutes with every translated `ZXZ`
stabilizer. -/
private lemma globalZ_anticommute {N : ℕ} (i : Fin N) (v : NSiteSpace 2 N) :
    clusterChainStabilizer i (globalZ v) = -globalZ (clusterChainStabilizer i v) := by
  ext s
  simp only [clusterChainStabilizer_apply, globalZ_apply, Pi.neg_apply]
  change
    (-1 : ℂ) ^ ((s i).val + (s (cyclicForwardSite i 2)).val) *
        (paritySign (flipConfig (cyclicForwardSite i 1) s) *
          v (flipConfig (cyclicForwardSite i 1) s)) =
      -(paritySign s *
        ((-1 : ℂ) ^ ((s i).val + (s (cyclicForwardSite i 2)).val) *
          v (flipConfig (cyclicForwardSite i 1) s)))
  rw [paritySign_flip]
  ring

private lemma globalZ_mem_common_neg_of_plus {N : ℕ} (v : NSiteSpace 2 N)
    (hv : v ∈ ⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) 1) :
    globalZ v ∈ ⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) (-1) := by
  rw [Submodule.mem_iInf] at hv ⊢
  intro i
  have hi := hv i
  rw [Module.End.mem_eigenspace_iff] at hi ⊢
  rw [globalZ_anticommute, hi]
  simp

private lemma globalZ_mem_common_plus_of_neg {N : ℕ} (v : NSiteSpace 2 N)
    (hv : v ∈ ⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) (-1)) :
    globalZ v ∈ ⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) 1 := by
  rw [Submodule.mem_iInf] at hv ⊢
  intro i
  have hi := hv i
  rw [Module.End.mem_eigenspace_iff] at hi ⊢
  rw [globalZ_anticommute, hi]
  simp

private lemma source_span_eq_globalZ_cluster_span {N : ℕ} (hN : 3 ≤ N) :
    mpvSubmodule clusterSourceTensor N =
      Submodule.span ℂ {globalZ (mpv clusterTensor : NSiteSpace 2 N)} := by
  rw [mpvSubmodule, source_mpv_vector_relation hN]
  apply Submodule.span_singleton_smul_eq
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero N
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by norm_num))))))

/-- Nonvanishing transported from the normalized cluster MPV through the
invertible global `Z` action and the nonzero scalar `sqrt(2)^N`.

See arXiv:quant-ph/0608197, local TeX lines 374--387. -/
theorem clusterSource_mpv_ne_zero {N : ℕ} (hN : 3 ≤ N) :
    (mpv clusterSourceTensor : NSiteSpace 2 N) ≠ 0 := by
  have hcluster : (mpv clusterTensor : NSiteSpace 2 N) ≠ 0 :=
    mpv_ne_zero_of_isNBlkInjective cluster_isNBlkInjective_two
      (by norm_num) (by omega)
  intro hsource
  have hrel := source_mpv_vector_relation hN
  rw [hsource] at hrel
  have hz : globalZ (mpv clusterTensor : NSiteSpace 2 N) = 0 := by
    apply (smul_eq_zero.mp hrel.symm).resolve_left
    exact pow_ne_zero N
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by norm_num))))
  exact hcluster (globalZ_injective (by simpa using hz))

/-- The common source `-1` eigenspace is obtained from the normalized cluster
`+1` eigenspace by the involutive global on-site `Z` action.

See arXiv:quant-ph/0608197, local TeX lines 374--387. -/
theorem clusterSource_iInf_eigenspace_eq_mpvSubmodule {N : ℕ} (hN : 3 ≤ N) :
    (⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) (-1)) =
      mpvSubmodule clusterSourceTensor N := by
  rw [source_span_eq_globalZ_cluster_span hN]
  apply le_antisymm
  · intro v hv
    have hzplus := globalZ_mem_common_plus_of_neg v hv
    have hzspan : globalZ v ∈ mpvSubmodule clusterTensor N := by
      rw [← cluster_iInf_eigenspace_eq_mpvSubmodule hN]
      exact hzplus
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hzspan
    rw [Submodule.mem_span_singleton]
    obtain ⟨c, hc⟩ := hzspan
    refine ⟨c, ?_⟩
    have hzc := congrArg (fun w : NSiteSpace 2 N => globalZ w) hc
    simpa only [map_smul, globalZ_involutive v] using hzc
  · intro v hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, hc⟩ := hv
    have hzc := congrArg (fun w : NSiteSpace 2 N => globalZ w) hc
    have hzspan : globalZ v ∈ mpvSubmodule clusterTensor N := by
      rw [mpvSubmodule, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      simpa only [map_smul,
        globalZ_involutive (mpv clusterTensor : NSiteSpace 2 N)] using hzc
    have hzplus : globalZ v ∈
        ⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) 1 := by
      rw [cluster_iInf_eigenspace_eq_mpvSubmodule hN]
      exact hzspan
    have hneg := globalZ_mem_common_neg_of_plus (globalZ v) hzplus
    simpa only [globalZ_involutive v] using hneg

/-- Uniqueness follows from the transported one-dimensional span, without an
injectivity proof for the source matrices.

See arXiv:quant-ph/0608197, local TeX lines 374--387. -/
theorem clusterSource_stabilizer_unique_gs {N : ℕ} (hN : 3 ≤ N) :
    HasUniqueGroundState
      (⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) (-1)) := by
  rw [clusterSource_iInf_eigenspace_eq_mpvSubmodule hN, mpvSubmodule]
  exact finrank_span_singleton (clusterSource_mpv_ne_zero hN)

/-! ### The stabilizer sum as a sum of squares -/

private def coefficientNormSq {N : ℕ} (v : NSiteSpace 2 N) : ℝ :=
  ∑ s, Complex.normSq (v s)

private def stabilizerEnergy {N : ℕ} (i : Fin N) (v : NSiteSpace 2 N) : ℝ :=
  ∑ s, (star (v s) * (clusterChainStabilizer i v) s).re

private def hamiltonianEnergy {N : ℕ} (v : NSiteSpace 2 N) : ℝ :=
  ∑ s, (star (v s) * ((∑ i : Fin N, clusterChainStabilizer i) v) s).re

private lemma normSq_add_eq_star_mul_re (z w : ℂ) :
    Complex.normSq (z + w) =
      Complex.normSq z + Complex.normSq w + 2 * (star z * w).re := by
  rw [Complex.normSq_add]
  change Complex.normSq z + Complex.normSq w + 2 * (z * conj w).re =
    Complex.normSq z + Complex.normSq w + 2 * (conj z * w).re
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma stabilizer_normSq_apply {N : ℕ} (i : Fin N) (v : NSiteSpace 2 N)
    (s : Fin N → Fin 2) :
    Complex.normSq ((clusterChainStabilizer i v) s) =
      Complex.normSq (v (flipConfig (cyclicForwardSite i 1) s)) := by
  simp only [clusterChainStabilizer_apply]
  change Complex.normSq
      ((-1 : ℂ) ^ ((s i).val + (s (cyclicForwardSite i 2)).val) *
        v (flipConfig (cyclicForwardSite i 1) s)) = _
  rw [Complex.normSq_mul, map_pow]
  norm_num

private lemma stabilizer_preserves_coefficientNormSq {N : ℕ} (i : Fin N)
    (v : NSiteSpace 2 N) :
    ∑ s, Complex.normSq ((clusterChainStabilizer i v) s) = coefficientNormSq v := by
  simp_rw [stabilizer_normSq_apply]
  exact (flipConfig_bijective (cyclicForwardSite i 1)).sum_comp
    (fun s => Complex.normSq (v s))

private lemma hamiltonianEnergy_eq_sum_stabilizerEnergy {N : ℕ}
    (v : NSiteSpace 2 N) :
    hamiltonianEnergy v = ∑ i : Fin N, stabilizerEnergy i v := by
  unfold hamiltonianEnergy stabilizerEnergy
  calc
    (∑ s, (star (v s) * ((∑ i : Fin N, clusterChainStabilizer i) v) s).re) =
        ∑ s, ∑ i : Fin N,
          (star (v s) * (clusterChainStabilizer i v) s).re := by
            apply Finset.sum_congr rfl
            intro s _
            simp only [LinearMap.sum_apply, Finset.sum_apply, Finset.mul_sum,
              Complex.re_sum]
    _ = _ := Finset.sum_comm

private lemma stabilizer_sumOfSquares {N : ℕ} (i : Fin N) (v : NSiteSpace 2 N) :
    (∑ s, Complex.normSq (v s + (clusterChainStabilizer i v) s)) =
      2 * (coefficientNormSq v + stabilizerEnergy i v) := by
  simp_rw [normSq_add_eq_star_mul_re]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    stabilizer_preserves_coefficientNormSq]
  unfold coefficientNormSq stabilizerEnergy
  rw [← Finset.mul_sum]
  ring

/-- The coefficient version of
`sum_i ‖(I + K_i)v‖² = 2 (N ‖v‖² + Re ⟨v,Hv⟩)`. -/
private lemma hamiltonian_sumOfSquares {N : ℕ} (v : NSiteSpace 2 N) :
    (∑ i : Fin N, ∑ s,
        Complex.normSq (v s + (clusterChainStabilizer i v) s)) =
      2 * ((N : ℝ) * coefficientNormSq v + hamiltonianEnergy v) := by
  rw [Finset.sum_congr rfl (fun i _ => stabilizer_sumOfSquares i v),
    hamiltonianEnergy_eq_sum_stabilizerEnergy]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

private lemma hamiltonianEnergy_eq_of_eigen {N : ℕ} (v : NSiteSpace 2 N)
    (hv : (∑ i : Fin N, clusterChainStabilizer i) v = (-(N : ℂ)) • v) :
    hamiltonianEnergy v = -(N : ℝ) * coefficientNormSq v := by
  unfold hamiltonianEnergy coefficientNormSq
  rw [hv]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (conj (v s) * (-(N : ℂ) * v s)).re =
    -(N : ℝ) * Complex.normSq (v s)
  rw [Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.neg_re, Complex.natCast_re, Complex.neg_im, Complex.natCast_im]
  ring

private lemma mem_common_neg_of_sumOfSquares_eq_zero {N : ℕ}
    (v : NSiteSpace 2 N)
    (hzero : (∑ i : Fin N, ∑ s,
      Complex.normSq (v s + (clusterChainStabilizer i v) s)) = 0) :
    v ∈ ⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) (-1) := by
  rw [Submodule.mem_iInf]
  intro i
  rw [Module.End.mem_eigenspace_iff]
  ext s
  have hi : (∑ s,
      Complex.normSq (v s + (clusterChainStabilizer i v) s)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun s _ => Complex.normSq_nonneg
        (v s + (clusterChainStabilizer i v) s))).mp hzero i (Finset.mem_univ i)
  have hs : Complex.normSq (v s + (clusterChainStabilizer i v) s) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
      Complex.normSq_nonneg (v s + (clusterChainStabilizer i v) s))).mp
        hi s (Finset.mem_univ s)
  have hz := Complex.normSq_eq_zero.mp hs
  simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul]
  rw [eq_neg_iff_add_eq_zero]
  simpa only [add_comm] using hz

/-- The bottom eigenspace of the stabilizer sum is exactly the common `-1`
eigenspace, hence the span of the source cluster MPV.

See arXiv:quant-ph/0608197, local TeX lines 374--387. -/
theorem clusterSource_hamiltonian_eigenspace_eq_mpvSubmodule {N : ℕ} (hN : 3 ≤ N) :
    Module.End.eigenspace (∑ i : Fin N, clusterChainStabilizer i) (-(N : ℂ)) =
      mpvSubmodule clusterSourceTensor N := by
  apply le_antisymm
  · intro v hv
    rw [← clusterSource_iInf_eigenspace_eq_mpvSubmodule hN]
    have hvHam : (∑ i : Fin N, clusterChainStabilizer i) v = (-(N : ℂ)) • v :=
      Module.End.mem_eigenspace_iff.mp hv
    apply mem_common_neg_of_sumOfSquares_eq_zero
    rw [hamiltonian_sumOfSquares, hamiltonianEnergy_eq_of_eigen v hvHam]
    ring
  · rw [← clusterSource_iInf_eigenspace_eq_mpvSubmodule hN]
    intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [Module.End.mem_eigenspace_iff]
    simp only [LinearMap.sum_apply]
    calc
      (∑ i : Fin N, clusterChainStabilizer i v) =
          ∑ i : Fin N, (-1 : ℂ) • v := by
            apply Finset.sum_congr rfl
            intro i _
            exact Module.End.mem_eigenspace_iff.mp (hv i)
      _ = (-(N : ℂ)) • v := by
        ext s
        simp [Pi.smul_apply, Finset.sum_const, smul_eq_mul]

/-- The Hamiltonian expectation is bounded below by minus `N` times the
coefficient-space squared norm.

See arXiv:quant-ph/0608197, local TeX lines 374--387. -/
theorem clusterSource_energy_lower_bound {N : ℕ} (_hN : 3 ≤ N) (v : NSiteSpace 2 N) :
    -(N : ℝ) * (∑ s, ‖v s‖ ^ 2) ≤
      (∑ s, star (v s) * ((∑ i : Fin N, clusterChainStabilizer i) v) s).re := by
  have hsos : 0 ≤
      (∑ i : Fin N, ∑ s,
        Complex.normSq (v s + (clusterChainStabilizer i v) s)) := by
    exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [hamiltonian_sumOfSquares] at hsos
  have hbound : -(N : ℝ) * coefficientNormSq v ≤ hamiltonianEnergy v := by
    nlinarith
  rw [Complex.re_sum]
  simpa only [coefficientNormSq, hamiltonianEnergy,
    Complex.normSq_eq_norm_sq] using hbound


end
end MPSTensor
