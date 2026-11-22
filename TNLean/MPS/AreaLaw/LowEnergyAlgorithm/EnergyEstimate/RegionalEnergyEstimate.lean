/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.Truncation.HardTruncationResidual
import QICLean.ManyBody.Entropy.ZeroEntropy
import QICLean.Analysis.Order.QuadraticScalarShift
import QICLean.ManyBody.Entropy.Cut.RegionalOperatorCoordinates
import QICLean.Spectral.Eigenvalue.CompressionEnergyInterval
import QICLean.Analysis.TensorProduct.MatrixTensorCoordinates
import QICLean.Analysis.Subspace.ViableSubspaceCoordinates
import QICLean.ManyBody.Sites.RegionMatrix
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Replica.RelativePin

/-!
# Native interval compressed energy estimates

The actual matrix on an interval is chosen before the candidate space.
A sufficiently viable candidate has compressed minimum within three of
that matrix's genuine minimum. Subtracting three gives a one-sided
estimate. This is a variational auxiliary for ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632, and its
correctness proof at lines 1793–1807. No filtering procedure or running
time is asserted here. The explicit candidate loss bound
`1 / (100 * (L + 1))` does not follow from a constant-accuracy tree.
The source energy estimate compresses the generated soft Hamiltonian;
closing that estimate requires its own quantitative energy argument.
-/

open ManyBody (interval mem_interval)

open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator TensorProduct Kronecker

namespace TNLean.MPS.AreaLaw

open Matrix

/-- The native interval operator and its minimum are chosen before every
candidate. A candidate viable for the full original ground space has an
actual compressed minimum within three of the regional minimum.
Subtracting three gives a one-sided estimate. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632, and lines 1793–1807. -/
theorem exists_native_regional_compressed_energy_estimate {L q l r : ℕ}
    (hq : 0 < q) (hlr : l ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let _ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
    let H := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH)
    let J := interval L l r
    let beta := fun _ : Fin L ↦ Fin q
    let tau := (ManyBody.cutEquiv beta J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun (ManyBody.ComplConfig beta J) ℂ).tensorProduct
      (EuclideanSpace.basisFun (ManyBody.RegionConfig beta J) ℂ)).repr
    let Tm := (U.trans Phi.symm).trans (TensorProduct.commIsometry ℂ
      (EuclideanSpace ℂ (ManyBody.ComplConfig beta J))
      (EuclideanSpace ℂ (ManyBody.RegionConfig beta J)))
    ∃ (K : Matrix (J → Fin q) (J → Fin q) ℂ) (hK : K.IsHermitian),
      aklvRegionalHamiltonians l r Φ 1 = ManyBody.place (X := fun _ ↦ Fin q) J K ∧
      let _ : Nonempty (J → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
      let e := minEigenvalue hK
      ∀ (δ : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q))),
        0 ≤ δ → δ ≤ 1 / (100 * ((L : ℝ) + 1)) →
        Submodule.IsViable (F := EuclideanSpace ℂ ({x // x ∉ J} → Fin q)) δ S
          (G.map Tm.toLinearEquiv.toLinearMap) →
        ∃ (n : ℕ) (hn : Module.finrank ℂ S = n + 1),
          let lam := (S.orthogonalCompression_isSymmetric
            (isSymmetric_toEuclideanLin_iff.mpr hK)).eigenvalues hn (Fin.last n)
          e ≤ lam ∧ lam ≤ e + 3 ∧ e - 3 ≤ lam - 3 ∧ lam - 3 ≤ e := by
  classical
  intro config H hH G J beta tau U Phi Tm
  let : Nonempty (Fin L → Fin q) := config
  let : Nonempty (J → Fin q) := ⟨fun _ ↦ ⟨0, hq⟩⟩
  let σ0 : Fin L → Fin q := fun _ ↦ ⟨0, hq⟩
  let y0 := ((ManyBody.cutEquiv (fun _ ↦ Fin q) J) σ0).2
  let g : (J → Fin q) → (Fin L → Fin q) := fun x ↦
    (ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm (x, y0)
  have hginj : Function.Injective g := by
    intro x y heq
    exact congrArg Prod.fst ((ManyBody.cutEquiv (fun _ ↦ Fin q) J).symm.injective heq)
  let A := aklvRegionalHamiltonians l r Φ 1
  let K := A.submatrix g g
  have hAs : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) A J := by
    change _ ∈ ManyBody.supportedOperators _ _
    apply sum_mem
    intro i hi
    apply (Φ.mem i).mono
    intro v hv
    have hi' : l ≤ i.val ∧ i.val + 1 < r := (Finset.mem_filter.mp hi).2
    rw [mem_interval] at hv ⊢
    omega
  have hApos : A.PosSemidef := (Finset.sum_nonneg fun i _ ↦ h0 i).posSemidef
  have hK : K.IsHermitian := hApos.isHermitian.submatrix g
  have hAK : A = ManyBody.place (X := fun _ ↦ Fin q) J K := by
    obtain ⟨K', hAK'⟩ := ManyBody.exists_eq_place_of_mem_supportedOperators hAs
    have hKK' : K = K' := by
      ext x y
      change ManyBody.cutOperator J A (x, y0) (y, y0) = K' x y
      rw [hAK', ManyBody.cutOperator_place]
      simp
    rw [hKK']
    exact hAK'
  obtain ⟨e0, x0, hx0, hAx0, hC, hCnorm, hground, hproject⟩ :=
    exists_regional_ground_energy_bound hq hlr hrL Φ h0 h1
  have hKlow : (K - (e0 : ℂ) • 1).PosSemidef := by
    have hC' : (A - (e0 : ℂ) • 1).PosSemidef := hC
    have hsub := hC'.submatrix g
    change (A.submatrix g g - (e0 : ℂ) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ).submatrix g g).PosSemidef at hsub
    rw [submatrix_one g hginj] at hsub
    exact hsub
  have hlift (s : ℝ) : ManyBody.place (X := fun _ ↦ Fin q) J
      (K - (s : ℂ) • 1) = A - (s : ℂ) • 1 := by
    have hsub : ManyBody.place (X := fun _ ↦ Fin q) J (K - (s : ℂ) • 1) =
        ManyBody.place J K - ManyBody.place J ((s : ℂ) • 1) :=
      ManyBody.place_sub _ _
    rw [hsub, ManyBody.place_smul, ManyBody.place_one, ← hAK]
  let e := minEigenvalue hK
  have hKmin : (K - (e : ℂ) • 1).PosSemidef := sub_minEigenvalue_smul_one_posSemidef hK
  have hAlow : (A - (e : ℂ) • 1).PosSemidef := by
    rw [← hlift e]
    exact (hKmin.kronecker (PosSemidef.one :
      (1 : Matrix ({v : Fin L // v ∉ J} → Fin q)
        ({v : Fin L // v ∉ J} → Fin q) ℂ).PosSemidef)).submatrix
      (ManyBody.cutEquiv (fun _ ↦ Fin q) J)
  have he0 : e0 = e :=
    minEigenvalue_eq_of_attained_lower_bounds A K hK e0 x0 hx0 hAx0 hKlow hAlow
  have hTA (v : EuclideanSpace ℂ (Fin L → Fin q)) :
      Tm (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) A v) =
        TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) K)
          (1 : EuclideanSpace ℂ ({x // x ∉ J} → Fin q) →L[ℂ]
            EuclideanSpace ℂ ({x // x ∉ J} → Fin q)) (Tm v) := by
    have hh : Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) A ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) K)
        (1 : EuclideanSpace ℂ ({x // x ∉ J} → Fin q) →L[ℂ]
          EuclideanSpace ℂ ({x // x ∉ J} → Fin q)) := by
      rw [hAK]
      exact Entropy.localLift_middleFirst_conjugation J K
    have hv := congrArg (fun f ↦ f (Tm v)) hh
    change Tm (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) A (Tm.symm (Tm v))) = _ at hv
    rw [Tm.symm_apply_apply] at hv
    exact hv
  refine ⟨K, hK, hAK, ?_⟩
  intro localConfig eChosen δ S hδ0 hδsmall hviable
  let V := (S.tensorProd (⊤ : Submodule ℂ (EuclideanSpace ℂ ({x // x ∉ J} → Fin q)))).comap
    Tm.toLinearEquiv.toLinearMap
  have hmap : V.map Tm.toLinearEquiv.toLinearMap = S.tensorProd
      (⊤ : Submodule ℂ (EuclideanSpace ℂ ({x // x ∉ J} → Fin q))) :=
    Submodule.map_comap_eq_of_surjective Tm.surjective _
  have hclose : Submodule.IsCloseTo δ V G := by
    apply (Submodule.isCloseTo_map_iff Tm).mp
    rw [hmap]
    exact hviable
  obtain ⟨_hwhole, v, hv, hvne, hvenergy⟩ := hproject δ V hδ0 hδsmall hclose
  have hAv : (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) A v) v).re ≤
      (e + 3) * ‖v‖ ^ 2 := by
    change (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (A - (e0 : ℂ) • 1) v) v).re ≤ 3 * ‖v‖ ^ 2 at hvenergy
    rw [he0] at hvenergy
    rw [Matrix.re_inner_toEuclideanCLM_sub_ofReal_smul_one A e v] at hvenergy
    nlinarith only [hvenergy]
  have hwenergy : (inner ℂ
      (TensorProduct.mapL (toEuclideanCLM (𝕜 := ℂ) (n := J → Fin q) K)
        (1 : EuclideanSpace ℂ ({x // x ∉ J} → Fin q) →L[ℂ]
          EuclideanSpace ℂ ({x // x ∉ J} → Fin q)) (Tm v)) (Tm v)).re ≤
        (e + 3) * ‖Tm v‖ ^ 2 := by
    rw [← hTA v, Tm.inner_map_map, Tm.norm_map]
    exact hAv
  have hwne : Tm v ≠ 0 := by
    intro heq
    exact hvne (Tm.injective (heq.trans Tm.map_zero.symm))
  obtain ⟨n, hn, hlower, hlam⟩ := hK.exists_compression_min_between_of_tensor_energy
    S e (e + 3) hKmin hv hwne hwenergy
  refine ⟨n, hn, hlower, hlam, ?_, ?_⟩
  · exact sub_le_sub_right hlower 3
  · exact (sub_le_iff_le_add).mpr hlam

end TNLean.MPS.AreaLaw
