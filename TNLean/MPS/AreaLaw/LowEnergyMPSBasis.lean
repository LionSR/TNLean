/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowDensityDesignatedApproximation
import TNLean.MPS.AreaLaw.OpenMPSSpan
import QICLean.Analysis.ApproximateBasisImage
import QICLean.Analysis.ViableSubspaceOrder

/-!
# A matrix product basis for an approximation to an original low-energy band

A common rank factor is chosen before an orthonormal basis of the actual
inner band. Approximate its basis vectors with the proved physical MPS
construction, then take the actual linear image of that basis. Summed
squared errors prove injectivity, the exact dimension, and closeness in
both directions. Every vector of the resulting space is a linear
combination of the same MPS family. Its actual standard orthonormal basis
therefore has the additional honest generator-count bond factor.

This is a mathematical basis-existence consequence of ALVV,
arXiv:1602.08828v2, introductory statement at line 288 and Theorem
`thm:al-ld`, lines 1096–1105. It is not the probabilistic efficient
algorithm in Theorem `t:alg2`, lines 1869–1874, and makes no running-time
or energy-eigenstate assertion. The zero inner band, scalar local space
and empty chain are included.
-/

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- The actual basis-defined linear image of the original inner band has
its exact dimension, approximates it in both directions, and has a native
orthonormal MPS basis. The factor is chosen before the basis and vectors.
Mathematical basis consequence of ALVV, arXiv:1602.08828v2, line 288 and
Theorem `thm:al-ld`, lines 1096–1105; no algorithmic conclusion is claimed. -/
theorem exists_fixed_bandwidth_low_energy_orthonormal_mps_basis
    (etaLD : ℝ) (hLD : 0 < etaLD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L q : ℕ) (v : ℝ) (hq : 0 < q), 0 < v →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
          (h i) (interval L i.val (i.val + 2)))
        (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1),
      let _ : Nonempty (Fin L → Fin q) :=
        ⟨fun _ ↦ ⟨0, hq⟩⟩
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      let G := fun c : ℝ ↦ Submodule.spectralSpanLE
        hH.eigenvectorBasis hH.eigenvalues (minEigenvalue hH + c)
      let rInner := Module.finrank ℂ (G (etaLD - v))
      let rOuter := Module.finrank ℂ (G etaLD)
      let g := min (min v (etaLD / 2) / 6) 1
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      let eps := delta / (8 * ((rInner : ℝ) + 1))
      let a := 16 + Real.log (1 / g) +
        Real.log (1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / delta)
      ∃ B : ℕ, 1 ≤ B ∧ Real.log (B : ℝ) ≤
        K * (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) * u) *
          (1 + Real.log a) ∧
      let targetBasis := stdOrthonormalBasis ℂ (G (etaLD - v))
      ∃ phi : Fin rInner → EuclideanSpace ℂ (Fin L → Fin q),
        (∀ i, ‖phi i‖ = 1 ∧ IsOpenMPS L q (rOuter * B) (fun x ↦ phi i x) ∧
          ‖phi i - (targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤ eps / 2) ∧
      let F := targetBasis.toBasis.constr ℂ phi
      let V := LinearMap.range F
      Function.Injective F ∧ Module.finrank ℂ V = rInner ∧ Module.finrank ℂ V ≤ rOuter ∧
        V = Submodule.span ℂ (Set.range phi) ∧
        Submodule.IsCloseTo delta V (G (etaLD - v)) ∧
        Submodule.IsCloseTo delta (G (etaLD - v)) V ∧
        Submodule.IsCloseTo delta (G etaLD) V ∧
        (∀ x ∈ V, IsOpenMPS L q (rInner * rOuter * B) (fun w ↦ x w)) ∧
      let basis := stdOrthonormalBasis ℂ V
      ∀ i, IsOpenMPS L q (rInner * rOuter * B)
        (fun w ↦ (basis i : EuclideanSpace ℂ (Fin L → Fin q)) w) := by
  classical
  obtain ⟨K, hK, hactual⟩ :=
    exists_fixed_bandwidth_low_energy_designated_isOpenMPS_approximation etaLD hLD
  refine ⟨K, hK, ?_⟩
  intro L q v hq hv h hs h0 h1 config H hH G rInner rOuter g u
    delta hdelta hdelta1 eps a
  let : Nonempty (Fin L → Fin q) := config
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have heps1 : eps ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * ((rInner : ℝ) + 1))).2
    have hn : 0 ≤ (rInner : ℝ) := Nat.cast_nonneg rInner
    linarith only [hdelta1, hn]
  obtain ⟨Bs, B, hBs, hBsg, _hlogs, hlogB, hvec⟩ :=
    hactual L q v hq hv h hs h0 h1 eps heps heps1
  have hscale : 128 * ((L : ℝ) + 1) / eps =
      1024 * ((L : ℝ) + 1) * ((rInner : ℝ) + 1) / delta := by
    dsimp only [eps]
    field_simp
    ring
  rw [hscale] at hlogB
  refine ⟨B, hBs.trans hBsg, hlogB, ?_⟩
  intro targetBasis
  have happrox (i : Fin rInner) :
      ∃ x : EuclideanSpace ℂ (Fin L → Fin q), ‖x‖ = 1 ∧
        IsOpenMPS L q (rOuter * B) (fun w ↦ x w) ∧
        ‖x - (targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤ eps / 2 := by
    have hn : ‖(targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ = 1 :=
      targetBasis.norm_eq_one i
    obtain ⟨x, hx, hmps, _hrank, _hoverlap, hdist⟩ :=
      hvec 0 (targetBasis i) (targetBasis i).property hn
    exact ⟨x, hx, hmps, hdist⟩
  choose phi hnorm hmps herr using happrox
  refine ⟨phi, fun i ↦ ⟨hnorm i, hmps i, herr i⟩, ?_⟩
  intro F V
  have hsum : (∑ i, ‖phi i -
      (targetBasis i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2) ≤ delta / 16 := by
    calc
      _ ≤ ∑ _i : Fin rInner, eps / 2 := Finset.sum_le_sum fun i _ ↦ herr i
      _ = (rInner : ℝ) * (eps / 2) := by simp
      _ = ((rInner : ℝ) * delta) / (16 * ((rInner : ℝ) + 1)) := by
        dsimp only [eps]
        field_simp
        ring
      _ ≤ delta / 16 := by
        apply (div_le_iff₀ (by positivity : 0 < 16 * ((rInner : ℝ) + 1))).2
        nlinarith only [hdelta]
  obtain ⟨hinj, hdim, hspan, hVT, hTV⟩ :=
    OrthonormalBasis.range_constr_isCloseTo_of_sum_norm_sq_le (G (etaLD - v))
      targetBasis phi (delta / 16) (by linarith only [hdelta1]) hsum
  have hmono : G (etaLD - v) ≤ G etaLD :=
    Submodule.spectralSpanLE_mono_cutoff hH.eigenvectorBasis hH.eigenvalues
      (by linarith only [hv])
  have hforward : Submodule.IsCloseTo delta V (G (etaLD - v)) :=
    hVT.of_le (by linarith only [hdelta])
  have hback : Submodule.IsCloseTo delta (G (etaLD - v)) V :=
    hTV.of_le (by linarith only [hdelta])
  have hall : ∀ x ∈ V, IsOpenMPS L q (rInner * rOuter * B) (fun w ↦ x w) := by
    intro x hx
    let R : EuclideanSpace ℂ (Fin L → Fin q) →ₗ[ℂ] ((Fin L → Fin q) → ℂ) :=
      (WithLp.linearEquiv 2 ℂ ((Fin L → Fin q) → ℂ)).toLinearMap
    have hxspan : x ∈ Submodule.span ℂ (Set.range phi) := by
      rw [← hspan]
      exact hx
    have hxread : R x ∈ Submodule.span ℂ (Set.range (fun i ↦ R (phi i))) := by
      simpa only [← Set.range_comp, Function.comp_def] using
        Submodule.apply_mem_span_image_of_mem_span R hxspan
    simpa [R, Nat.mul_assoc] using
      isOpenMPS_of_mem_span_range (fun i ↦ R (phi i)) hmps hxread
  refine ⟨hinj, hdim, ?_, hspan, hforward, hback, hback.mono hmono, hall, ?_⟩
  · rw [hdim]
    exact Submodule.finrank_mono hmono
  · intro basis i
    exact hall (basis i) (basis i).property

end TNLean.MPS.AreaLaw
