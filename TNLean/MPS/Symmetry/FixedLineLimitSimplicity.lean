/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith

/-!
# Stability of a fixed line under uniformly contracting spectral limits

Let a sequence of finite-dimensional complex operators converge, with one
common nonzero fixed vector. Suppose the eigenvalue one is algebraically
simple for every operator in the sequence, and every other eigenvalue has
modulus at most one fixed number q<1. Then the fixed space of the limiting
operator is exactly the original line.

The proof uses a fixed basis of the quotient by this line. Its operator
coordinates converge because they are continuous scalar functionals of the
original operators. Algebraic simplicity excludes one from each quotient
spectrum. The uniform contraction bounds the determinant of identity minus
the quotient operator away from zero, so one is also absent from the
limiting quotient spectrum.

These are finite-dimensional spectral statements. They do not deduce a
uniform transfer contraction from a physical Hamiltonian gap. Their source
context is the varying-support argument in arXiv:1010.3732, Appendix C,
lines 2653–2717.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open Filter Topology Module

private theorem norm_prod_sub_ge
    (z : ℂ) (q : ℝ) (hq : q ≤ ‖z‖) (s : Multiset ℂ)
    (hs : ∀ w ∈ s, ‖w‖ ≤ q) :
    (‖z‖ - q) ^ s.card ≤ ‖(s.map (fun w => z - w)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
    have hw : ‖z‖ - q ≤ ‖z - w‖ := by
      have h := norm_sub_norm_le z w
      have hw := hs w (Multiset.mem_cons_self w s)
      linarith
    have hrest : ∀ u ∈ s, ‖u‖ ≤ q := fun u hu =>
      hs u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul]
    rw [pow_succ']
    exact mul_le_mul hw (ih hrest) (pow_nonneg (sub_nonneg.mpr hq) _) (norm_nonneg _)

/-- A spectral bound separates the determinant from zero outside the closed disc. -/
private theorem Matrix.norm_det_scalar_sub_ge_of_spectrum_norm_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (z : ℂ) (q : ℝ) (hq : q ≤ ‖z‖)
    (hspec : ∀ w ∈ spectrum ℂ M, ‖w‖ ≤ q) :
    (‖z‖ - q) ^ Fintype.card n ≤ ‖(Matrix.scalar n z - M).det‖ := by
  have hsplits := IsAlgClosed.splits M.charpoly
  have hprod := hsplits.eval_eq_prod_roots_of_monic M.charpoly_monic z
  have hcard : M.charpoly.roots.card = Fintype.card n := by
    rw [← hsplits.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  have hbound := norm_prod_sub_ge z q hq M.charpoly.roots (fun w hw =>
    hspec w (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      ((Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hw)))
  rw [hcard, ← hprod, Matrix.eval_charpoly] at hbound
  exact hbound

/-- A uniform spectral contraction bounds the determinant away from zero. -/
private theorem Matrix.norm_det_one_sub_ge_of_spectrum_norm_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (q : ℝ) (hq : q ≤ 1)
    (hspec : ∀ z ∈ spectrum ℂ M, ‖z‖ ≤ q) :
    (1 - q) ^ Fintype.card n ≤ ‖(1 - M).det‖ := by
  simpa only [norm_one, map_one] using
    Matrix.norm_det_scalar_sub_ge_of_spectrum_norm_le M 1 q
      (by simpa only [norm_one] using hq) hspec

/-- The identity remains outside the spectrum of a limit with uniform spectral contraction. -/
private theorem Matrix.isUnit_one_sub_of_tendsto_of_uniform_spectrum_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : ℕ → Matrix n n ℂ) (M₀ : Matrix n n ℂ)
    (hM : Filter.Tendsto M Filter.atTop (nhds M₀))
    (q : ℝ) (hq : q < 1)
    (hspec : ∀ j z, z ∈ spectrum ℂ (M j) → ‖z‖ ≤ q) :
    IsUnit (1 - M₀) := by
  have hdet : Filter.Tendsto (fun j => ‖(1 - M j).det‖)
      Filter.atTop (nhds ‖(1 - M₀).det‖) := by
    exact ((continuous_const.sub continuous_id).matrix_det.norm).continuousAt.tendsto.comp hM
  have hbound : (1 - q) ^ Fintype.card n ≤ ‖(1 - M₀).det‖ :=
    ge_of_tendsto hdet (Filter.Eventually.of_forall fun j =>
      Matrix.norm_det_one_sub_ge_of_spectrum_norm_le (M j) q hq.le (hspec j))
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (norm_pos_iff.mp
    (lt_of_lt_of_le (pow_pos (sub_pos.mpr hq) _) hbound))


/-- Coordinates of operators on a fixed invariant quotient commute with limits.
No continuously chosen quotient basis is needed: the basis is fixed. -/
theorem Submodule.tendsto_toMatrix_mapQ_of_tendsto
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [Fintype ι] [DecidableEq ι]
    (p : Submodule ℂ V) (b : Basis ι ℂ (V ⧸ p))
    (f : ℕ → V →L[ℂ] V) (f₀ : V →L[ℂ] V)
    (hf : Tendsto f atTop (𝓝 f₀))
    (hp : ∀ n, p ≤ p.comap (f n : V →ₗ[ℂ] V))
    (hp₀ : p ≤ p.comap (f₀ : V →ₗ[ℂ] V)) :
    Tendsto (fun n => LinearMap.toMatrix b b (p.mapQ p (f n : V →ₗ[ℂ] V) (hp n)))
      atTop (𝓝 (LinearMap.toMatrix b b (p.mapQ p (f₀ : V →ₗ[ℂ] V) hp₀))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  obtain ⟨x, hx⟩ := p.mkQ_surjective (b j)
  have hEval : Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)) :=
    (ContinuousLinearMap.apply ℂ V x).continuous.continuousAt.tendsto.comp hf
  have hCoord : Continuous (fun y : V => b.repr (p.mkQ y) i) :=
    ((b.coord i).comp p.mkQ).continuous_of_finiteDimensional
  convert hCoord.continuousAt.tendsto.comp hEval using 1 <;>
    simp only [LinearMap.toMatrix_apply, ← hx, Submodule.mkQ_apply,
      Submodule.mapQ_apply, Function.comp_def, ContinuousLinearMap.coe_coe]

private theorem fixedLine_eq_maxGenEigenspace_of_simple
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) (v : V) (hv : v ≠ 0) (hfv : f v = v)
    (hSimple : f.charpoly.rootMultiplicity 1 = 1) :
    Submodule.span ℂ {v} = Module.End.maxGenEigenspace f 1 := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem ..).mpr
      (Module.End.eigenspace_le_maxGenEigenspace
        (Module.End.mem_eigenspace_iff.mpr (by simpa only [one_smul] using hfv)))
  · rw [finrank_span_singleton hv,
      LinearMap.finrank_maxGenEigenspace_eq, hSimple]

private theorem spectrum_fixedLineQuotient_subset
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) (v : V) (hv : v ≠ 0) (hfv : f v = v)
    (hSimple : f.charpoly.rootMultiplicity 1 = 1)
    (hp : Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap f) :
    spectrum ℂ ((Submodule.span ℂ {v}).mapQ (Submodule.span ℂ {v}) f hp) ⊆
      spectrum ℂ f \ {1} := by
  let p : Submodule ℂ V := Submodule.span ℂ {v}
  intro z hz
  obtain ⟨u, hu⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  obtain ⟨x, rfl⟩ := p.mkQ_surjective u
  have hrel : p.mkQ (f x - z • x) = 0 := by
    rw [map_sub, map_smul]
    exact sub_eq_zero.mpr (by
      simpa only [Submodule.mkQ_apply, Submodule.mapQ_apply] using hu.apply_eq_smul)
  have hmem : f x - z • x ∈ p := by
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hrel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp only [one_smul] at hc
    have hxGen : x ∈ Module.End.maxGenEigenspace f 1 :=
      (Module.End.mem_maxGenEigenspace f 1 x).mpr ⟨2, by
        simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply,
          Module.End.one_apply, one_smul, ← hc,
          map_smul, hfv, sub_self, smul_zero]⟩
    exact hu.2 ((Submodule.Quotient.mk_eq_zero p).mpr
      ((fixedLine_eq_maxGenEigenspace_of_simple f v hv hfv hSimple).ge hxGen))
  have hcoef : c + c / (z - 1) = z * (c / (z - 1)) := by
    field_simp [sub_ne_zero.mpr hz1]
    ring
  have hfCorr : f (x + (c / (z - 1)) • v) = z • (x + (c / (z - 1)) • v) := by
    simp only [map_add, map_smul, hfv, smul_add, smul_smul]
    rw [sub_eq_iff_eq_add.mp hc.symm, add_comm (c • v) (z • x), add_assoc,
      ← add_smul, hcoef]
  have hvQ : p.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero p).mpr
    (Submodule.mem_span_singleton_self v)
  have hCorr : x + (c / (z - 1)) • v ≠ 0 := fun hzero => hu.2 (by
    simpa only [map_add, map_smul, hvQ, smul_zero, add_zero, map_zero] using
      congrArg p.mkQ hzero)
  exact ⟨Module.End.hasEigenvalue_iff_mem_spectrum.mp
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hfCorr, hCorr⟩),
    by simpa only [Set.mem_singleton_iff] using hz1⟩


private theorem invariant_span_of_fixed
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (v : V) (hfv : f v = v) :
    Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap f := by
  rw [Submodule.span_singleton_le_iff_mem]
  change f v ∈ Submodule.span ℂ {v}
  rw [hfv]
  exact Submodule.mem_span_singleton_self v

/-- Uniform contraction away from an algebraically simple fixed eigenvalue
prevents additional fixed vectors from appearing in a finite-dimensional
operator limit. -/
theorem ContinuousLinearMap.eigenspace_one_limit_eq_span_of_uniform_spectrum_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (f : ℕ → V →L[ℂ] V) (f₀ : V →L[ℂ] V)
    (hf : Tendsto f atTop (𝓝 f₀)) (v : V) (hv : v ≠ 0)
    (hFix : ∀ n, f n v = v)
    (hSimple : ∀ n, (f n : V →ₗ[ℂ] V).charpoly.rootMultiplicity 1 = 1)
    (q : ℝ) (hq : q < 1)
    (hBound : ∀ n z, z ∈ spectrum ℂ (f n : V →ₗ[ℂ] V) → z ≠ 1 → ‖z‖ ≤ q) :
    Module.End.eigenspace (f₀ : V →ₗ[ℂ] V) 1 = Submodule.span ℂ {v} := by
  classical
  have hEval : Tendsto (fun n => f n v) atTop (𝓝 (f₀ v)) :=
    (ContinuousLinearMap.apply ℂ V v).continuous.continuousAt.tendsto.comp hf
  have hFix₀ : f₀ v = v :=
    tendsto_nhds_unique (by simpa only [hFix] using hEval) tendsto_const_nhds
  let p := Submodule.span ℂ {v}
  have hp : ∀ n, p ≤ p.comap (f n : V →ₗ[ℂ] V) :=
    fun n => invariant_span_of_fixed (f n : V →ₗ[ℂ] V) v (hFix n)
  have hp₀ : p ≤ p.comap (f₀ : V →ₗ[ℂ] V) :=
    invariant_span_of_fixed (f₀ : V →ₗ[ℂ] V) v hFix₀
  let fQ : ℕ → (V ⧸ p →ₗ[ℂ] V ⧸ p) :=
    fun n => p.mapQ p (f n : V →ₗ[ℂ] V) (hp n)
  let fQ₀ : V ⧸ p →ₗ[ℂ] V ⧸ p := p.mapQ p (f₀ : V →ₗ[ℂ] V) hp₀
  let b := Module.finBasis ℂ (V ⧸ p)
  let M := fun n => LinearMap.toMatrix b b (fQ n)
  let M₀ := LinearMap.toMatrix b b fQ₀
  have hM : Tendsto M atTop (𝓝 M₀) :=
    Submodule.tendsto_toMatrix_mapQ_of_tendsto p b f f₀ hf hp hp₀
  have hSpec : ∀ n z, z ∈ spectrum ℂ (M n) → ‖z‖ ≤ q := by
    intro n z hz
    have hzQ : z ∈ spectrum ℂ (fQ n) := by
      simpa only [M, LinearMap.spectrum_toMatrix] using hz
    have hzF := spectrum_fixedLineQuotient_subset
      (f n : V →ₗ[ℂ] V) v hv (hFix n) (hSimple n) (hp n) hzQ
    exact hBound n z hzF.1 (by simpa only [Set.mem_singleton_iff] using hzF.2)
  have hUnit := Matrix.isUnit_one_sub_of_tendsto_of_uniform_spectrum_bound M M₀ hM q hq hSpec
  have hNotSpec : (1 : ℂ) ∉ spectrum ℂ fQ₀ := by
    intro hz
    have hzM : (1 : ℂ) ∈ spectrum ℂ M₀ := by
      simpa only [M₀, LinearMap.spectrum_toMatrix] using hz
    exact (spectrum.mem_iff.mp hzM) (by simpa only [map_one] using hUnit)
  ext x
  rw [Module.End.mem_eigenspace_iff]
  simp only [one_smul, ContinuousLinearMap.coe_coe]
  constructor
  · intro hx
    have hxQ : fQ₀ (p.mkQ x) = p.mkQ x := by
      simp only [fQ₀, Submodule.mkQ_apply, Submodule.mapQ_apply,
        ContinuousLinearMap.coe_coe, hx]
    have hZero : p.mkQ x = 0 := by
      by_contra hNonzero
      apply hNotSpec
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp
        (Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr (by simpa only [one_smul] using hxQ), hNonzero⟩)
    exact (Submodule.Quotient.mk_eq_zero p).mp hZero
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hc, map_smul, hFix₀]


/-- A uniform closed-disc spectral bound survives matrix limits. -/
private theorem Matrix.spectrum_norm_le_of_tendsto_of_uniform_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : ℕ → Matrix n n ℂ) (M₀ : Matrix n n ℂ)
    (hM : Tendsto M atTop (𝓝 M₀)) (q : ℝ)
    (hspec : ∀ j z, z ∈ spectrum ℂ (M j) → ‖z‖ ≤ q) :
    ∀ z ∈ spectrum ℂ M₀, ‖z‖ ≤ q := by
  intro z hz
  by_contra hbound
  have hq : q < ‖z‖ := lt_of_not_ge hbound
  have hdet : Tendsto (fun j => ‖(Matrix.scalar n z - M j).det‖)
      atTop (𝓝 ‖(Matrix.scalar n z - M₀).det‖) :=
    ((continuous_const.sub continuous_id).matrix_det.norm).continuousAt.tendsto.comp hM
  have hLower : (‖z‖ - q) ^ Fintype.card n ≤ ‖(Matrix.scalar n z - M₀).det‖ :=
    ge_of_tendsto hdet (Eventually.of_forall fun j =>
      Matrix.norm_det_scalar_sub_ge_of_spectrum_norm_le (M j) z q hq.le (hspec j))
  have hUnit : IsUnit (Matrix.scalar n z - M₀) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (norm_pos_iff.mp (lt_of_lt_of_le (pow_pos (sub_pos.mpr hq) _) hLower)))
  exact (spectrum.mem_iff.mp hz) (by
    simpa only [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.algebraMap_self_apply] using hUnit)

/-- The bound on nontrivial eigenvalues survives a limit with a common fixed line.
The eigenvalue one need not be algebraically simple for the limiting operator. -/
theorem ContinuousLinearMap.spectrum_limit_norm_le_of_uniform_nontrivial_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (f : ℕ → V →L[ℂ] V) (f₀ : V →L[ℂ] V)
    (hf : Tendsto f atTop (𝓝 f₀)) (v : V) (hv : v ≠ 0)
    (hFix : ∀ n, f n v = v)
    (hSimple : ∀ n, (f n : V →ₗ[ℂ] V).charpoly.rootMultiplicity 1 = 1)
    (q : ℝ)
    (hBound : ∀ n z, z ∈ spectrum ℂ (f n : V →ₗ[ℂ] V) → z ≠ 1 → ‖z‖ ≤ q) :
    ∀ z ∈ spectrum ℂ (f₀ : V →ₗ[ℂ] V), z ≠ 1 → ‖z‖ ≤ q := by
  classical
  have hEval : Tendsto (fun n => f n v) atTop (𝓝 (f₀ v)) :=
    (ContinuousLinearMap.apply ℂ V v).continuous.continuousAt.tendsto.comp hf
  have hFix₀ : f₀ v = v :=
    tendsto_nhds_unique (by simpa only [hFix] using hEval) tendsto_const_nhds
  let p := Submodule.span ℂ {v}
  have hp : ∀ n, p ≤ p.comap (f n : V →ₗ[ℂ] V) :=
    fun n => invariant_span_of_fixed (f n : V →ₗ[ℂ] V) v (hFix n)
  have hp₀ : p ≤ p.comap (f₀ : V →ₗ[ℂ] V) :=
    invariant_span_of_fixed (f₀ : V →ₗ[ℂ] V) v hFix₀
  let fQ : ℕ → (V ⧸ p →ₗ[ℂ] V ⧸ p) :=
    fun n => p.mapQ p (f n : V →ₗ[ℂ] V) (hp n)
  let fQ₀ : V ⧸ p →ₗ[ℂ] V ⧸ p := p.mapQ p (f₀ : V →ₗ[ℂ] V) hp₀
  let b := Module.finBasis ℂ (V ⧸ p)
  let M := fun n => LinearMap.toMatrix b b (fQ n)
  let M₀ := LinearMap.toMatrix b b fQ₀
  have hM : Tendsto M atTop (𝓝 M₀) :=
    Submodule.tendsto_toMatrix_mapQ_of_tendsto p b f f₀ hf hp hp₀
  have hSpec : ∀ n z, z ∈ spectrum ℂ (M n) → ‖z‖ ≤ q := by
    intro n z hz
    have hzQ : z ∈ spectrum ℂ (fQ n) := by
      simpa only [M, LinearMap.spectrum_toMatrix] using hz
    have hzF := spectrum_fixedLineQuotient_subset
      (f n : V →ₗ[ℂ] V) v hv (hFix n) (hSimple n) (hp n) hzQ
    exact hBound n z hzF.1 (by simpa only [Set.mem_singleton_iff] using hzF.2)
  intro z hz hz1
  obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have hxQ : p.mkQ x ≠ 0 := by
    intro hzero
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      ((Submodule.Quotient.mk_eq_zero p).mp hzero)
    have hfx : f₀ x = x := by rw [← hc, map_smul, hFix₀]
    have hzsmul : (z - 1) • x = 0 := by
      rw [sub_smul, one_smul, ← hx.apply_eq_smul]
      change f₀ x - x = 0
      rw [hfx, sub_self]
    exact (smul_eq_zero.mp hzsmul).elim (fun h => hz1 (sub_eq_zero.mp h)) hx.2
  have hzQ : z ∈ spectrum ℂ fQ₀ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (by
          simpa only [fQ₀, Submodule.mkQ_apply, Submodule.mapQ_apply,
            ContinuousLinearMap.coe_coe, map_smul] using congrArg p.mkQ hx.apply_eq_smul), hxQ⟩)
  have hzM : z ∈ spectrum ℂ M₀ := by
    simpa only [M₀, LinearMap.spectrum_toMatrix] using hzQ
  exact Matrix.spectrum_norm_le_of_tendsto_of_uniform_bound M M₀ hM q hSpec z hzM
