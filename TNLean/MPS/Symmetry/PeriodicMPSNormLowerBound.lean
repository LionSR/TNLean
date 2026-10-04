/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import TNLean.Algebra.TraceInvariantSubmodule
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import QICLean.Channel.Peripheral.JordanBlocks
import TNLean.MPS.Preparation.SecondOrderOverlap
import QICLean.Channel.KrausMap
import Mathlib.Analysis.SpecificLimits.Basic
import TNLean.MPS.Core.BlockingTransfer

/-!
# Uniform lower bounds for periodic MPS norms

For a unital tensor with a one-dimensional transfer fixed space, Wolf
Proposition 6.2 excludes a Jordan block at the eigenvalue one. Thus that
characteristic root has algebraic multiplicity one. If every other transfer
eigenvalue has modulus at most `q`, the squared norm of the periodic state of
length `N` differs from one by at most `(D² - 1) q^N`.

The proof passes to the quotient by the identity line, applies spectral mapping
to each power, and bounds its trace by its dimension times the spectral bound.
It requires neither diagonalizability nor faithful stationary density.

For a family with a common bound `0 ≤ q < 1`, all sufficiently long rings have
squared norm at least one half. A single physical blocking therefore makes every
positive ring nonzero. These are auxiliary transfer-spectrum statements; no
implication from a physical Hamiltonian gap to their hypotheses is asserted.
-/


/-!
# Uniform periodic tensor norm estimates from transfer spectra

The algebraic multiplicity of a transfer eigenvalue is its multiplicity as a root
of the characteristic polynomial. A simple eigenvalue one contributes exactly one
to every positive trace power. The complementary quotient contributes at most its
dimension times the corresponding power of a uniform spectral bound.
-/
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

private theorem norm_multiset_sum_le_card_mul
    (s : Multiset ℂ) (c : ℝ) (hs : ∀ z ∈ s, ‖z‖ ≤ c) :
    ‖s.sum‖ ≤ s.card * c := by
  apply (norm_multiset_sum_le s).trans
  simpa only [Multiset.card_map, nsmul_eq_mul] using
    Multiset.sum_le_card_nsmul (s.map fun z => ‖z‖) c
      (fun x hx => by
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
        exact hs z hz)

private theorem norm_trace_le_of_spectrum_norm_le
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) (c : ℝ) (hspec : ∀ z ∈ spectrum ℂ f, ‖z‖ ≤ c) :
    ‖LinearMap.trace ℂ V f‖ ≤ Module.finrank ℂ V * c := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits f.charpoly)]
  have hcard : f.charpoly.roots.card = Module.finrank ℂ V := by
    rw [← (IsAlgClosed.splits f.charpoly).natDegree_eq_card_roots,
      LinearMap.charpoly_natDegree]
  rw [← hcard]
  exact norm_multiset_sum_le_card_mul f.charpoly.roots c (fun z hz =>
    hspec z ((Module.End.mem_spectrum_iff_isRoot_charpoly f z).mpr
      ((Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mp hz)))

private theorem norm_trace_pow_le_of_spectrum_norm_le
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) (q : ℝ)
    (hspec : ∀ z ∈ spectrum ℂ f, ‖z‖ ≤ q) (N : ℕ) :
    ‖LinearMap.trace ℂ V (f ^ N)‖ ≤ Module.finrank ℂ V * q ^ N := by
  cases N with
  | zero =>
    simp only [pow_zero, LinearMap.trace_one, Complex.norm_natCast, mul_one, le_refl]
  | succ n =>
    apply norm_trace_le_of_spectrum_norm_le
    rintro z hz
    rw [spectrum.map_pow_of_pos f (Nat.succ_pos n)] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [norm_pow] using
      pow_le_pow_left₀ (norm_nonneg w) (hspec w hw) (n + 1)


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

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


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

/-- Wolf Proposition 6.2 identifies geometric and algebraic multiplicity at one
for a positive unital map. -/
private theorem simple_fixedEigenvalue_of_unital_positive
    {D : ℕ} [NeZero D]
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (hPos : IsPositiveMap T) (hOne : T 1 = 1)
    (hDim : Module.finrank ℂ (Module.End.eigenspace T 1) = 1) :
    T.charpoly.rootMultiplicity 1 = 1 := by
  have hEq : Module.End.maxGenEigenspace T 1 = Module.End.eigenspace T 1 := by
    apply le_antisymm _ Module.End.eigenspace_le_maxGenEigenspace
    intro X hX
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T 1 X).mp hX
    have h := hPos.peripheral_Jordan_trivial_of_unital hOne 1 (by simp) k X hk
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h
    exact Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp h)
  rw [← LinearMap.finrank_maxGenEigenspace_eq, hEq, hDim]

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

/-- A fixed nonzero vector contributes one to every trace power; the remaining
contribution is the trace power of the quotient by its line. -/
private theorem LinearMap.trace_pow_eq_one_add_trace_fixedLineQuotient
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) (v : V) (hv : v ≠ 0) (hfv : f v = v)
    (hp : Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap f) (N : ℕ) :
    LinearMap.trace ℂ V (f ^ N) = 1 +
      LinearMap.trace ℂ (V ⧸ Submodule.span ℂ {v})
        (((Submodule.span ℂ {v}).mapQ (Submodule.span ℂ {v}) f hp) ^ N) := by
  let p : Submodule ℂ V := Submodule.span ℂ {v}
  have hfix : ∀ x ∈ p, f x = x := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [map_smul, hfv]
  have hpowfix : ∀ x ∈ p, (f ^ N) x = x := by
    intro x hx
    induction N with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hfix x hx, ih]
  have hpowmem : ∀ x ∈ p, (f ^ N) x ∈ p := by
    intro x hx
    rw [hpowfix x hx]
    exact hx
  have hrestrict : (f ^ N).restrict hpowmem = LinearMap.id := by
    ext x
    exact hpowfix x x.property
  rw [LinearMap.trace_eq_trace_restrict_add_trace_quotient p (f ^ N) hpowmem,
    hrestrict, LinearMap.trace_id]
  have hdim : Module.finrank ℂ p = 1 := finrank_span_singleton hv
  rw [hdim]
  simp only [Nat.cast_one]
  congr 2
  exact Submodule.mapQ_pow p hp N


private theorem norm_trace_pow_sub_one_le_of_simple_fixedVector
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) (v : V) (hv : v ≠ 0) (hfv : f v = v)
    (hSimple : f.charpoly.rootMultiplicity 1 = 1) (q : ℝ)
    (hspec : ∀ z ∈ spectrum ℂ f, z ≠ 1 → ‖z‖ ≤ q) (N : ℕ) :
    ‖LinearMap.trace ℂ V (f ^ N) - 1‖ ≤ (Module.finrank ℂ V - 1 : ℕ) * q ^ N := by
  let p : Submodule ℂ V := Submodule.span ℂ {v}
  have hp : p ≤ p.comap f := (Submodule.span_singleton_le_iff_mem ..).mpr (by
    change f v ∈ p
    rw [hfv]
    exact Submodule.mem_span_singleton_self v)
  have hquot : ∀ z ∈ spectrum ℂ (p.mapQ p f hp), ‖z‖ ≤ q := by
    intro z hz
    obtain ⟨hzf, hz1⟩ := spectrum_fixedLineQuotient_subset f v hv hfv hSimple hp hz
    exact hspec z hzf (by simpa only [Set.mem_singleton_iff] using hz1)
  have hdim : Module.finrank ℂ (V ⧸ p) = Module.finrank ℂ V - 1 := by
    have h := p.finrank_quotient_add_finrank
    have hpdim : Module.finrank ℂ p = 1 := finrank_span_singleton hv
    omega
  rw [LinearMap.trace_pow_eq_one_add_trace_fixedLineQuotient f v hv hfv hp N,
    add_sub_cancel_left]
  simpa only [hdim] using norm_trace_pow_le_of_spectrum_norm_le (p.mapQ p f hp) q hquot N

namespace MPSTensor

/-- A uniform bound on all transfer eigenvalues other than one bounds the
squared periodic MPS norm. Unital positivity makes the eigenvalue one
semisimple (Wolf Proposition 6.2), so a one-dimensional fixed space supplies
algebraic multiplicity one. No diagonalizability is assumed. -/
theorem abs_norm_mpvState_sq_sub_one_le_of_transfer_spectrum
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hUnital : Kraus.IsUnital A)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1)
    (q : ℝ) (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q)
    (N : ℕ) :
    |‖mpvState A N‖ ^ 2 - 1| ≤ (D * D - 1 : ℕ) * q ^ N := by
  have hOne : Kraus.transferMap A 1 = 1 := Kraus.map_one_of_isUnital A hUnital
  have hSimple : (Kraus.transferMap A).charpoly.rootMultiplicity 1 = 1 :=
    simple_fixedEigenvalue_of_unital_positive (Kraus.transferMap A)
      (Kraus.isPositiveMap_mapLM A) hOne hDim
  have hTrace : LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
      ((Kraus.transferMap A) ^ N) = mpvOverlap A A N := by
    simpa only [Kraus.mixedMapLM_self] using
      trace_mixedMapLM_pow_eq_mpvOverlap A A N
  have hBound := norm_trace_pow_sub_one_le_of_simple_fixedVector
    (Kraus.transferMap A) (1 : Matrix (Fin D) (Fin D) ℂ) one_ne_zero
    hOne hSimple q hspec N
  rw [hTrace, ← ofReal_norm_mpvState_sq A N] at hBound
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one] using hBound

/-- The squared norm of a periodic MPS differs from one by at most the
contribution of the remaining transfer eigenvalues, counted with algebraic
multiplicity. -/
theorem one_sub_le_norm_mpvState_sq_of_transfer_spectrum
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hUnital : Kraus.IsUnital A)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1)
    (q : ℝ) (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q)
    (N : ℕ) :
    1 - (D * D - 1 : ℕ) * q ^ N ≤ ‖mpvState A N‖ ^ 2 := by
  have h := (abs_le.mp
    (abs_norm_mpvState_sq_sub_one_le_of_transfer_spectrum A hUnital hDim q hspec N)).1
  linarith

/-- A common spectral bound strictly below one gives a common positive lower
bound for all sufficiently long periodic MPS, throughout an arbitrary family.
No continuity assumption on the family is required. -/
theorem exists_uniform_norm_mpvState_sq_lowerBound_of_transfer_spectrum
    {T : Type*} {d D : ℕ} [NeZero D] (A : T → MPSTensor d D)
    (hUnital : ∀ t, Kraus.IsUnital (A t))
    (hDim : ∀ t, Module.finrank ℂ
      (Module.End.eigenspace (Kraus.transferMap (A t)) 1) = 1)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hspec : ∀ t z, z ∈ spectrum ℂ (Kraus.transferMap (A t)) → z ≠ 1 → ‖z‖ ≤ q) :
    ∃ L : ℕ, 0 < L ∧ ∀ t N, L ≤ N → (1 / 2 : ℝ) ≤ ‖mpvState (A t) N‖ ^ 2 := by
  have hDecay : Filter.Tendsto (fun N : ℕ => (D * D - 1 : ℕ) * q ^ N)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hqOne).const_mul
        ((D * D - 1 : ℕ) : ℝ)
  have hEventually : ∀ᶠ N : ℕ in Filter.atTop,
      (D * D - 1 : ℕ) * q ^ N < (1 / 2 : ℝ) :=
    hDecay.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hEventually
  refine ⟨max L 1, by omega, ?_⟩
  intro t N hN
  have hSmall := hL N (le_trans (le_max_left L 1) hN)
  have hLower := one_sub_le_norm_mpvState_sq_of_transfer_spectrum
    (A t) (hUnital t) (hDim t) q (hspec t) N
  linarith

private theorem norm_mpvState_blockTensor_sq {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (L N : ℕ) :
    ‖mpvState (blockTensor A L) N‖ ^ 2 = ‖mpvState A (L * N)‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [ofReal_norm_mpvState_sq, ofReal_norm_mpvState_sq,
    ← trace_mixedMapLM_pow_eq_mpvOverlap, ← trace_mixedMapLM_pow_eq_mpvOverlap,
    Kraus.mixedMapLM_self, Kraus.mixedMapLM_self]
  change LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)
      ((Kraus.transferMap (blockTensor A L)) ^ N) =
    LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ) ((Kraus.transferMap A) ^ (L * N))
  rw [transferMap_blockTensor, ← pow_mul]

/-- A single physical blocking length makes every positive periodic ring
nonzero, uniformly over any family with a common spectral bound below one. -/
theorem exists_uniform_blocking_mpvState_ne_zero_of_transfer_spectrum
    {T : Type*} {d D : ℕ} [NeZero D] (A : T → MPSTensor d D)
    (hUnital : ∀ t, Kraus.IsUnital (A t))
    (hDim : ∀ t, Module.finrank ℂ
      (Module.End.eigenspace (Kraus.transferMap (A t)) 1) = 1)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hspec : ∀ t z, z ∈ spectrum ℂ (Kraus.transferMap (A t)) → z ≠ 1 → ‖z‖ ≤ q) :
    ∃ L : ℕ, 0 < L ∧ ∀ t N, 0 < N →
      (1 / 2 : ℝ) ≤ ‖mpvState (blockTensor (A t) L) N‖ ^ 2 ∧
      mpvState (blockTensor (A t) L) N ≠ 0 := by
  obtain ⟨L, hL, hBound⟩ :=
    exists_uniform_norm_mpvState_sq_lowerBound_of_transfer_spectrum
      A hUnital hDim q hq hqOne hspec
  refine ⟨L, hL, ?_⟩
  intro t N hN
  have hLN : L ≤ L * N := by
    simpa using Nat.mul_le_mul_left L hN
  have hNorm : (1 / 2 : ℝ) ≤ ‖mpvState (blockTensor (A t) L) N‖ ^ 2 := by
    rw [norm_mpvState_blockTensor_sq]
    exact hBound t (L * N) hLN
  refine ⟨hNorm, ?_⟩
  intro hZero
  rw [hZero, norm_zero, zero_pow (by norm_num)] at hNorm
  norm_num at hNorm

end MPSTensor
