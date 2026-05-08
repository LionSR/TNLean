/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.Analysis.ProjectionGeometry
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Martingale-method spectral-gap framework for parent Hamiltonians

**Root-only.** This module is currently not imported downstream — it is a
source-facing theorem surface that formalizes the martingale-method
infrastructure for the MPS parent-Hamiltonian spectral gap. The
Friedrichs-angle estimate needed to close `parentHamiltonian_gapped` is
tracked by issues #952 and #460 (#190). See issue #1512 for the root-only
audit.

This file sets up the martingale approach to proving
that MPS parent Hamiltonians are gapped, following
Kastoryano–Lucia 2018 (arXiv:1705.09491), Nachtergaele 1996
(Comm. Math. Phys. 175, 565), and Fannes–Nachtergaele–Werner 1992.

## Proof route

1. **Frustration-freeness** (`parentHamiltonian_frustrationFree`): every local
   term annihilates the MPV ground state.
2. **Local projector structure** (`parentInteraction`/`localTerm`): each local
   term is an orthogonal projector on its `L`-site window.
3. **Intersection property** (`groundSpace_intersection`): for an injective
   MPS tensor, the kernel of the sum of two overlapping local terms equals
   the intersection of their kernels.
4. **Martingale operator bound**: the intersection property gives a positive
   Friedrichs angle between adjacent local ground spaces, which is the
   quantitative content of

        `h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)`

   with constants `c_{ij}` depending only on the MPS tensor, not on `N`.
5. **Row-sum bound** `∑_{j ≠ i} c_{ij} ≤ 1`: at most `2(L-1)` local terms
   overlap a given local term.
6. **Quadratic form ⟹ norm bound**: combining the above with `h_i^2 = h_i`
   yields `H² ≥ γ H` as a quadratic form, which by the spectral theorem
   gives `γ ‖v‖ ≤ ‖H v‖` for `v ⊥ ker H`.

The last step — the implication from the quadratic-form inequality
`H² ≥ γ H` to the norm bound `γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ` — is stated
as the abstract lemma `FrustrationFree.spectralGap_of_martingale` below.
Its hypothesis is the quadratic-form inequality (in inner-product form),
and its proof is the spectral-theorem argument: diagonalising the
positive symmetric operator `H` in an orthonormal eigenbasis with
nonnegative eigenvalues `μᵢ`, applying the hypothesis to each eigenvector
gives `γ μᵢ ≤ μᵢ²`, so every nonzero eigenvalue satisfies `μᵢ ≥ γ`;
expanding `v` in the basis and discarding the `ker H` components (which
vanish on `(ker H)ᗮ`) then yields `γ² ‖v‖² ≤ ‖H v‖²`.

The MPS-specific step (producing the finite-overlap estimate for
`parentHamiltonianES A L N`) is the remaining obligation of
`MPSTensor.parentHamiltonianES_gap_bound_of_friedrichs`, which states a
concrete Friedrichs-angle/row-sum lower bound that
`MPSTensor.parentHamiltonian_gapped` turns into the existential gap statement.

## Main results

* `FrustrationFree.spectralGap_of_martingale` — abstract martingale
  criterion: the quadratic-form inequality `γ ⟨H v, v⟩ ≤ ⟨H v, H v⟩`
  for a `LinearMap.IsPositive` operator `H` implies the norm bound
  `γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ`.
* `MPSTensor.localTermESSummand_isPositive` — positivity of the conjugated
  cyclic-window summands expected to appear in the averaged
  `EuclideanSpace` formula for local terms.
* `MPSTensor.localTermES_isSymmetricProjection` — each transported local term is
  a symmetric projection, with idempotence inherited from the local orthogonal
  projector on every cyclic window.
* `MPSTensor.localTermES_re_inner_nonneg_of_cyclic_windows_disjoint` — disjoint
  cyclic windows give commuting transported local projections and hence
  nonnegative ordered cross terms.
* `MPSTensor.localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap` — failure
  of the concrete cyclic-support overlap predicate gives the same nonnegative
  ordered cross term.
* `MPSTensor.adjacent_localTermES_eq_zero_iff_mem_groundSpaceES_succ` — the
  open-chain intersection property restated as an equality between the kernels
  of two adjacent transported local terms and the `(L+1)`-site MPS ground space.
* `MPSTensor.parentHamiltonianES_gap_bound_of_quadratic_form` — the explicit
  reduction from the parent-Hamiltonian gap statement to the uniform
  Friedrichs/martingale quadratic-form estimate.
* `MPSTensor.parentHamiltonianES_gap_bound_of_ordered_local_term_bounds` — a
  reusable reduction from explicit ordered cross-term row bounds for the
  local symmetric projections to the quadratic-form hypothesis above.
* `MPSTensor.parentHamiltonianES_gap_bound_of_finite_overlap_friedrichs` — a
  finite-overlap reduction turning explicit local projection, overlap,
  non-overlap positivity, and Friedrichs estimates into the gap estimate.
* `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs` — the
  same reduction specialized to the concrete cyclic-window overlap predicate,
  its `2 * (L - 1)` row-cardinality bound, and the non-overlap positivity theorem.
* `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound` —
  the final reduction from the overlapping-window norm-compression Friedrichs
  estimate to the explicit gap bound.
* `MPSTensor.parentHamiltonian_gapped` — uniform spectral gap for MPS
  parent Hamiltonians on injective tensors, obtained from the
  Friedrichs-angle bound stated in
  `parentHamiltonianES_gap_bound_of_friedrichs`.
-/

open scoped BigOperators InnerProductSpace

/-! ### Abstract martingale criterion

The quadratic-form ⟹ norm-bound step is purely operator-theoretic and has no
MPS content in its signature, so it lives in its own `FrustrationFree`
namespace. The MPS-specific theorem `MPSTensor.parentHamiltonian_gapped` below
instantiates it for the parent Hamiltonian. -/

namespace FrustrationFree

/--
**Abstract martingale criterion (quadratic form ⟹ norm bound).**

Let `H` be a positive linear operator (in the sense of `LinearMap.IsPositive`:
symmetric with `0 ≤ re ⟪H v, v⟫`) on a finite-dimensional complex Hilbert
space satisfying the quadratic-form inequality

    `γ ⟨v, H v⟩ ≤ ⟨H v, H v⟩` for all `v`,

i.e.\ `H² ≥ γ H` as a quadratic form. Then on the orthogonal complement
of `ker H`, `H` is bounded below in norm by `γ`:

    `γ ‖v‖ ≤ ‖H v‖` for all `v ⊥ ker H`.

The positivity hypothesis is essential: it rules out negative eigenvalues of
small magnitude (such as `H = -Id`, which otherwise satisfies
`γ ⟨v, H v⟩ ≤ ⟨H v, H v⟩` vacuously but fails the conclusion). For the MPS
parent Hamiltonian this hypothesis is automatic because `H = ∑ᵢ hᵢ` is a
sum of orthogonal projectors.

This is the operator-theoretic content of the Kastoryano–Lucia /
Nachtergaele martingale method: once the MPS-specific projector
geometry (Friedrichs angle on overlapping local ground spaces plus
the row-sum bound) produces the operator inequality `H² ≥ γ H` for the
PSD operator `H`, the norm lower bound — and hence the spectral gap
for eigenvectors of `H` — follows by the spectral theorem. This lemma
provides the final spectral-theorem step; the remaining MPS-specific
quadratic-form hypothesis is stated separately in
`MPSTensor.parentHamiltonianES_gap_bound_of_friedrichs`. -/
theorem spectralGap_of_martingale {ι : Type*} [Fintype ι] {γ : ℝ} (hγ : 0 < γ)
    {H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hH : H.IsPositive)
    (hOpIneq : ∀ v, γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖ := by
  classical
  -- Spectral setup: diagonalise the positive symmetric operator.
  set n := Fintype.card ι with hn_def
  have hn : Module.finrank ℂ (EuclideanSpace ℂ ι) = n := by
    simp [hn_def]
  have hSym : H.IsSymmetric := hH.isSymmetric
  set b := hSym.eigenvectorBasis hn with hb_def
  set μ : Fin n → ℝ := hSym.eigenvalues hn with hμ_def
  have hμ_nn : ∀ i, 0 ≤ μ i := fun i => hH.nonneg_eigenvalues hn i
  have hHb : ∀ i, H (b i) = ((μ i : ℂ)) • b i := fun i =>
    hSym.apply_eigenvectorBasis hn i
  have hbb : ∀ i j : Fin n, ⟪b i, b j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  -- Apply the operator inequality to each eigenvector: `γ μᵢ ≤ μᵢ²`.
  have hμ_ineq : ∀ i, γ * μ i ≤ μ i * μ i := by
    intro i
    have key := hOpIneq (b i)
    rw [hHb i] at key
    have e1 : (⟪((μ i : ℂ)) • b i, b i⟫_ℂ).re = μ i := by
      rw [inner_smul_left, hbb i i, if_pos rfl, mul_one, Complex.conj_ofReal,
          Complex.ofReal_re]
    have e2 : (⟪((μ i : ℂ)) • b i, ((μ i : ℂ)) • b i⟫_ℂ).re = μ i * μ i := by
      rw [inner_smul_left, inner_smul_right, hbb i i, if_pos rfl, mul_one,
          Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [e1, e2] at key
    exact key
  -- Combined with `μᵢ ≥ 0`, this gives `μᵢ = 0 ∨ γ ≤ μᵢ` for each `i`.
  have hμ_alt : ∀ i, μ i = 0 ∨ γ ≤ μ i := by
    intro i
    rcases (hμ_nn i).lt_or_eq with hpos | hzero
    · right
      have := hμ_ineq i
      have hpos' : 0 < μ i := hpos
      nlinarith
    · left; exact hzero.symm
  -- Main argument on `v ∈ (ker H)ᗮ`.
  intro v hv
  -- Eigenvectors with zero eigenvalue lie in `ker H`, hence are orthogonal to `v`.
  have hker : ∀ i, μ i = 0 → b i ∈ LinearMap.ker H := by
    intro i hi
    rw [LinearMap.mem_ker, hHb i]
    simp [hi]
  have hv_perp : ∀ i, μ i = 0 → ⟪b i, v⟫_ℂ = 0 := fun i hi =>
    Submodule.inner_right_of_mem_orthogonal (hker i hi) hv
  -- Express `‖v‖²` and `‖Hv‖²` through the eigenvector basis.
  have hv_sq : ‖v‖ ^ 2 = ∑ i, ‖(b.repr v) i‖ ^ 2 := by
    have hiso := b.repr.norm_map v
    rw [← hiso, EuclideanSpace.norm_sq_eq]
  have hHv_sq : ‖H v‖ ^ 2 = ∑ i, (μ i) ^ 2 * ‖(b.repr v) i‖ ^ 2 := by
    have hiso := b.repr.norm_map (H v)
    rw [← hiso, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hSym.eigenvectorBasis_apply_self_apply hn v i, norm_mul, mul_pow,
        RCLike.norm_ofReal, sq_abs]
  -- The quadratic-form bound `γ² ‖v‖² ≤ ‖Hv‖²` is now term-by-term.
  have h_sq : γ ^ 2 * ‖v‖ ^ 2 ≤ ‖H v‖ ^ 2 := by
    rw [hv_sq, hHv_sq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases hμ_alt i with hi | hi
    · have h0 : (b.repr v) i = 0 := by
        rw [b.repr_apply_apply]
        exact hv_perp i hi
      rw [h0, norm_zero]
      simp
    · have hγ_sq : γ ^ 2 ≤ (μ i) ^ 2 :=
        pow_le_pow_left₀ hγ.le hi 2
      have hnn : (0 : ℝ) ≤ ‖(b.repr v) i‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hγ_sq hnn
  -- Take square roots to conclude `γ ‖v‖ ≤ ‖Hv‖`.
  have h1 : (γ * ‖v‖) ^ 2 ≤ ‖H v‖ ^ 2 := by
    rw [mul_pow]; exact h_sq
  have h2 : 0 ≤ γ * ‖v‖ := mul_nonneg hγ.le (norm_nonneg v)
  have h3 : 0 ≤ ‖H v‖ := norm_nonneg _
  have hsqrt := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq h2, Real.sqrt_sq h3] at hsqrt

end FrustrationFree

namespace MPSTensor

variable {d D : ℕ}

/-! ### Euclidean local projector ingredients -/

/-- The `L`-site parent interaction viewed directly on the Hilbert-space model
`EuclideanSpace ℂ (Cfg d L)`. Equivalently, this is the orthogonal projector
onto `(groundSpaceES A L)ᗮ`. -/
noncomputable def parentInteractionES (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  ((groundSpaceES A L)ᗮ.starProjection.toLinearMap)

/-- The `EuclideanSpace` parent interaction is the symmetric projection onto
`(groundSpaceES A L)ᗮ`. -/
theorem parentInteractionES_isSymmetricProjection (A : MPSTensor d D) (L : ℕ) :
    (parentInteractionES A L).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection ((groundSpaceES A L)ᗮ)

/-- The `EuclideanSpace` parent interaction is positive because it is an
orthogonal projection. -/
theorem parentInteractionES_isPositive (A : MPSTensor d D) (L : ℕ) :
    (parentInteractionES A L).IsPositive :=
  (parentInteractionES_isSymmetricProjection A L).isPositive

/-- The kernel of the Euclidean parent interaction is exactly the Euclidean MPS
local ground space. -/
theorem parentInteractionES_apply_eq_zero_iff (A : MPSTensor d D) (L : ℕ)
    (v : EuclideanSpace ℂ (Cfg d L)) :
    parentInteractionES A L v = 0 ↔ v ∈ groundSpaceES A L := by
  change (groundSpaceES A L)ᗮ.starProjection v = 0 ↔ v ∈ groundSpaceES A L
  rw [Submodule.starProjection_orthogonal']
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- The cyclic window restriction map transported from `NSiteSpace` to the
Hilbert-space model `EuclideanSpace`. -/
noncomputable def cyclicRestrictES {N : ℕ} (hN : 0 < N) (L : ℕ) (i : Fin N)
    (τ : Fin N → Fin d) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) hN L i τ)

/-- One positive summand in the future averaged `EuclideanSpace` formula for a
local parent-Hamiltonian term.

This is the conjugate `Rᵢ,τ† P_L Rᵢ,τ` of the local orthogonal projector
`P_L = parentInteractionES A L` by the transported cyclic restriction map
`Rᵢ,τ = cyclicRestrictES hN L i τ`. -/
noncomputable def localTermESSummand {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    (L : ℕ) (i : Fin N) (τ : Fin N → Fin d) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  (cyclicRestrictES (d := d) hN L i τ).adjoint ∘ₗ
    parentInteractionES A L ∘ₗ
    cyclicRestrictES (d := d) hN L i τ

/-- Each conjugated cyclic-restriction summand `Rᵢ,τ† P_L Rᵢ,τ` is positive. -/
theorem localTermESSummand_isPositive {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    (L : ℕ) (i : Fin N) (τ : Fin N → Fin d) :
    (localTermESSummand A hN L i τ).IsPositive := by
  simpa [localTermESSummand, LinearMap.adjoint_adjoint] using
    (LinearMap.IsPositive.conj_adjoint
      (hT := parentInteractionES_isPositive A L)
      ((cyclicRestrictES (d := d) hN L i τ).adjoint))

/-- The unnormalised finite sum of the future averaging summands is positive. -/
theorem localTermESSummand_sum_isPositive {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    (L : ℕ) (i : Fin N) :
    (∑ τ : Cfg d N, localTermESSummand A hN L i τ).IsPositive := by
  exact LinearMap.isPositive_sum _ fun τ _ =>
    localTermESSummand_isPositive A hN L i τ

/-! ### Ground-space and Hamiltonian transport to `EuclideanSpace` -/

/-- The translated local parent-Hamiltonian term transported to the
`EuclideanSpace` model. -/
noncomputable def localTermES {N : ℕ} (A : MPSTensor d D) (L : ℕ) (i : Fin N) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace d N))
  e.symm.toLinearMap.comp ((localTerm A L N i).comp e.toLinearMap)

/-- Site-disjointness for two cyclic `L`-windows on an `N`-site periodic chain.

The window starting at `i` contains exactly the sites whose cyclic offset from `i`
is `< L`.  Thus `CyclicWindowsDisjoint L i j` says that no site has offset `< L`
from both starting points.  This is the non-overlap condition used by the
finite-overlap martingale reduction. -/
def CyclicWindowsDisjoint {N : ℕ} (L : ℕ) (i j : Fin N) : Prop :=
  ∀ k : Fin N,
    ((k.val + N - i.val) % N < L) → ((k.val + N - j.val) % N < L) → False

/-- Cyclic-window disjointness is symmetric. -/
theorem CyclicWindowsDisjoint.symm {N : ℕ} {L : ℕ} {i j : Fin N}
    (hij : CyclicWindowsDisjoint L i j) : CyclicWindowsDisjoint L j i :=
  fun k hj hi => hij k hi hj

/-- If the cyclic supports of two windows do not overlap, then the windows are site-disjoint. -/
theorem CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap {N L : ℕ}
    {i j : Fin N} (hij : ¬ cyclicWindowsOverlap N L i j) :
    CyclicWindowsDisjoint L i j := by
  intro k hki hkj
  apply hij
  refine ⟨k, ?_, ?_⟩
  · rw [cyclicWindowSupport, Finset.mem_image]
    refine ⟨(k.val + N - i.val) % N, Finset.mem_range.mpr hki, ?_⟩
    exact (eq_cyclic_site_of_offset_eq (Fin.pos i) (i := i) (k := k)
      (r := (k.val + N - i.val) % N) rfl).symm
  · rw [cyclicWindowSupport, Finset.mem_image]
    refine ⟨(k.val + N - j.val) % N, Finset.mem_range.mpr hkj, ?_⟩
    exact (eq_cyclic_site_of_offset_eq (Fin.pos j) (i := j) (k := k)
      (r := (k.val + N - j.val) % N) rfl).symm

/-- Ground-space submodule for the finite-size parent Hamiltonian,
transported to the `EuclideanSpace` (inner-product) setting so that
orthogonal complements are available. -/
noncomputable def parentHamiltonianGroundSpaceES (A : MPSTensor d D)
    (L N : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) :=
  (LinearMap.ker (parentHamiltonian A L N)).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap

/-- The parent Hamiltonian transported to `EuclideanSpace`. -/
noncomputable def parentHamiltonianES (A : MPSTensor d D) (L N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace d N))
  e.symm.toLinearMap.comp ((parentHamiltonian A L N).comp e.toLinearMap)

/-- The transported parent Hamiltonian is the sum of the transported local
terms. -/
theorem parentHamiltonianES_eq_sum_localTermES (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonianES A L N = ∑ i : Fin N, localTermES A L i := by
  ext v σ
  simp [parentHamiltonianES, parentHamiltonian, localTermES]

attribute [local instance] Classical.propDecidable

private theorem cyclicCfg_eq_replaceWindow {N : ℕ} (hN : 0 < N) (L : ℕ)
    (hLN : L ≤ N) (i : Fin N) (σ : Cfg d L) (τ : Cfg d N) :
    cyclicCfg hN L i σ τ = replaceWindow L hLN i τ σ := by
  rfl

@[simp] private theorem cyclicRestrictES_apply {N : ℕ} (hN : 0 < N) (L : ℕ)
    (i : Fin N) (τ : Cfg d N) (v : EuclideanSpace ℂ (Cfg d N)) (ω : Cfg d L) :
    cyclicRestrictES (d := d) hN L i τ v ω = v (cyclicCfg hN L i ω τ) := rfl

private def SameOutsideWindow {N : ℕ} (L : ℕ) (i : Fin N) (σ τ : Cfg d N) : Prop :=
  ∀ k : Fin N, ¬ ((k.val + N - i.val) % N < L) → τ k = σ k

private theorem cyclicRestrictES_eq_of_sameOutsideWindow {N : ℕ} (hN : 0 < N)
    {L : ℕ} (i : Fin N) {σ τ : Cfg d N}
    (hστ : SameOutsideWindow (L := L) i σ τ) :
    cyclicRestrictES (d := d) hN L i τ = cyclicRestrictES hN L i σ := by
  ext v ω
  change v.ofLp (cyclicCfg hN L i ω τ) = v.ofLp (cyclicCfg hN L i ω σ)
  exact congrArg v.ofLp <| by
    ext k
    by_cases hk : ((k.val + N - i.val) % N) < L
    · simp [cyclicCfg, hk]
    · simp [cyclicCfg, hk, hστ k hk]

private theorem sameOutsideWindow_of_cyclicCfg_eq {N : ℕ} (hN : 0 < N) {L : ℕ}
    (i : Fin N) {σ τ : Cfg d N} {ω : Cfg d L}
    (hEq : cyclicCfg hN L i ω τ = σ) :
    SameOutsideWindow (L := L) i σ τ := by
  intro k hk
  have hEqk := congrFun hEq k
  simpa [cyclicCfg, hk] using hEqk

private theorem cyclic_offset_window_site_lt {N L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (r : Fin L) :
    (((i.val + r.val) % N + N - i.val) % N) < L := by
  rw [offset_mod_eq i.isLt (Nat.lt_of_lt_of_le r.isLt hLN)]
  exact r.isLt

private theorem extractWindow_replaceWindow_of_cyclic_windows_disjoint {N L : ℕ}
    (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j)
    (σ : Cfg d N) (τ : Cfg d L) :
    extractWindow L i (replaceWindow L hLN j σ τ) = extractWindow L i σ := by
  funext r
  unfold extractWindow replaceWindow
  have hi : (((i.val + r.val) % N + N - i.val) % N) < L :=
    cyclic_offset_window_site_lt hLN i r
  have hnotj : ¬ (((i.val + r.val) % N + N - j.val) % N < L) := by
    intro hj
    exact hij ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ hi hj
  rw [dif_neg hnotj]

private theorem replaceWindow_commute_of_cyclic_windows_disjoint {N L : ℕ}
    (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j)
    (σ : Cfg d N) (α β : Cfg d L) :
    replaceWindow L hLN j (replaceWindow L hLN i σ α) β =
      replaceWindow L hLN i (replaceWindow L hLN j σ β) α := by
  funext k
  by_cases hi : ((k.val + N - i.val) % N < L)
  · have hnotj : ¬ ((k.val + N - j.val) % N < L) := fun hj => hij k hi hj
    simp [replaceWindow, hi, hnotj]
  · by_cases hj : ((k.val + N - j.val) % N < L)
    · simp [replaceWindow, hi, hj]
    · simp [replaceWindow, hi, hj]

private theorem euclideanSpace_eq_sum_single {α : Type*} [Fintype α] [DecidableEq α]
    (x : EuclideanSpace ℂ α) :
    x = ∑ a : α, x a • EuclideanSpace.single a (1 : ℂ) := by
  ext a
  simp [Finset.sum_apply, Pi.single_apply]

private theorem linearMap_apply_eq_sum {α : Type*} [Fintype α] [DecidableEq α]
    (P : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (x : EuclideanSpace ℂ α) (a : α) :
    P x a = ∑ a' : α, x a' * P (EuclideanSpace.single a' (1 : ℂ)) a := by
  conv_lhs => rw [euclideanSpace_eq_sum_single x]
  simp [Finset.sum_apply]

private theorem scalar_sum_comm {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℂ) (p : α → ℂ) (q : β → ℂ) :
    (∑ a, (∑ b, F a b * q b) * p a) =
      ∑ b, (∑ a, F a b * p a) * q b := by
  calc
    (∑ a, (∑ b, F a b * q b) * p a)
        = ∑ a, ∑ b, F a b * q b * p a := by
      simp_rw [Finset.sum_mul]
    _ = ∑ b, ∑ a, F a b * q b * p a := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, F a b * p a * q b := by
      refine Finset.sum_congr rfl ?_
      intro b _
      refine Finset.sum_congr rfl ?_
      intro a _
      ring
    _ = ∑ b, (∑ a, F a b * p a) * q b := by
      simp_rw [Finset.sum_mul]

private theorem separateLinearMap_apply_commute
    {α β : Type*} [Fintype α] [Fintype β]
    (P : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (Q : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β)
    (F : α → β → ℂ) (a : α) (b : β) :
    P (WithLp.toLp 2 (fun a' => Q (WithLp.toLp 2 (fun b' => F a' b')) b)) a =
      Q (WithLp.toLp 2 (fun b' => P (WithLp.toLp 2 (fun a' => F a' b')) a)) b := by
  classical
  calc
    P (WithLp.toLp 2 (fun a' => Q (WithLp.toLp 2 (fun b' => F a' b')) b)) a
        = ∑ a', (Q (WithLp.toLp 2 (fun b' => F a' b')) b) *
            P (EuclideanSpace.single a' (1 : ℂ)) a := by
      rw [linearMap_apply_eq_sum]
    _ = ∑ a', (∑ b', F a' b' * Q (EuclideanSpace.single b' (1 : ℂ)) b) *
            P (EuclideanSpace.single a' (1 : ℂ)) a := by
      refine Finset.sum_congr rfl ?_
      intro a' _
      rw [linearMap_apply_eq_sum]
    _ = ∑ b', (∑ a', F a' b' * P (EuclideanSpace.single a' (1 : ℂ)) a) *
            Q (EuclideanSpace.single b' (1 : ℂ)) b := by
      exact scalar_sum_comm F
        (fun a' => P (EuclideanSpace.single a' (1 : ℂ)) a)
        (fun b' => Q (EuclideanSpace.single b' (1 : ℂ)) b)
    _ = ∑ b', (P (WithLp.toLp 2 (fun a' => F a' b')) a) *
            Q (EuclideanSpace.single b' (1 : ℂ)) b := by
      refine Finset.sum_congr rfl ?_
      intro b' _
      have hP : (∑ a', F a' b' * P (EuclideanSpace.single a' (1 : ℂ)) a) =
          P (WithLp.toLp 2 (fun a' => F a' b')) a := by
        simpa using
          (linearMap_apply_eq_sum P (WithLp.toLp 2 (fun a' => F a' b')) a).symm
      rw [hP]
    _ = Q (WithLp.toLp 2 (fun b' => P (WithLp.toLp 2 (fun a' => F a' b')) a)) b := by
      rw [linearMap_apply_eq_sum]

private theorem cyclicRestrictES_single_of_sameOutsideWindow {N : ℕ} (hN : 0 < N) {L : ℕ}
    (hLN : L ≤ N) (i : Fin N) (σ τ : Cfg d N)
    (hστ : SameOutsideWindow (L := L) i σ τ) :
    cyclicRestrictES (d := d) hN L i τ (EuclideanSpace.single σ (1 : ℂ)) =
      EuclideanSpace.single (extractWindow L i σ) (1 : ℂ) := by
  ext ω
  by_cases hω : ω = extractWindow L i σ
  · subst hω
    have hreplace : replaceWindow L hLN i τ (extractWindow L i σ) =
        replaceWindow L hLN i σ (extractWindow L i σ) := by
      ext k
      by_cases hk : ((k.val + N - i.val) % N) < L
      · simp [replaceWindow, hk]
      · simp [replaceWindow, hk, hστ k hk]
    have hEq : cyclicCfg hN L i (extractWindow L i σ) τ = σ := by
      rw [cyclicCfg_eq_replaceWindow hN L hLN]
      simpa using hreplace.trans (replaceWindow_extractWindow L hLN i σ)
    rw [PiLp.single_apply]
    simp [hEq]
  · have hneq : cyclicCfg hN L i ω τ ≠ σ := by
      intro hEq
      apply hω
      have hextract := congrArg (extractWindow L i) hEq
      simpa [cyclicCfg_eq_replaceWindow, hLN] using hextract
    simp [cyclicRestrictES, hneq, hω]

private theorem cyclicRestrictES_single_of_not_sameOutsideWindow {N : ℕ} (hN : 0 < N) {L : ℕ}
    (i : Fin N) (σ τ : Cfg d N)
    (hστ : ¬ SameOutsideWindow (L := L) i σ τ) :
    cyclicRestrictES (d := d) hN L i τ (EuclideanSpace.single σ (1 : ℂ)) = 0 := by
  ext ω
  have hneq : cyclicCfg hN L i ω τ ≠ σ := by
    intro hEq
    exact hστ (sameOutsideWindow_of_cyclicCfg_eq hN i hEq)
  simp [cyclicRestrictES, hneq]

private theorem cyclicRestrictES_adjoint_apply {N : ℕ} (hN : 0 < N) {L : ℕ}
    (hLN : L ≤ N) (i : Fin N) (σ τ : Cfg d N)
    (v : EuclideanSpace ℂ (Cfg d L)) :
    ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ =
      if SameOutsideWindow (L := L) i σ τ then v (extractWindow L i σ) else 0 := by
  classical
  by_cases hστ : SameOutsideWindow (L := L) i σ τ
  · calc
      ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ
          = ⟪EuclideanSpace.single σ (1 : ℂ),
              (cyclicRestrictES (d := d) hN L i τ).adjoint v⟫_ℂ := by
              simpa using (EuclideanSpace.inner_single_left σ (1 : ℂ)
                ((cyclicRestrictES (d := d) hN L i τ).adjoint v)).symm
      _ = ⟪cyclicRestrictES (d := d) hN L i τ
              (EuclideanSpace.single σ (1 : ℂ)), v⟫_ℂ := by
            rw [LinearMap.adjoint_inner_right]
      _ = ⟪EuclideanSpace.single (extractWindow L i σ) (1 : ℂ), v⟫_ℂ := by
            rw [cyclicRestrictES_single_of_sameOutsideWindow hN hLN i σ τ hστ]
      _ = if SameOutsideWindow (L := L) i σ τ then v (extractWindow L i σ) else 0 := by
            simpa [hστ] using
              (EuclideanSpace.inner_single_left (extractWindow L i σ) (1 : ℂ) v)
  · calc
      ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ
          = ⟪EuclideanSpace.single σ (1 : ℂ),
              (cyclicRestrictES (d := d) hN L i τ).adjoint v⟫_ℂ := by
              simpa using (EuclideanSpace.inner_single_left σ (1 : ℂ)
                ((cyclicRestrictES (d := d) hN L i τ).adjoint v)).symm
      _ = ⟪cyclicRestrictES (d := d) hN L i τ
              (EuclideanSpace.single σ (1 : ℂ)), v⟫_ℂ := by
            rw [LinearMap.adjoint_inner_right]
      _ = ⟪0, v⟫_ℂ := by
            rw [cyclicRestrictES_single_of_not_sameOutsideWindow hN i σ τ hστ]
      _ = if SameOutsideWindow (L := L) i σ τ then v (extractWindow L i σ) else 0 := by
            simp [hστ]

@[simp] private theorem localTermES_apply {N : ℕ} (A : MPSTensor d D) (L : ℕ) (i : Fin N)
    (hLN : L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    localTermES A L i v σ =
      parentInteractionES A L ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v)
        (extractWindow L i σ) := by
  have hcfg :
      WithLp.toLp 2 ((LinearMap.pi fun τ =>
        (LinearMap.proj (replaceWindow L hLN i σ τ) : NSiteSpace d N →ₗ[ℂ] ℂ)) v.ofLp) =
      (cyclicRestrictES (d := d) (Fin.pos i) L i σ) v := by
    ext τ
    simp [cyclicRestrictES, cyclicCfg_eq_replaceWindow, hLN]
  have hself : cyclicCfg (d := d) (Fin.pos i) L i (extractWindow L i σ) σ = σ := by
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
    exact replaceWindow_extractWindow L hLN i σ
  simp [localTermES, localTerm, hLN, parentInteraction, parentInteractionES]
  simp [hcfg, hself]

private theorem cyclicRestrictES_localTermES {N : ℕ} (A : MPSTensor d D) {L : ℕ}
    (hLN : L ≤ N) (i : Fin N) (τ : Cfg d N) (v : EuclideanSpace ℂ (Cfg d N)) :
    cyclicRestrictES (d := d) (Fin.pos i) L i τ (localTermES A L i v) =
      parentInteractionES A L (cyclicRestrictES (d := d) (Fin.pos i) L i τ v) := by
  ext ω
  rw [cyclicRestrictES_apply]
  rw [localTermES_apply A L i hLN v (cyclicCfg (d := d) (Fin.pos i) L i ω τ)]
  have hsame : SameOutsideWindow (L := L) i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) τ :=
    sameOutsideWindow_of_cyclicCfg_eq (d := d) (Fin.pos i) i rfl
  have hrestrict :
      cyclicRestrictES (d := d) (Fin.pos i) L i τ =
        cyclicRestrictES (d := d) (Fin.pos i) L i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) :=
    cyclicRestrictES_eq_of_sameOutsideWindow (d := d) (Fin.pos i) i hsame
  have hextract : extractWindow L i (cyclicCfg (d := d) (Fin.pos i) L i ω τ) = ω := by
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
    exact extractWindow_replaceWindow L hLN i τ ω
  rw [← hrestrict, hextract]

/-- A transported local term vanishes exactly when every boundary-filled cyclic
restriction to its window lies in the `L`-site MPS ground space. -/
theorem localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    localTermES A L i v = 0 ↔
      ∀ τ : Cfg d N,
        cyclicRestrictES (d := d) (Fin.pos i) L i τ v ∈ groundSpaceES A L := by
  constructor
  · intro hv τ
    rw [← parentInteractionES_apply_eq_zero_iff]
    rw [← cyclicRestrictES_localTermES A hLN i τ v, hv, map_zero]
  · intro hv
    ext σ
    rw [localTermES_apply A L i hLN v σ]
    have hker := (parentInteractionES_apply_eq_zero_iff A L
      (cyclicRestrictES (d := d) (Fin.pos i) L i σ v)).2 (hv σ)
    rw [hker]
    rfl

/-- If a transported local term vanishes, every cyclic restriction to its window
is an element of the corresponding MPS ground space. -/
theorem cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) (i : Fin N)
    {v : EuclideanSpace ℂ (Cfg d N)} (hv : localTermES A L i v = 0)
    (τ : Cfg d N) :
    cyclicRestrictES (d := d) (Fin.pos i) L i τ v ∈ groundSpaceES A L :=
  (localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN i v).1 hv τ

private theorem restrictLast_eq_cyclicRestrictES_zero {L : ℕ}
    (v : EuclideanSpace ℂ (Cfg d (L + 1))) (τ : Cfg d (L + 1)) :
    restrictLast ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))) v) (τ (Fin.last L)) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
        (cyclicRestrictES (d := d) (Fin.pos (0 : Fin (L + 1))) L (0 : Fin (L + 1))
          τ v) := by
  ext σ
  change v.ofLp (Fin.snoc σ (τ (Fin.last L))) = v.ofLp
    (cyclicCfg (d := d) (Fin.pos (0 : Fin (L + 1))) L (0 : Fin (L + 1)) σ τ)
  apply congrArg v.ofLp
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨r, rfl⟩ | rfl
  · have hmod : r.val % (L + 1) = r.val := Nat.mod_eq_of_lt (by omega)
    simp [cyclicCfg, hmod]
  · simp [cyclicCfg]

private theorem restrictFirst_eq_cyclicRestrictES_one {L : ℕ} (hL : 0 < L)
    (v : EuclideanSpace ℂ (Cfg d (L + 1))) (τ : Cfg d (L + 1)) :
    restrictFirst ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))) v) (τ 0) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d L))
        (cyclicRestrictES (d := d) (Fin.pos (1 : Fin (L + 1))) L (1 : Fin (L + 1))
          τ v) := by
  ext σ
  change v.ofLp (Fin.cons (τ 0) σ) = v.ofLp
    (cyclicCfg (d := d) (Fin.pos (1 : Fin (L + 1))) L (1 : Fin (L + 1)) σ τ)
  apply congrArg v.ofLp
  funext k
  have hOneNat : 1 % (L + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨r, rfl⟩
  · simp [cyclicCfg, hOneNat]
  · have hmod : (r.val + 1 + L) % (L + 1) = r.val := by
      rw [show r.val + 1 + L = r.val + (L + 1) by omega]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp [cyclicCfg, hOneNat, hmod]

/-- Forward local intersection property for adjacent transported local terms.

On an `(L+1)`-site chain, if the two overlapping `L`-site local terms based at
`0` and `1` both annihilate a vector, then the vector lies in the `(L+1)`-site
MPS ground space.  This is the Euclidean/local-projector form of the
open-chain intersection property `groundSpace_intersection`; it is a structural
predecessor to the quantitative Friedrichs-angle estimate for overlapping
windows. -/
theorem mem_groundSpaceES_succ_of_adjacent_localTermES_eq_zero {A : MPSTensor d D}
    (hA : IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))}
    (hleft : localTermES A L (0 : Fin (L + 1)) v = 0)
    (hright : localTermES A L (1 : Fin (L + 1)) v = 0) :
    v ∈ groundSpaceES A (L + 1) := by
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))
  have hLN : L ≤ L + 1 := by omega
  have hLeft : InLeftGround A L (eN v) := by
    intro j
    have hmemES : cyclicRestrictES (d := d) (Fin.pos (0 : Fin (L + 1))) L
        (0 : Fin (L + 1)) (fun _ => j) v ∈ groundSpaceES A L :=
      cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero A hLN
        (0 : Fin (L + 1)) hleft (fun _ => j)
    have hmemNS := (mem_groundSpaceES_iff A L _).1 hmemES
    rwa [restrictLast_eq_cyclicRestrictES_zero v (fun _ => j)]
  have hRight : InRightGround A L (eN v) := by
    intro i
    have hmemES : cyclicRestrictES (d := d) (Fin.pos (1 : Fin (L + 1))) L
        (1 : Fin (L + 1)) (fun _ => i) v ∈ groundSpaceES A L :=
      cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero A hLN
        (1 : Fin (L + 1)) hright (fun _ => i)
    have hmemNS := (mem_groundSpaceES_iff A L _).1 hmemES
    rwa [restrictFirst_eq_cyclicRestrictES_one (by omega : 0 < L) v (fun _ => i)]
  have hψ : eN v ∈ groundSpace A (L + 1) :=
    groundSpace_intersection hA hL hLeft hRight
  exact (mem_groundSpaceES_iff A (L + 1) v).2 hψ

/-- Vectors in the `(L+1)`-site MPS ground space are killed by the two adjacent
`L`-site transported local terms. -/
theorem adjacent_localTermES_eq_zero_of_mem_groundSpaceES_succ
    (A : MPSTensor d D) {L : ℕ} (hL : 0 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))} (hv : v ∈ groundSpaceES A (L + 1)) :
    localTermES A L (0 : Fin (L + 1)) v = 0 ∧
      localTermES A L (1 : Fin (L + 1)) v = 0 := by
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))
  have hψ : eN v ∈ groundSpace A (L + 1) := (mem_groundSpaceES_iff A (L + 1) v).1 hv
  have hLN : L ≤ L + 1 := by omega
  constructor
  · rw [localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN
      (0 : Fin (L + 1)) v]
    intro τ
    rw [mem_groundSpaceES_iff]
    rw [← restrictLast_eq_cyclicRestrictES_zero v τ]
    exact groundSpace_inLeftGround A L hψ (τ (Fin.last L))
  · rw [localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A hLN
      (1 : Fin (L + 1)) v]
    intro τ
    rw [mem_groundSpaceES_iff]
    rw [← restrictFirst_eq_cyclicRestrictES_one hL v τ]
    exact groundSpace_inRightGround A L hψ (τ 0)

/-- Adjacent local kernels on an `(L+1)`-site chain intersect in the MPS ground
space.  This restates the open-chain intersection property in the same
Euclidean local-projector language used by the martingale proof. -/
theorem adjacent_localTermES_eq_zero_iff_mem_groundSpaceES_succ {A : MPSTensor d D}
    (hA : IsInjective A) {L : ℕ} (hL : 1 < L)
    {v : EuclideanSpace ℂ (Cfg d (L + 1))} :
    localTermES A L (0 : Fin (L + 1)) v = 0 ∧
      localTermES A L (1 : Fin (L + 1)) v = 0 ↔
        v ∈ groundSpaceES A (L + 1) := by
  constructor
  · intro h
    exact mem_groundSpaceES_succ_of_adjacent_localTermES_eq_zero hA hL h.1 h.2
  · intro hv
    exact adjacent_localTermES_eq_zero_of_mem_groundSpaceES_succ A (by omega : 0 < L) hv

@[simp] private theorem localTermESSummand_apply {N : ℕ} (A : MPSTensor d D) (hN : 0 < N)
    {L : ℕ} (hLN : L ≤ N) (i : Fin N) (τ v σ) :
    localTermESSummand A hN L i τ v σ =
      if SameOutsideWindow (L := L) i σ τ then localTermES A L i v σ else 0 := by
  classical
  rw [localTermESSummand]
  simp only [LinearMap.comp_apply]
  by_cases hστ : SameOutsideWindow (L := L) i σ τ
  · rw [cyclicRestrictES_adjoint_apply hN hLN i σ τ]
    rw [if_pos hστ, localTermES_apply A L i hLN v σ]
    simp [hστ, cyclicRestrictES_eq_of_sameOutsideWindow hN i hστ]
  · rw [cyclicRestrictES_adjoint_apply hN hLN i σ τ, if_neg hστ]
    simp [hστ]

private theorem sameOutsideWindow_card {N : ℕ} {L : ℕ} (hLN : L ≤ N)
    (i : Fin N) (σ : Cfg d N) :
    Fintype.card {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ} = d ^ L := by
  let f : Cfg d L → {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ} :=
    fun ω => ⟨replaceWindow L hLN i σ ω, by
      intro k hk
      simp [replaceWindow, hk]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro ω₁ ω₂ h
      have h' := congrArg (fun τ : {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ} =>
        extractWindow L i τ.1) h
      simpa [f] using h'
    · intro τ
      refine ⟨extractWindow L i τ.1, ?_⟩
      apply Subtype.ext
      have hreplace : replaceWindow L hLN i σ (extractWindow L i τ.1) =
          replaceWindow L hLN i τ.1 (extractWindow L i τ.1) := by
        ext k
        by_cases hk : ((k.val + N - i.val) % N) < L
        · simp [replaceWindow, hk]
        · simp [replaceWindow, hk, τ.2 k hk]
      simpa [f] using hreplace.trans (replaceWindow_extractWindow L hLN i τ.1)
  calc
    Fintype.card {τ : Cfg d N // SameOutsideWindow (L := L) i σ τ}
        = Fintype.card (Cfg d L) := (Fintype.card_of_bijective (f := f) hf).symm
    _ = d ^ L := by simp [Cfg]

/-- The transported local term is the cyclic average of the positive Euclidean
summands `Rᵢ,τ† P_L Rᵢ,τ`. -/
theorem localTermES_eq_average_localTermESSummand {N : ℕ} (A : MPSTensor d D)
    {L : ℕ} (hLN : L ≤ N) (i : Fin N) :
    localTermES A L i =
      ((((d ^ L : ℕ) : ℂ)⁻¹) •
        (∑ τ : Cfg d N, localTermESSummand A (Fin.pos i) L i τ)) := by
  classical
  ext v σ
  let q : Cfg d N → Prop := SameOutsideWindow (L := L) i σ
  let sq : Finset (Cfg d N) := Finset.univ.filter q
  have hfilter :
      (∑ τ : Cfg d N, if q τ then localTermES A L i v σ else 0) =
        sq.sum (fun _ => localTermES A L i v σ) := by
    dsimp [sq]
    symm
    simpa using (Finset.sum_filter (s := Finset.univ) (p := q)
      (f := fun _ => localTermES A L i v σ))
  have hsconst :
      sq.sum (fun _ => localTermES A L i v σ) =
        sq.card • localTermES A L i v σ := by
    exact Finset.sum_const (s := sq) (b := localTermES A L i v σ)
  have hcard_filter : sq.card = Fintype.card {τ : Cfg d N // q τ} := by
    dsimp [sq]
    symm
    simpa using (Fintype.card_subtype q)
  have hne_nat : (d ^ L : ℕ) ≠ 0 := by
    have hcard : Fintype.card (Cfg d L) = d ^ L := by
      simp [Cfg]
    have : Fintype.card (Cfg d L) ≠ 0 := by
      let _ : Nonempty (Cfg d L) := ⟨extractWindow L i σ⟩
      exact Fintype.card_ne_zero
    rwa [hcard] at this
  have hne : (((d ^ L : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast hne_nat
  calc
    localTermES A L i v σ
        = (((d ^ L : ℕ) : ℂ)⁻¹) * ((d ^ L) • localTermES A L i v σ) := by
            symm
            rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (Fintype.card {τ : Cfg d N // q τ} • localTermES A L i v σ) := by
            rw [sameOutsideWindow_card hLN i σ]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (sq.card • localTermES A L i v σ) := by rw [hcard_filter]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (sq.sum (fun _ => localTermES A L i v σ)) := by rw [hsconst]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (∑ τ : Cfg d N, if q τ then localTermES A L i v σ else 0) := by rw [hfilter]
    _ = (((d ^ L : ℕ) : ℂ)⁻¹) *
          (∑ τ : Cfg d N, localTermESSummand A (Fin.pos i) L i τ v σ) := by
            simp [q, localTermESSummand_apply, hLN]
    _ = ((((d ^ L : ℕ) : ℂ)⁻¹) • (∑ τ : Cfg d N,
          localTermESSummand A (Fin.pos i) L i τ)) v σ := by
            simp

private theorem isPositive_smul_of_real_re_nonneg {ι : Type*} [Fintype ι]
    {T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hT : T.IsPositive) {c : ℂ}
    (hc_star : star c = c) (hc_re : 0 ≤ c.re) :
    (c • T).IsPositive := by
  refine ⟨hT.left.smul hc_star, fun x => ?_⟩
  have him : c.im = 0 := by
    have him' := congrArg Complex.im hc_star
    simp at him'
    linarith
  have himstar : RCLike.im ((starRingEnd ℂ) c) = 0 := by
    simp [him]
  have hre : RCLike.re ((starRingEnd ℂ) c) = c.re := by
    simp
  change 0 ≤ RCLike.re ⟪c • T x, x⟫_ℂ
  rw [inner_smul_left, RCLike.mul_re, himstar, zero_mul, sub_zero, hre]
  exact mul_nonneg hc_re (hT.re_inner_nonneg_left x)

/-- The transported local term is positive because it is a finite cyclic average
of the positive summands `Rᵢ,τ† P_L Rᵢ,τ`. -/
theorem localTermES_isPositive {N : ℕ} (A : MPSTensor d D) (L : ℕ) (i : Fin N) :
    (localTermES A L i).IsPositive := by
  by_cases hLN : L ≤ N
  · rw [localTermES_eq_average_localTermESSummand A hLN i]
    refine isPositive_smul_of_real_re_nonneg
      (localTermESSummand_sum_isPositive A (Fin.pos i) L i) ?_ ?_
    · simp
    · rw [Complex.inv_re, Complex.normSq_natCast]
      have hnonneg : 0 ≤ ((d ^ L : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (d ^ L)
      exact div_nonneg hnonneg (mul_nonneg hnonneg hnonneg)
  · simp [localTermES, localTerm, hLN]

private theorem localTermES_isIdempotentElem {N : ℕ} (A : MPSTensor d D) (L : ℕ)
    (i : Fin N) : IsIdempotentElem (localTermES A L i) := by
  by_cases hLN : L ≤ N
  · rw [isIdempotentElem_iff]
    ext v σ
    change localTermES A L i (localTermES A L i v) σ = localTermES A L i v σ
    rw [localTermES_apply A L i hLN (localTermES A L i v) σ]
    rw [cyclicRestrictES_localTermES A hLN i σ v]
    rw [localTermES_apply A L i hLN v σ]
    have hPapply :
        parentInteractionES A L
            (parentInteractionES A L ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v)) =
          parentInteractionES A L ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v) := by
      simpa [Module.End.mul_apply] using
        LinearMap.congr_fun
          (parentInteractionES_isSymmetricProjection A L).isIdempotentElem.eq
          ((cyclicRestrictES (d := d) (Fin.pos i) L i σ) v)
    rw [hPapply]
  · simpa [localTermES, localTerm, hLN] using
      (IsIdempotentElem.zero :
        IsIdempotentElem
          (0 : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N)))

/-- Each transported local parent-Hamiltonian term is a symmetric projection.

This is the Euclidean-space version of the fact that the local term is the
orthogonal projector onto the complement of the translated local ground space.
For `L ≤ N`, idempotence follows by restricting to the cyclic window, applying
the local projector `parentInteractionES`, and using `P_L^2 = P_L`; for `L > N`
the definition gives the zero projection. -/
theorem localTermES_isSymmetricProjection {N : ℕ} (A : MPSTensor d D) (L : ℕ)
    (i : Fin N) : (localTermES A L i).IsSymmetricProjection :=
  ⟨localTermES_isIdempotentElem A L i, (localTermES_isPositive A L i).isSymmetric⟩

/-- Transported local terms on site-disjoint cyclic windows commute pointwise.

If `L ≤ N` and no site belongs to both cyclic windows based at `i` and `j`, then
applying the two transported local ES terms in either order gives the same vector.
This is the non-overlap commutation input for the finite-overlap martingale
reduction. -/
theorem localTermES_commute_of_cyclic_windows_disjoint {N : ℕ} (A : MPSTensor d D)
    {L : ℕ} (hLN : L ≤ N) {i j : Fin N} (hij : CyclicWindowsDisjoint L i j)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    localTermES A L i (localTermES A L j v) =
      localTermES A L j (localTermES A L i v) := by
  ext σ
  let P := parentInteractionES A L
  let F : Cfg d L → Cfg d L → ℂ := fun α β =>
    v (replaceWindow L hLN j (replaceWindow L hLN i σ α) β)
  have hleft :
      cyclicRestrictES (d := d) (Fin.pos i) L i σ (localTermES A L j v) =
        WithLp.toLp 2 (fun α => P (WithLp.toLp 2 (fun β => F α β))
          (extractWindow L j σ)) := by
    ext α
    rw [cyclicRestrictES_apply]
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
    rw [localTermES_apply A L j hLN v (replaceWindow L hLN i σ α)]
    rw [extractWindow_replaceWindow_of_cyclic_windows_disjoint (d := d) hLN hij.symm σ α]
    have hrestrict :
        cyclicRestrictES (d := d) (Fin.pos j) L j (replaceWindow L hLN i σ α) v =
          WithLp.toLp 2 (fun β => F α β) := by
      ext β
      rw [cyclicRestrictES_apply]
      rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos j) L hLN]
    rw [hrestrict]
  have hright :
      cyclicRestrictES (d := d) (Fin.pos j) L j σ (localTermES A L i v) =
        WithLp.toLp 2 (fun β => P (WithLp.toLp 2 (fun α => F α β))
          (extractWindow L i σ)) := by
    ext β
    rw [cyclicRestrictES_apply]
    rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos j) L hLN]
    rw [localTermES_apply A L i hLN v (replaceWindow L hLN j σ β)]
    rw [extractWindow_replaceWindow_of_cyclic_windows_disjoint (d := d) hLN hij σ β]
    have hrestrict :
        cyclicRestrictES (d := d) (Fin.pos i) L i (replaceWindow L hLN j σ β) v =
          WithLp.toLp 2 (fun α => F α β) := by
      ext α
      rw [cyclicRestrictES_apply]
      rw [cyclicCfg_eq_replaceWindow (d := d) (Fin.pos i) L hLN]
      simp only [F]
      rw [← replaceWindow_commute_of_cyclic_windows_disjoint (d := d) hLN hij σ α β]
    rw [hrestrict]
  rw [localTermES_apply A L i hLN (localTermES A L j v) σ]
  rw [localTermES_apply A L j hLN (localTermES A L i v) σ]
  rw [hleft, hright]
  simpa [P] using separateLinearMap_apply_commute P P F (extractWindow L i σ)
    (extractWindow L j σ)

/-- Non-overlap positivity for transported local terms on disjoint cyclic windows.

For `L ≤ N`, if the cyclic windows based at `i` and `j` have no common site, then
the ordered cross term of the corresponding transported local ES projections is
nonnegative: `0 ≤ Re ⟪h_i v, h_j v⟫`. -/
theorem localTermES_re_inner_nonneg_of_cyclic_windows_disjoint {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : CyclicWindowsDisjoint L i j) (v : EuclideanSpace ℂ (Cfg d N)) :
    0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re :=
  LinearMap.IsSymmetricProjection.re_inner_apply_apply_nonneg_of_commute
    (localTermES_isSymmetricProjection A L i)
    (localTermES_isSymmetricProjection A L j)
    (localTermES_commute_of_cyclic_windows_disjoint A hLN hij) v

/-- Non-overlap positivity for the concrete cyclic-window overlap predicate.

When `cyclicWindowsOverlap N L i j` fails and `L ≤ N`, the two windows are
site-disjoint, so the transported local terms commute and have nonnegative ordered
cross term. -/
theorem localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap {N : ℕ}
    (A : MPSTensor d D) {L : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : ¬ cyclicWindowsOverlap N L i j) (v : EuclideanSpace ℂ (Cfg d N)) :
    0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re :=
  localTermES_re_inner_nonneg_of_cyclic_windows_disjoint A hLN
    (CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap hij) v

/-- The full transported parent Hamiltonian is positive because it is a finite
sum of positive transported local terms. -/
theorem parentHamiltonianES_isPositive (A : MPSTensor d D) (L N : ℕ) :
    (parentHamiltonianES A L N).IsPositive := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A L i

/-- The transported parent-Hamiltonian ground space is exactly the kernel of the
transported parent Hamiltonian. -/
theorem parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES
    (A : MPSTensor d D) (L N : ℕ) :
    parentHamiltonianGroundSpaceES A L N =
      LinearMap.ker (parentHamiltonianES A L N) := by
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  ext v
  constructor
  · intro hv
    rw [parentHamiltonianGroundSpaceES, Submodule.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [LinearMap.mem_ker] at hw ⊢
    simpa [parentHamiltonianES, e] using congrArg e.symm hw
  · intro hv
    rw [LinearMap.mem_ker] at hv
    rw [parentHamiltonianGroundSpaceES, Submodule.mem_map]
    refine ⟨e v, ?_, by simp [e]⟩
    rw [LinearMap.mem_ker]
    have hv' := congrArg e hv
    simpa [parentHamiltonianES, e] using hv'

@[simp] theorem mem_parentHamiltonianGroundSpaceES_iff
    (A : MPSTensor d D) (L N : ℕ) (v : EuclideanSpace ℂ (Cfg d N)) :
    v ∈ parentHamiltonianGroundSpaceES A L N ↔ parentHamiltonianES A L N v = 0 := by
  rw [parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES, LinearMap.mem_ker]

/-! ### Martingale quadratic-form reduction -/

/-- A uniform quadratic-form estimate for the transported parent Hamiltonians
implies the corresponding norm lower bound on the orthogonal complement of the
transported ground space.

This theorem isolates the operator-theoretic part of the remaining
Friedrichs-angle route. The hypotheses already include the quantitative
martingale/Friedrichs estimate

`γ * re ⟪H_N v, v⟫ ≤ re ⟪H_N v, H_N v⟫`,

to be supplied later from the finite-overlap projection geometry. The proof
uses the established positivity of `parentHamiltonianES`, the kernel
identification `parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES`, and
the abstract spectral-theorem step `FrustrationFree.spectralGap_of_martingale`. -/
theorem parentHamiltonianES_norm_bound_of_quadratic_form
    (A : MPSTensor d D) (L : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hQuad : ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
        γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
          (⟪parentHamiltonianES A L N v,
              parentHamiltonianES A L N v⟫_ℂ).re) :
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  intro N hLN v hv
  have hvKer : v ∈ (LinearMap.ker (parentHamiltonianES A L N))ᗮ := by
    simpa [parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES A L N] using hv
  exact FrustrationFree.spectralGap_of_martingale (ι := Cfg d N) hγ
    (parentHamiltonianES_isPositive A L N) (hQuad N hLN) v hvKer

/-- The exact explicit gap-bound reduction needed by
`parentHamiltonianES_gap_bound_of_friedrichs` follows from the corresponding
uniform quadratic-form estimate with constant `1 / (4 * L)`.

Thus the remaining MPS-specific content is precisely to prove the hypothesis
`hQuad` from the Friedrichs-angle / anti-commutator estimate and the finite
row-sum bound; the positivity, kernel transport, and spectral-theorem conversion
are already available here. -/
theorem parentHamiltonianES_gap_bound_of_quadratic_form
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hQuad : ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
        ((1 : ℝ) / (4 * (L : ℝ))) *
          (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
            (⟪parentHamiltonianES A L N v,
                parentHamiltonianES A L N v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  have hγ : 0 < (1 : ℝ) / (4 * (L : ℝ)) := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hL)
    exact div_pos (by norm_num) (mul_pos (by norm_num) hLpos)
  exact ⟨hγ, parentHamiltonianES_norm_bound_of_quadratic_form A L hγ hQuad⟩

/-- Fixed-chain martingale quadratic-form estimate from ordered local
cross-term row bounds.

This theorem is the parent-Hamiltonian instantiation of the abstract projection
geometry in `ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum`.
The local projection input is supplied by `localTermES_isSymmetricProjection`, so
its hypotheses are only the ordered row-summable cross-term bounds

`Re ⟪hᵢ v, hⱼ v⟫ ≥ -(1 - γ) cᵢⱼ Re ⟪hᵢ v, v⟫`.

Under these hypotheses the transported Hamiltonian satisfies `H² ≥ γ H` as a
quadratic form, exactly in the shape consumed by
`parentHamiltonianES_norm_bound_of_quadratic_form`. -/
theorem parentHamiltonianES_quadratic_form_of_ordered_local_term_bounds
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (c : Fin N → Fin N → ℝ)
    (hRow : ∀ i : Fin N, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCross : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - γ) * c i j * (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) c hRow hCross v)

/-- Uniform explicit gap-bound reduction from ordered local cross-term row
bounds.

For every chain length `N ≥ 2L`, assume the transported local terms satisfy the
ordered row-summable cross-term estimate with constant `γ = 1 / (4L)`. The local
symmetric-projection input is already supplied by `localTermES_isSymmetricProjection`.
Then the existing quadratic-form-to-gap theorem applies and yields the explicit
norm lower bound. This exact reduction leaves proving the Friedrichs/row-sum
hypotheses for the concrete MPS local terms as the model-specific analytic task. -/
theorem parentHamiltonianES_gap_bound_of_ordered_local_term_bounds
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (c : ∀ N : ℕ, Fin N → Fin N → ℝ)
    (hRow : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      (∑ j ∈ Finset.univ.erase i, c N i j) ≤ 1)
    (hCross : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * c N i j *
            (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  refine parentHamiltonianES_gap_bound_of_quadratic_form A L hL ?_
  intro N hLN v
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hL)
  have hLge_one : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hL)
  have hγle : ((1 : ℝ) / (4 * (L : ℝ))) ≤ 1 := by
    have hden : 0 < 4 * (L : ℝ) := mul_pos (by norm_num) hLpos
    rw [div_le_iff₀ hden]
    nlinarith [hLge_one]
  exact parentHamiltonianES_quadratic_form_of_ordered_local_term_bounds
    A L N hγle (c N) (hRow N hLN) (hCross N hLN) v

/-- Fixed-chain martingale quadratic-form estimate from finite-overlap
Friedrichs data.

This is the local-window specialization of
`ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap`.  The
predicate `overlaps i j` marks the off-diagonal pairs for which a Friedrichs-angle
estimate is needed.  If each row has at most `m` such pairs, the non-overlap
cross terms are nonnegative, and every overlap obeys the ordered estimate with
coefficient `1 / m`, then the transported parent Hamiltonian satisfies
`H² ≥ γ H` as a quadratic form. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_friedrichs
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hProj : ∀ i : Fin N, (localTermES A L i).IsSymmetricProjection)
    (hCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hFriedrichs : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        - (1 - γ) * ((m : ℝ)⁻¹) * (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i) hProj overlaps hm hCard hDisjoint
      hFriedrichs v)

/-- Fixed-chain martingale quadratic-form estimate from finite-overlap
norm-compression Friedrichs data.

For each overlapping pair, it is enough to bound the compressed product
`‖hᵢ (hⱼ v)‖` by `(1 - γ) / m` times `‖hᵢ v‖`.  The abstract projection-geometry
lemma converts this principal-angle style norm estimate into the ordered
cross-term bound consumed by the finite-overlap row-sum reduction. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound
    (A : MPSTensor d D) (L N : ℕ) {γ : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hOverlapNorm : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        ‖localTermES A L i (localTermES A L j v)‖ ≤
          ((1 - γ) * ((m : ℝ)⁻¹)) * ‖localTermES A L i v‖) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_norm_bound
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) overlaps hm hCard
      hDisjoint hOverlapNorm v)

/-- Fixed-chain finite-overlap quadratic-form estimate from a separate
norm-compression coefficient.

If the compressed products on overlapping pairs are bounded by `η`, and
`η ≤ (1 - γ) / m`, then the fixed-chain martingale quadratic form follows with
constant `γ`.  This version keeps the analytic overlap constant separate from the
gap parameter. -/
theorem parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound_of_le
    (A : MPSTensor d D) (L N : ℕ) {γ η : ℝ} (hγle : γ ≤ 1)
    (overlaps : Fin N → Fin N → Prop) [DecidableRel overlaps] {m : ℕ} (hm : 0 < m)
    (hCard : ∀ i : Fin N,
      ((Finset.univ.erase i).filter (fun j => overlaps i j)).card ≤ m)
    (hDisjoint : ∀ i j : Fin N, j ∈ Finset.univ.erase i → ¬ overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hηle : η ≤ (1 - γ) * ((m : ℝ)⁻¹))
    (hOverlapNorm : ∀ i j : Fin N, j ∈ Finset.univ.erase i → overlaps i j →
      ∀ v : EuclideanSpace ℂ (Cfg d N),
        ‖localTermES A L i (localTermES A L j v)‖ ≤
          η * ‖localTermES A L i v‖) :
    ∀ v : EuclideanSpace ℂ (Cfg d N),
      γ * (⟪parentHamiltonianES A L N v, v⟫_ℂ).re ≤
        (⟪parentHamiltonianES A L N v,
          parentHamiltonianES A L N v⟫_ℂ).re := by
  intro v
  simpa [parentHamiltonianES_eq_sum_localTermES A L N] using
    (ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_norm_bound_of_le
      (ι := Fin N) (E := EuclideanSpace ℂ (Cfg d N)) hγle
      (fun i : Fin N => localTermES A L i)
      (fun i : Fin N => localTermES_isSymmetricProjection A L i) overlaps hm hCard
      hDisjoint hηle hOverlapNorm v)

/-- Uniform explicit gap-bound reduction from finite-overlap Friedrichs data.

For parent-Hamiltonian windows of length `L`, the expected finite-range bound is
`m = 2 * (L - 1)`: each local term overlaps at most that many other cyclic
translates when `N ≥ 2L`.  This theorem leaves the transported local projection
structure, the cyclic-window overlap predicate, non-overlap positivity, and the
Friedrichs-angle estimate as explicit hypotheses. It only performs the finite-overlap
row-sum reduction and the existing quadratic-form-to-gap conversion. -/
theorem parentHamiltonianES_gap_bound_of_finite_overlap_friedrichs
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (overlaps : ∀ N : ℕ, Fin N → Fin N → Prop)
    [∀ N : ℕ, DecidableRel (overlaps N)]
    (hProj : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      (localTermES A L i).IsSymmetricProjection)
    (hCard : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i : Fin N),
      ((Finset.univ.erase i).filter (fun j => overlaps N i j)).card ≤ 2 * (L - 1))
    (hDisjoint : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → ¬ overlaps N i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          0 ≤ (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re)
    (hFriedrichs : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → overlaps N i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
                (⟪localTermES A L i v, v⟫_ℂ).re ≤
            (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  refine parentHamiltonianES_gap_bound_of_quadratic_form A L hL ?_
  intro N hLN v
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hL)
  have hLge_one : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hL)
  have hγle : ((1 : ℝ) / (4 * (L : ℝ))) ≤ 1 := by
    have hden : 0 < 4 * (L : ℝ) := mul_pos (by norm_num) hLpos
    rw [div_le_iff₀ hden]
    nlinarith [hLge_one]
  have hm : 0 < 2 * (L - 1) :=
    Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)
  exact parentHamiltonianES_quadratic_form_of_finite_overlap_friedrichs
    A L N hγle (overlaps N) hm (hProj N hLN) (hCard N hLN)
    (hDisjoint N hLN) (hFriedrichs N hLN) v

/-- Uniform explicit gap-bound reduction using the concrete cyclic-window overlap
predicate.

For chains with `N ≥ 2L`, the predicate `cyclicWindowsOverlap N L i j` marks the
cyclic translates whose length-`L` windows have the finite-range overlap relevant
to the martingale method.  The row-cardinality estimate is supplied by
`cyclicWindowsOverlap_card_le`, local projection structure is supplied by
`localTermES_isSymmetricProjection`, and non-overlap positivity is supplied by
`localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap`.  Consequently the
only remaining local hypothesis is the Friedrichs-angle estimate for pairs
marked by `cyclicWindowsOverlap`. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hFriedrichs : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
                (⟪localTermES A L i v, v⟫_ℂ).re ≤
            (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  exact parentHamiltonianES_gap_bound_of_finite_overlap_friedrichs A L hL
    (fun N => cyclicWindowsOverlap N L)
    (fun N _hLN i => localTermES_isSymmetricProjection A L i)
    (fun N hLN i => cyclicWindowsOverlap_card_le hLN hL i)
    (fun N hLN i j _hij hnot v =>
      localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap A (by omega) hnot v)
    hFriedrichs

/-- Uniform explicit gap-bound reduction from the remaining overlapping-window
Friedrichs estimate.

The concrete cyclic-window row-cardinality bound, local symmetric-projection
structure, and non-overlap positivity are already proved.  Consequently it is
enough to assume the displayed ordered Friedrichs lower bound only for pairs whose
cyclic supports overlap. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_friedrichs
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hFriedrichs : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
                (⟪localTermES A L i v, v⟫_ℂ).re ≤
            (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  exact parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs A L hL hFriedrichs

/-- Uniform explicit gap-bound reduction from a norm-compression form of the
overlapping-window Friedrichs estimate.

It suffices to prove that for every overlapping off-diagonal pair the compressed
product of transported local projections satisfies
`‖hᵢ (hⱼ v)‖ ≤ (1 - 1/(4L)) / (2(L-1)) * ‖hᵢ v‖`.  The abstract projection
geometry converts this principal-angle style condition into the ordered
Friedrichs lower bound and then applies the finite-overlap martingale reduction. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            ((1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) * ‖localTermES A L i v‖) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  refine parentHamiltonianES_gap_bound_of_cyclic_window_overlap_friedrichs A L hL ?_
  intro N hLN i j hij hoverlap v
  have hCross :
      -((1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
          (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) *
        (⟪localTermES A L i v, v⟫_ℂ).re ≤
          (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re :=
    (localTermES_isSymmetricProjection A L i).re_inner_apply_apply_ge_neg_of_norm_apply_le
      (hOverlapNorm N hLN i j hij hoverlap) v
  convert hCross using 1
  ring

/-- Uniform gap-bound reduction from an overlap norm-compression estimate with a
separate coefficient.

For cyclic windows with at most `2 * (L - 1)` overlapping off-diagonal neighbours,
a compression estimate with coefficient `η` gives any positive gap parameter `γ`
satisfying `η ≤ (1 - γ) / (2 * (L - 1))`.  This is the constant-flexible form of
`parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound`. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_le
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L) {γ η : ℝ}
    (hγpos : 0 < γ) (hγle : γ ≤ 1)
    (hηle : η ≤ (1 - γ) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹))
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            η * ‖localTermES A L i v‖) :
    0 < γ ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  refine ⟨hγpos, ?_⟩
  refine parentHamiltonianES_norm_bound_of_quadratic_form A L hγpos ?_
  intro N hLN v
  have hm : 0 < 2 * (L - 1) :=
    Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)
  exact parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound_of_le
    A L N hγle (cyclicWindowsOverlap N L) hm
    (fun i => cyclicWindowsOverlap_card_le hLN hL i)
    (fun _i _j _hij hnot w =>
      localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap A (by omega) hnot w)
    hηle (fun i j hij hoverlap w => hOverlapNorm N hLN i j hij hoverlap w) v

/-- Uniform gap-bound reduction from a strict overlap norm-compression constant.

If every overlapping off-diagonal cyclic pair satisfies the compression estimate
with coefficient `η`, and `η * (2 * (L - 1)) < 1`, then the transported parent
Hamiltonians have gap constant `1 - η * (2 * (L - 1))`.  Thus any uniform
compression constant strictly below the reciprocal of the cyclic overlap degree
yields a positive gap. -/
theorem parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_lt
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L) {η : ℝ}
    (hηnonneg : 0 ≤ η)
    (hηlt : η * (((2 * (L - 1) : ℕ) : ℝ)) < 1)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            η * ‖localTermES A L i v‖) :
    0 < 1 - η * (((2 * (L - 1) : ℕ) : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        (1 - η * (((2 * (L - 1) : ℕ) : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  have hm : 0 < 2 * (L - 1) :=
    Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hL)
  have hmRpos : 0 < (((2 * (L - 1) : ℕ) : ℝ)) := by
    exact_mod_cast hm
  have hγpos : 0 < 1 - η * (((2 * (L - 1) : ℕ) : ℝ)) := by
    linarith
  have hγle : 1 - η * (((2 * (L - 1) : ℕ) : ℝ)) ≤ 1 := by
    have hmul_nonneg : 0 ≤ η * (((2 * (L - 1) : ℕ) : ℝ)) :=
      mul_nonneg hηnonneg hmRpos.le
    linarith
  have hηle :
      η ≤ (1 - (1 - η * (((2 * (L - 1) : ℕ) : ℝ)))) *
        (((2 * (L - 1) : ℕ) : ℝ)⁻¹) := by
    have hmne : (((2 * (L - 1) : ℕ) : ℝ)) ≠ 0 := ne_of_gt hmRpos
    have hηeq :
        η = (1 - (1 - η * (((2 * (L - 1) : ℕ) : ℝ)))) *
          (((2 * (L - 1) : ℕ) : ℝ)⁻¹) := by
      calc
        η = η * (((2 * (L - 1) : ℕ) : ℝ) *
            (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) := by
              rw [mul_inv_cancel₀ hmne, mul_one]
        _ = (1 - (1 - η * (((2 * (L - 1) : ℕ) : ℝ)))) *
            (((2 * (L - 1) : ℕ) : ℝ)⁻¹) := by ring
    exact le_of_eq hηeq
  exact parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_le
    A L hL hγpos hγle hηle hOverlapNorm

/-! ### Uniform spectral gap for the MPS parent Hamiltonian -/

/- Scout report (2026-04-19, Layer 4 KL martingale).

1. **Friedrichs-angle surface:** TNLean currently has no dedicated
`FriedrichsAngle`/principal-angle development in `TNLean/Analysis`. Mathlib provides
orthogonal-projection structure (for example
`Mathlib.Analysis.InnerProductSpace.Projection.Basic` and
`Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`, exposing
`Submodule.starProjection` and `orthogonalProjection`) but not a ready-made
Kastoryano–Lucia-style angle-to-anticommutator bound. This is a real blocker
for quantitative overlap constants.
2. **Projection/positivity formulation:** the local `EuclideanSpace` projector
`parentInteractionES A L` and each transported local term are now available as
symmetric projections, and the conjugated cyclic-restriction summands
`localTermESSummand A hN L i τ = Rᵢ,τ† P_L Rᵢ,τ` plus the full transported
Hamiltonian are available as positive operators.
3. **Quadratic-form reduction:**
`parentHamiltonianES_norm_bound_of_quadratic_form` and
`parentHamiltonianES_gap_bound_of_quadratic_form` reduce the gap statement to a
uniform estimate `γ * re ⟪H_N v, v⟫ ≤ re ⟪H_N v, H_N v⟫`.
4. **Projection-geometry row reduction:**
`ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum`,
`parentHamiltonianES_quadratic_form_of_ordered_local_term_bounds`, and
`parentHamiltonianES_gap_bound_of_ordered_local_term_bounds` now formalize the
finite-sum algebra turning explicit ordered cross-term row bounds for local
symmetric projections into the quadratic-form hypothesis above.
5. **Remaining local analytic step:** local projection structure, cyclic-window
row cardinality, and non-overlap positivity are now formalized above. The remaining
hypothesis is the Friedrichs-angle estimate for overlapping cyclic windows with the
coefficient required by the finite-overlap row reduction.
6. **Spectral-gap theorem:** `parentHamiltonian_gapped` is the subsequent
existential theorem, now proved by applying the Friedrichs-angle theorem
below. The theorem `parentHamiltonianES_gap_bound_of_friedrichs` still depends
on the missing Friedrichs-angle formulation; this is the blocker and should not
be replaced with axioms or unrelated sorrys. -/
/-- Friedrichs-angle and row-sum estimate for the MPS parent Hamiltonian.

This is the remaining MPS-specific martingale estimate: it should produce a
specific uniform positive lower bound for the transported parent Hamiltonian
from the intersection property and finite-overlap geometry. The concrete
constant is intentionally part of this theorem statement, so the public
`parentHamiltonian_gapped` theorem only has to re-express it as an existential
spectral gap. -/
theorem parentHamiltonianES_gap_bound_of_friedrichs
    (A : MPSTensor d D) (_hA : IsInjective A) (L : ℕ) (_hL : 1 < L) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  -- Remaining obligation: prove the overlapping cyclic-window Friedrichs-angle
  -- estimate required by `parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs`.
  -- Local projection structure, row cardinality, non-overlap positivity, kernel
  -- identification, and the spectral-theorem conversion are already formalized above.
  -- Proof obligation tracked by #952 and #460 (#190).
  sorry

/--
**Spectral gap for MPS parent Hamiltonians.**

For an injective MPS tensor `A` and interaction range `L > 1`, there exists
a uniform gap `γ > 0` (independent of system size `N`) such that for all
`N ≥ 2L`, every vector in the orthogonal complement of the ground space
satisfies `γ * ‖v‖ ≤ ‖H_ES v‖`.

The orthogonal complement is computed in the `EuclideanSpace` structure
on `NSiteSpace d N ≃ Cfg d N → ℂ`.

**Proof strategy (Kastoryano–Lucia 2018 / Nachtergaele 1996).** The parent
Hamiltonian `H_N = ∑ᵢ hᵢ` is a frustration-free sum of local orthogonal
projectors (`parentHamiltonian_frustrationFree`). The intersection property
`groundSpace_intersection` bounds the Friedrichs angle between adjacent local
ground spaces away from zero, which provides the martingale operator
inequality

    `h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)`

with constants `c_{ij}` depending only on the MPS tensor (not on `N`). At most
`2(L-1)` local terms overlap a given `h_i`, so the row-sum bound
`∑_{j≠i} c_{ij} ≤ 1` holds uniformly in `N`. Combined with `h_i^2 = h_i`,
this yields the quadratic-form inequality `H² ≥ γ H`, which feeds into
the abstract lemma `FrustrationFree.spectralGap_of_martingale` to produce
the norm bound `γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ`. The `LinearMap.IsPositive`
hypothesis required by `FrustrationFree.spectralGap_of_martingale` is
automatic here because `H_N = ∑ᵢ hᵢ` is a sum of orthogonal projectors.

The proof below invokes the MPS-specific Friedrichs-angle theorem
`parentHamiltonianES_gap_bound_of_friedrichs`, whose proof is the remaining
Friedrichs-angle and row-sum obligation. -/
theorem parentHamiltonian_gapped
    (A : MPSTensor d D) (hA : IsInjective A) (L : ℕ) (hL : 1 < L) :
    ∃ γ > 0, ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  obtain ⟨hγ, hgap⟩ := parentHamiltonianES_gap_bound_of_friedrichs A hA L hL
  exact ⟨(1 : ℝ) / (4 * (L : ℝ)), hγ, hgap⟩

end MPSTensor
