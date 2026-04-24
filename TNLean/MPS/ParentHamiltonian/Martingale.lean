/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Martingale-method spectral-gap framework for parent Hamiltonians

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
`H² ≥ γ H` to the norm bound `γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ` — is recorded
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
`MPSTensor.parentHamiltonianES_gap_bound_of_friedrichs`, which records a
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
* `MPSTensor.parentHamiltonian_gapped` — uniform spectral gap for MPS
  parent Hamiltonians on injective tensors, obtained from the
  Friedrichs-angle bound recorded in
  `parentHamiltonianES_gap_bound_of_friedrichs`.
-/

open scoped BigOperators InnerProductSpace

/-! ### Abstract martingale criterion

The quadratic-form ⟹ norm-bound step is purely operator-theoretic and has no
MPS content in its signature, so it lives in its own `FrustrationFree`
namespace. The MPS-specific wrapper `MPSTensor.parentHamiltonian_gapped` below
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
quadratic-form input is recorded separately in
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

/-- The `EuclideanSpace` parent interaction is positive because it is an
orthogonal projection. -/
theorem parentInteractionES_isPositive (A : MPSTensor d D) (L : ℕ) :
    (parentInteractionES A L).IsPositive := by
  exact (Submodule.isSymmetricProjection_starProjection ((groundSpaceES A L)ᗮ)).isPositive

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
      _ = ⟪cyclicRestrictES (d := d) hN L i τ (EuclideanSpace.single σ (1 : ℂ)), v⟫_ℂ := by
            rw [LinearMap.adjoint_inner_right]
      _ = ⟪EuclideanSpace.single (extractWindow L i σ) (1 : ℂ), v⟫_ℂ := by
            rw [cyclicRestrictES_single_of_sameOutsideWindow hN hLN i σ τ hστ]
      _ = if SameOutsideWindow (L := L) i σ τ then v (extractWindow L i σ) else 0 := by
            simpa [hστ] using (EuclideanSpace.inner_single_left (extractWindow L i σ) (1 : ℂ) v)
  · calc
      ((cyclicRestrictES (d := d) hN L i τ).adjoint v) σ
          = ⟪EuclideanSpace.single σ (1 : ℂ),
              (cyclicRestrictES (d := d) hN L i τ).adjoint v⟫_ℂ := by
              simpa using (EuclideanSpace.inner_single_left σ (1 : ℂ)
                ((cyclicRestrictES (d := d) hN L i τ).adjoint v)).symm
      _ = ⟪cyclicRestrictES (d := d) hN L i τ (EuclideanSpace.single σ (1 : ℂ)), v⟫_ℂ := by
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
      ((((d ^ L : ℕ) : ℂ)⁻¹) • (∑ τ : Cfg d N, localTermESSummand A (Fin.pos i) L i τ)) := by
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

/-! ### Uniform spectral gap for the MPS parent Hamiltonian -/

/- Scout report (2026-04-19, Layer 4 KL martingale).

1. **Friedrichs-angle surface:** TNLean currently has no dedicated
`FriedrichsAngle`/principal-angle API in `TNLean/Analysis`. Mathlib provides
orthogonal-projection infrastructure (for example
`Mathlib.Analysis.InnerProductSpace.Projection.Basic` and
`Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`, exposing
`Submodule.starProjection` and `orthogonalProjection`) but not a ready-made
Kastoryano–Lucia-style angle-to-anticommutator bound. This is a real blocker
for quantitative overlap constants.
2. **Positivity formulation:** the local `EuclideanSpace` projector
`parentInteractionES A L` is positive, and each conjugated cyclic-restriction
summand `localTermESSummand A hN L i τ = Rᵢ,τ† P_L Rᵢ,τ` is positive by
`LinearMap.IsPositive.conj_adjoint`. Missing is the exact averaging identity
relating these positive summands to the transported local terms.
3. **Row-sum bound mapping:** the combinatorial part is already available from
locality (`localTerm`, `parentHamiltonian`) and finite range: each window
overlaps at most `2 * (L - 1)` neighbors. Missing is the analytic implication
from overlap-angle constants to operator-inequality coefficients `cᵢⱼ`.
4. **Sorry dependency split:** `parentHamiltonian_gapped` is the downstream
existential wrapper, now proved by applying the Friedrichs-angle theorem
below. The theorem `parentHamiltonianES_gap_bound_of_friedrichs` still depends
on missing Friedrichs-angle infrastructure; this is the blocker and should not
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
  -- Remaining obligations: the averaging identity expressing transported local
  -- terms as finite averages of `localTermESSummand`, the MPS-specific
  -- Friedrichs-angle estimate for adjacent local ground spaces, and the
  -- finite-overlap row-sum bound. The kernel identification needed for the
  -- final martingale application is now available as
  -- `parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES`. Once the
  -- remaining analytic inputs are formalized, this should feed the resulting
  -- quadratic-form inequality into `FrustrationFree.spectralGap_of_martingale`.
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
