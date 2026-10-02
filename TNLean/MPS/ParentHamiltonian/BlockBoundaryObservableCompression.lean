/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryObservableCompression
import TNLean.MPS.ParentHamiltonian.BoundaryCrossObservableCompression
import TNLean.MPS.ParentHamiltonian.GroundSpaceSectorCompressionDecay

/-!
# Centered observables and the full multiblock ground projection

For a finite family of pairwise inequivalent normalized primitive tensors,
center an interior observable in one distinguished sector. Its compression
from that sector into the sum of all sector ground spaces tends to zero as
both free intervals expand. The diagonal compression vanishes by primitive
transfer convergence; the off-diagonal compressions vanish by prefix locality
and decay of distinct-sector overlaps. The finite-family projection comparison
then assembles these limits.

This supplies the full ground-projection subtraction in Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. The theorem concerns the joint
finite-chain ground space and does not infer finite-chain uniqueness or
purity of a completed state.
-/

open Filter
open scoped Topology Matrix ComplexOrder

namespace MPSTensor

variable {ι : Type*} [Finite ι] {d : ℕ} {D : ι → ℕ} [∀ i, NeZero (D i)]

/-- A sector-centered interior observable has vanishing compression into the
full joint ground space of finitely many inequivalent primitive sectors.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675, combined with
Lemma `commutation` (i) and the distinct-sector overlap limit `limP12`. -/
theorem bulkObservable_iSup_groundSpace_compression_tendsto_zero
    (A : ∀ i, MPSTensor d (D i))
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (α : ι) {k : ℕ} (hk : 0 < k) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hcenter : observableInsertionExpectation (A α) (ρ α) X = 0)
    {κ : Type*} {f : Filter κ} {ℓ r : κ → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n =>
      ‖(⨆ i, groundSpaceES (A i) ((ℓ n + k) + r n)).starProjection.comp
        ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
          (bulkObservable X (ℓ n) (r n))).comp
            (groundSpaceES (A α) ((ℓ n + k) + r n)).starProjection)‖) f (𝓝 0) := by
  let N := fun n => (ℓ n + k) + r n
  have hN : Tendsto N f atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hℓ.eventually (eventually_ge_atTop b)] with n hn
    dsimp [N]
    omega
  refine Submodule.tendsto_norm_iSup_starProjection_comp_zero_of_sector_compressions
    (E := fun n => EuclideanSpace ℂ (Cfg d (N n)))
    (C := ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖)
    (fun n i => groundSpaceES (A i) (N n)) (fun n => groundSpaceES (A α) (N n))
    (fun n => Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ)
      (bulkObservable X (ℓ n) (r n))) ?_ ?_ ?_
  · intro ε hε
    exact hN.eventually (eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_all.2 fun hij =>
        (hP i).eventually_norm_inner_groundSpaceES_le_of_inequivalent
          (hP j) (hρ i) (hρ j) (hDistinct i j hij) hε)
  · exact Eventually.of_forall fun n => norm_toEuclideanCLM_bulkObservable_le hk X (ℓ n) (r n)
  · intro i
    by_cases hi : i = α
    · subst i
      exact (hP α).bulkObservable_groundSpace_compression_tendsto_zero
        (hρ α) X hcenter hℓ hr
    · exact (hP i).bulkObservable_cross_groundSpace_compression_tendsto_zero_of_inequivalent
        (hP α) (hρ i) (hρ α) (hDistinct i α hi) hk X hℓ

end MPSTensor
