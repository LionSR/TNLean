/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalSectorStateDecomposition
import TNLean.MPS.ParentHamiltonian.PhysicalSectorProjectorTransport

/-!
# The full kernel of a two-sector periodic projector Hamiltonian

For two local spaces on disjoint exhaustive physical alphabets, the actual
periodic complementary-projector kernel is exactly the sum of the embedded
component kernels. Mixed-sector exclusion supplies an actual state
decomposition, and orthogonal component dynamics supplies the two kernel
equations. Neither conclusion is assumed as an extra hypothesis.

This is the physical-sector assembly in the finite-prefix investigation of
SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880. The result applies to
arbitrary local spaces, not to an assumed classification of a particular model.
-/

namespace MPSTensor

/-- The exact full periodic kernel of the complementary projection of two
embedded local spaces is the sum of their actual component kernels. The
physical alphabet split is exhaustive, and the range is at least two.
Source: physical-sector assembly for the SPWC10 finite-prefix investigation. -/
theorem ker_physical_sum_projectorHamiltonian
    {a b R M : ℕ} (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (hR : 2 ≤ R) (hRM : R ≤ M) :
    LinearMap.ker (periodicInteractionHamiltonianES
      ((S.map
          (Function.Embedding.piCongrRight
            (fun _ : Fin R ↦ Fin.castAddEmb b)).euclideanExtendByZero.toLinearMap ⊔
        T.map
          (Function.Embedding.piCongrRight
            (fun _ : Fin R ↦ Fin.natAddEmb a)).euclideanExtendByZero.toLinearMap)ᗮ
        .starProjection.toLinearMap) M) =
      (LinearMap.ker (periodicInteractionHamiltonianES Sᗮ.starProjection.toLinearMap M)).map
        (Function.Embedding.piCongrRight
          (fun _ : Fin M ↦ Fin.castAddEmb b)).euclideanExtendByZero.toLinearMap ⊔
      (LinearMap.ker (periodicInteractionHamiltonianES Tᗮ.starProjection.toLinearMap M)).map
        (Function.Embedding.piCongrRight
          (fun _ : Fin M ↦ Fin.natAddEmb a)).euclideanExtendByZero.toLinearMap := by
  let e : Fin a ↪ Fin (a + b) := Fin.castAddEmb b
  let f : Fin b ↪ Fin (a + b) := Fin.natAddEmb a
  have hdisj (i : Fin a) (j : Fin b) : e i ≠ f j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = a + j.val at hv
    have hi := i.isLt
    omega
  let E := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ e)).euclideanExtendByZero
  let F := (Function.Embedding.piCongrRight (fun _ : Fin M ↦ f)).euclideanExtendByZero
  ext ψ
  constructor
  · intro hψ
    let x : MPVSpace a M := WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.castAdd b (w i))
    let y : MPVSpace b M := WithLp.toLp 2 fun w ↦ ψ (fun i ↦ Fin.natAdd a (w i))
    have hdecomp : ψ = E x + F y :=
      physical_sum_state_decomposition_of_projectorHamiltonian_eq_zero S T hR hRM ψ hψ
    have hcomponents := (physical_sector_projectorHamiltonian_sum_eq_zero_iff e f hdisj
      (by omega) hRM S T x y).mp (hdecomp ▸ hψ)
    rw [hdecomp]
    exact Submodule.add_mem_sup
      (Submodule.mem_map.mpr ⟨x, hcomponents.1, rfl⟩)
      (Submodule.mem_map.mpr ⟨y, hcomponents.2, rfl⟩)
  · intro hψ
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hψ
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hy
    exact (physical_sector_projectorHamiltonian_sum_eq_zero_iff e f hdisj
      (by omega) hRM S T x y).mpr ⟨hx, hy⟩

end MPSTensor
