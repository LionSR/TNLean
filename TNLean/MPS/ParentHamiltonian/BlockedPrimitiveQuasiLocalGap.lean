/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedQuasiLocalGap
import TNLean.MPS.ParentHamiltonian.BlockedQuasiLocalFace
import TNLean.MPS.ParentHamiltonian.EventualKernelGroundStateSupport
import TNLean.MPS.ParentHamiltonian.QuasiLocalEventualKernelGap

/-!
# Pure-state commutator gaps from an exact blocked primitive presentation

Suppose that every boundary-condition space of a tensor blocked by a positive
length is exactly the joint space of an inequivalent primitive family with
faithful invariant matrices. For a positive finite-range interaction with the
original boundary spaces as its eventual open-chain kernels, one positive
constant bounds the literal infinite-volume commutator energy in every pure
zero-energy state and for every centered local observable.

The interaction is grouped into a sufficiently long coarse interval. Its
primitive-sector gap transfers to the original lattice by positive comparison.
The support classification identifies every pure zero-energy state with a
transported sector. Translation invariance of a competing state is unnecessary.
The primitive family may be empty, in which case the state face is empty.

**Scope restriction (exact blocked primitive presentation):** The finite-space
representation is supplied here. Its derivation from periodic tensor data is
separate, as is identification of a general GVBS construction with these tensor
boundary spaces. See
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
No finite-volume gap in unaligned residue classes is asserted.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
the site grouping at lines 825--836, and Section 6, lines 2649--2675.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D L R b : ℕ} [NeZero d] [NeZero L]
  {E : Fin b → ℕ} [∀ j, NeZero (E j)]
/-- An exact blocked primitive presentation and the eventual original kernel
identity give one positive literal commutator gap for all pure zero-energy
states on the original chain. The interaction range is arbitrary and positive,
and both interval margins may diverge along any filter.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947,
and Section 6, lines 2649--2675. -/
theorem exists_pos_quasiLocalCommutator_limit_gap_of_blocked_primitive_family
    (A : MPSTensor d D) (μ : Fin b → ℂ)
    (B : ∀ j, MPSTensor (blockPhysDim d L) (E j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (E j)) (Fin (E j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : E j = E i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hJoint : ∀ N, groundSpaceES (blockTensor A L) N =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES A N) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
        ∀ (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          0 < k → φ (quasiLocalIntervalObservable d a k X) = 0 →
          ∀ {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ},
            Tendsto ℓ f atTop → Tendsto r f atTop →
          ∃ e : ℂ, Tendsto (fun n => φ
            (star (quasiLocalIntervalObservable d a k X) *
              (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                  (openInteractionMatrix h ((ℓ n + k) + r n)) *
                quasiLocalIntervalObservable d a k X -
                quasiLocalIntervalObservable d a k X *
                  quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
                    (openInteractionMatrix h ((ℓ n + k) + r n))))) f (𝓝 e) ∧
            (γ : ℂ) * φ (star (quasiLocalIntervalObservable d a k X) *
              quasiLocalIntervalObservable d a k X) ≤ e := by
  let K := R + L
  have hK : 0 < K := by dsimp [K]; omega
  have hcover : R + L ≤ K * L + 1 :=
    (Nat.le_mul_of_pos_right (R + L) (NeZero.pos L)).trans (Nat.le_succ _)
  have hkerB : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES
        (Matrix.toEuclideanLin (blockedInteractionMatrix h L K)) N) =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N :=
    (eventually_ker_openInteractionHamiltonianES_blockedInteractionMatrix_eq_groundSpaceES
      A h hh hR hK hcover hker).mono fun N hN => hN.trans (hJoint N)
  obtain ⟨γ, hγ, _hFinite, hGap⟩ :=
    exists_pos_multiblock_quasiLocalCommutator_gap_of_eventual_kernel
      μ B hμ ρ hP hρ hDistinct hK (blockedInteractionMatrix h L K)
      (blockedInteractionMatrix_posSemidef h hh hR L K) hkerB
  have hM : 0 < ((K * L + 1 - R : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt
      ((Nat.lt_add_of_pos_right (NeZero.pos L)).trans_le hcover)
  refine ⟨γ / (K * L + 1 - R : ℕ), div_pos hγ hM, ?_⟩
  intro φ hφ hφPure
  have hSupport := (mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
    A h hR hh hker φ).mp hφ
  obtain ⟨j, hφj⟩ :=
    (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
      A μ B hμ ρ hP hρ hDistinct hJoint φ hφ.1).mp ⟨hSupport.2, hφPure⟩
  have hInv : (quasiLocalBlockingFunctional d L).symm φ =
      quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
    rw [hφj]
    exact (quasiLocalBlockingFunctional d L).symm_apply_apply _
  intro a k X hk hcenter ι f ℓ r hℓ hr
  apply quasiLocalCommutator_limit_gap_of_blocking φ hφ.1.2.2 h hR hh hK hcover hφ.2 γ
    (fun a' k' Y hk' hcenter' => ?_) hℓ hr a X hk hcenter
  simpa only [hInv] using hGap j a' Y hk' (by simpa only [hInv] using hcenter')
end MPSTensor
