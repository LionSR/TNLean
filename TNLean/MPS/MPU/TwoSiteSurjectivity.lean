/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteCyclicInverse
import TNLean.MPS.MPU.TwoSitePropagation
import TNLean.MPS.MPU.TwoSiteTranslationCovariance
import TNLean.QCA.IsQCA
import TNLean.QCA.FinitePropagation

/-!
# Actual local preimages of the supplied standard-form action

Choose a sufficiently buffered periodic chain for a target observable.
The actual finite inverse is supported in its ring neighbourhood. Since
the target is away from the seam, that neighbourhood is contained in the
ordinary integer neighbourhood and is itself buffered. Evaluating the
actual completed forward map on this inverse therefore returns the target.
No inverse standard form or local surjectivity hypothesis is supplied.

Source: arXiv:1703.09188, supplied StandardForm/SF and eq:appendix-1,
lines 603–622 and 2300–2306.

**Scope restriction (supplied standard form):** The automorphism here
consumes an actual positive-block standard form and has its four-block
radius. Bare MPU reduction and the source bond-dimension radius are
separate; see `docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

open Fin.CommRing

namespace SpinChain

/-- A buffered target has no wraparound in its fixed-radius ring
neighbourhood. Source context: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306. -/
theorem finiteRingNeighbourhood_subset_regionSumset
    {a : ℤ} {N : ℕ} [NeZero N] (J : Finset ℤ) (R : ℕ)
    (hbuffer : ∀ x ∈ J, a + R ≤ x ∧ x + R < a + N) :
    finiteRingNeighbourhood a N J R ⊆
      regionSumset J (Finset.Icc (-(R : ℤ)) R) := by
  classical
  intro y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨j, hj, m, hm, hij⟩ := Set.mem_toFinset.mp hi
  have hbounds := hbuffer (finiteChainSiteEquiv a N j).val hj
  simp only [finiteChainSiteEquiv_val] at hbounds
  have hm' := abs_le.mp hm
  let z : ℤ := j.val + m
  have hz₀ : 0 ≤ z := by dsimp [z]; omega
  have hzN : z < N := by dsimp [z]; omega
  have hcast : (z.toNat : Fin N) = (z : Fin N) := by
    have h := congrArg (fun t : ℤ => (t : Fin N)) (Int.toNat_of_nonneg hz₀)
    simpa only [Int.cast_natCast] using h
  have hiCast : i = (z.toNat : Fin N) := by
    calc
      i = j + (m : Fin N) := hij
      _ = (z : Fin N) := by simp only [z, Int.cast_add, Int.cast_natCast, Fin.cast_val_eq_self]
      _ = (z.toNat : Fin N) := hcast.symm
  have hiVal : (i.val : ℤ) = z := by
    have hzlt : z.toNat < N := by omega
    rw [hiCast, Fin.val_natCast, Nat.mod_eq_of_lt hzlt]
    exact Int.toNat_of_nonneg hz₀
  apply (mem_regionSumset _ J _).mpr
  refine ⟨(finiteChainSiteEquiv a N j).val, hj, m, ?_, ?_⟩
  · simpa only [Finset.mem_Icc] using hm'
  · simp only [finiteChainSiteEquiv_val, hiVal]
    dsimp [z]
    omega

variable {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
  (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
  {u : Matrix (Fin ℓ × Fin r)
    (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
  {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (Fin r × Fin ℓ) ℂ}
  (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)

/-- Every actual local target has a local preimage under the completed
forward action, supported within four supplied blocks of the target.
The preimage is the actual finite inverse on one sufficiently buffered
chain. Source: arXiv:1703.09188, eq:appendix-1, lines 2300–2306,
with supplied StandardForm/SF, lines 603–622. -/
theorem exists_local_preimage_bufferedMPUQuasiLocalAction
    (J : Finset ℤ) (B : LocalAlgebra d J) :
    ∃ A : LocalAlgebra d
        (regionSumset J (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ)))),
      bufferedMPUQuasiLocalAction hU k hk S
        (quasiLocalObservable d _ A) = quasiLocalObservable d J B := by
  classical
  let K := regionSumset J (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ)))
  obtain ⟨a, N, hN, hJ₀, hbuffer, _⟩ :=
    exists_finiteChainLocalObservable_bufferedMPULocalAction hU (3 * k) (J ∪ {0})
  have hJ : J ⊆ finiteChainRegion a N := Finset.subset_union_left.trans hJ₀
  have hzero := hbuffer 0 (Finset.mem_union_right J (Finset.mem_singleton_self 0))
  have hNk : 3 * (2 * k) ≤ N := by omega
  let : NeZero N := ⟨by omega⟩
  have htarget : ∀ x ∈ J, a + (4 * k : ℕ) ≤ x ∧
      x + (4 * k : ℕ) < a + N := by
    intro x hx
    have h := hbuffer x (Finset.mem_union_left {0} hx)
    omega
  have hRing : finiteRingNeighbourhood a N J (4 * k) ⊆ K := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      finiteRingNeighbourhood_subset_regionSumset J (4 * k) htarget
  have hKbounds : ∀ x ∈ K, a ≤ x - (2 * k : ℕ) ∧
      x + (4 * k : ℕ) ≤ a + N := by
    intro x hx
    obtain ⟨y, hy, m, hm, rfl⟩ := (mem_regionSumset x J _).mp hx
    have h := hbuffer y (Finset.mem_union_left {0} hy)
    have hm' := Finset.mem_Icc.mp hm
    omega
  have hK : K ⊆ finiteChainRegion a N := by
    intro x hx
    have h := hKbounds x hx
    simp only [finiteChainRegion, Finset.mem_Ico]
    omega
  obtain ⟨A, hA⟩ := finiteChainConjugation_symm_mem_range_ringNeighbourhood
    hU k hk hNk a S hJ B
  let C := localInclusion hRing A
  have hC : localInclusion hK C =
      (finiteChainConjugation hU hN a).symm (localInclusion hJ B) := by
    rw [show localInclusion hK C =
      localInclusion (finiteRingNeighbourhood_subset a N J (4 * k)) A by
        exact DFunLike.congr_fun (localInclusion_trans hRing hK) A]
    exact hA
  refine ⟨C, ?_⟩
  rw [bufferedMPUQuasiLocalAction_finiteChainConjugation hU k hk S K a N hN hK hKbounds C,
    hC, StarAlgEquiv.apply_symm_apply, quasiLocalObservable_localInclusion]

/-- Local preimages and completeness make the actual completed forward
map surjective. Source: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306, with supplied StandardForm/SF, lines 603–622. -/
theorem bufferedMPUQuasiLocalAction_surjective :
    Function.Surjective (bufferedMPUQuasiLocalAction hU k hk S) := by
  intro X
  change X ∈ Set.range (bufferedMPUQuasiLocalAction hU k hk S)
  induction X using UniformSpace.Completion.induction_on with
  | hp => exact (bufferedMPUQuasiLocalAction_isometry hU k hk S).isClosedEmbedding.isClosed_range
  | ih A =>
      induction A using DirectLimit.induction with
      | _ J B =>
          obtain ⟨C, hC⟩ := exists_local_preimage_bufferedMPUQuasiLocalAction hU k hk S J B
          exact ⟨quasiLocalObservable d _ C, hC⟩

/-- The actual completed supplied-standard-form action as a star-automorphism.
Its inverse is obtained from actual finite local preimages, without
constructing or assuming a second standard form. Source: arXiv:1703.09188,
StandardForm/SF and eq:appendix-1, lines 603–622 and 2300–2306. -/
noncomputable def bufferedMPUQuasiLocalAut :
    QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  StarAlgEquiv.ofBijective (bufferedMPUQuasiLocalAction hU k hk S)
    ⟨(bufferedMPUQuasiLocalAction_isometry hU k hk S).injective,
      bufferedMPUQuasiLocalAction_surjective hU k hk S⟩

/-- The actual automorphism evaluates as the already constructed completed
forward action. Source: arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
@[simp] theorem bufferedMPUQuasiLocalAut_apply (X : QuasiLocalAlgebra d) :
    bufferedMPUQuasiLocalAut hU k hk S X = bufferedMPUQuasiLocalAction hU k hk S X := rfl

/-- The actual automorphism has the derived four-block propagation bound.
Source: arXiv:1703.09188, Appendix, lines 2298–2306,
with supplied StandardForm/SF, lines 603–622. -/
theorem bufferedMPUQuasiLocalAut_propagatesWithin :
    PropagatesWithin (bufferedMPUQuasiLocalAut hU k hk S)
      (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ))) := by
  intro Λ X hX
  exact bufferedMPUQuasiLocalAction_supportedIn hU k hk S hX

/-- The actual supplied-standard-form action is a translation-covariant QCA.
Both surjectivity and forward propagation are derived from actual finite
conjugation; no inverse standard form is supplied.
Source: arXiv:1703.09188, StandardForm/SF and Appendix eq:appendix-1,
lines 603–622 and 2298–2306. -/
theorem bufferedMPUQuasiLocalAut_isQCA :
    IsQCA (bufferedMPUQuasiLocalAut hU k hk S) := by
  apply IsQCA.mk ?_ ⟨_, bufferedMPUQuasiLocalAut_propagatesWithin hU k hk S⟩
  apply (translationCovariant_iff _).mpr
  intro t X
  exact bufferedMPUQuasiLocalAction_translation hU k hk S t X

end SpinChain
