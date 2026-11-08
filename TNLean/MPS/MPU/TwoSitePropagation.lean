/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteQuasiLocalAction
import TNLean.QCA.FinitePropagation

/-!
# Actual forward propagation of a supplied MPU standard form

The actual completed forward endomorphism sends a finite supported region
into its sum with the radius-four-block neighbourhood. The support bound
is derived from the actual finite-chain formula on one-site algebras and
finite tensor generation, rather than imposed as a field.

Source: arXiv:1703.09188, Appendix finite support and finite conjugation,
lines 2298--2306.

**Scope restriction (supplied standard form):** The radius is expressed
in the supplied positive block length. Its source bond-dimension bound,
the bare-MPU standard-form construction and the inverse automorphism
remain separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

namespace SpinChain

private theorem singleton_window_subset_regionSumset (k : ℕ) (Λ : Finset ℤ)
    (x : ℤ) (hx : x ∈ Λ) :
    finiteChainRegion (x - (2 * k : ℕ)) (3 * (2 * k)) ⊆
      regionSumset Λ (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ))) := by
  intro y hy
  have hy' := Finset.mem_Ico.mp hy
  apply (mem_regionSumset y Λ _).mpr
  refine ⟨x, hx, y - x, ?_, by omega⟩
  simp only [Finset.mem_Icc]
  omega

variable {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
  (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
  {u : Matrix (Fin ℓ × Fin r)
    (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
  {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (Fin r × Fin ℓ) ℂ}
  (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)

/-- Actual forward MPU conjugation propagates algebraic-local support by
at most four supplied blocks. The proof derives the output support from
actual one-site finite-chain formulas and finite generation.
Source: arXiv:1703.09188, Appendix lines 2298--2306. -/
theorem bufferedMPUAlgebraicAction_supportedIn {Λ : Finset ℤ}
    {X : AlgebraicLocalAlgebra d} (hX : SupportedIn X Λ) :
    SupportedIn (bufferedMPUAlgebraicAction hU k hk S X)
      (regionSumset Λ (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ)))) := by
  classical
  obtain ⟨A, rfl⟩ := hX
  let K := regionSumset Λ (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ)))
  let T := (localObservable d K).range.comap (bufferedMPUAlgebraicAction hU k hk S)
  have hsites : ∀ x ∈ Λ, (localObservable d {x}).range ≤ T := by
    intro x hx z hz
    obtain ⟨B, rfl⟩ := hz
    let b := x - (2 * k : ℕ)
    have hN : 1 < 3 * (2 * k) := by omega
    have hsite : ({x} : Finset ℤ) ⊆ finiteChainRegion b (3 * (2 * k)) := by
      intro y hy
      have hyx := Finset.mem_singleton.mp hy
      subst y
      simp only [finiteChainRegion, Finset.mem_Ico]
      dsimp [b]
      omega
    have hb : ∀ y ∈ ({x} : Finset ℤ),
        b ≤ y - (2 * k : ℕ) ∧ y + (4 * k : ℕ) ≤ b + (3 * (2 * k) : ℕ) := by
      intro y hy
      have hyx := Finset.mem_singleton.mp hy
      subst y
      dsimp [b]
      omega
    change bufferedMPULocalAction hU k {x} B ∈ (localObservable d K).range
    rw [bufferedMPULocalAction_eq_finiteChainLocalObservable hU k hk S
      {x} b (3 * (2 * k)) hN hsite hb]
    apply range_localObservable_mono d (singleton_window_subset_regionSumset k Λ x hx)
    exact ⟨finiteChainConjugation hU hN b (localInclusion hsite B), rfl⟩
  have hmem : localObservable d Λ A ∈ T :=
    range_localObservable_le_of_singletons Λ T hsites ⟨A, rfl⟩
  exact hmem

/-- The actual completed forward endomorphism has the derived finite
propagation bound on every finite supported quasi-local observable.
No inverse or propagation hypothesis is supplied.
Source: arXiv:1703.09188, Appendix lines 2298--2306. -/
theorem bufferedMPUQuasiLocalAction_supportedIn {Λ : Finset ℤ}
    {X : QuasiLocalAlgebra d} (hX : QuasiLocalSupportedIn X Λ) :
    QuasiLocalSupportedIn (bufferedMPUQuasiLocalAction hU k hk S X)
      (regionSumset Λ (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ)))) := by
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨B, hB⟩ := bufferedMPUAlgebraicAction_supportedIn hU k hk S
    (show SupportedIn (localObservable d Λ A) Λ from ⟨A, rfl⟩)
  refine ⟨B, ?_⟩
  rw [bufferedMPUQuasiLocalAction_quasiLocalObservable]
  exact congrArg (algebraicToQuasiLocal d) hB

end SpinChain
