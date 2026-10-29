/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.IntervalCoordinates
import TNLean.Circuit.SiteEmbedding

/-!
# Finite local inclusions in numbered support coordinates

An arbitrary local inclusion into an integer interval is precisely the
existing finite site embedding after the sites are numbered. Thus its
matrix belongs to the existing supported-operator algebra on the numbered
retained sites. No interval shape of the retained region is required.

Source: arXiv:1703.09188, Appendix, identity-tensor inclusions,
lines 2285–2295.
-/

namespace SpinChain

/-- Numbering an arbitrary finite local inclusion gives the existing
finite site embedding. Source: arXiv:1703.09188, Appendix, lines 2285–2295. -/
theorem intervalCoordinates_localInclusion_eq_embedOp
    {d N : ℕ} {a : ℤ} {Λ : Finset ℤ} (hΛ : Λ ⊆ finiteChainRegion a N)
    (A : LocalAlgebra d Λ) :
    intervalCoordinates d a N (localInclusion hΛ A) =
      QuantumCircuit.embedOp
        (fun x : Λ => (finiteChainSiteEquiv a N).symm ⟨x.val, hΛ x.property⟩)
        (CStarMatrix.ofMatrix.symm A) := by
  classical
  let E := finiteChainSiteEquiv a N
  let e : Λ → Fin N := fun x => E.symm ⟨x.val, hΛ x.property⟩
  ext σ τ
  have hAgree : (Config.splitEquiv hΛ (finiteChainConfigEquiv d N a σ)).2 =
      (Config.splitEquiv hΛ (finiteChainConfigEquiv d N a τ)).2 ↔
      QuantumCircuit.AgreeOff e σ τ := by
    constructor
    · intro h i hi
      have hx : (E i).val ∉ Λ := by
        intro hx
        exact hi ⟨(E i).val, hx⟩ (by simp only [e, Equiv.symm_apply_apply])
      have h' := congrFun h ⟨(E i).val, Finset.mem_sdiff.mpr ⟨(E i).property, hx⟩⟩
      change σ (E.symm (E i)) = τ (E.symm (E i)) at h'
      simpa only [Equiv.symm_apply_apply] using h'
    · intro h
      funext x
      let i := E.symm ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩
      apply h i
      intro y hy
      have hyx : y.val = x.val := by
        have hval := congrArg (fun j => (E j).val) hy
        simpa only [e, i, Equiv.apply_symm_apply] using hval
      exact (Finset.mem_sdiff.mp x.property).2 (hyx ▸ y.property)
  rw [intervalCoordinates_apply, localInclusion_apply, QuantumCircuit.embedOp_apply]
  change A (σ ∘ e) (τ ∘ e) *
      (if (Config.splitEquiv hΛ (finiteChainConfigEquiv d N a σ)).2 =
        (Config.splitEquiv hΛ (finiteChainConfigEquiv d N a τ)).2 then 1 else 0) =
      if QuantumCircuit.AgreeOff e σ τ then A (σ ∘ e) (τ ∘ e) else 0
  rw [hAgree]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- Every actual local inclusion is supported on the same numbered sites.
Source: arXiv:1703.09188, Appendix, lines 2285–2295. -/
theorem intervalCoordinates_localInclusion_mem_supportedOperators
    {d N : ℕ} {a : ℤ} {Λ : Finset ℤ} (hΛ : Λ ⊆ finiteChainRegion a N)
    (A : LocalAlgebra d Λ) :
    intervalCoordinates d a N (localInclusion hΛ A) ∈
      QuantumCircuit.supportedOperators d
        {i : Fin N | (finiteChainSiteEquiv a N i).val ∈ Λ} := by
  classical
  rw [intervalCoordinates_localInclusion_eq_embedOp]
  let e : Λ → Fin N := fun x => (finiteChainSiteEquiv a N).symm ⟨x.val, hΛ x.property⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun i => (finiteChainSiteEquiv a N i).val) hxy
    simpa only [e, Equiv.apply_symm_apply] using h
  apply QuantumCircuit.supportedOperators_mono ?_
    (QuantumCircuit.embedOp_mem_supportedOperators he (CStarMatrix.ofMatrix.symm A))
  rintro _ ⟨x, rfl⟩
  simpa only [e, Equiv.apply_symm_apply] using x.property

end SpinChain
