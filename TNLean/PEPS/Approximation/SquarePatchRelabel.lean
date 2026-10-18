/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchSupply
import TNLean.PEPS.Approximation.InformationReset

/-!
# Relabelling the sites of a square patch

A bijection of finite site sets preserves the nested-cylinder data of a square
patch and transports its cylinder sum along the induced configuration bijection.
The corresponding adaptive patch conclusion retains the same dimension bound
and approximation error for the transported input vector.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 24–49 and 563–603, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS.EncodedFrame

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] {q : ℕ}

/-- Relabelling the sites preserves the radii and inside dimensions of a square
patch, and transports its literal cylinder sum by the induced configuration
bijection. No nonemptiness condition is imposed on the sites or samples.

Source: the coordinate-independent cylinder representation in the polynomial-PEPS
manuscript, Proposition 4.1, `03-patches.tex`, lines 24–49 and 563–603, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem SquarePatch.exists_relabel (e : V ≃ W) {pos : V → ℝ × ℝ}
    (P : SquarePatch pos q) :
    ∃ (P' : SquarePatch (fun w ↦ pos (e.symm w)) q) (hn : P'.n = P.n),
      P'.center = P.center ∧ P'.scale = P.scale ∧
      (∀ j, P'.radius (Fin.cast hn.symm j) = P.radius j) ∧
      (∀ j, P'.dim (Fin.cast hn.symm j) = P.dim j) ∧
      P'.cylSum =
        Matrix.reindex (Equiv.arrowCongr e (Equiv.refl (Fin q)))
          (Equiv.arrowCongr e (Equiv.refl (Fin q))) P.cylSum := by
  classical
  let R (r : ℝ) : squareSample pos P.center r ≃
      squareSample (fun w ↦ pos (e.symm w)) P.center r :=
    e.subtypeEquiv (fun _ ↦ by simp [squareSample])
  let U (r : ℝ) := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.arrowCongr (R r) (Equiv.refl (Fin q)))
  let E := Matrix.reindexAlgEquiv ℂ ℂ (Equiv.arrowCongr e (Equiv.refl (Fin q)))
  have hlift (r : ℝ) (v : EuclideanSpace ℂ (squareSample pos P.center r → Fin q)) :
      siteLift (squareSample (fun w ↦ pos (e.symm w)) P.center r) (rankOne (U r v)) =
        E (siteLift (squareSample pos P.center r) (rankOne v)) := by
    have hrank : rankOne (U r v) =
        Matrix.reindex (Equiv.arrowCongr (R r) (Equiv.refl (Fin q)))
          (Equiv.arrowCongr (R r) (Equiv.refl (Fin q))) (rankOne v) := rfl
    simp only [hrank, E, Matrix.coe_reindexAlgEquiv,
      ← QuantumCircuit.embedOp_equiv_eq_reindex, siteLift,
      QuantumCircuit.embedOp_embedOp Subtype.val_injective,
      QuantumCircuit.embedOp_embedOp e.injective]
    rfl
  let P' : SquarePatch (fun w ↦ pos (e.symm w)) q := {
    center := P.center
    scale := P.scale
    scale_pos := P.scale_pos
    n := P.n
    radius := P.radius
    radius_mono := P.radius_mono
    scale_le_radius := P.scale_le_radius
    radius_le := P.radius_le
    dim := P.dim
    vec := fun j ℓ ↦ U (P.radius j) (P.vec j ℓ)
    norm_vec := fun j ℓ ↦ ((U (P.radius j)).norm_map _).trans (P.norm_vec j ℓ)
    orthogonal := by
      intro s s' hs
      rw [hlift, hlift, ← map_mul, P.orthogonal s s' hs, map_zero] }
  refine ⟨P', rfl, rfl, rfl, (fun _ ↦ rfl), (fun _ ↦ rfl), ?_⟩
  change P'.cylSum = E P.cylSum
  simp only [SquarePatch.cylSum, map_sum]
  exact Finset.sum_congr rfl (fun s _ ↦ hlift (P.radius s.1) (P.vec s.1 s.2))

/-- The adaptive patch conclusion is preserved under a bijection of sites,
with the same constants, center and scale and the transported input vector.
The dimension bound and the error of the literal cylinder sum are unchanged.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 24–49 and 563–603, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem HasAdaptivePatch.relabel {pos : V → ℝ × ℝ}
    {Ω : EuclideanSpace ℂ (V → Fin q)} {C c p : ℝ} {L : ℕ}
    {z : ℝ × ℝ} {u : ℝ} (h : HasAdaptivePatch pos Ω C c p L z u)
    (e : V ≃ W) :
    HasAdaptivePatch (fun w ↦ pos (e.symm w))
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.arrowCongr e (Equiv.refl (Fin q))) Ω) C c p L z u := by
  obtain ⟨P, hz, hu, hd, he⟩ := h
  obtain ⟨P', hn, hz', hu', _, hdim, hcyl⟩ := SquarePatch.exists_relabel e P
  have hsum : ∑ j, P.dim j = ∑ j, P'.dim j :=
    Fintype.sum_equiv (finCongr hn.symm) _ _ (fun j ↦ (hdim j).symm)
  refine ⟨P', hz'.trans hz, hu'.trans hu, hsum ▸ hd, ?_⟩
  have hnorm := Approximation.norm_reindex_mulVec_sub
    (Equiv.arrowCongr e (Equiv.refl (Fin q))) P.cylSum (⇑Ω) (⇑Ω)
  rw [act_sub, act_one, norm_sub_rev] at he ⊢
  have hΩ : LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.arrowCongr e (Equiv.refl (Fin q))) Ω =
        WithLp.toLp 2 (Ω.ofLp ∘ (Equiv.arrowCongr e (Equiv.refl (Fin q))).symm) := rfl
  rw [hcyl, hΩ, act_apply]
  exact hnorm.le.trans he

end TNLean.PEPS.EncodedFrame
