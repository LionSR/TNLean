/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteLocalAction
import TNLean.QCA.QuasiLocal

/-!
# Completed actual forward MPU action

The actual norm-preserving algebraic-local action extends to an isometric
unital star-algebra endomorphism of the existing quasi-local completion.
Its value on each finite observable is the actual finite-chain local
family already constructed, followed by the canonical completion map.

Source: arXiv:1703.09188, Appendix norm completion and finite conjugation,
lines 2292--2306.

**Scope restriction (supplied standard form):** A positive supplied block
length and its two-site standard form remain inputs. This is the derived
forward endomorphism; an inverse, surjectivity, the bare-MPU standard-form
construction and the source bond-dimension radius remain separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

open scoped Topology

namespace SpinChain

variable {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
  (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
  {u : Matrix (Fin ℓ × Fin r)
    (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
  {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (Fin r × Fin ℓ) ℂ}
  (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)

/-- Actual algebraic-local MPU conjugation is isometric, by its proved
operator-norm formula. Source: arXiv:1703.09188, Appendix lines 2292--2306. -/
theorem bufferedMPUAlgebraicAction_isometry :
    Isometry (bufferedMPUAlgebraicAction hU k hk S) := by
  rw [isometry_iff_dist_eq]
  intro A B
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_bufferedMPUAlgebraicAction]

/-- The completed actual forward action, using Mathlib's completion map
of the actual ring homomorphism. The involution and scalar identities
follow on the dense algebraic local algebra.
Source: arXiv:1703.09188, Appendix lines 2292--2306. -/
noncomputable def bufferedMPUQuasiLocalAction :
    QuasiLocalAlgebra d →⋆ₐ[ℂ] QuasiLocalAlgebra d where
  __ := UniformSpace.Completion.mapRingHom
    (bufferedMPUAlgebraicAction hU k hk S).toRingHom
    (bufferedMPUAlgebraicAction_isometry hU k hk S).continuous
  commutes' c := by
    change UniformSpace.Completion.map (bufferedMPUAlgebraicAction hU k hk S)
      ((algebraMap ℂ (AlgebraicLocalAlgebra d) c : AlgebraicLocalAlgebra d) :
        QuasiLocalAlgebra d) =
      ((algebraMap ℂ (AlgebraicLocalAlgebra d) c : AlgebraicLocalAlgebra d) :
        QuasiLocalAlgebra d)
    rw [UniformSpace.Completion.map_coe
      (bufferedMPUAlgebraicAction_isometry hU k hk S).uniformContinuous]
    exact congrArg (fun X : AlgebraicLocalAlgebra d => (X : QuasiLocalAlgebra d))
      ((bufferedMPUAlgebraicAction hU k hk S).commutes c)
  map_star' X := by
    change UniformSpace.Completion.map (bufferedMPUAlgebraicAction hU k hk S) (star X) =
      star (UniformSpace.Completion.map (bufferedMPUAlgebraicAction hU k hk S) X)
    induction X using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih A =>
        simp only [← UniformSpace.Completion.coe_star,
          UniformSpace.Completion.map_coe
            (bufferedMPUAlgebraicAction_isometry hU k hk S).uniformContinuous, map_star]

/-- The completed forward action is the completion map of the actual
algebraic-local action; arXiv:1703.09188, Appendix lines 2296--2306. -/
theorem bufferedMPUQuasiLocalAction_apply (X : QuasiLocalAlgebra d) :
    bufferedMPUQuasiLocalAction hU k hk S X =
      UniformSpace.Completion.map (bufferedMPUAlgebraicAction hU k hk S) X := rfl

/-- The completed action agrees with the derived algebraic-local action
on its dense canonical image; arXiv:1703.09188, Appendix lines 2296--2306. -/
@[simp]
theorem bufferedMPUQuasiLocalAction_algebraicToQuasiLocal (A : AlgebraicLocalAlgebra d) :
    bufferedMPUQuasiLocalAction hU k hk S (algebraicToQuasiLocal d A) =
      algebraicToQuasiLocal d (bufferedMPUAlgebraicAction hU k hk S A) :=
  UniformSpace.Completion.map_coe
    (bufferedMPUAlgebraicAction_isometry hU k hk S).uniformContinuous A

/-- The completed forward action evaluates on every finite observable
by its actual finite MPU conjugation family.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
@[simp]
theorem bufferedMPUQuasiLocalAction_quasiLocalObservable (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) :
    bufferedMPUQuasiLocalAction hU k hk S (quasiLocalObservable d Λ A) =
      algebraicToQuasiLocal d (bufferedMPULocalAction hU k Λ A) := by
  rw [quasiLocalObservable, StarAlgHom.comp_apply,
    bufferedMPUQuasiLocalAction_algebraicToQuasiLocal]
  rfl

/-- The actual completed forward action equals original-site finite
MPU conjugation on every sufficiently buffered interval. This is the
finite-chain formula with compatibility derived from the supplied
standard form, rather than a value only on the canonically chosen chain.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem bufferedMPUQuasiLocalAction_finiteChainConjugation
    (Λ : Finset ℤ) (b : ℤ) (N : ℕ) (hN : 1 < N) (hΛ : Λ ⊆ finiteChainRegion b N)
    (hb : ∀ x ∈ Λ, b ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b + N)
    (A : LocalAlgebra d Λ) :
    bufferedMPUQuasiLocalAction hU k hk S (quasiLocalObservable d Λ A) =
      quasiLocalObservable d (finiteChainRegion b N)
        (finiteChainConjugation hU hN b (localInclusion hΛ A)) := by
  rw [bufferedMPUQuasiLocalAction_quasiLocalObservable,
    bufferedMPULocalAction_eq_finiteChainLocalObservable hU k hk S Λ b N hN hΛ hb]
  rfl

/-- The actual completed forward endomorphism is isometric, with no
surjectivity or inverse assumption. Source: arXiv:1703.09188,
Appendix norm completion in lines 2296--2306. -/
theorem bufferedMPUQuasiLocalAction_isometry :
    Isometry (bufferedMPUQuasiLocalAction hU k hk S) :=
  (bufferedMPUAlgebraicAction_isometry hU k hk S).completion_map

/-- The actual completed forward action preserves the physical operator
norm; arXiv:1703.09188, Appendix lines 2296--2306. -/
theorem norm_bufferedMPUQuasiLocalAction (X : QuasiLocalAlgebra d) :
    ‖bufferedMPUQuasiLocalAction hU k hk S X‖ = ‖X‖ :=
  (bufferedMPUQuasiLocalAction_isometry hU k hk S).norm_map_of_map_zero
    (map_zero (bufferedMPUQuasiLocalAction hU k hk S)) X

end SpinChain
