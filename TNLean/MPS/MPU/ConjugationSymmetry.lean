/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryConjugationTransposeSign
import TNLean.MPS.MPU.FundamentalTheoremGates

/-!
# Conjugation equations of a supplied two-site standard form

The literal gate equation `conj(u) = (x ⊗ y) u` implies the Kronecker identity
needed for the common symmetric or skew-symmetric case. Both literal gate
equations imply that every positive-length periodic operator of the supplied
two-site standard form is fixed by entrywise complex conjugation: conjugate
the two circuit layers, then cancel each internal unitary against its adjoint.

These are the algebraic and contraction steps in arXiv:1703.09188, Proposition
`prop1conj`, lines 1006–1039. Existence of the local gauges from global
conjugation invariance is not assumed or asserted here.

**Scope restriction (blocked rings):** The periodic result concerns the
supplied blocked tensor; for a standard form of `blockTwo U`, it therefore
concerns even lengths of the original tensor `U`. See
`docs/paper-gaps/mpu_standard_form_parity_gap.tex` for the unblocked reading.
-/

open scoped Matrix Kronecker BigOperators

namespace Matrix

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-- Entrywise conjugation preserves both unitary identities of a rectangular
gate, as used for the conjugate comparison in arXiv:1703.09188,
`prop1conj`, lines 1030–1033. -/
theorem IsUnitaryBetween.map_star {A : Matrix a b ℂ} (hA : A.IsUnitaryBetween) :
    (A.map (starRingEnd ℂ)).IsUnitaryBetween := by
  have hstar : (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) :=
    (Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])).symm
  constructor
  · change (A.map (starRingEnd ℂ))ᴴ * A.map (starRingEnd ℂ) = 1
    rw [hstar, ← Matrix.map_mul, hA.1]
    simp
  · change A.map (starRingEnd ℂ) * (A.map (starRingEnd ℂ))ᴴ = 1
    rw [hstar, ← Matrix.map_mul, hA.2]
    simp

/-- Applying the literal unshifted gate equation twice and cancelling the
coisometric gate gives the Kronecker identity of arXiv:1703.09188,
`paper_v2.tex` lines 1033–1035. This identity is derived, not assumed. -/
theorem kronecker_map_star_mul_eq_one_of_gate_conjugation
    {x : Matrix a a ℂ} {y : Matrix b b ℂ} {u : Matrix (a × b) c ℂ}
    (hu : u.IsCoisometry)
    (hconj : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) :
    (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) = 1 := by
  have hmap : (x ⊗ₖ y).map (starRingEnd ℂ) =
      x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.kroneckerMap_apply]
  have hdouble := congrArg (fun M ↦ M.map (starRingEnd ℂ)) hconj
  have hinvolutive : (u.map (starRingEnd ℂ)).map (starRingEnd ℂ) = u := by
    ext i j
    simp
  rw [hinvolutive, Matrix.map_mul, hmap, hconj] at hdouble
  have hright : u * uᴴ = 1 := hu
  calc
    (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) =
        (x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ)) * (x ⊗ₖ y) :=
      Matrix.mul_kronecker_mul _ _ _ _
    _ = ((x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ)) * (x ⊗ₖ y)) *
        (u * uᴴ) := by rw [hright, Matrix.mul_one]
    _ = ((x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ)) *
        ((x ⊗ₖ y) * u)) * uᴴ := by simp only [Matrix.mul_assoc]
    _ = u * uᴴ := by rw [← hdouble]
    _ = 1 := hright

/-- The local equation for a coisometric gate already forces the two unitary
factors to be both symmetric or both skew-symmetric, as in arXiv:1703.09188,
`paper_v2.tex` lines 1033–1038. -/
theorem transpose_eq_self_or_transpose_eq_neg_of_gate_conjugation
    [Nonempty a] [Nonempty b]
    {x : Matrix a a ℂ} {y : Matrix b b ℂ} {u : Matrix (a × b) c ℂ}
    (hx : x ∈ unitaryGroup a ℂ) (hy : y ∈ unitaryGroup b ℂ)
    (hu : u.IsCoisometry)
    (hconj : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) :
    (xᵀ = x ∧ yᵀ = y) ∨ (xᵀ = -x ∧ yᵀ = -y) :=
  transpose_eq_self_or_transpose_eq_neg_of_kronecker_map_star_mul_eq_one hx hy
    (kronecker_map_star_mul_eq_one_of_gate_conjugation hu hconj)

end Matrix

namespace MPOTensor

variable {d D ℓ r N : ℕ}

/-- Entrywise conjugation of an MPO tensor, without a physical or virtual
index swap. Source: arXiv:1703.09188, `prop1conj`, lines 1008–1010. -/
def mapStar (W : MPOTensor d D) : MPOTensor d D :=
  fun i j ↦ (W i j).map (starRingEnd ℂ)

/-- Conjugating every coefficient conjugates the periodic operator at each
length, including zero. This is the finite-chain meaning of conjugation in
arXiv:1703.09188, `paper_v2.tex` lines 1008–1010. -/
theorem mpo_map_star (W : MPOTensor d D) (N : ℕ) :
    mpo (mapStar W) N =
      (mpo W N).map (starRingEnd ℂ) := by
  ext σ τ
  change Matrix.trace (evalWord _ (List.ofFn σ) (List.ofFn τ)) =
    starRingEnd ℂ (Matrix.trace (evalWord W (List.ofFn σ) (List.ofFn τ)))
  rw [evalWord_ofFn, evalWord_ofFn, AddMonoidHom.map_trace]
  congr 1
  simpa only [List.map_ofFn, Function.comp_def, RingHom.mapMatrix_apply] using
    (map_list_prod (starRingEnd ℂ).mapMatrix
      (List.ofFn fun i : Fin N ↦ W (σ i) (τ i))).symm

/-- Conjugating every coefficient transports the actual supplied standard
form to the conjugate tensor, with gates exactly `conj(u), conj(v)`.
This is the comparison standard form used in arXiv:1703.09188, proof of
`prop1conj`, lines 1030–1033; no new choice of gates is made. -/
def TwoSiteStandardFormData.mapStar
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) :
    TwoSiteStandardFormData (MPOTensor.mapStar W)
      (u.map (starRingEnd ℂ)) (v.map (starRingEnd ℂ)) := by
  refine {
    phys_pos := S.phys_pos
    bond_pos := S.bond_pos
    left_pos := S.left_pos
    right_pos := S.right_pos
    X₁ := S.X₁.map (starRingEnd ℂ)
    X₂ := S.X₂.map (starRingEnd ℂ)
    u_unitary := Matrix.IsUnitaryBetween.map_star (A := u) S.u_unitary
    v_unitary := Matrix.IsUnitaryBetween.map_star (A := v) S.v_unitary
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ s t
    simpa only [Matrix.map_apply, map_sum, map_mul] using
      congrArg (starRingEnd ℂ) (S.v_apply i₁ i₂ s t)
  · intro i j α γ
    simpa only [Matrix.map_apply, map_sum, map_mul] using
      congrArg (starRingEnd ℂ) (S.W_apply i j α γ)

/-- Entrywise conjugation of the unshifted layer conjugates its supplied
gate, in arXiv:1703.09188, equation `uconjugation`, lines 1021–1022. -/
theorem twoSiteUnshiftedLayer_map_star
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) :
    (twoSiteUnshiftedLayer (N := N) u).map (starRingEnd ℂ) =
      twoSiteUnshiftedLayer (N := N) (u.map (starRingEnd ℂ)) := by
  ext i j
  simp [twoSiteUnshiftedLayer, Matrix.map_apply, map_prod]

/-- Entrywise conjugation of the shifted layer conjugates its supplied gate,
in arXiv:1703.09188, equation `vconjugation`, lines 1023–1025. -/
theorem twoSiteShiftedLayer_map_star [NeZero N]
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    (twoSiteShiftedLayer (N := N) v).map (starRingEnd ℂ) =
      twoSiteShiftedLayer (N := N) (v.map (starRingEnd ℂ)) := by
  ext i j
  simp [twoSiteShiftedLayer, Matrix.map_apply, map_prod]

/-- Contracting the two literal conjugation equations makes every periodic
operator of the supplied two-site standard form invariant under entrywise
conjugation. This is the direct circuit-contraction argument in
arXiv:1703.09188, Proposition `prop1conj`, lines 1029–1030, on positive
blocked rings. No generic MPS symmetry theorem is used. -/
theorem TwoSiteStandardFormData.map_star_mpo_eq_of_gate_conjugation [NeZero N]
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v)
    (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ)
    (hu : u.map (starRingEnd ℂ) =
      ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u)
    (hv : v.map (starRingEnd ℂ) = v *
      (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))) :
    (mpo W N).map (starRingEnd ℂ) = mpo W N := by
  let e := (twoSitePairConfigEquiv d N).symm
  apply (Matrix.reindex e e).injective
  have hcircuit := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := N) W u v S
  change (Matrix.reindex e e (mpo W N)).map (starRingEnd ℂ) =
    Matrix.reindex e e (mpo W N)
  rw [hcircuit, Matrix.map_mul, twoSiteShiftedLayer_map_star,
    twoSiteUnshiftedLayer_map_star, hu, hv, twoSiteCircuit_eq_of_gate_gauges]

end MPOTensor
