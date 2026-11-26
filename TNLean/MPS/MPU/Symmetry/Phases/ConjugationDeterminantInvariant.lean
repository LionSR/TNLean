/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Phases.ConjugationStrictEquivalence
import TNLean.MPS.Operator.Unitary.Simple
import QICLean.Spectral.Eigenvalue.ShiftedZeroTraceNilpotent

/-!
# The determinant invariant of conjugation symmetry

Theorem `conjphs` of arXiv:1703.09188 (lines 1406--1414) states that, when one of the ranks
`r, ℓ` of the standard form is odd, two conjugation-invariant MPUs are strictly equivalent under
conjugation if and only if `det(u₁ v₁) = det(u₂ v₂)`. The "if" direction is
`MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_of_det_mul_eq`. This file proves the
"only if" direction and assembles the equivalence.

The source proves "only if" (lines 1421--1424) by reading `det(u v) = ±1` along the continuous
gates supplied by Lemma `lem:equivalent-symmetry`. Here the determinant is read off the MPU
itself: on a ring of one standard-form site, the MPU is `v` after the exchange of the two
factors after `u`, so its determinant is `det(u v)`, read through the swap, times the sign of
the exchange of the two physical sites (`TwoSiteStandardFormData.det_mpo_one_eq`). Along a
path of MPUs invariant under conjugation, the operator on one site is real and unitary, so its
determinant is a continuous function with values `±1`, hence constant.

The operator on one site is unitary for every MPU, although the MPU property only asks for
unitarity on rings of at least two sites (`IsMPU.mpo_one_mem_unitaryGroup`). The double layer
`U^{(N)†} U^{(N)}` is the identity for `N ≥ 2`; for a single letter `X` of it, the traces of
`X^N` are then constant for `N ≥ 2`, and shifted nilpotence recovers the trace of `X`.

**Local fix (proof route):** the "only if" direction is proved without the forward direction of
Lemma `lem:equivalent-symmetry`, which is available only after blocking
(`docs/paper-gaps/mpu_symmetry_path_criterion_blocking.tex`). The statement keeps the source's
hypotheses; the "only if" direction does not use that one rank is odd.

## Main results

* `MPOTensor.IsMPU.mpo_one_mem_unitaryGroup`: an MPU is unitary on one site.
* `MPOTensor.TwoSiteStandardFormData.det_mpo_one_eq`: the determinant on one standard-form site.
* `MPOTensor.StrictlyEquivalentUnderSymmetry.det_mpo_one_eq_of_conjugation`: strict
  equivalence under conjugation fixes the determinant on one site.
* `MPOTensor.StrictlyEquivalentUnderSymmetry.det_mul_eq_of_conjugation`: the "only if"
  direction of Theorem `conjphs`.
* `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_iff_det_mul_eq`: Theorem `conjphs`,
  for tensors on pairs of sites in canonical form with any standard forms.
* `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_reindexPhysical_iff_det_mul_eq`: the
  same after a physical relabelling, as for the two-site blocks of one-site tensors.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D D₁ D₂ ℓ r : ℕ}

private theorem evalWord_replicate (M : MPOTensor d D) (i j : Fin d) (N : ℕ) :
    evalWord M (List.replicate N i) (List.replicate N j) = M (i, j) ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.replicate_succ, List.replicate_succ, evalWord_cons, ih, pow_succ']

/-- A tensor whose periodic operators are the identity on every ring of at least two sites has
the identity as its operator on one site.

Source context: arXiv:1703.09188, MPU unitarity at lengths `N = 2, 3, …`, lines 319--335. -/
theorem mpo_one_eq_one_of_forall_one_lt {T : MPOTensor d D}
    (h : ∀ N : ℕ, 1 < N → mpo T N = 1) : mpo T 1 = 1 := by
  have hpow : ∀ (i j : Fin d) (N : ℕ), 1 < N →
      Matrix.trace (T (i, j) ^ N) = if i = j then 1 else 0 := by
    intro i j N hN
    have hentry := congrFun (congrFun (h N hN) (fun _ ↦ i)) (fun _ ↦ j)
    rw [mpo_apply, mpoMatrixEntry, List.ofFn_const, List.ofFn_const, evalWord_replicate]
      at hentry
    rw [hentry, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have : (fun _ : Fin N ↦ i) ≠ fun _ ↦ j := fun he ↦
        hij (congrFun he ⟨0, by omega⟩)
      simp [hij, this]
  ext σ τ
  rw [mpo_apply, mpoMatrixEntry, Matrix.one_apply]
  have hσ : List.ofFn σ = [σ 0] := by simp [List.ofFn_succ]
  have hτ : List.ofFn τ = [τ 0] := by simp [List.ofFn_succ]
  rw [hσ, hτ, evalWord_cons, evalWord_nil, Matrix.mul_one]
  have hστ : (σ = τ) ↔ σ 0 = τ 0 := ⟨fun h ↦ h ▸ rfl, fun h ↦ funext fun x ↦ by
    rw [Fin.fin_one_eq_zero x, h]⟩
  by_cases h0 : σ 0 = τ 0
  · rw [ite_eq_left (hστ.mpr h0)]
    refine Matrix.trace_eq_one_of_forall_trace_pow_eq_one_of_one_lt _ fun N hN ↦ ?_
    rw [hpow _ _ N hN, ite_eq_left h0]
  · rw [ite_eq_right (fun h ↦ h0 (hστ.mp h))]
    have hnil := Matrix.isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt (T (σ 0, τ 0))
      fun N hN ↦ by rw [hpow _ _ N hN, ite_eq_right h0]
    exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero

/-- **An MPU is unitary on one site.** The MPU property asks for unitarity on rings of at least
two sites; unitarity on one site follows, since the double layer has the identity as its operator
on every ring of at least two sites.

Source: arXiv:1703.09188, equation `UisUnitary`, lines 319--335, with the double layer of
lines 363--388. -/
theorem IsMPU.mpo_one_mem_unitaryGroup {U : MPOTensor d D} (hU : IsMPU U) :
    mpo U 1 ∈ Matrix.unitaryGroup (Fin 1 → Fin d) ℂ := by
  have h : (mpo U 1)ᴴ * mpo U 1 = 1 := by
    rw [← mpo_doubleLayerTensor]
    refine mpo_one_eq_one_of_forall_one_lt fun N hN ↦ ?_
    rw [mpo_doubleLayerTensor]
    exact Matrix.mem_unitaryGroup_iff'.mp (hU N hN)
  exact Matrix.mem_unitaryGroup_iff'.mpr h

/-- An MPU whose operator on one site is fixed by complex conjugation has determinant `±1` on
one site.

Source: arXiv:1703.09188, proof of Theorem `conjphs`, lines 1421--1424, with the conjugation
symmetry of lines 1005--1010. -/
theorem IsMPU.det_mpo_one_eq_one_or_neg_one_of_map_star_eq {U : MPOTensor d D}
    (hU : IsMPU U) (hc : (mpo U 1).map (starRingEnd ℂ) = mpo U 1) :
    (mpo U 1).det = 1 ∨ (mpo U 1).det = -1 :=
  Matrix.det_eq_one_or_neg_one_of_map_star_eq hU.mpo_one_mem_unitaryGroup hc

/-- **The determinant on one standard-form site.** For a standard form with gates `u, v`, the
operator on a ring of one standard-form site is `v` after the exchange of the two factors after
`u`. Its determinant is the sign of the exchange of the two physical sites times `det(u v)`,
read on `ℂ^ℓ ⊗ ℂ^r` through the swap as in `Matrix.det_gauge_mul_swap`.

Source: arXiv:1703.09188, equation `StandardForm`, lines 603--617, and the determinant
`det(u v)` of Theorem `conjphs`, lines 1406--1416. -/
theorem TwoSiteStandardFormData.det_mpo_one_eq {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) :
    (mpo W 1).det = (Equiv.Perm.sign (Equiv.prodComm (Fin d) (Fin d)) : ℂ) *
      ((u * v).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det := by
  set σ : Equiv.Perm (Fin d × Fin d) := Equiv.prodComm (Fin d) (Fin d)
  set τ := Equiv.prodComm (Fin ℓ) (Fin r)
  set e₁ : (Fin 1 → Fin d × Fin d) ≃ Fin d × Fin d := Equiv.funUnique (Fin 1) _
  set e₂ : (Fin 1 → Fin ℓ × Fin r) ≃ Fin ℓ × Fin r := Equiv.funUnique (Fin 1) _
  have hcirc := TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted (N := 1) W u v S
  have hshift : twoSiteShiftedLayer (N := 1) v = (v.submatrix σ τ).submatrix e₁ e₂ := by
    ext i h
    simp [twoSiteShiftedLayer, σ, τ, e₁, e₂, Equiv.funUnique, Prod.swap]
  have hunshift : twoSiteUnshiftedLayer (N := 1) u = u.submatrix e₂ e₁ := by
    ext h j
    simp [twoSiteUnshiftedLayer, e₁, e₂, Equiv.funUnique]
  rw [hshift, hunshift, Matrix.submatrix_mul_equiv] at hcirc
  have hdet := congrArg Matrix.det hcirc
  rw [Matrix.det_reindex_self, Matrix.det_submatrix_equiv_self] at hdet
  rw [hdet]
  have hσ : v.submatrix σ τ * u = (v.submatrix id τ * u).submatrix σ id := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hσ, Matrix.det_permute]
  congr 1
  -- `det (X u) = det (u X)` for the rectangular factors, through one identification.
  have hcard : Fintype.card (Fin ℓ × Fin r) = Fintype.card (Fin d × Fin d) := by
    have h1 := Matrix.IsIsometry.card_le u S.u_unitary.1
    have h2 := Matrix.IsCoisometry.card_le u S.u_unitary.2
    omega
  set e : Fin ℓ × Fin r ≃ Fin d × Fin d := Fintype.equivOfCardEq hcard
  have hsplit : v.submatrix id τ * u =
      (v.submatrix id τ).submatrix id e.symm * u.submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv]
    simp
  have hsplit' : u.submatrix e.symm id * (v.submatrix id τ).submatrix id e.symm =
      (u * v.submatrix id τ).submatrix e.symm e.symm := by
    simpa only [Equiv.coe_refl] using
      Matrix.submatrix_mul_equiv u (v.submatrix id τ) e.symm (Equiv.refl _) e.symm
  have huv : (u * v).submatrix id τ = u * v.submatrix id τ := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hsplit, Matrix.det_mul_comm, hsplit', Matrix.det_submatrix_equiv_self, huv]

/-- **Strict equivalence under conjugation fixes the determinant on one site.** Along a path of
MPUs invariant under conjugation, the operator on one site is real and unitary, so its
determinant is a continuous function with values `±1`. The endpoints need not be simple, and the
physical dimensions are equal but need not be equal by definition.

Source: arXiv:1703.09188, proof of Theorem `conjphs`, lines 1421--1424, with Definition
`def:strictly-equivalent-symmetry`, lines 1345--1354. -/
theorem StrictlyEquivalentUnderSymmetry.det_mpo_one_eq_of_conjugation {da db Da Db : ℕ}
    {U : MPOTensor da Da} {V : MPOTensor db Db} {hphys : da = db}
    (h : StrictlyEquivalentUnderSymmetry (conjugationSymmetry db) U V hphys) :
    (mpo U 1).det = (mpo V 1).det := by
  subst hphys
  obtain ⟨-, -, D', ha, hb, hj⟩ := h
  have hmem := hj.somePath_mem
  have hcont : Continuous fun t ↦ (mpo (hj.somePath t) 1).det :=
    ((continuous_mpo 1).comp hj.somePath.continuous).matrix_det
  have hsq : Set.EqOn ((fun t ↦ (mpo (hj.somePath t) 1).det) ^ 2) 1 Set.univ := by
    intro t _
    obtain ⟨hW, hS⟩ := hmem t
    change (mpo (hj.somePath t) 1).det ^ 2 = 1
    rcases hW.det_mpo_one_eq_one_or_neg_one_of_map_star_eq
      (hS (show (1 : ℕ) ∈ (conjugationSymmetry da).applicable from Nat.one_pos)) with h' | h' <;>
      rw [h'] <;> norm_num
  have hends : (mpo (hj.somePath 0) 1).det = (mpo (hj.somePath 1) 1).det := by
    rcases isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hcont.continuousOn hsq with h' | h'
    · simpa using (h' (Set.mem_univ 0)).trans (h' (Set.mem_univ 1)).symm
    · simpa using (h' (Set.mem_univ 0)).trans (h' (Set.mem_univ 1)).symm
  rw [Path.source, Path.target, mpo_reindexPhysical, Matrix.det_reindex_self, mpo_padBond,
    mpo_padBond] at hends
  exact hends

/-- **Conjugation symmetry, the "only if" direction of Theorem `conjphs`.** Let `W₁, W₂` be
tensors on pairs of sites with standard forms with gates `u_i, v_i` of the same ranks `ℓ, r`.
If the tensors, after the physical relabelling `eP`, are strictly equivalent under
conjugation, then `det(u₁ v₁) = det(u₂ v₂)`, read on `ℂ^ℓ ⊗ ℂ^r` through the swap as in
`Matrix.det_gauge_mul_swap`.

The source assumes one of `r, ℓ` odd; this direction does not use it. The proof reads the
determinant off the MPU on one standard-form site instead of using the forward direction of
Lemma `lem:equivalent-symmetry`; see the module docstring.

Source: arXiv:1703.09188, Theorem `conjphs`, lines 1406--1414, "only if" direction, proof at
lines 1421--1424. -/
theorem StrictlyEquivalentUnderSymmetry.det_mul_eq_of_conjugation {d' : ℕ}
    (eP : Fin d' ≃ Fin (d * d)) {W₁ : MPOTensor (d * d) D₁} {W₂ : MPOTensor (d * d) D₂}
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData W₁ u₁ v₁) (S₂ : TwoSiteStandardFormData W₂ u₂ v₂)
    (h : StrictlyEquivalentUnderSymmetry (conjugationSymmetry d')
      (reindexPhysical eP W₁) (reindexPhysical eP W₂) rfl) :
    ((u₁ * v₁).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      ((u₂ * v₂).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det := by
  have hdet := h.det_mpo_one_eq_of_conjugation
  rw [mpo_reindexPhysical, mpo_reindexPhysical, Matrix.det_reindex_self, Matrix.det_reindex_self,
    S₁.det_mpo_one_eq, S₂.det_mpo_one_eq] at hdet
  have hs : (Equiv.Perm.sign (Equiv.prodComm (Fin d) (Fin d)) : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.prodComm (Fin d) (Fin d))) with h' | h' <;>
      simp [h']
  exact mul_left_cancel₀ hs hdet

/-- **Theorem `conjphs`, for relabelled tensors on pairs of sites.** The statement of
`strictlyEquivalentUnderSymmetry_conjugation_iff_det_mul_eq` after a physical relabelling `eP`,
as for the alphabet of length-two words of a one-site tensor.

Source: arXiv:1703.09188, Theorem `conjphs`, lines 1406--1414, proof at lines 1419--1446. -/
theorem strictlyEquivalentUnderSymmetry_conjugation_reindexPhysical_iff_det_mul_eq {d' : ℕ}
    (eP : Fin d' ≃ Fin (d * d)) {W₁ : MPOTensor (d * d) D₁} {W₂ : MPOTensor (d * d) D₂}
    (hcf₁ : MPSTensor.IsMPUCanonicalForm (reindexPhysical eP W₁).toMPSTensor)
    (hcf₂ : MPSTensor.IsMPUCanonicalForm (reindexPhysical eP W₂).toMPSTensor)
    (hc₁ : ∀ N : ℕ, 0 < N → mpo W₁ N = (mpo W₁ N).map (starRingEnd ℂ))
    (hc₂ : ∀ N : ℕ, 0 < N → mpo W₂ N = (mpo W₂ N).map (starRingEnd ℂ))
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData W₁ u₁ v₁) (S₂ : TwoSiteStandardFormData W₂ u₂ v₂)
    (hodd : Odd ℓ ∨ Odd r) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry d')
        (reindexPhysical eP W₁) (reindexPhysical eP W₂) rfl ↔
      ((u₁ * v₁).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
        ((u₂ * v₂).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det :=
  ⟨StrictlyEquivalentUnderSymmetry.det_mul_eq_of_conjugation eP S₁ S₂,
    strictlyEquivalentUnderSymmetry_conjugation_reindexPhysical_of_det_mul_eq eP hcf₁ hcf₂
      hc₁ hc₂ S₁ S₂ hodd⟩

/-- **Theorem `conjphs`.** Let `W₁, W₂` be tensors on pairs of sites in canonical form whose
MPUs are invariant under conjugation, with standard forms with gates `u_i, v_i` of the same
ranks `ℓ, r`, one of them odd. Then `W₁` and `W₂` are strictly equivalent under conjugation if
and only if `det(u₁ v₁) = det(u₂ v₂)`, read on `ℂ^ℓ ⊗ ℂ^r` through the swap. No canonical
form II is assumed; the canonical form of the two tensors is part of strict equivalence.

Source: arXiv:1703.09188, Theorem `conjphs`, lines 1406--1414, proof at lines 1419--1446; the
"only if" direction follows the route of the module docstring. -/
theorem strictlyEquivalentUnderSymmetry_conjugation_iff_det_mul_eq
    {W₁ : MPOTensor (d * d) D₁} {W₂ : MPOTensor (d * d) D₂}
    (hcf₁ : MPSTensor.IsMPUCanonicalForm W₁.toMPSTensor)
    (hcf₂ : MPSTensor.IsMPUCanonicalForm W₂.toMPSTensor)
    (hc₁ : ∀ N : ℕ, 0 < N → mpo W₁ N = (mpo W₁ N).map (starRingEnd ℂ))
    (hc₂ : ∀ N : ℕ, 0 < N → mpo W₂ N = (mpo W₂ N).map (starRingEnd ℂ))
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData W₁ u₁ v₁) (S₂ : TwoSiteStandardFormData W₂ u₂ v₂)
    (hodd : Odd ℓ ∨ Odd r) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (d * d)) W₁ W₂ rfl ↔
      ((u₁ * v₁).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
        ((u₂ * v₂).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det :=
  strictlyEquivalentUnderSymmetry_conjugation_reindexPhysical_iff_det_mul_eq (Equiv.refl _)
    hcf₁ hcf₂ hc₁ hc₂ S₁ S₂ hodd

end MPOTensor
