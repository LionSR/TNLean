/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CleanUnitaryImplementation
import TNLean.MPS.Preparation.ArbitrarySiteGateEmbedding

/-!
# Placement of clean circuits in a common workspace

A circuit on selected logical sites and a small clean workspace can be
placed in a larger logical register with one shared clean workspace. The
operator identity below holds on every logical input. The extra workspace
sites remain zero, and the neighboring-pair decomposition is obtained by
routing the actual local circuit.

These are the placement identities used for leaves, inverse child circuits,
and repeated image reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor
open QuantumCircuit
open scoped BigOperators

namespace MPSPreparation

variable {d m n b A K : ℕ}

/-- Place the local logical sites and local scratch sites in their respective
parts of the larger register. Source: the common workspace construction in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cleanImplementationSites (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A) :
    Fin (m + b) ↪ Fin (n + A) where
  toFun := Fin.append (fun j ↦ Fin.castAdd A (e j)) (fun j ↦ Fin.natAdd n (t j))
  inj' := by
    apply Fin.append_injective_iff.mpr
    refine ⟨(Fin.castAdd_injective n A).comp e.injective, ?_, ?_⟩
    · intro i j hij
      apply t.injective
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simp only [Fin.val_natAdd] at hval
      omega
    · intro i j hij
      have hval := congrArg Fin.val hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := (e i).isLt
      omega

/-- The logical part of a clean placement. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem cleanImplementationSites_castAdd (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    (j : Fin m) :
    cleanImplementationSites e t (Fin.castAdd b j) = Fin.castAdd A (e j) := by
  change Fin.append (fun i ↦ Fin.castAdd A (e i)) (fun i ↦ Fin.natAdd n (t i))
    (Fin.castAdd b j) = _
  exact Fin.append_left _ _ j

/-- The scratch part of a clean placement. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem cleanImplementationSites_natAdd (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    (j : Fin b) :
    cleanImplementationSites e t (Fin.natAdd m j) = Fin.natAdd n (t j) := by
  change Fin.append (fun i ↦ Fin.castAdd A (e i)) (fun i ↦ Fin.natAdd n (t i))
    (Fin.natAdd m j) = _
  exact Fin.append_right _ _ j

variable [NeZero d]

/-- An initialized row inclusion vanishes off the zero-workspace subspace.
Source: the initialized workspace in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initializedBasisMatrix_zeroWorkspace_mul_apply
    (Z : Matrix (Cfg d n) (Cfg d m) ℂ) (z : Cfg d (n + A)) (x : Cfg d m) :
    (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) * Z) z x =
      if ∀ j, z (Fin.natAdd n j) = 0 then
        Z (fun j ↦ z (Fin.castAdd A j)) x else 0 := by
  classical
  simp only [Matrix.mul_apply, initializedBasisMatrix, Matrix.submatrix_apply, id_eq,
    Matrix.one_apply]
  change (∑ y : Cfg d n, (if z = Fin.append y 0 then (1 : ℂ) else 0) * Z y x) = _
  by_cases hz : ∀ j, z (Fin.natAdd n j) = 0
  · rw [ite_eq_left hz]
    let y : Cfg d n := fun j ↦ z (Fin.castAdd A j)
    have hzy : z = Fin.append y 0 := by
      funext j
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
      · simp only [Fin.append_left, y]
      · simpa only [Fin.append_right, Pi.zero_apply] using hz i
    rw [Finset.sum_eq_single y]
    · rw [ite_eq_left hzy, one_mul]
    · intro y' _ hne
      have hne' : z ≠ Fin.append y' 0 := by
        intro h
        apply hne
        funext i
        have hval := congrFun (h.symm.trans hzy) (Fin.castAdd A i)
        simpa only [Fin.append_left] using hval
      rw [ite_eq_right hne', zero_mul]
    · simp
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro y _
    have hne : z ≠ Fin.append y 0 := by
      intro h
      apply hz
      intro j
      simp only [h, Fin.append_right, Pi.zero_apply]
    rw [ite_eq_right hne, zero_mul]

private theorem cleanImplementationSites_agreeOff_iff
    (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    (z : Cfg d (n + A)) (x : Cfg d n) :
    (AgreeOff (cleanImplementationSites e t) z (Fin.append x 0) ∧
        ∀ j, z (Fin.natAdd n (t j)) = 0) ↔
      ((∀ j, z (Fin.natAdd n j) = 0) ∧
        AgreeOff e (fun j ↦ z (Fin.castAdd A j)) x) := by
  constructor
  · rintro ⟨hag, hzero⟩
    constructor
    · intro j
      by_cases hj : ∃ i, t i = j
      · obtain ⟨i, rfl⟩ := hj
        exact hzero i
      · have h := hag (Fin.natAdd n j) (by
          intro p
          refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) p
          · rw [cleanImplementationSites_castAdd]
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            have := (e i).isLt
            omega
          · rw [cleanImplementationSites_natAdd]
            intro h
            exact hj ⟨i, (Fin.natAdd_injective A n) h⟩)
        simpa only [Fin.append_right, Pi.zero_apply] using h
    · intro j hj
      have h := hag (Fin.castAdd A j) (by
        intro p
        refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) p
        · rw [cleanImplementationSites_castAdd]
          intro h
          exact hj i ((Fin.castAdd_injective n A) h)
        · rw [cleanImplementationSites_natAdd]
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          have := j.isLt
          omega)
      simpa only [Fin.append_left] using h
  · rintro ⟨hzero, hag⟩
    constructor
    · intro p hp
      refine Fin.addCases (fun j hj ↦ ?_) (fun j _ ↦ ?_) p hp
      · have h := hag j (by
          intro i hi
          apply hj (Fin.castAdd b i)
          simp only [cleanImplementationSites_castAdd, hi])
        simpa only [Fin.append_left] using h
      · simpa only [Fin.append_right, Pi.zero_apply] using hzero j
    · intro j
      exact hzero (t j)

/-- A local clean implementation remains clean after placing its logical
sites and scratch sites in a larger register. The entire larger workspace
starts and ends in zero, for every logical input. Source: the common
workspace argument in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem IsCleanImplementation.embedOp
    (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    {U : Matrix (Cfg d (m + b)) (Cfg d (m + b)) ℂ}
    {Z : Matrix (Cfg d m) (Cfg d m) ℂ}
    (hlocal : IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := m) (a := b))) U Z) :
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)))
      (embedOp (cleanImplementationSites e t) U) (embedOp e Z) := by
  classical
  change QuantumCircuit.embedOp (cleanImplementationSites e t) U *
    initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) = _
  rw [mul_initializedBasisMatrix]
  ext z x
  change QuantumCircuit.embedOp (cleanImplementationSites e t) U z (Fin.append x 0) = _
  rw [initializedBasisMatrix_zeroWorkspace_mul_apply]
  have hrestrict : (Fin.append x (0 : Cfg d A)) ∘ cleanImplementationSites e t =
      Fin.append (x ∘ e) 0 := by
    funext j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp only [Function.comp_apply, cleanImplementationSites_castAdd, Fin.append_left]
    · simp only [Function.comp_apply, cleanImplementationSites_natAdd, Fin.append_right,
        Pi.zero_apply]
  change U * initializedBasisMatrix
      (zeroWorkspaceEmbedding (d := d) (n := m) (a := b)) = _ at hlocal
  have hentry := congrArg (fun M ↦ M (z ∘ cleanImplementationSites e t) (x ∘ e)) hlocal
  rw [mul_initializedBasisMatrix, initializedBasisMatrix_zeroWorkspace_mul_apply] at hentry
  change U (z ∘ cleanImplementationSites e t) (Fin.append (x ∘ e) 0) = _ at hentry
  simp only [Function.comp_apply, cleanImplementationSites_natAdd,
    cleanImplementationSites_castAdd] at hentry
  rw [embedOp_apply, hrestrict, hentry, embedOp_apply]
  simp only [← ite_and, cleanImplementationSites_agreeOff_iff]
  rfl

/-- The routed circuit and the shared-pool cleanup equation follow from
an actual local pair circuit and its local clean action. No larger-register
circuit or cleanup witness is assumed. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_isCleanImplementation_embedOp
    (hd : 0 < d) (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    {U : Matrix (Cfg d (m + b)) (Cfg d (m + b)) ℂ}
    {Z : Matrix (Cfg d m) (Cfg d m) ℂ}
    (hU : IsPairProduct d (m + b) K U)
    (hlocal : IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := m) (a := b))) U Z) :
    IsPairProduct d (n + A) (K * (2 * (n + A)))
        (embedOp (cleanImplementationSites e t) U) ∧
      IsCleanImplementation
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)))
        (embedOp (cleanImplementationSites e t) U) (embedOp e Z) :=
  ⟨hU.embedOp_injective hd (cleanImplementationSites e t).injective,
    hlocal.embedOp e t⟩

end MPSPreparation
