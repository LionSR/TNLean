/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CleanUnitaryImplementation

/-!
# Reflecting selected zero flags with a shared initialized workspace

An injective choice of `a` sites in an `n`-site logical register determines
the subspace where all selected flags are zero. A neighboring-pair circuit
reflects this subspace using `a` scratch sites appended to the logical
register. The scratch sites return exactly to zero on every logical input;
unselected physical sites remain arbitrary. The same scratch pool may
therefore be reused in every image reflection of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The circuit and the clean implementation are derived explicitly. No circuit,
conjunction, or cleanup witness is supplied as an assumption. An empty set
of flags gives the global phase minus one, implemented by one neighboring
pair gate when the logical chain has at least two sites.
-/

open Matrix MPSTensor
open QuantumCircuit

namespace MPSPreparation

variable {d n a : ℕ}

/-- Place the selected logical flags before their appended scratch sites.
Source: the shared scratch pool in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def selectedZeroRegisterSites (s : Fin a ↪ Fin n) : Fin (a + a) ↪ Fin (n + a) where
  toFun := Fin.append (fun j ↦ Fin.castAdd a (s j)) (Fin.natAdd n)
  inj' := by
    apply Fin.append_injective_iff.mpr
    refine ⟨(Fin.castAdd_injective n a).comp s.injective, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simp only [Fin.val_natAdd] at hval
      omega
    · intro i j hij
      have hval := congrArg Fin.val hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := (s i).isLt
      omega

/-- The first half of the placement reads exactly the selected logical sites.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem selectedZeroRegisterSites_castAdd (s : Fin a ↪ Fin n) (j : Fin a) :
    selectedZeroRegisterSites s (Fin.castAdd a j) = Fin.castAdd a (s j) := by
  change Fin.append (fun i ↦ Fin.castAdd a (s i)) (Fin.natAdd n) (Fin.castAdd a j) = _
  exact Fin.append_left _ _ j

/-- The second half of the placement is exactly the appended scratch pool.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem selectedZeroRegisterSites_natAdd (s : Fin a ↪ Fin n) (j : Fin a) :
    selectedZeroRegisterSites s (Fin.natAdd a j) = Fin.natAdd n j := by
  change Fin.append (fun i ↦ Fin.castAdd a (s i)) (Fin.natAdd n) (Fin.natAdd a j) = _
  exact Fin.append_right _ _ j

variable [NeZero d]

/-- The logical reflection has phase minus one precisely when every selected
flag is zero, and phase plus one otherwise. Source: initialized-subspace
reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def selectedZeroRegisterLogical (s : Fin a ↪ Fin n) :
    Matrix (Cfg d n) (Cfg d n) ℂ :=
  diagonal fun x ↦ if ∀ j, x (s j) = 0 then -1 else 1

/-- The selected-flags reflection is a full logical unitary. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem selectedZeroRegisterLogical_mem_unitary (s : Fin a ↪ Fin n) :
    selectedZeroRegisterLogical (d := d) s ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [selectedZeroRegisterLogical, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal]
  ext x y
  by_cases hx : ∀ j, x (s j) = 0 <;> simp [diagonal_apply, Matrix.one_apply, hx]


/-- The logical diagonal phase is precisely `I - 2P`, where `P` projects
onto configurations having all selected flags zero. Source: initialized
subspace reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem selectedZeroRegisterLogical_eq_one_sub (s : Fin a ↪ Fin n) :
    selectedZeroRegisterLogical (d := d) s =
      1 - (2 : ℂ) • diagonal (fun x : Cfg d n ↦
        if ∀ j, x (s j) = 0 then (1 : ℂ) else 0) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hx : ∀ j, x (s j) = 0 <;>
      norm_num [selectedZeroRegisterLogical, Matrix.diagonal_apply, Matrix.one_apply, hx]
  · simp [selectedZeroRegisterLogical, hxy]

/-- The concrete shared-pool circuit for a nonempty selected register.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def selectedZeroRegisterReflection (s : Fin a ↪ Fin n) (ha : 0 < a) :
    Matrix (Cfg d (n + a)) (Cfg d (n + a)) ℂ :=
  embedOp (selectedZeroRegisterSites s) (zeroRegisterReflection ha)

/-- The placed reflection has an actual neighboring-pair decomposition with
its explicit swap-routing overhead. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_selectedZeroRegisterReflection (hd : 2 ≤ d)
    (s : Fin a ↪ Fin n) (ha : 0 < a) :
    IsPairProduct d (n + a) (zeroRegisterReflectionGateCount d a * (2 * (n + a)))
      (selectedZeroRegisterReflection s ha) :=
  isPairProduct_embedOp_zeroRegisterReflection hd ha (selectedZeroRegisterSites s).injective

/-- The concrete placed circuit restores the entire appended scratch pool
on every logical input. The only logical phase test is that the selected
flags are zero; all other logical sites are unrestricted. Source: the
reusable scratch construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isCleanImplementation_selectedZeroRegisterReflection (hd : 2 ≤ d)
    (s : Fin a ↪ Fin n) (ha : 0 < a) :
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a)))
      (selectedZeroRegisterReflection s ha) (selectedZeroRegisterLogical s) := by
  change selectedZeroRegisterReflection s ha *
    initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a)) = _
  rw [mul_initializedBasisMatrix]
  ext z x
  change embedOp (selectedZeroRegisterSites s) (zeroRegisterReflection ha) z
    (Fin.append x 0) = _
  rw [selectedZeroRegisterLogical, Matrix.mul_diagonal]
  change embedOp (selectedZeroRegisterSites s) (zeroRegisterReflection ha) z
      (Fin.append x 0) =
    (if z = Fin.append x 0 then (1 : ℂ) else 0) *
      (if ∀ j, x (s j) = 0 then -1 else 1)
  have hx : ∀ j, (Fin.append x (0 : Cfg d a))
      (selectedZeroRegisterSites s (Fin.natAdd a j)) = 0 := by
    intro j
    simp only [selectedZeroRegisterSites_natAdd, Fin.append_right, Pi.zero_apply]
  rw [embedOp_zeroRegisterReflection_apply_clean hd ha _ _ _ hx]
  simp only [selectedZeroRegisterSites_castAdd, Fin.append_left]
  exact mul_comm _ _

/-- With no selected flags, the logical reflection is the global phase
minus one. Source: the empty initialized-register test in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem selectedZeroRegisterLogical_empty (s : Fin 0 ↪ Fin n) :
    selectedZeroRegisterLogical (d := d) s = -1 := by
  classical
  ext x y
  by_cases hxy : x = y <;>
    simp [selectedZeroRegisterLogical, hxy]

/-- An explicit gate budget for all selected register sizes, including the
empty test. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def selectedZeroRegisterReflectionGateCount (d n a : ℕ) : ℕ :=
  if a = 0 then 1 else zeroRegisterReflectionGateCount d a * (2 * (n + a))

/-- Every selected zero-flags test has an actual clean neighboring-pair
implementation on one reusable appended scratch pool. The matrix, circuit,
and cleanup equality are constructed in the proof. No implementation
witness is a premise. For an empty selected register, the chain is assumed
to contain a neighboring pair to implement the exact global phase.
Source: image reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isPairProduct_isCleanImplementation_selectedZeroRegister
    (hd : 2 ≤ d) (hn : 2 ≤ n) (s : Fin a ↪ Fin n) :
    ∃ U : Matrix (Cfg d (n + a)) (Cfg d (n + a)) ℂ,
      IsPairProduct d (n + a) (selectedZeroRegisterReflectionGateCount d n a) U ∧
      IsCleanImplementation
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := a)))
        U (selectedZeroRegisterLogical s) := by
  by_cases ha : a = 0
  · subst a
    refine ⟨-1, ?_, ?_⟩
    · simpa only [selectedZeroRegisterReflectionGateCount, ite_true, Nat.add_zero] using
        isPairProduct_neg_one (d := d) hn
    · change (-1 : Matrix (Cfg d (n + 0)) (Cfg d (n + 0)) ℂ) *
        initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := 0)) = _
      rw [selectedZeroRegisterLogical_empty]
      simp
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    refine ⟨selectedZeroRegisterReflection s hapos, ?_,
      isCleanImplementation_selectedZeroRegisterReflection hd s hapos⟩
    simpa only [selectedZeroRegisterReflectionGateCount, ha, ite_false] using
      isPairProduct_selectedZeroRegisterReflection hd s hapos

end MPSPreparation
