/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SelectedZeroRegisterReflection

/-!
# Selected zero-flags reflections in a larger common scratch pool

A test of `a` selected logical sites uses only the first `a` sites of an
appended scratch pool of size `A ≥ a`. The construction is a full unitary
circuit on the `n + A` sites. Starting with the entire pool zero, the circuit
implements the selected logical reflection and returns every scratch site
to zero, including the unused sites of the pool.

This is the reusable pool construction for the recursive image reflections
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. Both the
circuit and its clean action are derived; no implementation witness is
supplied as an assumption.
-/

open Matrix MPSTensor
open QuantumCircuit

namespace MPSPreparation

variable {d n a A : ℕ}

/-- Place the selected flags and their `a` working scratch sites in the full
register with a pool of size `A`. The finite inclusion retains the original
site numbers and hence leaves the remaining pool sites untouched. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def selectedZeroRegisterPoolSites (s : Fin a ↪ Fin n) (hpool : a ≤ A) :
    Fin (a + a) ↪ Fin (n + A) :=
  (selectedZeroRegisterSites s).trans (Fin.castLEEmb (Nat.add_le_add_left hpool n))

/-- The pool placement reads exactly the selected logical sites. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem selectedZeroRegisterPoolSites_castAdd (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (j : Fin a) :
    selectedZeroRegisterPoolSites s hpool (Fin.castAdd a j) = Fin.castAdd A (s j) := by
  change Fin.castLE (Nat.add_le_add_left hpool n)
    (selectedZeroRegisterSites s (Fin.castAdd a j)) = _
  rw [selectedZeroRegisterSites_castAdd]
  apply Fin.ext
  rfl

/-- The working scratch sites are the first `a` sites of the full pool.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem selectedZeroRegisterPoolSites_natAdd (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (j : Fin a) :
    selectedZeroRegisterPoolSites s hpool (Fin.natAdd a j) =
      Fin.natAdd n (Fin.castLE hpool j) := by
  change Fin.castLE (Nat.add_le_add_left hpool n) (selectedZeroRegisterSites s (Fin.natAdd a j)) = _
  rw [selectedZeroRegisterSites_natAdd]
  apply Fin.ext
  rfl

variable [NeZero d]

/-- The actual placed zero-register reflection uses the first `a` scratch
sites and acts as the identity on all unused pool sites. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def selectedZeroRegisterReflectionPool (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (ha : 0 < a) : Matrix (Cfg d (n + A)) (Cfg d (n + A)) ℂ :=
  embedOp (selectedZeroRegisterPoolSites s hpool) (zeroRegisterReflection ha)

/-- The pool reflection has an actual neighboring-pair decomposition with
its explicit swap-routing overhead. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_selectedZeroRegisterReflectionPool (hd : 2 ≤ d)
    (s : Fin a ↪ Fin n) (hpool : a ≤ A) (ha : 0 < a) :
    IsPairProduct d (n + A) (zeroRegisterReflectionGateCount d a * (2 * (n + A)))
      (selectedZeroRegisterReflectionPool s hpool ha) :=
  isPairProduct_embedOp_zeroRegisterReflection hd ha
    (selectedZeroRegisterPoolSites s hpool).injective

/-- Every logical configuration is allowed, and every site of the larger
scratch pool returns to zero. In particular, unused scratch is not treated
as an arbitrary input in the cleanup statement. Source: the shared pool
construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isCleanImplementation_selectedZeroRegisterReflectionPool (hd : 2 ≤ d)
    (s : Fin a ↪ Fin n) (hpool : a ≤ A) (ha : 0 < a) :
    IsCleanImplementation
      (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)))
      (selectedZeroRegisterReflectionPool s hpool ha) (selectedZeroRegisterLogical s) := by
  change selectedZeroRegisterReflectionPool s hpool ha *
    initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) = _
  rw [mul_initializedBasisMatrix]
  ext z x
  change embedOp (selectedZeroRegisterPoolSites s hpool) (zeroRegisterReflection ha) z
    (Fin.append x 0) = _
  rw [selectedZeroRegisterLogical, Matrix.mul_diagonal]
  change embedOp (selectedZeroRegisterPoolSites s hpool) (zeroRegisterReflection ha) z
      (Fin.append x 0) =
    (if z = Fin.append x 0 then (1 : ℂ) else 0) *
      (if ∀ j, x (s j) = 0 then -1 else 1)
  have hx : ∀ j, (Fin.append x (0 : Cfg d A))
      (selectedZeroRegisterPoolSites s hpool (Fin.natAdd a j)) = 0 := by
    intro j
    simp only [selectedZeroRegisterPoolSites_natAdd, Fin.append_right, Pi.zero_apply]
  rw [embedOp_zeroRegisterReflection_apply_clean hd ha _ _ _ hx]
  simp only [selectedZeroRegisterPoolSites_castAdd, Fin.append_left]
  exact mul_comm _ _

/-- An explicit neighboring-pair budget, including one exact phase gate
when the selected register is empty. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def selectedZeroRegisterReflectionPoolGateCount (d n a A : ℕ) : ℕ :=
  if a = 0 then 1 else zeroRegisterReflectionGateCount d a * (2 * (n + A))

/-- A selected zero-flags reflection is implemented by an actual circuit
using a larger shared initialized pool. The circuit and cleanup identity
are constructed on all logical inputs. An empty selected register gives
one exact global-phase gate. Source: recursive image reflections in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isPairProduct_isCleanImplementation_selectedZeroRegisterPool
    (hd : 2 ≤ d) (hn : 2 ≤ n) (s : Fin a ↪ Fin n) (hpool : a ≤ A) :
    ∃ U : Matrix (Cfg d (n + A)) (Cfg d (n + A)) ℂ,
      IsPairProduct d (n + A) (selectedZeroRegisterReflectionPoolGateCount d n a A) U ∧
      IsCleanImplementation
        (initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)))
        U (selectedZeroRegisterLogical s) := by
  by_cases ha : a = 0
  · subst a
    refine ⟨-1, ?_, ?_⟩
    · simpa only [selectedZeroRegisterReflectionPoolGateCount, ite_true] using
        isPairProduct_neg_one (d := d) (n := n + A) (by omega)
    · change (-1 : Matrix (Cfg d (n + A)) (Cfg d (n + A)) ℂ) *
        initializedBasisMatrix (zeroWorkspaceEmbedding (d := d) (n := n) (a := A)) = _
      rw [selectedZeroRegisterLogical_empty]
      simp
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    refine ⟨selectedZeroRegisterReflectionPool s hpool hapos, ?_,
      isCleanImplementation_selectedZeroRegisterReflectionPool hd s hpool hapos⟩
    simpa only [selectedZeroRegisterReflectionPoolGateCount, ha, ite_false] using
      isPairProduct_selectedZeroRegisterReflectionPool hd s hpool hapos

end MPSPreparation
