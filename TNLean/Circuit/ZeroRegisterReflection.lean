/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.ZeroRegisterConjunction
open QuantumCircuit

/-!
# Zero-register reflection with reusable clean scratch

For a nonempty register of `a` sites, a reversible controlled-shift network
records the successive zero tests in `a` initially zero scratch sites.
Applying a minus sign when the final scratch value is one, then reversing
the network, reflects the all-zero data vector. Every data input is
allowed and all scratch sites return exactly to zero. The implementation
is a genuine neighboring-pair circuit with gate count quadratic in `a`
at fixed local dimension.

This is the initialized-register reflection in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The empty register test
is the scalar global phase minus one and is a separate case.
-/

open Matrix

namespace QuantumCircuit

variable {d a : ℕ} [NeZero d]

/-- The single-site phase which is minus one on level one and plus one
on all other levels. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def zeroScratchPhaseLocal : Matrix (Fin d) (Fin d) ℂ :=
  diagonal fun b ↦ if b = 1 then -1 else 1

/-- The conjunction phase is a full single-site unitary. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroScratchPhaseLocal_mem_unitary :
    zeroScratchPhaseLocal (d := d) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [zeroScratchPhaseLocal, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal]
  ext i j
  by_cases hi : i = 1 <;> simp [diagonal_apply, Matrix.one_apply, hi]

/-- The phase is applied to the last scratch coordinate. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroScratchPhase (ha : 0 < a) :
    Matrix (Fin (a + a) → Fin d) (Fin (a + a) → Fin d) ℂ :=
  siteOp (Fin.natAdd a ⟨a - 1, by omega⟩) zeroScratchPhaseLocal

/-- The scratch phase admits a neighboring-pair circuit after swap routing.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_zeroScratchPhase (hd : 2 ≤ d) (ha : 0 < a) :
    IsPairProduct d (a + a) (2 * (a + a)) (zeroScratchPhase (d := d) ha) := by
  let t : Fin (a + a) := Fin.natAdd a ⟨a - 1, by omega⟩
  change IsPairProduct d (a + a) (2 * (a + a)) (siteOp t zeroScratchPhaseLocal)
  exact isPairProduct_of_mem_supportedOperators_card_le_two
    (d := d) (n := a + a) (by omega) (by omega) (T := {t}) (by simp)
    (siteOp_mem_unitary t zeroScratchPhaseLocal_mem_unitary)
    (by simpa using (siteOp_mem_supportedOperators (d := d) t
      (zeroScratchPhaseLocal (d := d))))

/-- Compute the conjunction, phase the final scratch test, and uncompute.
The permutation-matrix convention sends a ket by the inverse permutation,
so the forward computation is the adjoint of the leftmost matrix. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def zeroRegisterReflection (ha : 0 < a) :
    Matrix (Fin (a + a) → Fin d) (Fin (a + a) → Fin d) ℂ :=
  (zeroConjunctionPerm a).permMatrix ℂ * zeroScratchPhase ha *
    ((zeroConjunctionPerm a).permMatrix ℂ)ᴴ

/-- Explicit gate count for compute, phase, and uncompute. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def zeroRegisterReflectionGateCount (d a : ℕ) : ℕ :=
  2 * a * zeroConjunctionStepGateCount d a + 2 * (a + a)

/-- The zero-register reflection is an actual neighboring-pair circuit with
quadratic gate count at fixed local dimension. No circuit or conjunction
witness is assumed. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_zeroRegisterReflection (hd : 2 ≤ d) (ha : 0 < a) :
    IsPairProduct d (a + a) (zeroRegisterReflectionGateCount d a)
      (zeroRegisterReflection (d := d) ha) := by
  have hnet := isPairProduct_zeroConjunctionPerm (a := a) hd a
  have hphase := isPairProduct_zeroScratchPhase hd ha
  have hcircuit := (hnet.mul hphase).mul hnet.star
  exact hcircuit.mono (le_of_eq (by dsimp [zeroRegisterReflectionGateCount]; ring))

/-- The implementation is a full unitary, including on nonzero scratch
inputs. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroRegisterReflection_mem_unitary (hd : 2 ≤ d) (ha : 0 < a) :
    zeroRegisterReflection (d := d) ha ∈
      unitary (Matrix (Fin (a + a) → Fin d) (Fin (a + a) → Fin d) ℂ) :=
  (isPairProduct_zeroRegisterReflection hd ha).mem_unitary

/-- The reflected phase is the final computed scratch test. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroRegisterReflection_eq_diagonal (ha : 0 < a) :
    zeroRegisterReflection (d := d) ha = diagonal fun z ↦
      if zeroConjunctionPerm a z (Fin.natAdd a ⟨a - 1, by omega⟩) = 1 then -1 else 1 := by
  classical
  rw [zeroRegisterReflection, zeroScratchPhase, zeroScratchPhaseLocal, siteOp_diagonal,
    conjTranspose_permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  simp [submatrix_apply, diagonal_apply, Equiv.Perm.inv_def]

/-- Every clean-scratch input basis state is reflected according to its
logical zero test and retains exactly zero scratch. All data configurations
are quantified. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroRegisterReflection_apply_clean (hd : 2 ≤ d) (ha : 0 < a)
    (x : (Fin a → Fin d)) (z : (Fin (a + a) → Fin d)) :
    zeroRegisterReflection (d := d) ha z (Fin.append x 0) =
      (if ∀ i, x i = 0 then (-1 : ℂ) else 1) *
        (if z = Fin.append x 0 then 1 else 0) := by
  classical
  rw [zeroRegisterReflection_eq_diagonal, diagonal_apply]
  by_cases hz : z = Fin.append x 0
  · subst z
    rw [zeroConjunctionPerm_apply_clean hd x a le_rfl]
    have hsucc : a - 1 + 1 = a := by omega
    simp only [zeroConjunctionState, Fin.append_right, Fin.isLt, ite_true, hsucc,
      zeroPrefixBit_eq_one hd, zeroPrefixTest, true_implies, mul_one]
  · simp [hz]

/-- The gate bound is explicitly quadratic in the number of tested sites.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroRegisterReflectionGateCount_eq (d a : ℕ) :
    zeroRegisterReflectionGateCount d a =
      8 * (38 * (d ^ 3) ^ 6 + 1) * a ^ 2 + 4 * a := by
  simp only [zeroRegisterReflectionGateCount, zeroConjunctionStepGateCount]
  ring


/-- On the entire clean-scratch subspace, the circuit intertwines the
logical reflection `1 - 2 |0⟩⟨0|` with the standard zero-scratch embedding.
This is an exact linear-map identity, so arbitrary superpositions and
reference entanglement are included. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem zeroRegisterReflection_mul_cleanEmbedding (hd : 2 ≤ d) (ha : 0 < a) :
    zeroRegisterReflection (d := d) ha *
        (Matrix.of fun (z : (Fin (a + a) → Fin d)) (x : (Fin a → Fin d)) ↦
          if z = Fin.append x 0 then (1 : ℂ) else 0) =
      (Matrix.of fun (z : (Fin (a + a) → Fin d)) (x : (Fin a → Fin d)) ↦
        if z = Fin.append x 0 then (1 : ℂ) else 0) *
          (1 - (2 : ℂ) • Matrix.diagonal fun x : Fin a → Fin d ↦
            if x = 0 then (1 : ℂ) else 0) := by
  classical
  let J : Matrix ((Fin (a + a) → Fin d)) ((Fin a → Fin d)) ℂ :=
    Matrix.of fun z x ↦ if z = Fin.append x 0 then 1 else 0
  change zeroRegisterReflection ha * J =
    J * (1 - (2 : ℂ) • Matrix.diagonal fun x : (Fin a → Fin d) ↦ if x = 0 then (1 : ℂ) else 0)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  ext z x
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.append x 0)]
  · simp only [J, Matrix.of_apply, ite_true, mul_one]
    rw [zeroRegisterReflection_apply_clean hd ha]
    have hzero : (∀ i, x i = 0) ↔ x = 0 := by
      exact ⟨fun h ↦ funext h, fun h ↦ by simp [h]⟩
    simp only [hzero]
    by_cases hx : x = 0
    · subst x
      by_cases hz : z = Fin.append 0 0 <;>
        norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_diagonal, hz]
    · by_cases hz : z = Fin.append x 0 <;>
        simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_diagonal, hz, hx]
  · intro u _ hu
    simp [J, hu]
  · simp

/-- The zero-register reflection may be placed at any distinct selected
sites of a larger chain. Every original gate is routed by swaps. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_embedOp_zeroRegisterReflection {n : ℕ}
    (hd : 2 ≤ d) (ha : 0 < a) {e : Fin (a + a) → Fin n}
    (he : Function.Injective e) :
    IsPairProduct d n (zeroRegisterReflectionGateCount d a * (2 * n))
      (embedOp e (zeroRegisterReflection (d := d) ha)) :=
  (isPairProduct_zeroRegisterReflection hd ha).embedOp_injective (by omega) he

/-- On arbitrary logical configurations of a larger chain, the placed
reflection changes only the phase of the selected zero-test register and
returns its selected scratch sites to zero. All other data sites remain
unrestricted. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem embedOp_zeroRegisterReflection_apply_clean {n : ℕ}
    (hd : 2 ≤ d) (ha : 0 < a) (e : Fin (a + a) → Fin n)
    (x z : (Fin n → Fin d)) (hx : ∀ j, x (e (Fin.natAdd a j)) = 0) :
    embedOp e (zeroRegisterReflection (d := d) ha) z x =
      (if ∀ j, x (e (Fin.castAdd a j)) = 0 then (-1 : ℂ) else 1) *
        (if z = x then 1 else 0) := by
  classical
  let y : (Fin a → Fin d) := fun j ↦ x (e (Fin.castAdd a j))
  have hrestrict : x ∘ e = Fin.append y 0 := by
    funext p
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) p
    · simp only [Function.comp_apply, Fin.append_left, y]
    · simp only [Function.comp_apply, Fin.append_right, Pi.zero_apply]
      exact hx j
  rw [embedOp_apply, hrestrict, zeroRegisterReflection_apply_clean hd ha]
  change (if AgreeOff e z x then
    (if ∀ j, y j = 0 then (-1 : ℂ) else 1) *
      (if z ∘ e = Fin.append y 0 then 1 else 0) else 0) = _
  by_cases hz : z = x
  · subst z
    simp [agreeOff_refl, hrestrict, y]
  · by_cases hag : AgreeOff e z x
    · have hne : z ∘ e ≠ Fin.append y 0 := by
        intro h
        apply hz
        funext p
        by_cases hp : ∃ j, e j = p
        · obtain ⟨j, rfl⟩ := hp
          exact congrFun (h.trans hrestrict.symm) j
        · exact hag p (fun j hj ↦ hp ⟨j, hj⟩)
      simp [hag, hne, hz]
    · simp [hag, hz]

omit [NeZero d] in
/-- Testing an empty initialized register gives the global phase minus one.
On a chain containing a neighboring pair this is one exact two-site gate,
including its global phase. This covers the empty-register case in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_neg_one {n : ℕ} (hn : 2 ≤ n) :
    IsPairProduct d n 1 (-1 : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ) := by
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨1, by omega⟩
  apply IsPairProduct.of_isNeighbourGate
  refine ⟨?_, p, q, rfl, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    simp
  · exact (supportedOperators d {p, q}).neg_mem (one_mem_supportedOperators _)

end QuantumCircuit
