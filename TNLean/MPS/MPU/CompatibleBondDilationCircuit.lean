/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.NormalizedBondDilation
import TNLean.MPS.MPU.BondRegisterBounds
import TNLean.Circuit.CleanUnitaryImplementation
import TNLean.MPS.Preparation.BlockUnitary

/-!
# Bond dilation circuits compatible with the child register encodings

Fix an injective encoding of the bond basis in `q` physical qudits. A packet
of `2 * q + 2` sites contains the two given child bond encodings, one binary
dilation flag, and one attenuation qudit. The logical joining pair is ordered
as `(y, x)`, following matrix vectorization; its physical registers contain
the left child's `x` label first and the right child's `y` label second.
The packet encoding is injective and sends zero bonds and both zero flags
to the all-zero physical configuration.

A positive definite balanced metric determines the normalized bond dilation.
Its tensor product with the identity on the full attenuation qudit admits
an exact neighboring-pair circuit on this prescribed product encoding. The
clean implementation identity holds on every logical state, including every
level of the attenuation qudit, and retains the exact phase.

If `q = Nat.clog d D`, the packet dimension is at most `d⁴ * D²`, and the
circuit uses at most `38 * (d⁴ * D²)⁶` neighboring-pair gates. No compatible
unitary or circuit witness is assumed. Source: the shared-register encoding
and finite-dimensional merger argument in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. This is a local packet
construction, separate from the complete recursive circuit theorem.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The joining bond coordinates, independently of the dilation flag. -/
def joiningBondPair {r : ℕ} (s : (Fin r × Fin r) ⊕ (Fin r × Fin r)) : Fin r × Fin r :=
  s.elim id id

/-- The two dilation flag values in the physical qudit basis. -/
def joiningDilationFlag {d r : ℕ} (hd : 2 ≤ d)
    (s : (Fin r × Fin r) ⊕ (Fin r × Fin r)) : Fin d :=
  s.elim (fun _ ↦ Fin.castLE hd 0) (fun _ ↦ Fin.castLE hd 1)

/-- Two child bond encodings followed by the dilation and attenuation flags. -/
def compatibleBondDilationCfg {d r q : ℕ} (hd : 2 ≤ d) (e : Fin r ↪ Cfg d q)
    (p : ((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d) : Cfg d (2 * q + 2) :=
  fun k ↦ if h : k.val < 2 * q then
      twoCfg e (joiningBondPair p.1).2 (joiningBondPair p.1).1 ⟨k.val, by omega⟩
    else if k.val = 2 * q then joiningDilationFlag hd p.1 else p.2

/-- The first packet register is exactly the left child's given bond encoding. -/
theorem compatibleBondDilationCfg_left {d r q : ℕ} (hd : 2 ≤ d)
    (e : Fin r ↪ Cfg d q) (p : ((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d)
    (j : Fin q) :
    compatibleBondDilationCfg hd e p ⟨j.val, by have := j.isLt; omega⟩ =
      e (joiningBondPair p.1).2 j := by
  simp [compatibleBondDilationCfg, twoCfg, j.isLt,
    show j.val < 2 * q by have := j.isLt; omega]

/-- The second packet register is exactly the right child's given bond encoding. -/
theorem compatibleBondDilationCfg_right {d r q : ℕ} (hd : 2 ≤ d)
    (e : Fin r ↪ Cfg d q) (p : ((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d)
    (j : Fin q) :
    compatibleBondDilationCfg hd e p ⟨q + j.val, by have := j.isLt; omega⟩ =
      e (joiningBondPair p.1).1 j := by
  simp [compatibleBondDilationCfg, twoCfg,
    show q + j.val < 2 * q by have := j.isLt; omega,
    show ¬q + j.val < q by omega]

/-- The penultimate physical site carries the dilation flag. -/
theorem compatibleBondDilationCfg_dilation {d r q : ℕ} (hd : 2 ≤ d)
    (e : Fin r ↪ Cfg d q) (p : ((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d) :
    compatibleBondDilationCfg hd e p ⟨2 * q, by omega⟩ = joiningDilationFlag hd p.1 := by
  simp [compatibleBondDilationCfg]

/-- The final physical site retains the full attenuation qudit. -/
theorem compatibleBondDilationCfg_attenuation {d r q : ℕ} (hd : 2 ≤ d)
    (e : Fin r ↪ Cfg d q) (p : ((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d) :
    compatibleBondDilationCfg hd e p ⟨2 * q + 1, by omega⟩ = p.2 := by
  simp [compatibleBondDilationCfg, show ¬2 * q + 1 < 2 * q by omega]

/-- The compatible packet coordinates retain both bond labels and both flags. -/
theorem compatibleBondDilationCfg_injective {d r q : ℕ} (hd : 2 ≤ d)
    (e : Fin r ↪ Cfg d q) : Function.Injective (compatibleBondDilationCfg hd e) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  have hab : a = b := by
    have ha := congrFun h ⟨2 * q + 1, by omega⟩
    simpa only [compatibleBondDilationCfg_attenuation] using ha
  have hflag : joiningDilationFlag hd s = joiningDilationFlag hd t := by
    have hf := congrFun h ⟨2 * q, by omega⟩
    simpa only [compatibleBondDilationCfg_dilation] using hf
  have hp : joiningBondPair s = joiningBondPair t := by
    have hcfg : twoCfg e (joiningBondPair s).2 (joiningBondPair s).1 =
        twoCfg e (joiningBondPair t).2 (joiningBondPair t).1 := by
      funext j
      have hj := congrFun h ⟨j.val, by have := j.isLt; omega⟩
      simpa only [compatibleBondDilationCfg, show j.val < 2 * q by
        have := j.isLt; omega, dite_true] using hj
    obtain ⟨hl, hr⟩ := twoCfg_injective (dig := e) (hdig := e.injective) hcfg
    exact Prod.ext hr hl
  cases s <;> cases t <;> simp_all [joiningBondPair, joiningDilationFlag, Fin.ext_iff]

/-- The compatible injective placement of the full logical bond-and-flag basis. -/
def compatibleBondDilationEmbedding {d r q : ℕ} (hd : 2 ≤ d) (e : Fin r ↪ Cfg d q) :
    (((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d) ↪ Cfg d (2 * q + 2) :=
  ⟨compatibleBondDilationCfg hd e, compatibleBondDilationCfg_injective hd e⟩

/-- Zero child bonds and two zero flags are encoded by the physical zero state. -/
theorem compatibleBondDilationEmbedding_zero {d r q : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (e : Fin r ↪ Cfg d q)
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0) :
    compatibleBondDilationEmbedding hd e
      (Sum.inl (⟨0, hr⟩, ⟨0, hr⟩), Fin.castLE hd 0) = fun _ ↦ Fin.castLE hd 0 := by
  funext k
  simp [compatibleBondDilationEmbedding, compatibleBondDilationCfg, joiningBondPair,
    joiningDilationFlag, twoCfg, he]

/-- The normalized bond dilation has a clean neighboring-pair implementation
on the prescribed child product encoding, with the attenuation qudit preserved
on all its physical levels.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_compatibleNormalizedBondDilation_circuit {d r q : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (e : Fin r ↪ Cfg d q)
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef) :
    ∃ U : Matrix (Cfg d (2 * q + 2)) (Cfg d (2 * q + 2)) ℂ,
      compatibleBondDilationEmbedding hd e
        (Sum.inl (⟨0, hr⟩, ⟨0, hr⟩), Fin.castLE hd 0) = (fun _ ↦ Fin.castLE hd 0) ∧
      IsPairProduct d (2 * q + 2) (38 * (d ^ (2 * q + 2)) ^ 6) U ∧
      IsCleanImplementation (initializedBasisMatrix (compatibleBondDilationEmbedding hd e)) U
        (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hu := Matrix.kronecker_mem_unitary
    (normalizedBondDilation_mem_unitaryGroup hP (⟨0, hr⟩, ⟨0, hr⟩))
    (one_mem (unitary (Matrix (Fin d) (Fin d) ℂ)))
  obtain ⟨U, hU, hclean⟩ := exists_isPairProduct_isCleanImplementation hd
    (by omega : 2 ≤ 2 * q + 2) (compatibleBondDilationEmbedding hd e) hu
  exact ⟨U, compatibleBondDilationEmbedding_zero hd hr e he, hU, hclean⟩

/-- The compatible logarithmic packet has polynomial Hilbert dimension. -/
theorem compatibleBondDilationPacket_dimension_le {d D : ℕ}
    (hd : 2 ≤ d) (hD : 0 < D) :
    d ^ (2 * Nat.clog d D + 2) ≤ d ^ 4 * D ^ 2 := by
  rw [Nat.mul_comm 2 (Nat.clog d D), pow_add, pow_mul]
  calc
    (d ^ Nat.clog d D) ^ 2 * d ^ 2 ≤ (d * D) ^ 2 * d ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (bond_register_dimension_bounds hd hD).2 2)
    _ = d ^ 4 * D ^ 2 := by ring

/-- For a common ceiling-logarithmic register chosen from a bond bound `D`,
the compatible dilation circuit has a gate bound polynomial in `D`.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_compatibleNormalizedBondDilation_circuit_bounded {d r D : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (hrD : r ≤ D)
    (e : Fin r ↪ Cfg d (Nat.clog d D))
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef) :
    ∃ U : Matrix (Cfg d (2 * Nat.clog d D + 2)) (Cfg d (2 * Nat.clog d D + 2)) ℂ,
      compatibleBondDilationEmbedding hd e
        (Sum.inl (⟨0, hr⟩, ⟨0, hr⟩), Fin.castLE hd 0) = (fun _ ↦ Fin.castLE hd 0) ∧
      IsPairProduct d (2 * Nat.clog d D + 2) (38 * (d ^ 4 * D ^ 2) ^ 6) U ∧
      IsCleanImplementation (initializedBasisMatrix (compatibleBondDilationEmbedding hd e)) U
        (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  obtain ⟨U, hz, hU, hclean⟩ := exists_compatibleNormalizedBondDilation_circuit hd hr e he hP
  refine ⟨U, hz, hU.mono ?_, hclean⟩
  exact Nat.mul_le_mul_left 38
    (Nat.pow_le_pow_left (compatibleBondDilationPacket_dimension_le hd (by omega)) 6)

end MPUCircuit
