/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.NormalizedBondDilation
import TNLean.MPS.MPU.BondRegisterBounds
import TNLean.Circuit.CleanUnitaryImplementation

/-!
# Exact neighboring-pair circuit for the normalized bond dilation

For a bond of dimension `r`, the normalized joining-bond dilation is a full
unitary on a space of dimension `2 * r²`. It embeds in a packet of
`max 2 (Nat.clog d (2 * r²) + 1)` qudits, whose Hilbert dimension is at most
`2 * d³ * r²`. Exact neighboring-pair synthesis therefore gives a circuit with
at most `38 * (2 * d³ * r²)⁶` gates.

Both the circuit and its basis inclusion are derived. The designated
first-flag reset state is encoded by the all-zero physical configuration.
Writing `J` for the inclusion and `D` for the normalized bond dilation, the
clean implementation identity is `U * J = J * D` on the entire logical space.
Thus this is an exact matrix implementation, with the global phase retained;
no unitary, dilation, or circuit witness is assumed.

Source: the leaf and merging packet argument in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. This module proves the
local packet result, rather than the complete recursive circuit bound.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The register size used for a normalized joining-bond dilation. -/
def bondDilationPacketSites (d r : ℕ) : ℕ :=
  max 2 (Nat.clog d (2 * r ^ 2) + 1)

/-- The packet Hilbert space has dimension polynomial in the bond dimension.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem bondDilationPacket_dimension_le {d r : ℕ} (hd : 2 ≤ d) (hr : 0 < r) :
    d ^ bondDilationPacketSites d r ≤ 2 * d ^ 3 * r ^ 2 := by
  simpa only [bondDilationPacketSites, Nat.clog_one_right, add_zero, mul_one, one_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    leaf_packet_dimension_le hd (Nat.mul_pos (by decide : 0 < 2) (pow_pos hr 2))
      (by decide : 0 < 1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- The entire flag-and-bond basis embeds in the packet, with a prescribed
first-flag bond basis state encoded by the zero physical configuration. -/
theorem exists_bondDilationPacket_embedding_zero {d : ℕ} (hd : 2 ≤ d) (z : ι × ι) :
    ∃ e : ((ι × ι) ⊕ (ι × ι)) ↪ Cfg d (bondDilationPacketSites d (Fintype.card ι)),
      e (Sum.inl z) = fun _ ↦ ⟨0, by omega⟩ := by
  classical
  have hcard : Fintype.card ((ι × ι) ⊕ (ι × ι)) = 2 * Fintype.card ι ^ 2 := by
    simp [Fintype.card_sum, Fintype.card_prod, pow_two, two_mul]
  have hpow : 2 * Fintype.card ι ^ 2 ≤
      d ^ bondDilationPacketSites d (Fintype.card ι) := by
    apply (Nat.le_pow_clog (by omega : 1 < d) (2 * Fintype.card ι ^ 2)).trans
    apply Nat.pow_le_pow_right (by omega : 0 < d)
    exact le_trans (Nat.le_succ _) (Nat.le_max_right _ _)
  have he : Nonempty (((ι × ι) ⊕ (ι × ι)) ↪
      Cfg d (bondDilationPacketSites d (Fintype.card ι))) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [hcard, Fintype.card_fun, Fintype.card_fin] using hpow)
  obtain ⟨e⟩ := he
  refine ⟨e.trans (Equiv.swap (e (Sum.inl z)) (fun _ ↦ ⟨0, by omega⟩)).toEmbedding, ?_⟩
  exact Equiv.swap_apply_left _ _

/-- A positive balanced bond metric determines an exact neighboring-pair
circuit for its normalized bond dilation. The designated first-flag reset state
is encoded as the zero physical configuration, and the circuit implements the
full logical unitary on every initialized basis column.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_normalizedBondDilation_circuit {d : ℕ} (hd : 2 ≤ d)
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι) :
    ∃ e : ((ι × ι) ⊕ (ι × ι)) ↪ Cfg d (bondDilationPacketSites d (Fintype.card ι)),
      ∃ U : Matrix
        (Cfg d (bondDilationPacketSites d (Fintype.card ι)))
        (Cfg d (bondDilationPacketSites d (Fintype.card ι))) ℂ,
      e (Sum.inl z) = (fun _ ↦ ⟨0, by omega⟩) ∧
      IsPairProduct d (bondDilationPacketSites d (Fintype.card ι))
        (38 * (2 * d ^ 3 * Fintype.card ι ^ 2) ^ 6) U ∧
      IsCleanImplementation (initializedBasisMatrix e) U (normalizedBondDilation P z) := by
  obtain ⟨e, he⟩ := exists_bondDilationPacket_embedding_zero hd z
  obtain ⟨U, hU, hclean⟩ := exists_isPairProduct_isCleanImplementation hd
    (le_max_left _ _) e (normalizedBondDilation_mem_unitaryGroup hP z)
  refine ⟨e, U, he, hU.mono ?_, hclean⟩
  exact Nat.mul_le_mul_left 38
    (Nat.pow_le_pow_left (bondDilationPacket_dimension_le hd Fintype.card_pos) 6)

end MPUCircuit
