/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CleanUnitaryImplementation
import TNLean.MPS.MPU.RegisterLayout

/-!
# Clean circuits for one-site interval isometries

The two bond labels of a one-site interval are encoded separately in the
same registers used by the neighboring intervals. An isometric interval
map extends to a full unitary on this logical packet. A single initialized
workspace qudit then gives an actual neighboring-pair circuit implementing
that full unitary on every logical input. In particular, its inverse returns
the workspace to zero on every logical state.

The two bond registers may have different widths, including width zero at
an endpoint cut. If both widths are at most `q = ceil(log_d D)`, the
packet with workspace has at most `2q + 2` sites and dimension at most
`d^4 D^2`, so its gate
cost is polynomial in `D` at fixed local dimension. The full-space extension
is essential for the inverse calls in the recursive construction.

Source: the leaf construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

variable {d qρ qσ : ℕ} {ρ σ : Type*}

/-- Encode the physical output and the two bond labels in separate registers.
Source: the leaf register convention in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def leafOutputEmbedding (eρ : ρ ↪ Cfg d qρ) (eσ : σ ↪ Cfg d qσ) :
    (Fin d × (ρ × σ)) ↪ Cfg d (1 + (qρ + qσ)) where
  toFun x := Fin.append (fun _ : Fin 1 ↦ x.1) (Fin.append (eρ x.2.1) (eσ x.2.2))
  inj' x y h := by
    apply Prod.ext
    · have hi := congrFun h (Fin.castAdd (qρ + qσ) (0 : Fin 1))
      simpa only [Fin.append_left] using hi
    · apply Prod.ext
      · apply eρ.injective
        funext i
        have hi := congrFun h (Fin.natAdd 1 (Fin.castAdd qσ i))
        simpa only [Fin.append_right, Fin.append_left] using hi
      · apply eσ.injective
        funext i
        have hi := congrFun h (Fin.natAdd 1 (Fin.natAdd qρ i))
        simpa only [Fin.append_right] using hi

variable [NeZero d]

/-- The physical input with both bond registers initialized to zero.
Source: the leaf inputs in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def leafInputEmbedding : Fin d ↪ Cfg d (1 + (qρ + qσ)) where
  toFun x := Fin.append (fun _ : Fin 1 ↦ x) 0
  inj' x y h := by
    have hi := congrFun h (Fin.castAdd (qρ + qσ) (0 : Fin 1))
    simpa only [Fin.append_left] using hi

/-- An isometric one-site interval extends to a full logical unitary in the
given product encoding. No unitary extension is supplied as a hypothesis.
Source: the leaf step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_leaf_logical_unitary [Fintype ρ] [Fintype σ]
    (eρ : ρ ↪ Cfg d qρ) (eσ : σ ↪ Cfg d qσ)
    {V : Matrix (Fin d × (ρ × σ)) (Fin d) ℂ} (hV : V.IsIsometry) :
    ∃ Z : Matrix (Cfg d (1 + (qρ + qσ))) (Cfg d (1 + (qρ + qσ))) ℂ,
      Z ∈ unitary (Matrix (Cfg d (1 + (qρ + qσ))) (Cfg d (1 + (qρ + qσ))) ℂ) ∧
      Z * initializedBasisMatrix (leafInputEmbedding (d := d) (qρ := qρ) (qσ := qσ)) =
        initializedBasisMatrix (leafOutputEmbedding eρ eσ) * V := by
  classical
  have hencoded := (initializedBasisMatrix_isIsometry (leafOutputEmbedding eρ eσ)).mul
    _ _ hV
  obtain ⟨Z, hZ, hcolumns⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq
    hencoded (leafInputEmbedding (d := d) (qρ := qρ) (qσ := qσ))
  refine ⟨Z, hZ, ?_⟩
  rw [mul_initializedBasisMatrix]
  ext x y
  exact hcolumns x y

/-- An encoded one-site interval has an actual neighboring-pair circuit with
one reusable workspace qudit. The logical unitary and the circuit are both
derived. Cleanup holds on the entire logical packet, so adjoint calls are
also clean. Source: the leaf construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_exact_clean_leaf_circuit [Fintype ρ] [Fintype σ]
    (hd : 2 ≤ d) (eρ : ρ ↪ Cfg d qρ) (eσ : σ ↪ Cfg d qσ)
    {V : Matrix (Fin d × (ρ × σ)) (Fin d) ℂ} (hV : V.IsIsometry) :
    ∃ Z : Matrix (Cfg d (1 + (qρ + qσ))) (Cfg d (1 + (qρ + qσ))) ℂ,
    ∃ U : Matrix (Cfg d ((1 + (qρ + qσ)) + 1))
        (Cfg d ((1 + (qρ + qσ)) + 1)) ℂ,
      Z ∈ unitary (Matrix (Cfg d (1 + (qρ + qσ))) (Cfg d (1 + (qρ + qσ))) ℂ) ∧
      Z * initializedBasisMatrix (leafInputEmbedding (d := d) (qρ := qρ) (qσ := qσ)) =
        initializedBasisMatrix (leafOutputEmbedding eρ eσ) * V ∧
      IsPairProduct d ((1 + (qρ + qσ)) + 1)
        (38 * (d ^ ((1 + (qρ + qσ)) + 1)) ^ 6) U ∧
      IsCleanImplementation
        (initializedBasisMatrix
          (zeroWorkspaceEmbedding (d := d) (n := 1 + (qρ + qσ)) (a := 1))) U Z := by
  obtain ⟨Z, hZ, hcolumns⟩ := exists_leaf_logical_unitary eρ eσ hV
  obtain ⟨U, hU, hclean⟩ := exists_isPairProduct_isCleanImplementation hd (by omega)
    (zeroWorkspaceEmbedding (d := d) (n := 1 + (qρ + qσ)) (a := 1)) hZ
  exact ⟨Z, U, hZ, hcolumns, hU, hclean⟩

omit [NeZero d] in
/-- The Hilbert-space dimension of the leaf packet with its reusable
workspace is polynomial in the common bond bound. Source: the leaf gate
estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem leaf_workspace_dimension_le {D : ℕ} (hd : 2 ≤ d) (hD : 0 < D) :
    d ^ ((1 + (bondRegisterWidth d D + bondRegisterWidth d D)) + 1) ≤
      d ^ 4 * D ^ 2 := by
  have hq := registerCapacity_le_mul_bondDim hd hD
  have hexp : (1 + (bondRegisterWidth d D + bondRegisterWidth d D)) + 1 =
      2 + (bondRegisterWidth d D + bondRegisterWidth d D) := by omega
  rw [hexp, pow_add, pow_add]
  calc
    _ ≤ d ^ 2 * ((d * D) * (d * D)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hq hq)
    _ = _ := by ring

omit [NeZero d] in
/-- The leaf circuit costs at most `38 * (d^4 D^2)^6` neighboring-pair gates.
Source: the leaf gate estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem leaf_workspace_gateCount_le {D : ℕ} (hd : 2 ≤ d) (hD : 0 < D) :
    38 * (d ^ ((1 + (bondRegisterWidth d D + bondRegisterWidth d D)) + 1)) ^ 6 ≤
      38 * (d ^ 4 * D ^ 2) ^ 6 :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (leaf_workspace_dimension_le hd hD) 6)

omit [NeZero d] in
/-- Endpoint bonds may use zero qudits. Any two widths at most the common
bond width obey the same packet dimension bound. Source: endpoint leaves
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem leaf_workspace_dimension_le_of_width_le {D : ℕ} (hd : 2 ≤ d)
    (hD : 0 < D) (hρ : qρ ≤ bondRegisterWidth d D)
    (hσ : qσ ≤ bondRegisterWidth d D) :
    d ^ ((1 + (qρ + qσ)) + 1) ≤ d ^ 4 * D ^ 2 := by
  exact (Nat.pow_le_pow_right (by omega : 0 < d) (by omega)).trans
    (leaf_workspace_dimension_le hd hD)

end MPUCircuit
