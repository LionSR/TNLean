/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalReduction.TPGauge
import TNLean.MPS.MPDO.CPSVSharpBlocking
import TNLean.MPS.ParentHamiltonian.BNTBlockDiagonalBoundaryClosing
import TNLean.MPS.ParentHamiltonian.BlockDiagonalOneSiteSpan
import TNLean.MPS.ParentHamiltonian.CoisometricReconstruction
import TNLean.MPS.SharedInfra.CoisometryGauge

/-!
# Original-lattice parent-Hamiltonian range for CPSV canonical form

For a tensor in the literal canonical form of
Cirac--Pérez-García--Schuch--Verstraete over a nontrivial physical alphabet,
there is an original-lattice parent Hamiltonian of interaction range at most
\(3D^5\).  Its local interaction is nonzero, and on every longer periodic
chain its kernel is spanned by the matrix product vectors of a basis of normal
tensors.

The proof uses the construction of Pérez-García--Verstraete--Wolf--Cirac,
Theorem 12.  Its printed global-cut argument proves the kernel identity at a
range \(R\) when \(N\geq R+L_0\).  We absorb this finite-size window into the
preliminary interaction range by taking
\[
  L_{\mathrm{aux}}=3(g-1)(D^4+1)+D^4.
\]
For \(N>L_{\mathrm{aux}}\), the theorem applies at
\(R=3(g-1)(D^4+1)+1\), and antitonicity of the cyclic chain space transports
the upper inclusion from range \(R\) to range \(L_{\mathrm{aux}}\).  The usual
frustration-free inclusion supplies the reverse containment.  Enlarging once
more to the uniform range \(L=3D^5\) preserves the equality and gives
\(D^2<d^L\).  For one BNT representative, the proof uses the normal-tensor
intersection and closure property reviewed in arXiv:2011.12127, Section IV.C.
The case of no BNT representatives is a formal boundary extension of these
source arguments.

The predicate `HasParentHamiltonianGroundSpaceSpanning` records only the
ground-space spanning clause of arXiv:1606.00608, Definition 3.9, lines
522--524.  The theorem separately proves the preceding condition
\(d^L>D^2\), which makes the local orthogonal complement nontrivial, under the
necessary physical-spin boundary \(1<d\).

**Local fix (physical-dimension boundary):** The parent-Hamiltonian claim in
arXiv:1606.00608, line 527, leaves implicit the feasibility condition already
imposed at line 515.  When \(D>0\), the inequality \(D^2<d^L\) is possible for
some positive \(L\) exactly when \(1<d\).  The main theorem states this
boundary explicitly and proves the inequality for its witness.  See
`docs/paper-gaps/cpsv16_parent_hamiltonian_range_short_ring.tex`.

## Main result

* `MPSTensor.IsCPSVCanonicalForm.exists_bnt_hasParentHamiltonianGroundSpaceSpanning`

## References

* arXiv:1606.00608, Definition 3.9 and line 527, source lines 511--527.
* arXiv:quant-ph/0608197, Theorem 12, proof lines 1424--1456.
* arXiv:2011.12127, Section IV.C, source lines 2078--2090.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A spectral-radius-one normal tensor admits the source-unital PGVWC07
orientation, together with a positive-definite fixed point of the dual
transfer map, without scalar rescaling.

This is the Perron normalization used in arXiv:quant-ph/0608197, canonical
normalization lines 742--763 and 816--832, specialized to a normal tensor in
the sense of arXiv:1606.00608, lines 231--235. -/
private theorem IsNormalTensor.exists_pgvwc07_unital_dualFixedPoint_gauge
    {A : MPSTensor d D} (hA : IsNormalTensor A) :
    ∃ (B : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ),
      GaugeEquiv A B ∧
      Λ.PosDef ∧
      (∑ i : Fin d, B i * (B i)ᴴ = 1) ∧
      Kraus.transferMap (d := d) (D := D) (fun i => (B i)ᴴ) Λ = Λ := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  have hIrr : Kraus.IsIrreducibleFamily A := hA.no_invariant_proj
  obtain ⟨ρ, r, hρ, hr, hρeig⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible
      A hIrr hA.exists_apply_ne_zero
  have hIrrMap : IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) A) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr
  have hradius :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (d := d) (D := D) A))).toReal = r :=
    spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp
      (Kraus.transferMap (d := d) (D := D) A) (Kraus.transferMap_isCPMap A)
      hIrrMap ρ r hρ hr hρeig
  have hradius_one :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (d := d) (D := D) A))).toReal = 1 := by
    rw [hA.spectral_radius_one]
    simp
  have hr_one : r = 1 := hradius.symm.trans hradius_one
  have hρfix : Kraus.transferMap (d := d) (D := D) A ρ = ρ := by
    simpa [hr_one] using hρeig
  let C : MPSTensor d D := Kraus.unitalGauge A ρ
  have hCUnital : ∑ i : Fin d, C i * (C i)ᴴ = 1 := by
    simpa [C, Kraus.IsUnital] using
      Kraus.unitalGauge_isUnital_of_map_fixedPoint A ρ hρ hρfix
  have hGaugeAC : GaugeEquiv A C := by
    simpa [C] using gaugeEquiv_unitalGauge A ρ hρ
  have hCNormal : IsNormalTensor C :=
    hA.of_gaugeEquiv hGaugeAC.symm
  obtain ⟨U, Λ, _hSame, hΛ, _hΛdiag, hBUnital, hDualFixed⟩ :=
    exists_unitary_diag_posDef_adjointFixedPoint_of_unital_of_isIrreducibleTensor
      C hCUnital hCNormal.no_invariant_proj (NeZero.pos D)
  let B : MPSTensor d D := fun i =>
    (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * C i *
      (↑U : Matrix (Fin D) (Fin D) ℂ)
  have hGaugeCB : GaugeEquiv C B := by
    refine ⟨(unitaryGL U)⁻¹, fun i => ?_⟩
    simp [B]
  exact ⟨B, Λ, hGaugeAC.trans hGaugeCB, hΛ, hBUnital, hDualFixed⟩

/-- Blockwise pure gauges preserve a CPSV basis of normal tensors. -/
private theorem IsCPSVBasisOfNormalTensors.of_family_gaugeEquiv
    {g : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B C : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩))
    (hGauge : ∀ j, GaugeEquiv (B j) (C j)) :
    IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, C j⟩) := by
  refine ⟨fun j => (hBNT.blocks_normal j).of_gaugeEquiv (hGauge j).symm, ?_, ?_⟩
  · intro N hN
    obtain ⟨c, hc⟩ := hBNT.spans_mpv N hN
    refine ⟨c, fun σ => (hc σ).trans ?_⟩
    apply Finset.sum_congr rfl
    intro j _
    rw [(hGauge j).sameMPV N σ]
  · obtain ⟨N₀, hLI⟩ := hBNT.eventually_li
    refine ⟨N₀, fun N hN => ?_⟩
    have hEq :
        (fun j : Fin g => mpvState (d := d) (B j) N) =
          fun j : Fin g => mpvState (d := d) (C j) N := by
      funext j
      ext σ
      exact (hGauge j).sameMPV N σ
    rw [← hEq]
    exact hLI N hN

/-- Nonzero scalar multiplication does not change a positive-length local MPS
space. -/
private theorem groundSpace_smul_eq_of_ne_zero
    {s n : ℕ} (A : MPSTensor s n) (ζ : ℂ) (hζ : ζ ≠ 0) (L : ℕ) :
    groundSpace (ζ • A) L = groundSpace A L := by
  have hMap (X : Matrix (Fin n) (Fin n) ℂ) :
      groundSpaceMap (ζ • A) L X = groundSpaceMap A L ((ζ ^ L) • X) := by
    ext σ
    rw [groundSpaceMap_apply, groundSpaceMap_apply]
    change Matrix.trace
        (Kraus.evalWord (fun i => ζ • A i) (List.ofFn σ) * X) = _
    rw [Kraus.evalWord_smul]
    simp [Matrix.trace_smul]
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    exact ⟨(ζ ^ L) • X, (hMap X).symm⟩
  · rintro _ ⟨Y, rfl⟩
    refine ⟨(ζ ^ L)⁻¹ • Y, ?_⟩
    rw [hMap]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero L hζ), one_smul]

/-- Changing only the presentation of the bond dimension does not change the
local MPS space. -/
private theorem groundSpace_cast_bond_dim
    {s D₁ D₂ : ℕ} (h : D₁ = D₂) (A : MPSTensor s D₁) (L : ℕ) :
    groundSpace (cast (congr_arg (MPSTensor s) h) A) L = groundSpace A L := by
  subst D₂
  rfl

/-- Enlarging the interaction range preserves the ground-space spanning
equation for a block-diagonal tensor with nonzero weights.

This is a derived monotonicity consequence of the parent-Hamiltonian
construction in arXiv:1606.00608, Definition 3.9, lines 511--525; it is not a
separate assertion of the paper. -/
private theorem hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_le
    {s r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (C : (j : Fin r) → MPSTensor s (dim j))
    (hμ : ∀ j, μ j ≠ 0) {L L' : ℕ}
    (hSpan : HasParentHamiltonianGroundSpaceSpanning
      (toTensorFromBlocks (d := s) μ C) L C)
    (hLL' : L ≤ L') :
    HasParentHamiltonianGroundSpaceSpanning
      (toTensorFromBlocks (d := s) μ C) L' C := by
  rw [hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_iff_ker_le_bntMPSVectorSpan
    μ C hμ] at hSpan ⊢
  intro N hN ψ hψ
  have hNpos : 0 < N := by omega
  have hL'N : L' ≤ N := by omega
  have hLN : L ≤ N := hLL'.trans hL'N
  apply hSpan N (lt_of_le_of_lt hLL' hN)
  rw [ker_parentHamiltonian_eq_chainGroundSpace
    (toTensorFromBlocks (d := s) μ C) hNpos hLN]
  rw [ker_parentHamiltonian_eq_chainGroundSpace
    (toTensorFromBlocks (d := s) μ C) hNpos hL'N] at hψ
  exact chainGroundSpace_le_chainGroundSpace_of_le
    (toTensorFromBlocks (d := s) μ C) hNpos hLL' hL'N hψ

/-- The positive-length local MPS space of literal CPSV canonical-form data is
the sum of the local spaces of its distinct normal representatives.

This is the unblocked form of equation `II_CF1` and the BNT regrouping in
equations `eq:II_ABasicTensors` and `decBSV`, arXiv:1606.00608, lines
237--301. -/
private theorem CPSVCanonicalFormData.groundSpace_eq_iSup_representatives
    {s d : ℕ} {A : MPSTensor s d} (data : CPSVCanonicalFormData A)
    (ref : data.BNTRefinement) {L : ℕ} (hL : 0 < L) :
    groundSpace A L =
      ⨆ j : Fin data.phaseClasses.g,
        groundSpace (data.blocks (data.representativeIndex j)) L := by
  classical
  have hCopy (k : Fin data.r) :
      groundSpace (data.blocks k) L =
        groundSpace (data.blocks (data.representativeIndex (data.classCopy k).1)) L := by
    have hGauge : GaugeEquiv (ref.regroupedBlocks k) (data.blocks k) :=
      ⟨ref.listedGauge k, ref.blocksEqListedGaugeConj k⟩
    have hPhaseNe : ref.copyPhase k ≠ 0 := by
      intro hk
      simpa [hk] using ref.copyPhaseNorm k
    calc
      groundSpace (data.blocks k) L = groundSpace (ref.regroupedBlocks k) L :=
        (hGauge.groundSpace_eq L).symm
      _ = groundSpace
          (ref.copyPhase k •
            cast (congr_arg (MPSTensor s) (ref.copyDimEq k))
              (data.blocks (data.representativeIndex (data.classCopy k).1))) L := by
        rw [ref.regroupedBlocksEq]
      _ = groundSpace
          (cast (congr_arg (MPSTensor s) (ref.copyDimEq k))
            (data.blocks (data.representativeIndex (data.classCopy k).1))) L :=
        groundSpace_smul_eq_of_ne_zero _ _ hPhaseNe L
      _ = groundSpace
          (data.blocks (data.representativeIndex (data.classCopy k).1)) L :=
        groundSpace_cast_bond_dim (ref.copyDimEq k) _ L
  have hCopies :
      (⨆ k : Fin data.r, groundSpace (data.blocks k) L) =
        ⨆ j : Fin data.phaseClasses.g,
          groundSpace (data.blocks (data.representativeIndex j)) L := by
    apply le_antisymm
    · refine iSup_le fun k => ?_
      rw [hCopy k]
      exact le_iSup (fun j : Fin data.phaseClasses.g =>
        groundSpace (data.blocks (data.representativeIndex j)) L) (data.classCopy k).1
    · refine iSup_le fun j => ?_
      let q : Fin (data.phaseClasses.copies j) :=
        ⟨0, data.phaseClasses.copies_pos j⟩
      let k : Fin data.r := data.classCopyEquiv ⟨j, q⟩
      have hkClass : (data.classCopy k).1 = j := by
        simpa [k] using congrArg Sigma.fst (data.classCopy_classCopyEquiv j q)
      have hkRep : k = data.representativeIndex j :=
        mpvPhaseClassData_enum_zero_eq_repr data.blocks j
      rw [← hkRep, hCopy k, hkClass]
      exact le_iSup (fun k : Fin data.r => groundSpace (data.blocks k) L) k
  calc
    groundSpace A L =
        groundSpace (toTensorFromBlocks (d := s) data.weights data.blocks) L :=
      groundSpace_eq_of_coisometry_reconstruction data.ambient_coisometry
        data.coisometric data.reconstruct hL
    _ = ⨆ k : Fin data.r, groundSpace (data.blocks k) L :=
      groundSpace_toTensorFromBlocks_eq_iSup
        data.weights data.blocks data.weights_ne_zero L
    _ = _ := hCopies

/-- The local space of literal CPSV canonical-form data agrees with that of
the direct sum of any pure gauges of its distinct representatives. -/
private theorem CPSVCanonicalFormData.groundSpace_eq_representativeGaugeSum
    {s d : ℕ} {A : MPSTensor s d} (data : CPSVCanonicalFormData A)
    (ref : data.BNTRefinement)
    {C : (j : Fin data.phaseClasses.g) →
      MPSTensor s (data.dim (data.representativeIndex j))}
    (hGauge : ∀ j,
      GaugeEquiv (data.blocks (data.representativeIndex j)) (C j))
    {L : ℕ} (hL : 0 < L) :
    groundSpace A L =
      groundSpace (toTensorFromBlocks (d := s) (fun _ => 1) C) L := by
  have hSup :
      (⨆ j : Fin data.phaseClasses.g,
          groundSpace (data.blocks (data.representativeIndex j)) L) =
        ⨆ j : Fin data.phaseClasses.g, groundSpace (C j) L := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      rw [(hGauge j).groundSpace_eq L]
      exact le_iSup (fun k : Fin data.phaseClasses.g => groundSpace (C k) L) j
    · refine iSup_le fun j => ?_
      rw [← (hGauge j).groundSpace_eq L]
      exact le_iSup (fun k : Fin data.phaseClasses.g =>
        groundSpace (data.blocks (data.representativeIndex k)) L) j
  calc
    groundSpace A L =
        ⨆ j : Fin data.phaseClasses.g,
          groundSpace (data.blocks (data.representativeIndex j)) L :=
      data.groundSpace_eq_iSup_representatives ref hL
    _ = ⨆ j : Fin data.phaseClasses.g, groundSpace (C j) L := hSup
    _ = groundSpace (toTensorFromBlocks (d := s) (fun _ => 1) C) L :=
      (groundSpace_toTensorFromBlocks_eq_iSup
        (fun _ => 1) C (by simp) L).symm

/-- A normal tensor of bond dimension at most \(K\) is block injective at
length \(K^4\). -/
private theorem IsNormalTensor.isNBlkInjective_cap_pow_four
    {s n K : ℕ} {A : MPSTensor s n} (hA : IsNormalTensor A)
    (hnK : n ≤ K) : Kraus.IsNBlkInjective A (K ^ 4) := by
  let : NeZero n := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, _hσ, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := hA.exists_tpGauge
  let B := Kraus.tpGauge (d := s) (D := n) A σ
  have hBNormal : Kraus.IsNormal B :=
    isNormal_of_tp_primitive_irreducible B hTP hPrim hIrr
  have hOwn : Kraus.IsNBlkInjective B (n ^ 4) :=
    isNBlkInjective_pow_four_of_isNormal_leftCanonical B hTP hBNormal
  have hAOwn : Kraus.IsNBlkInjective A (n ^ 4) :=
    isNBlkInjective_of_gaugeEquiv hOwn hGauge.symm
  exact isNBlkInjective_of_le
    (Nat.pow_pos (Nat.pos_of_ne_zero hA.bondDim_ne_zero)) hAOwn
    (Nat.pow_le_pow_left hnK 4)

/-- Numerical slack needed to absorb the PGVWC07 short-ring window into the
interaction range while retaining the CPSV16 bound. -/
private theorem three_mul_pred_mul_pow_four_add_one_add_pow_four_le_three_mul_pow_five
    {K : ℕ} (hK : 0 < K) :
    3 * ((K - 1) * (K ^ 4 + 1)) + K ^ 4 ≤ 3 * K ^ 5 := by
  have hTail : 3 * (K - 1) ≤ 2 * K ^ 4 := by
    by_cases hKone : K = 1
    · simp [hKone]
    · have hKtwo : 2 ≤ K := by omega
      have hPow : K ^ 2 ≤ K ^ 4 :=
        pow_le_pow_right' (a := K) hK (by omega)
      calc
        3 * (K - 1) ≤ 3 * K := Nat.mul_le_mul_left 3 (Nat.sub_le K 1)
        _ ≤ (2 * K) * K := Nat.mul_le_mul_right K (by omega)
        _ = 2 * K ^ 2 := by ring
        _ ≤ 2 * K ^ 4 := Nat.mul_le_mul_left 2 hPow
  calc
    3 * ((K - 1) * (K ^ 4 + 1)) + K ^ 4 =
        3 * (K - 1) * K ^ 4 + 3 * (K - 1) + K ^ 4 := by ring
    _ ≤ 3 * (K - 1) * K ^ 4 + 2 * K ^ 4 + K ^ 4 := by omega
    _ = 3 * ((K - 1) + 1) * K ^ 4 := by ring
    _ = 3 * K * K ^ 4 := by rw [Nat.sub_add_cancel (by omega)]
    _ = 3 * K ^ 5 := by ring

/-- The one-block interaction range also lies below the CPSV16 bound. -/
private theorem pow_four_add_one_le_three_mul_pow_five
    {K : ℕ} (hK : 0 < K) : K ^ 4 + 1 ≤ 3 * K ^ 5 := by
  have hPowPos : 0 < K ^ 4 := Nat.pow_pos hK
  calc
    K ^ 4 + 1 ≤ K ^ 4 + K ^ 4 := Nat.add_le_add_left (by omega) _
    _ = 2 * K ^ 4 := by ring
    _ ≤ (3 * K) * K ^ 4 := Nat.mul_le_mul_right (K ^ 4) (by omega)
    _ = 3 * K ^ 5 := by ring

/-- A nontrivial physical alphabet has enough words at the uniform CPSV16
range to leave a nonzero local orthogonal complement. -/
private theorem sq_lt_pow_three_mul_pow_five
    {s K : ℕ} (hs : 1 < s) (hK : 0 < K) :
    K ^ 2 < s ^ (3 * K ^ 5) := by
  have hBinary : K ^ 2 < 2 ^ (2 * K) := by
    have hStrict : K ^ 2 < 2 * K ^ 2 + 1 := by omega
    exact hStrict.trans_le (Nat.two_mul_sq_add_one_le_two_pow_two_mul K)
  have hBase : 2 ^ (2 * K) ≤ s ^ (2 * K) :=
    pow_le_pow_left' hs.le (2 * K)
  have hKlePow : K ≤ K ^ 5 := by
    simpa using pow_le_pow_right' (a := K) hK (by omega : 1 ≤ 5)
  have hExp : 2 * K ≤ 3 * K ^ 5 := by omega
  have hExponent : s ^ (2 * K) ≤ s ^ (3 * K ^ 5) :=
    pow_le_pow_right' (a := s) (by omega) hExp
  exact hBinary.trans_le (hBase.trans hExponent)

/-- **CPSV16 original-lattice parent-Hamiltonian range bound.**

For a tensor in literal CPSV canonical form over a nontrivial physical
alphabet, there are a basis of normal tensors and a positive interaction
range \(L\leq 3D^5\) with \(D^2<d^L\) such that, on every original periodic
chain of length \(N>L\), the parent-Hamiltonian kernel is exactly the span of
the BNT matrix product vectors.

Source: arXiv:1606.00608, Definition 3.9 and the first sentence of line 527,
source lines 511--527.  For at least two BNT representatives, the short-ring
completion uses the theorem cited there, arXiv:quant-ph/0608197, Theorem 12,
proof lines 1424--1456.  For one representative, it uses the normal-tensor
intersection and closure property reviewed in arXiv:2011.12127, Section IV.C,
source lines 2078--2090.  The no-representative case is a formal boundary
extension of these source arguments.

`HasParentHamiltonianGroundSpaceSpanning` unfolds precisely to Definition
3.9's spanning clause: the kernel/BNT-span equality for every \(N>L\).  The
separate conclusion \(D^2<d^L\) supplies the preceding construction condition
from source line 515 and therefore makes the local orthogonal-complement
projector nonzero.  The hypotheses `[NeZero D]` and `1 < d` record the
positive bond-dimension and nontrivial physical-spin boundaries; Perron-gauge
and short-ring data are derived internally. -/
theorem IsCPSVCanonicalForm.exists_bnt_hasParentHamiltonianGroundSpaceSpanning
    {A : MPSTensor d D} [NeZero D] (hd : 1 < d) (hA : IsCPSVCanonicalForm A) :
    ∃ g : ℕ, ∃ dim : Fin g → ℕ,
      ∃ B : (j : Fin g) → MPSTensor d (dim j), ∃ L : ℕ,
        IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩) ∧
        0 < L ∧ D ^ 2 < d ^ L ∧ L ≤ 3 * D ^ 5 ∧
        HasParentHamiltonianGroundSpaceSpanning A L B := by
  classical
  let data := Classical.choice hA
  let ref := data.bntRefinement
  let dim : Fin data.phaseClasses.g → ℕ := fun j =>
    data.dim (data.representativeIndex j)
  let B : (j : Fin data.phaseClasses.g) → MPSTensor d (dim j) := fun j =>
    data.blocks (data.representativeIndex j)
  have hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩) := by
    simpa [dim, B] using ref.representativesBNT
  have hDimSum : ∑ j, dim j ≤ D := by
    simpa [dim] using data.sum_representative_dim_le
  let Lmax := 3 * D ^ 5
  have hLmaxPos : 0 < Lmax := by
    dsimp [Lmax]
    exact Nat.mul_pos (by omega) (Nat.pow_pos (NeZero.pos D))
  have hLmaxDim : D ^ 2 < d ^ Lmax := by
    simpa [Lmax] using
      sq_lt_pow_three_mul_pow_five hd (NeZero.pos D)
  let : NeZero d := ⟨by omega⟩
  let : ∀ j : Fin data.phaseClasses.g, NeZero (dim j) := fun j =>
    ⟨(hBNT.blocks_dim_pos j).ne'⟩
  choose C Λ hGauge hΛ hUnital hDualFixed using fun j =>
    (hBNT.blocks_normal j).exists_pgvwc07_unital_dualFixedPoint_gauge
  have hCBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, C j⟩) :=
    hBNT.of_family_gaugeEquiv hGauge
  have hDimLe : ∀ j, dim j ≤ D := by
    intro j
    exact (Finset.single_le_sum (fun k _ => Nat.zero_le (dim k))
      (Finset.mem_univ j)).trans hDimSum
  have hCountLe : data.phaseClasses.g ≤ D := by
    calc
      data.phaseClasses.g = ∑ _j : Fin data.phaseClasses.g, 1 := by simp
      _ ≤ ∑ j : Fin data.phaseClasses.g, dim j :=
        Finset.sum_le_sum fun j _ => hBNT.blocks_dim_pos j
      _ ≤ D := hDimSum
  have hNormal : ∀ j, IsNormalTensor (C j) := hCBNT.blocks_normal
  have hIrr : HasIrreducibleBlocks (d := d) C :=
    HasIrreducibleBlocks.ofForall fun j => (hNormal j).no_invariant_proj
  have hBlocks : BlocksNotGaugePhaseEquiv (d := d) C :=
    hCBNT.blocks_not_gaugePhaseEquiv
  have hBlk : ∀ j, Kraus.IsNBlkInjective (C j) (D ^ 4) := fun j =>
    (hNormal j).isNBlkInjective_cap_pow_four (hDimLe j)
  by_cases hCountZero : data.phaseClasses.g = 0
  · have hOne : WordTupleSpanTop C 1 := by
      letI : IsEmpty (Fin data.phaseClasses.g) := by
        rw [hCountZero]
        infer_instance
      unfold WordTupleSpanTop
      apply top_unique
      intro X _
      have hX : X = 0 := by
        funext j
        exact isEmptyElim j
      rw [hX]
      exact Submodule.zero_mem _
    have hDirectSmall :
        HasParentHamiltonianGroundSpaceSpanning
          (toTensorFromBlocks (d := d) (fun _ => 1) C) 2 C :=
      hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_wordTupleSpanTop_one
        (fun _ => 1) C (by simp) hOne
    have hTwoLe : 2 ≤ Lmax := by
      dsimp [Lmax]
      have hD5 : 0 < D ^ 5 := Nat.pow_pos (NeZero.pos D)
      omega
    have hDirect :=
      hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_le
        (fun _ => 1) C (by simp) hDirectSmall hTwoLe
    have hLocal :
        groundSpace A Lmax =
          groundSpace (toTensorFromBlocks (d := d) (fun _ => 1) C) Lmax := by
      simpa [B, dim] using
        data.groundSpace_eq_representativeGaugeSum ref hGauge hLmaxPos
    exact ⟨data.phaseClasses.g, dim, C, Lmax, hCBNT, hLmaxPos, hLmaxDim,
      le_rfl, hDirect.of_groundSpace_eq hLocal⟩
  by_cases hCountOne : data.phaseClasses.g = 1
  · let L₀ := D ^ 4
    let L := L₀ + 1
    let j₀ : Fin data.phaseClasses.g := ⟨0, by omega⟩
    have hIndex (j : Fin data.phaseClasses.g) : j = j₀ := by
      apply Fin.ext
      omega
    have hGroundSup (M : ℕ) :
        (⨆ j : Fin data.phaseClasses.g, groundSpace (C j) M) =
          groundSpace (C j₀) M := by
      apply le_antisymm
      · refine iSup_le fun j => ?_
        rw [hIndex j]
      · exact le_iSup (fun j : Fin data.phaseClasses.g => groundSpace (C j) M) j₀
    have hChainSup (M : ℕ) :
        (⨆ j : Fin data.phaseClasses.g, chainGroundSpace (C j) L M) =
          chainGroundSpace (C j₀) L M := by
      apply le_antisymm
      · refine iSup_le fun j => ?_
        rw [hIndex j]
      · exact le_iSup
          (fun j : Fin data.phaseClasses.g => chainGroundSpace (C j) L M) j₀
    have hL₀ : 0 < L₀ := Nat.pow_pos (NeZero.pos D)
    have hDirectLocal :
        groundSpace (toTensorFromBlocks (d := d) (fun _ => 1) C) L =
          ⨆ j : Fin data.phaseClasses.g, groundSpace (C j) L :=
      groundSpace_toTensorFromBlocks_eq_iSup (fun _ => 1) C (by simp) L
    have hDirect :
        HasParentHamiltonianGroundSpaceSpanning
          (toTensorFromBlocks (d := d) (fun _ => 1) C) L C := by
      apply
        hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_chain_eq_iSup_chain
          (fun _ => 1) C (by simp)
      · intro N hN
        have hLocalSingle :
            groundSpace (toTensorFromBlocks (d := d) (fun _ => 1) C) L =
              groundSpace (C j₀) L :=
          hDirectLocal.trans (hGroundSup L)
        calc
          chainGroundSpace (toTensorFromBlocks (d := d) (fun _ => 1) C) L N =
              chainGroundSpace (C j₀) L N :=
            chainGroundSpace_eq_of_groundSpace_eq hLocalSingle
          _ = ⨆ j : Fin data.phaseClasses.g, chainGroundSpace (C j) L N := by
            exact (hChainSup N).symm
      · intro N hN j
        exact chainGroundSpace_eq_mpvSubmodule_normal
          (hNormal j).isNormal (hBlk j) hL₀ (by omega) (by omega) (by omega) (by omega)
    have hLBound : L ≤ Lmax := by
      simpa [L, L₀, Lmax] using
        pow_four_add_one_le_three_mul_pow_five (NeZero.pos D)
    have hDirectMax :=
      hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_le
        (fun _ => 1) C (by simp) hDirect hLBound
    have hLocal :
        groundSpace A Lmax =
          groundSpace (toTensorFromBlocks (d := d) (fun _ => 1) C) Lmax := by
      simpa [B, dim] using
        data.groundSpace_eq_representativeGaugeSum ref hGauge hLmaxPos
    exact ⟨data.phaseClasses.g, dim, C, Lmax, hCBNT, hLmaxPos, hLmaxDim,
      le_rfl, hDirectMax.of_groundSpace_eq hLocal⟩
  · have hCountTwo : 2 ≤ data.phaseClasses.g := by omega
    let L₀ := D ^ 4
    let base := (data.phaseClasses.g - 1) *
      ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))
    let R := base + 1
    let L := base + L₀
    have hL₀ : 0 < L₀ := Nat.pow_pos (NeZero.pos D)
    have hRleL : R ≤ L := by
      dsimp [R, L]
      omega
    have hDirect :
        HasParentHamiltonianGroundSpaceSpanning
          (toTensorFromBlocks (d := d) (fun _ => 1) C) L C := by
      rw [hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_iff_ker_le_bntMPSVectorSpan
        (fun _ => 1) C (by simp)]
      intro N hN
      have hNpos : 0 < N := by omega
      have hLN : L ≤ N := by omega
      have hRN : R ≤ N := hRleL.trans hLN
      have hNlarge : R + L₀ ≤ N := by
        dsimp [R, L]
        omega
      have hSmall :=
        ker_parentHamiltonian_toTensorFromBlocks_eq_bntMPSVectorSpan_pgvwc07_of_dualFixedPoint
          (fun _ => 1) C (by simp) hCountTwo hIrr hBlocks Λ hΛ hDualFixed hBlk hL₀
            hUnital (by simp [R, base]) hNlarge
      intro ψ hψ
      rw [← hSmall]
      rw [ker_parentHamiltonian_eq_chainGroundSpace
        (toTensorFromBlocks (d := d) (fun _ => 1) C) hNpos hLN] at hψ
      rw [ker_parentHamiltonian_eq_chainGroundSpace
        (toTensorFromBlocks (d := d) (fun _ => 1) C) hNpos hRN]
      exact chainGroundSpace_le_chainGroundSpace_of_le
        (toTensorFromBlocks (d := d) (fun _ => 1) C) hNpos hRleL hLN hψ
    have hPredLe : data.phaseClasses.g - 1 ≤ D - 1 :=
      Nat.sub_le_sub_right hCountLe 1
    have hBaseLe : base ≤
        (D - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) :=
      Nat.mul_le_mul_right _ hPredLe
    have hLBound : L ≤ 3 * D ^ 5 := by
      calc
        L ≤ (D - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1))) + L₀ :=
          Nat.add_le_add_right hBaseLe L₀
        _ = 3 * ((D - 1) * (D ^ 4 + 1)) + D ^ 4 := by
          simp only [L₀]
          ring
        _ ≤ 3 * D ^ 5 :=
          three_mul_pred_mul_pow_four_add_one_add_pow_four_le_three_mul_pow_five
            (NeZero.pos D)
    have hDirectMax :=
      hasParentHamiltonianGroundSpaceSpanning_toTensorFromBlocks_of_le
        (fun _ => 1) C (by simp) hDirect (by simpa [Lmax] using hLBound)
    have hLocal :
        groundSpace A Lmax =
          groundSpace (toTensorFromBlocks (d := d) (fun _ => 1) C) Lmax := by
      simpa [B, dim] using
        data.groundSpace_eq_representativeGaugeSum ref hGauge hLmaxPos
    exact ⟨data.phaseClasses.g, dim, C, Lmax, hCBNT, hLmaxPos, hLmaxDim,
      le_rfl, hDirectMax.of_groundSpace_eq hLocal⟩

end MPSTensor
