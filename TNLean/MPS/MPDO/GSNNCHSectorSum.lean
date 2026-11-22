/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Order.PosSemidefCommute
import TNLean.MPS.MPDO.InverseMapActiveSectorRecurrence

/-!
# Positivity and translation invariance of the GSNNCH sector sum

For the sector data of Definition 4.8 of arXiv:1606.00608 (`GSNNCHData`),
this file proves the properties the source asserts of the represented
finite-chain operator $\bigoplus_x n_x \prod_j \tau_j(B^{(x)})$
(arXiv:1606.00608, lines 843--850):

* all cyclic translates of one sector bond commute pairwise, extending the
  neighboring commutation $[B^{(x)}, \tau_1(B^{(x)})] = 0$ required by the
  definition (arXiv:1606.00608, lines 843--850);
* the represented operator is positive semidefinite, as each summand is a
  product of commuting positive bonds with a natural multiplicity;
* the represented operator is invariant under the cyclic shift; this is the
  translation invariance stated at arXiv:1606.00608, lines 838--842;
* every chain operator with the sector form is positive semidefinite, so an
  MPO tensor with the sector form at every length and nonvanishing traces
  satisfies the full density-operator predicate `IsGSNNCH`
  (arXiv:1606.00608, Definition 4.8, lines 829--850).

Consequently, an injective tensor satisfying the saturated area law generates
Gibbs states of a nearest-neighbor commuting Hamiltonian: the commuting
product form of Proposition C.8 (arXiv:1606.00608, Appendix C.2, lines
1569--1594) together with the density normalization of Definition 4.8. The
one-sector form is the commuting product form in which Proposition C.8 states
its conclusion for an injective tensor.

This completes the first step of the elimination plan in
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. Constructing the
outer sectors and natural multiplicities of a general simple tensor from its
basis of normal tensors remains open; see the same note.

## Main declarations

* `MPOTensor.placeAlong_ringWindow_submatrix_rotateConfig`
* `MPOTensor.GSNNCHData.bondAt_posSemidef`
* `MPOTensor.GSNNCHData.bondAt_comm`
* `MPOTensor.GSNNCHData.sectorProduct_posSemidef`
* `MPOTensor.GSNNCHData.unnormalizedState_posSemidef`
* `MPOTensor.GSNNCHData.sectorProduct_submatrix_rotateConfig`
* `MPOTensor.GSNNCHData.unnormalizedState_submatrix_rotateConfig`
* `MPOTensor.HasGSNNCHFormAt.posSemidef`
* `MPOTensor.HasGSNNCHFormAt.submatrix_rotateConfig`
* `MPOTensor.hasGSNNCHFormAt_normalizedMPO`
* `MPOTensor.isGSNNCH_of_hasGSNNCHForm`
* `MPOTensor.isGSNNCH_of_isInjective_of_isSAL`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.8 and Appendix C.2
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix ManyBody

namespace MPOTensor

variable {d D N : ℕ}

/-! ## Transport of placed local operators along the cyclic shift -/

/-- **Transport of a placed local operator along the cyclic shift.**
Reindexing both configurations of $\tau_i(B)$, the operator `B` placed on the window of `L`
consecutive sites starting at `i`, by the cyclic shift gives the translate at the shifted
base site.

Source: arXiv:1606.00608, Definition 4.8, lines 829--842: the translates
$\tau_j(B)$ are the cyclic shifts of one two-site operator. -/
theorem placeAlong_ringWindow_submatrix_rotateConfig (L : ℕ) {N : ℕ} (hLN : L ≤ N)
    (i : Fin N) (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    (placeAlong (X := fun _ ↦ Fin d) (ringWindow hLN i) B).submatrix
        (rotateConfig N d) (rotateConfig N d)
      = placeAlong (X := fun _ ↦ Fin d) (ringWindow hLN (finRotate N i)) B := by
  have : NeZero N := NeZero.of_pos (Fin.pos i)
  have hrot : ⇑(rotateConfig N d) = (· ∘ ⇑(finRotate N)) :=
    funext (rotateConfig_apply N d)
  rw [hrot, placeAlong_submatrix_comp, ringWindow_trans_finRotate, finRotate_apply]

/-- Reindexing by the cyclic shift is multiplicative on chain operators. -/
private theorem submatrix_rotateConfig_mul (A B : ChainOperator d N) :
    (A * B).submatrix (rotateConfig N d) (rotateConfig N d)
      = A.submatrix (rotateConfig N d) (rotateConfig N d)
        * B.submatrix (rotateConfig N d) (rotateConfig N d) :=
  (Matrix.submatrix_mul_equiv A B _ (rotateConfig N d) _).symm

namespace GSNNCHData

variable {N : ℕ}

/-- Every translate of a sector bond is positive semidefinite.

Source: arXiv:1606.00608, lines 843--850: each $B^{(x)}$ is positive
semidefinite. -/
theorem bondAt_posSemidef (data : GSNNCHData d N) (x : Fin data.sectorCount)
    (i : Fin N) : (data.bondAt x i).PosSemidef :=
  posSemidef_placeAlong _ (data.bond_pos x)

/-- **All cyclic translates of one sector bond commute pairwise.** Translates
with disjoint windows commute by locality; the neighboring commutation
required by Definition 4.8 covers the overlapping pairs after transport along
the cyclic shift.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850: the definition
requires $[B^{(x)}, \tau_1(B^{(x)})] = 0$, and the product over all
translates is unambiguous exactly because all translates commute. -/
theorem bondAt_comm (data : GSNNCHData d N) (x : Fin data.sectorCount)
    (i j : Fin N) :
    data.bondAt x i * data.bondAt x j = data.bondAt x j * data.bondAt x i := by
  have hN2 : 2 ≤ N := data.hN
  have hadj : ∀ p : ℕ,
      data.bondAt x ((finRotate N : Fin N → Fin N)^[p] ⟨0, by omega⟩) *
          data.bondAt x ((finRotate N : Fin N → Fin N)^[p] ⟨1, by omega⟩)
        = data.bondAt x ((finRotate N : Fin N → Fin N)^[p] ⟨1, by omega⟩) *
            data.bondAt x ((finRotate N : Fin N → Fin N)^[p] ⟨0, by omega⟩) := by
    intro p
    induction p with
    | zero => simpa [GSNNCHData.bondAt] using data.neighboring_comm x
    | succ p ih =>
        have h := congrArg (fun A : ChainOperator d N =>
          A.submatrix (rotateConfig N d) (rotateConfig N d)) ih
        simp only [submatrix_rotateConfig_mul, GSNNCHData.bondAt,
          placeAlong_ringWindow_submatrix_rotateConfig] at h
        simpa [GSNNCHData.bondAt, Function.iterate_succ_apply'] using h
  have hstep : ∀ k : Fin N,
      data.bondAt x k * data.bondAt x (MPSTensor.cyclicForwardSite k 1)
        = data.bondAt x (MPSTensor.cyclicForwardSite k 1) * data.bondAt x k := by
    intro k
    have h := hadj k.val
    have h0 : (finRotate N : Fin N → Fin N)^[k.val] ⟨0, by omega⟩ = k := by
      apply Fin.ext
      rw [coe_finRotate_pow]
      simpa using Nat.mod_eq_of_lt k.isLt
    have h1 : (finRotate N : Fin N → Fin N)^[k.val] ⟨1, by omega⟩
        = MPSTensor.cyclicForwardSite k 1 := by
      apply Fin.ext
      rw [coe_finRotate_pow]
      simp [MPSTensor.cyclicForwardSite, Nat.add_comm]
    rwa [h0, h1] at h
  by_cases hover : MPSTensor.cyclicWindowsOverlap N 2 i j
  · rcases MPSTensor.cyclicWindowsOverlap_twoSite_cases hover with rfl | rfl | rfl
    · rfl
    · exact hstep i
    · exact (hstep j).symm
  · exact (commute_placeAlong_of_disjoint (X := fun _ ↦ Fin d) (ringWindow data.hN i)
      (disjoint_map_ringWindow_of_not_cyclicWindowsOverlap data.hN hover)
      (data.bond x) (data.bond x)).eq

/-- **Each sector product is positive semidefinite**: it is a product of
pairwise commuting positive-semidefinite translates of one sector bond.

Source: arXiv:1606.00608, Definition 4.8, lines 843--850: each summand
$\prod_j \tau_j(B^{(x)})$ with $B^{(x)} \ge 0$ and commuting translates
represents the positive operator $e^{-\sum_j \tau_j(h^{(x)})}$ of the
defining equation at lines 829--842. -/
theorem sectorProduct_posSemidef (data : GSNNCHData d N)
    (x : Fin data.sectorCount) : (data.sectorProduct x).PosSemidef := by
  refine Matrix.posSemidef_list_prod (fun A hA => ?_) ?_
  · rw [List.mem_ofFn] at hA
    obtain ⟨i, rfl⟩ := hA
    exact data.bondAt_posSemidef x i
  · rw [List.pairwise_ofFn]
    intro a b _
    exact data.bondAt_comm x a b

/-- **The GSNNCH sector sum is positive semidefinite.**

Source: arXiv:1606.00608, Definition 4.8, lines 829--850: the represented
operator is a density operator up to normalization. -/
theorem unnormalizedState_posSemidef (data : GSNNCHData d N) :
    data.unnormalizedState.PosSemidef := by
  refine Finset.sum_induction _ Matrix.PosSemidef (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero (fun x _ => ?_)
  rw [(Complex.ofReal_natCast (data.multiplicity x)).symm]
  exact (data.sectorProduct_posSemidef x).smul
    (by exact_mod_cast Nat.cast_nonneg (data.multiplicity x))

/-- Each sector product is invariant under the cyclic shift: the shift
permutes its commuting factors cyclically.

Source: arXiv:1606.00608, lines 838--842: the represented density operator is
translationally invariant on the periodic chain. -/
theorem sectorProduct_submatrix_rotateConfig (data : GSNNCHData d N)
    (x : Fin data.sectorCount) :
    (data.sectorProduct x).submatrix (rotateConfig N d) (rotateConfig N d)
      = data.sectorProduct x := by
  have hdist : ∀ l : List (ChainOperator d N),
      l.prod.submatrix (rotateConfig N d) (rotateConfig N d)
        = (l.map fun A : ChainOperator d N =>
            A.submatrix (rotateConfig N d) (rotateConfig N d)).prod := by
    intro l
    induction l with
    | nil =>
        simp only [List.prod_nil, List.map_nil]
        exact Matrix.submatrix_one_equiv (α := ℂ) (rotateConfig N d)
    | cons A l ih =>
        simp only [List.prod_cons, List.map_cons, submatrix_rotateConfig_mul, ih]
  rw [GSNNCHData.sectorProduct, hdist, List.map_ofFn]
  have hshift : ((fun A : ChainOperator d N =>
        A.submatrix (rotateConfig N d) (rotateConfig N d))
          ∘ fun i => data.bondAt x i)
      = fun i => data.bondAt x (finRotate N i) := by
    funext i
    simp only [Function.comp_apply, GSNNCHData.bondAt,
      placeAlong_ringWindow_submatrix_rotateConfig]
  rw [hshift]
  have hperm : (List.ofFn fun i => data.bondAt x (finRotate N i)).Perm
      (List.ofFn fun i => data.bondAt x i) :=
    Equiv.Perm.ofFn_comp_perm (finRotate N) fun i => data.bondAt x i
  have hpair : (List.ofFn fun i => data.bondAt x (finRotate N i)).Pairwise
      Commute := by
    rw [List.pairwise_ofFn]
    intro a b _
    exact (commute_iff_eq _ _).mpr (data.bondAt_comm x _ _)
  exact hperm.prod_eq' hpair

/-- **Translation invariance of the GSNNCH sector sum.** Reindexing both
configurations by the cyclic shift leaves
$\bigoplus_x n_x \prod_j \tau_j(B^{(x)})$ unchanged.

Source: arXiv:1606.00608, lines 838--842: the density operator is
translationally invariant on the periodic chain, where spin $N+1$ is
identified with the first. -/
theorem unnormalizedState_submatrix_rotateConfig (data : GSNNCHData d N) :
    data.unnormalizedState.submatrix (rotateConfig N d) (rotateConfig N d)
      = data.unnormalizedState := by
  ext σ τ
  simp only [GSNNCHData.unnormalizedState, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have h := congrFun (congrFun (data.sectorProduct_submatrix_rotateConfig x) σ) τ
  simpa [Matrix.submatrix_apply] using h

end GSNNCHData

/-! ## Consequences for chain operators with the sector form -/

/-- A chain operator with the sector form of Definition 4.8 is positive
semidefinite.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
theorem HasGSNNCHFormAt.posSemidef {ρ : ChainOperator d N}
    (h : HasGSNNCHFormAt ρ) : ρ.PosSemidef := by
  obtain ⟨data, c, hc, rfl⟩ := h
  exact data.unnormalizedState_posSemidef.smul
    (by exact_mod_cast le_of_lt hc : (0 : ℂ) ≤ (c : ℂ))

/-- A chain operator with the sector form of Definition 4.8 is invariant
under the cyclic shift.

Source: arXiv:1606.00608, lines 838--842. -/
theorem HasGSNNCHFormAt.submatrix_rotateConfig {ρ : ChainOperator d N}
    (h : HasGSNNCHFormAt ρ) :
    ρ.submatrix (rotateConfig N d) (rotateConfig N d) = ρ := by
  obtain ⟨data, c, hc, rfl⟩ := h
  ext σ τ
  simp only [Matrix.submatrix_apply, Matrix.smul_apply]
  congr 1
  have h := congrFun (congrFun data.unnormalizedState_submatrix_rotateConfig σ) τ
  simpa [Matrix.submatrix_apply] using h

/-- The sector form passes from the chain operator to its trace
normalization.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
theorem hasGSNNCHFormAt_normalizedMPO {M : MPOTensor d D} {N : ℕ}
    (h : HasGSNNCHFormAt (mpo M N)) (htr : (mpo M N).trace ≠ 0) :
    HasGSNNCHFormAt (normalizedMPO M N) := by
  have hpsd : (mpo M N).PosSemidef := h.posSemidef
  have htr_nonneg : (0 : ℂ) ≤ (mpo M N).trace := hpsd.trace_nonneg
  have hre : 0 ≤ (mpo M N).trace.re := (RCLike.nonneg_iff.mp htr_nonneg).1
  have him : (mpo M N).trace.im = 0 := (RCLike.nonneg_iff.mp htr_nonneg).2
  set r : ℝ := (mpo M N).trace.re with hr
  have htr_eq : (mpo M N).trace = (r : ℂ) := Complex.ext rfl (by simp [him, hr])
  have hr_pos : 0 < r := by
    rcases lt_or_eq_of_le hre with h' | h'
    · exact h'
    · exact absurd (by rw [htr_eq, ← h']; simp) htr
  obtain ⟨data, c, hc, heq⟩ := h
  refine ⟨data, r⁻¹ * c, by positivity, ?_⟩
  rw [normalizedMPO, htr_eq, heq, smul_smul]
  congr 1
  push_cast
  ring

/-- **An MPO tensor with the sector form and nonvanishing traces is GSNNCH.**
Positivity of the normalized chain operators is derived from the sector form
itself, so only the nonvanishing of the traces is assumed.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
theorem isGSNNCH_of_hasGSNNCHForm {M : MPOTensor d D}
    (hForm : HasGSNNCHForm M)
    (htr : ∀ N : ℕ, 2 ≤ N → (mpo M N).trace ≠ 0) : IsGSNNCH M := by
  intro N hN
  have hform := hForm N hN
  exact ⟨normalizedMPO_posSemidef M N hform.posSemidef,
    normalizedMPO_trace M N (htr N hN),
    hasGSNNCHFormAt_normalizedMPO hform (htr N hN)⟩

/-- **An injective tensor with the saturated area law generates Gibbs states
of a nearest-neighbor commuting Hamiltonian.** The commuting product form is
Proposition C.8; positivity and normalization then give the density-operator
form of Definition 4.8, realized through one sector. The one-sector form is
the commuting product form in which Proposition C.8 states its conclusion for
an injective tensor.

**Local fix (inactive sectors):** the local structure data is constructed
through the inactive-sector repair; see
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (source label 3to4),
lines 1569--1594, and Definition 4.8, lines 829--850. -/
theorem isGSNNCH_of_isInjective_of_isSAL (K : MPOTensor d D)
    (hK : K.IsInjective) (hSAL : IsSAL K) : IsGSNNCH K := by
  obtain ⟨data⟩ := nonempty_etaLocalStructureData_of_isSAL K hK hSAL
  refine isGSNNCH_of_hasGSNNCHForm data.hasGSNNCHForm fun N hN => ?_
  obtain ⟨hMpdo, htr, -⟩ := hSAL
  exact htr N (by omega)

end MPOTensor
