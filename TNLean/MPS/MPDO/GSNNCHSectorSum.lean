/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.PosSemidefCommute
import TNLean.MPS.MPDO.InverseMapActiveSectorRecurrence

/-!
# Positivity and translation invariance of the GSNNCH sector sum

For the sector data of Definition 4.8 of arXiv:1606.00608 (`GSNNCHData`),
this file proves the properties the source asserts of the represented
finite-chain operator $\bigoplus_x n_x \prod_j \tau_j(B^{(x)})$ of equation
`rhoNCommv2`:

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
1569--1594) together with the density normalization of Definition 4.8. For an
injective tensor the basis of normal tensors has a single element, so the
one-sector form is the full source conclusion in this case.

This completes the first step of the elimination plan in
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. Constructing the
outer sectors and natural multiplicities of a general simple tensor from its
basis of normal tensors remains open; see the same note.

## Main declarations

* `MPOTensor.embedLocalOperator_submatrix_rotateConfig`
* `MPOTensor.embedLocalOperator_posSemidef`
* `MPOTensor.GSNNCHData.bondAt_comm`
* `MPOTensor.GSNNCHData.sectorProduct_posSemidef`
* `MPOTensor.GSNNCHData.unnormalizedState_posSemidef`
* `MPOTensor.GSNNCHData.unnormalizedState_submatrix_rotateConfig`
* `MPOTensor.HasGSNNCHFormAt.posSemidef`
* `MPOTensor.HasGSNNCHFormAt.submatrix_rotateConfig`
* `MPOTensor.isGSNNCH_of_hasGSNNCHForm`
* `MPOTensor.isGSNNCH_of_isInjective_of_isSAL`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.8 and Appendix C.2
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix

namespace MPOTensor

attribute [local instance] Classical.decEq Classical.propDecidable

variable {d D N : ℕ}

/-! ## Transport of embedded local operators along the cyclic shift -/

/-- The cyclic shift moves the residue offset of a site from a window base
the same way it moves the base. -/
private theorem rotate_offset_eq {N : ℕ} (k i : Fin N) :
    (((finRotate N) k).val + N - ((finRotate N) i).val) % N
      = (k.val + N - i.val) % N := by
  have hkN := k.isLt
  have hiN := i.isLt
  rw [coe_finRotate_mod, coe_finRotate_mod]
  rcases Nat.lt_or_ge (k.val + 1) N with hk1 | hk1 <;>
    rcases Nat.lt_or_ge (i.val + 1) N with hi1 | hi1
  · rw [Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt hi1]
    congr 1
    omega
  · have h2 : (i.val + 1) % N = 0 := by
      rw [show i.val + 1 = N by omega, Nat.mod_self]
    rw [Nat.mod_eq_of_lt hk1, h2,
      show k.val + 1 + N - 0 = k.val + 1 + N by omega, Nat.add_mod_right,
      show k.val + N - i.val = k.val + 1 by omega]
  · have h1 : (k.val + 1) % N = 0 := by
      rw [show k.val + 1 = N by omega, Nat.mod_self]
    rw [h1, Nat.mod_eq_of_lt hi1,
      show 0 + N - (i.val + 1) = N - i.val - 1 by omega,
      show k.val + N - i.val = N + (N - i.val - 1) by omega, Nat.add_mod_left]
  · rw [show k.val = i.val by omega,
      show (i.val + 1) % N + N - (i.val + 1) % N = N by omega,
      show i.val + N - i.val = N by omega]

/-- Extracting a cyclic window from a shifted configuration extracts the
window at the shifted base site. -/
private theorem extractWindow_comp_finRotate {N : ℕ} (L : ℕ) (i : Fin N)
    (σ : Fin N → Fin d) :
    MPSTensor.extractWindow L i (σ ∘ (finRotate N : Fin N → Fin N))
      = MPSTensor.extractWindow L (finRotate N i) σ := by
  funext j
  simp only [MPSTensor.extractWindow, Function.comp_apply]
  congr 1
  apply Fin.ext
  simp only [coe_finRotate_mod]
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

/-- Two shifted configurations agree outside the window at `i` exactly when
the original configurations agree outside the window at the shifted base. -/
private theorem agreesOutsideWindow_comp_finRotate {N : ℕ} (L : ℕ) (hLN : L ≤ N)
    (i : Fin N) (σ τ : Fin N → Fin d) :
    AgreesOutsideWindow (d := d) L hLN i
        (σ ∘ (finRotate N : Fin N → Fin N)) (τ ∘ (finRotate N : Fin N → Fin N))
      ↔ AgreesOutsideWindow (d := d) L hLN (finRotate N i) σ τ := by
  rw [agreesOutsideWindow_iff, agreesOutsideWindow_iff]
  constructor
  · intro h k hk
    have hk' : ¬ ((((finRotate N).symm k).val + N - i.val) % N < L) := by
      rw [← rotate_offset_eq ((finRotate N).symm k) i, Equiv.apply_symm_apply]
      exact hk
    have := h ((finRotate N).symm k) hk'
    rwa [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply] at this
  · intro h k hk
    have hk' : ¬ ((((finRotate N) k).val + N - ((finRotate N) i).val) % N < L) := by
      rw [rotate_offset_eq]
      exact hk
    exact h ((finRotate N) k) hk'

/-- **Transport of an embedded local operator along the cyclic shift.**
Reindexing both configurations of $\tau_i(B)$ by the cyclic shift gives the
translate at the shifted base site.

Source: arXiv:1606.00608, Definition 4.8, lines 829--842: the translates
$\tau_j(B)$ are the cyclic shifts of one two-site operator. -/
theorem embedLocalOperator_submatrix_rotateConfig (L : ℕ) {N : ℕ} (hLN : L ≤ N)
    (i : Fin N) (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    (embedLocalOperator (d := d) L N hLN i B).submatrix
        (rotateConfig N d) (rotateConfig N d)
      = embedLocalOperator (d := d) L N hLN (finRotate N i) B := by
  ext σ τ
  simp only [Matrix.submatrix_apply, rotateConfig_apply, embedLocalOperator_apply,
    extractWindow_comp_finRotate, agreesOutsideWindow_comp_finRotate]

/-- Reindexing by the cyclic shift is multiplicative on chain operators. -/
private theorem submatrix_rotateConfig_mul (A B : ChainOperator d N) :
    (A * B).submatrix (rotateConfig N d) (rotateConfig N d)
      = A.submatrix (rotateConfig N d) (rotateConfig N d)
        * B.submatrix (rotateConfig N d) (rotateConfig N d) :=
  (Matrix.submatrix_mul_equiv A B _ (rotateConfig N d) _).symm

/-! ## Positivity of embedded local operators -/

/-- An embedded positive-semidefinite local operator is positive semidefinite:
in cyclic-window coordinates it is the Kronecker product of the local operator
with the identity on the complement. -/
theorem embedLocalOperator_posSemidef (L : ℕ) {N : ℕ} (hLN : L ≤ N) (i : Fin N)
    {B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ} (hB : B.PosSemidef) :
    (embedLocalOperator (d := d) L N hLN i B).PosSemidef := by
  have h := reindex_embedLocalOperator_windowComplement (d := d) L N hLN i B
  have h2 : embedLocalOperator (d := d) L N hLN i B
      = (B ⊗ₖ (1 : Matrix (Fin (N - L) → Fin d) (Fin (N - L) → Fin d) ℂ)).submatrix
          (windowComplementEquiv (d := d) L N hLN i)
          (windowComplementEquiv (d := d) L N hLN i) := by
    rw [← h]
    ext σ τ
    simp [Matrix.reindex_apply]
  rw [h2]
  exact (hB.kronecker Matrix.PosSemidef.one).submatrix _

namespace GSNNCHData

variable {N : ℕ}

/-- Every translate of a sector bond is positive semidefinite.

Source: arXiv:1606.00608, equation `rhoNCommv2`, lines 843--850: each
$B^{(x)}$ is positive semidefinite. -/
theorem bondAt_posSemidef (data : GSNNCHData d N) (x : Fin data.sectorCount)
    (i : Fin N) : (data.bondAt x i).PosSemidef :=
  embedLocalOperator_posSemidef 2 data.hN i (data.bond_pos x)

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
          embedLocalOperator_submatrix_rotateConfig] at h
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
  · simpa [GSNNCHData.bondAt] using
      embedLocalOperator_commute_of_not_cyclicWindowsOverlap 2 N data.hN hover
        (data.bond x) (data.bond x)

/-- **Each sector product is positive semidefinite**: it is a product of
pairwise commuting positive-semidefinite translates of one sector bond.

Source: arXiv:1606.00608, Definition 4.8, lines 843--850: each summand
$\prod_j \tau_j(B^{(x)})$ with $B^{(x)} \ge 0$ and commuting translates
represents the positive operator $e^{-\sum_j \tau_j(h^{(x)})}$ of equation
`rhoNComm`. -/
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
      embedLocalOperator_submatrix_rotateConfig]
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

Source: arXiv:1606.00608, lines 838--842: the density operator of equation
`rhoNComm` is translationally invariant, where spin `N+1` is identified with
the first. -/
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
normalization. -/
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
form of Definition 4.8. For an injective tensor the basis of normal tensors
has one element, so the one-sector form is the full source conclusion.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines 1569--1594,
and Definition 4.8, lines 829--850. -/
theorem isGSNNCH_of_isInjective_of_isSAL (K : MPOTensor d D)
    (hK : K.IsInjective) (hSAL : IsSAL K) : IsGSNNCH K := by
  obtain ⟨data⟩ := nonempty_etaLocalStructureData_of_isSAL K hK hSAL
  refine isGSNNCH_of_hasGSNNCHForm data.hasGSNNCHForm fun N hN => ?_
  obtain ⟨hMpdo, htr, -⟩ := hSAL
  exact htr N (by omega)

end MPOTensor
