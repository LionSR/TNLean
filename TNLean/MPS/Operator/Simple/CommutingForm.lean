/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.DensityOperator.ZCL
import QICLean.Algebra.Hermitian.OrthogonalProjection
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonian
import TNLean.MPS.Tensor.GroundSpace.CyclicWindow
import QICLean.Algebra.Combinatorics.FinSumPermutation

/-!
# Commuting form and GSNNCH data for simple MPDOs

This file states the commuting-form side of the simple MPDO story from
arXiv:1606.00608 Section 4.4 and Appendix C.2.

A commuting bond is a positive semidefinite two-site matrix `B` whose translates
on the periodic chain pairwise commute at every chain length. The commuting form
of an MPO tensor is a commuting bond whose translate product reproduces the
operator `σ^{(N)}` up to a positive scalar at every chain length `N ≥ 2`
(Proposition C.8, equation `expression`, lines 1569--1594). The separate
`GSNNCHData` follows Definition 4.8 by recording the orthogonal one-site sectors,
their natural multiplicities, and one positive bond in every sector. At one chain
length, the single-bond presentation is exactly its one-sector case
(`MPOTensor.exists_oneSector_gsnnchData_iff`). The theorem
`MPOTensor.nonempty_commutingForm_of_isSAL` proves the entropy-side implication
from SAL; this is Proposition C.8 of arXiv:1606.00608, Appendix C.2,
lines 1569--1594.

## Main declarations

* `MPOTensor.ChainOperator`
* `MPOTensor.windowComplementEquiv`,
  `MPOTensor.reindex_placeAlong_ringWindow_windowComplement` — an operator placed on
  a window of the ring (`ManyBody.placeAlong` along `ManyBody.ringWindow`) is the
  window operator tensored with the identity on the complement
* `MPOTensor.CommutingBond`, `MPOTensor.CommutingForm`
* `MPOTensor.GSNNCHData`
* `MPOTensor.HasGSNNCHFormAt`
* `MPOTensor.HasGSNNCHForm`
* `MPOTensor.IsGSNNCHAt`
* `MPOTensor.IsGSNNCH`
* `MPOTensor.exists_oneSector_gsnnchData_iff`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Section 4.4 and Appendix C.2
-/

open scoped Matrix Kronecker BigOperators ComplexOrder
open Matrix Finset ManyBody

namespace MPOTensor

attribute [local instance] Classical.decEq Classical.propDecidable

variable {d D N : ℕ}

/-- The matrix algebra on an `N`-site chain with local dimension `d`. -/
abbrev ChainOperator (d N : ℕ) :=
  Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ

/-- Decompose a periodic configuration into a cyclic window and its cyclic
complement. -/
def windowComplementEquiv (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
    (Fin N → Fin d) ≃ ((Fin L → Fin d) × (Fin (N - L) → Fin d)) where
  toFun σ :=
    (MPSTensor.extractWindow L i σ,
      fun r ↦ σ ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩)
  invFun x := fun k ↦
    let offset := (k.val + N - i.val) % N
    if h : offset < L then x.1 ⟨offset, h⟩
    else x.2 ⟨offset - L, by
      have hoffN : offset < N := Nat.mod_lt _ (Fin.pos i)
      omega⟩
  left_inv σ := by
    funext k
    simp only
    let offset := (k.val + N - i.val) % N
    have hsite : (i.val + offset) % N = k.val :=
      MPSTensor.add_offset_mod_eq i.isLt k.isLt
    by_cases hoff : offset < L
    · rw [dite_eq_left hoff]
      exact congrArg σ (Fin.ext hsite)
    · rw [dite_eq_right hoff]
      apply congrArg σ
      apply Fin.ext
      change (i.val + L + (offset - L)) % N = k.val
      calc
        _ = (i.val + offset) % N := by congr 1; omega
        _ = k.val := hsite
  right_inv x := by
    apply Prod.ext
    · funext r
      simp only [MPSTensor.extractWindow]
      have hoff : (((i.val + r.val) % N + N - i.val) % N) = r.val :=
        MPSTensor.offset_mod_eq i.isLt (Nat.lt_of_lt_of_le r.isLt hLN)
      rw [dite_eq_left (hoff.symm ▸ r.isLt)]
      exact congrArg x.1 (Fin.ext hoff)
    · funext r
      simp only
      have hrN : L + r.val < N := by omega
      have hoff :
          (((i.val + L + r.val) % N + N - i.val) % N) = L + r.val := by
        simpa [Nat.add_assoc] using MPSTensor.offset_mod_eq i.isLt hrN
      have hnot :
          ¬ (((i.val + L + r.val) % N + N - i.val) % N) < L := by
        omega
      rw [dite_eq_right hnot]
      apply congrArg x.2
      apply Fin.ext
      change (((i.val + L + r.val) % N + N - i.val) % N) - L = r.val
      omega

@[simp] private theorem windowComplementEquiv_replaceWindow
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (σ : Fin N → Fin d) (τ : Fin L → Fin d) :
    windowComplementEquiv (d := d) L N hLN i
        (MPSTensor.replaceWindow L hLN i σ τ) =
      (τ, (windowComplementEquiv (d := d) L N hLN i σ).2) := by
  apply Prod.ext
  · exact MPSTensor.extractWindow_replaceWindow L hLN i σ τ
  · funext r
    simp only [windowComplementEquiv, Equiv.coe_fn_mk]
    unfold MPSTensor.replaceWindow
    have hrN : L + r.val < N := by omega
    have hoff :
        (((i.val + L + r.val) % N + N - i.val) % N) = L + r.val := by
      simpa [Nat.add_assoc] using MPSTensor.offset_mod_eq i.isLt hrN
    have hnot :
        ¬ (((i.val + L + r.val) % N + N - i.val) % N) < L := by
      omega
    rw [dite_eq_right hnot]

/-- In cyclic-window coordinates, an operator placed on the window of `L`
consecutive sites starting at `i` is the tensor product of the window operator
with the identity on the complement. -/
theorem reindex_placeAlong_ringWindow_windowComplement
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    Matrix.reindex (windowComplementEquiv (d := d) L N hLN i)
        (windowComplementEquiv (d := d) L N hLN i)
        (placeAlong (X := fun _ ↦ Fin d) (ringWindow hLN i) B) =
      B ⊗ₖ (1 : Matrix (Fin (N - L) → Fin d) (Fin (N - L) → Fin d) ℂ) := by
  let e := windowComplementEquiv (d := d) L N hLN i
  ext ⟨x, u⟩ ⟨y, v⟩
  let σ := e.symm (x, u)
  let τ := e.symm (y, v)
  have heσ : e σ = (x, u) := e.apply_symm_apply (x, u)
  have heτ : e τ = (y, v) := e.apply_symm_apply (y, v)
  have hx : MPSTensor.extractWindow L i σ = x := congrArg Prod.fst heσ
  have hy : MPSTensor.extractWindow L i τ = y := congrArg Prod.fst heτ
  have hAgree : (∀ k, (∀ r, ringWindow hLN i r ≠ k) → σ k = τ k) ↔ v = u := by
    rw [MPSTensor.forall_ringWindow_ne_imp_iff_replaceWindow]
    constructor
    · intro h
      have heq := congrArg e h
      have hsnd := congrArg Prod.snd heq
      simpa [e, σ, τ] using hsnd
    · intro h
      apply e.injective
      rw [windowComplementEquiv_replaceWindow, heσ, heτ, h, hx]
  change placeAlong (X := fun _ ↦ Fin d) (ringWindow hLN i) B σ τ =
    B x y * (if u = v then 1 else 0)
  rw [placeAlong_apply, ← MPSTensor.extractWindow_eq_comp_ringWindow hLN,
    ← MPSTensor.extractWindow_eq_comp_ringWindow hLN, hx, hy]
  by_cases h : v = u
  · rw [ite_eq_left (hAgree.mpr h), ite_eq_left h.symm, mul_one]
  · rw [ite_eq_right (hAgree.not.mpr h), ite_eq_right (Ne.symm h), mul_zero]

/-- Cyclic windows that do not overlap have disjoint images, so operators placed on
them commute (`ManyBody.commute_placeAlong_of_disjoint`).

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1571--1593. -/
theorem disjoint_map_ringWindow_of_not_cyclicWindowsOverlap {L : ℕ} (hLN : L ≤ N)
    {i j : Fin N} (hij : ¬ MPSTensor.cyclicWindowsOverlap N L i j) :
    Disjoint (Finset.univ.map (ringWindow hLN i)) (Finset.univ.map (ringWindow hLN j)) := by
  rw [Finset.disjoint_left]
  intro k hki hkj
  exact hij ⟨k, (MPSTensor.mem_cyclicWindowSupport_iff hLN i k).mpr
      ((MPSTensor.mem_map_ringWindow_iff hLN i k).mp hki),
    (MPSTensor.mem_cyclicWindowSupport_iff hLN j k).mpr
      ((MPSTensor.mem_map_ringWindow_iff hLN j k).mp hkj)⟩

/-- A commuting bond: one positive semidefinite two-site matrix `B` whose
translates `B_{i,i+1}` on the periodic chain pairwise commute at every chain
length `N ≥ 2`.

The bond is placed on the windows of two consecutive sites of the ring
(`ManyBody.placeAlong`, `ManyBody.ringWindow`). It is the length-independent local
ingredient of the commuting product `σ^{(N)} ∝ ∏_n B_{n,n+1}`.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), equation
`expression`, lines 1571--1576: `B_{n,n+1} ≥ 0` acts on nearest neighbours and the
translates commute; the proof builds one bond for every `n` and every `N`. -/
structure CommutingBond (d : ℕ) where
  /-- The positive semidefinite two-site bond `B`. -/
  bond : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ
  /-- Positivity of the bond. -/
  bond_pos : Matrix.PosSemidef bond
  /-- Pairwise commutativity of the translates of the bond on every finite periodic
  chain. -/
  bond_comm :
    ∀ {N : ℕ}, ∀ hN : 2 ≤ N, ∀ i j : Fin N,
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) bond
        * placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) bond
      = placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) bond
          * placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) bond

namespace CommutingBond

/-- The translate `B_{i,i+1}` of the bond on the `N`-site periodic chain. -/
noncomputable def bondAt (B : CommutingBond d) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    ChainOperator d N :=
  placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) B.bond

/-- Any two translates of the bond commute. -/
theorem bondAt_comm (B : CommutingBond d) {N : ℕ} (hN : 2 ≤ N) (i j : Fin N) :
    B.bondAt hN i * B.bondAt hN j = B.bondAt hN j * B.bondAt hN i :=
  B.bond_comm hN i j

/-- The commuting product `∏_i B_{i,i+1}` on the `N`-site periodic chain, taken in
the natural order of `Fin N`.

Source: arXiv:1606.00608, Appendix C.2, equation `expression`, lines 1571--1576. -/
noncomputable def product (B : CommutingBond d) {N : ℕ} (hN : 2 ≤ N) :
    ChainOperator d N :=
  (List.ofFn fun i : Fin N ↦ B.bondAt hN i).prod

end CommutingBond

/-- The projection onto the two-site sector determined by a one-site
orthogonal projection.

Source: arXiv:1606.00608, Definition 4.8, lines 838--842: for each sector
label, the global sector space is the tensor product of the corresponding
orthogonal one-site spaces. -/
noncomputable def twoSiteSectorProjection
    (P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  Matrix.reindex (finTwoArrowEquiv (Fin d)).symm
    (finTwoArrowEquiv (Fin d)).symm (P ⊗ₖ P)

@[simp] theorem twoSiteSectorProjection_one :
    twoSiteSectorProjection (d := d) 1 = 1 := by
  ext σ τ
  by_cases h0 : σ 0 = τ 0
  · by_cases h1 : σ 1 = τ 1
    · have hστ : σ = τ := by
        funext i
        fin_cases i
        · exact h0
        · exact h1
      subst τ
      simp [twoSiteSectorProjection, finTwoArrowEquiv]
    · have hστ : σ ≠ τ := fun h ↦ h1 (congrFun h 1)
      simp [twoSiteSectorProjection, finTwoArrowEquiv, h1, hστ]
  · have hστ : σ ≠ τ := fun h ↦ h0 (congrFun h 0)
    simp [twoSiteSectorProjection, finTwoArrowEquiv, h0, hστ]

/-- Source-faithful sector decomposition for a Gibbs state of a
nearest-neighbor commuting Hamiltonian on a periodic chain.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850, in the equivalent
positive-bond form of equation `rhoNCommv2`.  Lines 839--840 decompose the
global Hilbert space into uniform product sectors and require the corresponding
one-site spaces to be mutually orthogonal.  They do not assert that those
one-site spaces exhaust a larger one-site ambient space, so no local resolution
of the identity is imposed here. -/
structure GSNNCHData (d N : ℕ) where
  /-- The source definition concerns a genuine nearest-neighbor chain.
  Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
  hN : 2 ≤ N
  /-- Number of orthogonal global sectors labelled by `x`.
  Source: arXiv:1606.00608, lines 836--842. -/
  sectorCount : ℕ
  /-- Natural multiplicity `n_x` of each sector.
  Source: arXiv:1606.00608, equations `rhoNComm` and `rhoNCommv2`. -/
  multiplicity : Fin sectorCount → ℕ
  /-- Orthogonal projection onto the one-site space `H_n^x`.
  Source: arXiv:1606.00608, lines 838--842. -/
  sectorProjection : Fin sectorCount → Matrix (Fin d) (Fin d) ℂ
  /-- Each one-site sector projection is orthogonal.
  Source: arXiv:1606.00608, lines 838--842. -/
  sectorProjection_isOrthogonal :
    ∀ x : Fin sectorCount, IsOrthogonalProjection (sectorProjection x)
  /-- Distinct one-site sector projections have orthogonal ranges.
  Source: arXiv:1606.00608, lines 838--842. -/
  sectorProjection_orthogonal : ∀ {x y : Fin sectorCount}, x ≠ y →
    sectorProjection x * sectorProjection y = 0
  /-- The positive two-site operator `B^(x)` in each sector.
  Source: arXiv:1606.00608, equation `rhoNCommv2`, lines 843--850. -/
  bond : Fin sectorCount → Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ
  /-- Positivity of every sector bond.
  Source: arXiv:1606.00608, equation `rhoNCommv2`, lines 843--850. -/
  bond_pos : ∀ x : Fin sectorCount, (bond x).PosSemidef
  /-- The bond `B^(x)` acts within `H_x ⊗ H_x`.
  Source: arXiv:1606.00608, lines 838--850. -/
  bond_supported : ∀ x : Fin sectorCount,
    twoSiteSectorProjection (sectorProjection x) * bond x *
      twoSiteSectorProjection (sectorProjection x) = bond x
  /-- The bond commutes with its translate by one site.
  Source: arXiv:1606.00608, Definition 4.8 and equation `rhoNCommv2`. -/
  neighboring_comm : ∀ x : Fin sectorCount,
    placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) (bond x) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) (bond x) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) (bond x) *
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) (bond x)

namespace GSNNCHData

variable {N : ℕ}

/-- The translate `τ_i(B^(x))` of a sector bond. -/
noncomputable def bondAt (data : GSNNCHData d N)
    (x : Fin data.sectorCount) (i : Fin N) : ChainOperator d N :=
  placeAlong (X := fun _ ↦ Fin d) (ringWindow data.hN i) (data.bond x)

/-- The periodic product of the translated bonds in sector `x`. -/
noncomputable def sectorProduct (data : GSNNCHData d N)
    (x : Fin data.sectorCount) : ChainOperator d N :=
  (List.ofFn fun i : Fin N ↦ data.bondAt x i).prod

/-- The unnormalized orthogonal sector sum
`⊕_x n_x ∏_j τ_j(B^(x))` from equation `rhoNCommv2`.

Source: arXiv:1606.00608, equation `rhoNCommv2`, lines 843--850. -/
noncomputable def unnormalizedState (data : GSNNCHData d N) : ChainOperator d N :=
  ∑ x : Fin data.sectorCount, (data.multiplicity x : ℂ) • data.sectorProduct x

/-- The sector decomposition realizes a chain operator up to the positive
normalization denoted by proportionality in equation `rhoNCommv2`.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
def Realizes (data : GSNNCHData d N) (ρ : ChainOperator d N) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ρ = (c : ℂ) • data.unnormalizedState

/-- A positive two-site bond whose translates on the first two windows commute is
the one-sector case of the GSNNCH sector decomposition, with trivial sector
projection and multiplicity one.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
noncomputable def ofBond (hN : 2 ≤ N) (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (hB : B.PosSemidef)
    (hcomm :
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) B *
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) B =
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) B *
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) B) :
    GSNNCHData d N where
  hN := hN
  sectorCount := 1
  multiplicity := fun _ ↦ 1
  sectorProjection := fun _ ↦ 1
  sectorProjection_isOrthogonal := fun _ ↦ ⟨Matrix.isHermitian_one, by simp⟩
  sectorProjection_orthogonal := by
    intro x y hxy
    exact (hxy (Subsingleton.elim x y)).elim
  bond := fun _ ↦ B
  bond_pos := fun _ ↦ hB
  bond_supported := by
    intro x
    simp [twoSiteSectorProjection_one]
  neighboring_comm := fun _ ↦ hcomm

@[simp] theorem ofBond_unnormalizedState (hN : 2 ≤ N)
    (B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) (hB : B.PosSemidef) hcomm :
    (ofBond hN B hB hcomm).unnormalizedState =
      (List.ofFn fun i : Fin N ↦ placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) B).prod := by
  change ∑ _x : Fin 1, ((1 : ℕ) : ℂ) • (List.ofFn fun i : Fin N ↦
    placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) B).prod = _
  rw [Fin.sum_univ_one, Nat.cast_one, one_smul]

end GSNNCHData

/-- A chain operator has the explicit sector form in Definition 4.8, without
separately asserting density-matrix normalization.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
def HasGSNNCHFormAt {d N : ℕ} (ρ : ChainOperator d N) : Prop :=
  ∃ data : GSNNCHData d N, data.Realizes ρ

/-- Every chain operator generated by the MPO tensor has the explicit sector
form in Definition 4.8, without separately asserting density-matrix
normalization.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
def HasGSNNCHForm (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 2 ≤ N → HasGSNNCHFormAt (mpo M N)

/-- A density operator is GSNNCH when it has the explicit orthogonal sector
decomposition of Definition 4.8.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
def IsGSNNCHAt {d N : ℕ} (ρ : ChainOperator d N) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1 ∧ HasGSNNCHFormAt ρ

/-- At every chain length, the normalized density operator generated by the
MPO tensor satisfies the source GSNNCH definition.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
def IsGSNNCH (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 2 ≤ N → IsGSNNCHAt (normalizedMPO M N)

/-- At one chain length, a positive scalar multiple of the product of the translates
of a positive two-site bond whose first two translates commute has the GSNNCH form.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850, one-sector case. -/
theorem hasGSNNCHFormAt_of_eq_smul_prod {N : ℕ} (hN : 2 ≤ N)
    {B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ} (hB : B.PosSemidef)
    (hcomm :
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) B *
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) B =
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) B *
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) B)
    {ρ : ChainOperator d N} {c : ℝ} (hc : 0 < c)
    (hρ : ρ = (c : ℂ) •
      (List.ofFn fun i : Fin N ↦ placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) B).prod) :
    HasGSNNCHFormAt ρ :=
  ⟨GSNNCHData.ofBond hN B hB hcomm, c, hc, by simpa using hρ⟩

/-- At one chain length, the one-sector GSNNCH presentations of `ρ` are exactly the
positive scalar multiples of the product of the translates of one positive two-site
bond whose first two translates commute.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850, one-sector case. -/
theorem exists_oneSector_gsnnchData_iff {N : ℕ} (hN : 2 ≤ N) (ρ : ChainOperator d N) :
    (∃ data : GSNNCHData d N, data.sectorCount = 1 ∧ data.Realizes ρ) ↔
      ∃ B : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ, B.PosSemidef ∧
        placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) B *
            placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) B =
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨1, by omega⟩) B *
            placeAlong (X := fun _ ↦ Fin d) (ringWindow hN ⟨0, by omega⟩) B ∧
        ∃ c : ℝ, 0 < c ∧ ρ = (c : ℂ) •
          (List.ofFn fun i : Fin N ↦
            placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) B).prod := by
  constructor
  · rintro ⟨data, hcount, c, hc, hρ⟩
    obtain ⟨x⟩ : Nonempty (Fin data.sectorCount) := ⟨⟨0, by omega⟩⟩
    have hsum : data.unnormalizedState =
        (data.multiplicity x : ℂ) • data.sectorProduct x := by
      rw [GSNNCHData.unnormalizedState]
      refine Fintype.sum_eq_single x fun y hy ↦ ?_
      exact (hy (Fin.ext (by have := y.isLt; have := x.isLt; omega))).elim
    rcases Nat.eq_zero_or_pos (data.multiplicity x) with hn | hn
    · refine ⟨0, Matrix.PosSemidef.zero, by simp only [placeAlong_zero], 1, one_pos, ?_⟩
      have hprod : (List.ofFn fun i : Fin N ↦
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i)
            (0 : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)).prod = 0 := by
        obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
        rw [List.ofFn_succ, List.prod_cons, placeAlong_zero, zero_mul]
      rw [hρ, hsum, hn, hprod, Nat.cast_zero, zero_smul, smul_zero, smul_zero]
    · refine ⟨data.bond x, data.bond_pos x, data.neighboring_comm x,
        c * data.multiplicity x, mul_pos hc (by exact_mod_cast hn), ?_⟩
      rw [hρ, hsum, smul_smul]
      push_cast
      rfl
  · rintro ⟨B, hB, hcomm, c, hc, hρ⟩
    exact ⟨GSNNCHData.ofBond hN B hB hcomm, rfl, c, hc, by simpa using hρ⟩

/-- The commuting form of a matrix product operator tensor: one commuting bond `B`
such that, at every chain length `N ≥ 2`, the operator `σ^{(N)}(M)` is a positive
scalar multiple of the product `∏_n B_{n,n+1}` of the translates of `B`.

The bond is the same for every chain length, as in the proof of Proposition C.8
and as read by Proposition `4to2`.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8 (`3to4`), equation
`expression`, lines 1569--1594; Proposition `4to2`, lines 1597--1619. The reading
"one bond for every chain length" is recorded in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
structure CommutingForm (M : MPOTensor d D) extends CommutingBond d where
  /-- The operator on every finite periodic chain is a positive scalar multiple of
  the commuting bond product. -/
  realizes_mpo :
    ∀ N : ℕ, ∀ hN : 2 ≤ N,
      ∃ c : ℝ, 0 < c ∧ mpo M N = (c : ℂ) • toCommutingBond.product hN

/-- A commuting form gives the one-sector GSNNCH form at every chain length.

Source: arXiv:1606.00608, Definition 4.8, lines 829--850, and Appendix C.2,
equation `expression`, lines 1571--1576. -/
theorem CommutingForm.hasGSNNCHForm {M : MPOTensor d D} (F : CommutingForm M) :
    HasGSNNCHForm M := fun N hN ↦ by
  obtain ⟨c, hc, h⟩ := F.realizes_mpo N hN
  exact hasGSNNCHFormAt_of_eq_smul_prod hN F.bond_pos (F.bond_comm hN _ _) hc h

end MPOTensor
