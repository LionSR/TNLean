/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.ZCL
import QICLean.Algebra.OrthogonalProjection
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import QICLean.Algebra.FinSumPermutation

/-!
# Commuting-form and GSNNCH data for simple MPDOs

This file states the commuting-form side of the simple MPDO story from
arXiv:1606.00608 Section 4.4 and Appendix C.2.

For an `N`-site operator `ρ`, a commuting-form witness consists of a positive
semidefinite two-site matrix `B`, together with proofs that its translated
copies on the periodic chain pairwise commute and that their product
reproduces `ρ` up to a positive scalar. The separate `GSNNCHData` follows
Definition 4.8 by recording the orthogonal one-site
sectors, their natural multiplicities, and one positive bond in every sector.
The single-bond presentation gives its one-sector case; the converse comparison
is not asserted. The
theorem `MPOTensor.nonempty_etaLocalStructureData_of_isSAL` proves the
entropy-side implication from SAL; its local structure gives
`HasCommutingForm` through `MPOTensor.EtaLocalStructureData.hasCommutingForm`.
This is Proposition C.8 of arXiv:1606.00608, Appendix C.2, lines 1569--1594.

## Main declarations

* `MPOTensor.ChainOperator`
* `MPOTensor.windowComplementEquiv`,
  `MPOTensor.reindex_placeAlong_ringWindow_windowComplement` — an operator placed on
  a window of the ring (`ManyBody.placeAlong` along `ManyBody.ringWindow`) is the
  window operator tensored with the identity on the complement
* `MPOTensor.CommutingFormData`
* `MPOTensor.HasCommutingForm`
* `MPOTensor.GSNNCHData`
* `MPOTensor.HasGSNNCHFormAt`
* `MPOTensor.HasGSNNCHForm`
* `MPOTensor.IsGSNNCHAt`
* `MPOTensor.IsGSNNCH`

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

/-- Chain-level commuting-form data for the simple-MPDO theorem.

The current structure stores the translation-invariant two-site factor `B` together
with chain-level commutativity of its translated copies. The intended
nearest-neighbor support is encoded by placing the bond on the windows of two
consecutive sites of the ring (`ManyBody.placeAlong`, `ManyBody.ringWindow`); no separate
factorization structure is required later. -/
structure CommutingFormData (d N : ℕ) where
  /-- The theorem only makes sense for genuine nearest-neighbor chains. -/
  hN : 2 ≤ N
  /-- The positive semidefinite two-site factor `B`. -/
  bond : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ
  /-- Positivity of the local factor. -/
  bond_pos : Matrix.PosSemidef bond
  /-- Pairwise commutativity of the translated factors on the `N`-site chain. -/
  bond_comm :
    ∀ i j : Fin N,
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) bond
        * placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) bond
      = placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) bond
          * placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) bond

namespace CommutingFormData

variable {N : ℕ}

/-- The translated copy of the local bond operator at site `i`. -/
noncomputable def bondAt (data : CommutingFormData d N) (i : Fin N) :
    ChainOperator d N :=
  placeAlong (X := fun _ ↦ Fin d) (ringWindow data.hN i) data.bond

/-- Any two translated copies of the local bond commute. -/
theorem bondAt_comm (data : CommutingFormData d N) (i j : Fin N) :
    data.bondAt i * data.bondAt j = data.bondAt j * data.bondAt i :=
  data.bond_comm i j

/-- The commuting product `∏_i B_{i,i+1}` on the periodic chain, taken in the
natural order of `Fin N`. -/
noncomputable def product (data : CommutingFormData d N) : ChainOperator d N :=
  (List.ofFn fun i : Fin N => data.bondAt i).prod

/-- The commuting-form witness realizes `ρ` when `ρ` equals the commuting product
up to a positive real normalization factor. -/
def Realizes (data : CommutingFormData d N) (ρ : ChainOperator d N) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ρ = (c : ℂ) • data.product

end CommutingFormData

/-- Chainwise commuting-form property for an MPO tensor: each finite chain of
length at least `2` admits a commuting-form witness for the corresponding MPO
operator. The bond may depend on the chain length.

This is weaker than the hypothesis of source Proposition 4to2 in
arXiv:1606.00608, lines 1597--1619, which refers back to the single
translation-invariant bond family in the equation carrying the source label
expression. That source
hypothesis is represented by `EtaLocalStructureData`: one bond realizes every
finite chain. The distinction and the missing Bravyi--Vyalyi decomposition are
recorded in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def HasCommutingForm (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    ∃ data : CommutingFormData d N, data.Realizes (mpo M N)

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

/-- A single positive commuting bond is the one-sector case of the source
GSNNCH sector decomposition. -/
noncomputable def ofCommutingFormData
    (form : CommutingFormData d N) : GSNNCHData d N where
  hN := form.hN
  sectorCount := 1
  multiplicity := fun _ ↦ 1
  sectorProjection := fun _ ↦ 1
  sectorProjection_isOrthogonal := fun _ ↦ ⟨Matrix.isHermitian_one, by simp⟩
  sectorProjection_orthogonal := by
    intro x y hxy
    exact (hxy (Subsingleton.elim x y)).elim
  bond := fun _ ↦ form.bond
  bond_pos := fun _ ↦ form.bond_pos
  bond_supported := by
    intro x
    simp [twoSiteSectorProjection_one]
  neighboring_comm := fun _ ↦ form.bond_comm _ _

@[simp] theorem ofCommutingFormData_unnormalizedState
    (form : CommutingFormData d N) :
    (ofCommutingFormData form).unnormalizedState = form.product := by
  rw [unnormalizedState]
  change (∑ x : Fin 1, ((ofCommutingFormData form).multiplicity x : ℂ) •
    (ofCommutingFormData form).sectorProduct x) = form.product
  rw [Fin.sum_univ_one]
  unfold sectorProduct bondAt
  simp only [ofCommutingFormData]
  rw [Nat.cast_one, one_smul]
  unfold CommutingFormData.product CommutingFormData.bondAt
  congr

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

namespace CommutingFormData

variable {N : ℕ}

/-- A single-bond commuting-form realization gives the one-sector instance
of the source GSNNCH form.

Source comparison: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
theorem hasGSNNCHFormAt_of_realizes (data : CommutingFormData d N)
    {ρ : ChainOperator d N} (hρ : data.Realizes ρ) : HasGSNNCHFormAt ρ := by
  rcases hρ with ⟨c, hc, hρ⟩
  refine ⟨GSNNCHData.ofCommutingFormData data, c, hc, ?_⟩
  simpa using hρ

end CommutingFormData

end MPOTensor
