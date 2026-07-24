/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RFP
import TNLean.Algebra.OrthogonalProjection
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.CyclicWindow

/-!
# Commuting-form and GSNNCH data for simple MPDOs

This file states the commuting-form side of the simple MPDO story from
arXiv:1606.00608 Section 4.4 and Appendix C.2.

For an `N`-site operator `ρ`, a commuting-form witness consists of a positive
semidefinite two-site matrix `B`, together with proofs that its translated
copies on the periodic chain pairwise commute and that their product
reproduces `ρ` up to a positive scalar. The auxiliary
`CommutingBondProductData` records this single-bond presentation. The separate
`GSNNCHData` follows Definition 4.8 by recording the orthogonal one-site
sectors, their natural multiplicities, and one positive bond in every sector.
The single-bond presentation gives its one-sector case; the converse comparison
is not asserted. The
theorem `MPOTensor.nonempty_etaLocalStructureData_of_isSAL` proves the
entropy-side implication from SAL; its local structure gives
`HasCommutingForm` through `MPOTensor.EtaLocalStructureData.hasCommutingForm`.
This is Proposition C.8 of arXiv:1606.00608, Appendix C.2, lines 1569--1594.

## Main declarations

* `MPOTensor.ChainOperator`
* `MPOTensor.AgreesOutsideWindow`
* `MPOTensor.embedLocalOperator`
* `MPOTensor.CommutingFormData`
* `MPOTensor.HasCommutingForm`
* `MPOTensor.CommutingBondProductData`
* `MPOTensor.HasCommutingBondProductAt`
* `MPOTensor.HasCommutingBondProduct`
* `MPOTensor.HasCommutingBondProductWithZCL`
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
open Matrix Finset

namespace MPOTensor

attribute [local instance] Classical.decEq Classical.propDecidable

variable {d D N : ℕ}

/-- The matrix algebra on an `N`-site chain with local dimension `d`. -/
abbrev ChainOperator (d N : ℕ) :=
  Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ

/-- Two chain configurations agree outside the translated length-`L` window
starting at `i` when replacing the window of `τ` by that of `σ` recovers `σ`.
This is the matrix-entry side condition used to embed an `L`-site operator into
an `N`-site periodic chain. -/
def AgreesOutsideWindow (L : ℕ) {N : ℕ} (hLN : L ≤ N) (i : Fin N)
    (σ τ : Fin N → Fin d) : Prop :=
  MPSTensor.replaceWindow L hLN i τ (MPSTensor.extractWindow L i σ) = σ

/-- Embed an `L`-site operator into the periodic `N`-site chain at position `i`,
acting as the given local matrix on the window and as the identity on the
complement. -/
noncomputable def embedLocalOperator (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) : ChainOperator d N :=
  Matrix.of fun σ τ =>
    if AgreesOutsideWindow (d := d) L hLN i σ τ then
      B (MPSTensor.extractWindow L i σ) (MPSTensor.extractWindow L i τ)
    else 0

@[simp] theorem embedLocalOperator_apply (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (σ τ : Fin N → Fin d) :
    embedLocalOperator (d := d) L N hLN i B σ τ =
      if AgreesOutsideWindow (d := d) L hLN i σ τ then
        B (MPSTensor.extractWindow L i σ) (MPSTensor.extractWindow L i τ)
      else 0 :=
  rfl

/-- Two configurations agree outside a cyclic window exactly when their values
coincide at every site outside that window. -/
theorem agreesOutsideWindow_iff (L : ℕ) {N : ℕ} (hLN : L ≤ N)
    (i : Fin N) (σ τ : Fin N → Fin d) :
    AgreesOutsideWindow (d := d) L hLN i σ τ ↔
      ∀ k : Fin N, ¬ ((k.val + N - i.val) % N < L) → τ k = σ k := by
  constructor
  · intro h k hk
    have hk' := congrFun h k
    simpa [AgreesOutsideWindow, MPSTensor.replaceWindow, hk] using hk'
  · intro h
    rw [AgreesOutsideWindow]
    funext k
    unfold MPSTensor.replaceWindow
    by_cases hk : (k.val + N - i.val) % N < L
    · rw [dif_pos hk]
      have hself := congrFun (MPSTensor.replaceWindow_extractWindow L hLN i σ) k
      simpa [MPSTensor.replaceWindow, hk] using hself
    · simp [hk, h k hk]

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
    have hoffN : offset < N := Nat.mod_lt _ (Fin.pos i)
    have hsite : (i.val + offset) % N = k.val := by
      rcases lt_or_ge k.val i.val with hki | hik
      · have hmod : offset = k.val + N - i.val := by
          simp only [offset]
          rw [Nat.mod_eq_of_lt (by omega)]
        rw [hmod, show i.val + (k.val + N - i.val) = k.val + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
      · have hmod : offset = k.val - i.val := by
          simp only [offset]
          have heq : k.val + N - i.val = N + (k.val - i.val) := by omega
          rw [heq, Nat.add_mod_left,
            Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) k.isLt)]
        rw [hmod, Nat.add_sub_of_le hik, Nat.mod_eq_of_lt k.isLt]
    by_cases hoff : offset < L
    · rw [dif_pos hoff]
      exact congrArg σ (Fin.ext hsite)
    · rw [dif_neg hoff]
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
      rw [dif_pos (hoff.symm ▸ r.isLt)]
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
      rw [dif_neg hnot]
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
    rw [dif_neg hnot]

/-- In cyclic-window coordinates, a local operator is the tensor product of
the window operator with the identity on the complement. -/
theorem reindex_embedLocalOperator_windowComplement
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    Matrix.reindex (windowComplementEquiv (d := d) L N hLN i)
        (windowComplementEquiv (d := d) L N hLN i)
        (embedLocalOperator (d := d) L N hLN i B) =
      B ⊗ₖ (1 : Matrix (Fin (N - L) → Fin d) (Fin (N - L) → Fin d) ℂ) := by
  let e := windowComplementEquiv (d := d) L N hLN i
  ext ⟨x, u⟩ ⟨y, v⟩
  let σ := e.symm (x, u)
  let τ := e.symm (y, v)
  have heσ : e σ = (x, u) := e.apply_symm_apply (x, u)
  have heτ : e τ = (y, v) := e.apply_symm_apply (y, v)
  have hx : MPSTensor.extractWindow L i σ = x := congrArg Prod.fst heσ
  have hy : MPSTensor.extractWindow L i τ = y := congrArg Prod.fst heτ
  have hAgree : AgreesOutsideWindow (d := d) L hLN i σ τ ↔ v = u := by
    constructor
    · intro h
      have heq := congrArg e h
      have hsnd := congrArg Prod.snd heq
      simpa [e, σ, τ] using hsnd
    · intro h
      apply e.injective
      rw [windowComplementEquiv_replaceWindow, heσ, heτ, h, hx]
  by_cases h : v = u
  · change (if AgreesOutsideWindow (d := d) L hLN i σ τ then
        B (MPSTensor.extractWindow L i σ) (MPSTensor.extractWindow L i τ) else 0) =
      B x y * (if u = v then 1 else 0)
    rw [if_pos (hAgree.mpr h), hx, hy, if_pos h.symm, mul_one]
  · change (if AgreesOutsideWindow (d := d) L hLN i σ τ then
        B (MPSTensor.extractWindow L i σ) (MPSTensor.extractWindow L i τ) else 0) =
      B x y * (if u = v then 1 else 0)
    rw [if_neg (hAgree.not.mpr h), if_neg (Ne.symm h), mul_zero]

/-- Embedding two operators into the same cyclic window preserves their
product. -/
theorem embedLocalOperator_mul (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B C : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    embedLocalOperator (d := d) L N hLN i (B * C) =
      embedLocalOperator (d := d) L N hLN i B *
        embedLocalOperator (d := d) L N hLN i C := by
  let e := windowComplementEquiv (d := d) L N hLN i
  apply (Matrix.reindex e e).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (embedLocalOperator (d := d) L N hLN i (B * C)) =
    (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (embedLocalOperator (d := d) L N hLN i B *
        embedLocalOperator (d := d) L N hLN i C)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e,
    Matrix.coe_reindexLinearEquiv,
    reindex_embedLocalOperator_windowComplement,
    reindex_embedLocalOperator_windowComplement,
    reindex_embedLocalOperator_windowComplement,
    ← Matrix.mul_kronecker_mul]
  simp

/-- The action of a cyclically embedded local operator is the sum over
replacements of the configuration inside its window. -/
theorem embedLocalOperator_mulVec_apply (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ)
    (v : (Fin N → Fin d) → ℂ) (σ : Fin N → Fin d) :
    (embedLocalOperator (d := d) L N hLN i B).mulVec v σ =
      ∑ τ : Fin L → Fin d,
        B (MPSTensor.extractWindow L i σ) τ *
          v (MPSTensor.replaceWindow L hLN i σ τ) := by
  let e := windowComplementEquiv (d := d) L N hLN i
  rw [Matrix.mulVec, dotProduct]
  calc
    (∑ τ : Fin N → Fin d,
        embedLocalOperator (d := d) L N hLN i B σ τ * v τ) =
        ∑ x : (Fin L → Fin d) × (Fin (N - L) → Fin d),
          embedLocalOperator (d := d) L N hLN i B σ (e.symm x) * v (e.symm x) :=
      Fintype.sum_equiv e _ _ fun x ↦ by rw [e.symm_apply_apply]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro τ _
      have heσ : e σ =
          (MPSTensor.extractWindow L i σ, (e σ).2) := by
        exact Prod.ext rfl rfl
      have hreplace :
          e.symm (τ, (e σ).2) = MPSTensor.replaceWindow L hLN i σ τ := by
        apply e.injective
        rw [e.apply_symm_apply, windowComplementEquiv_replaceWindow]
      have hentry (u : Fin (N - L) → Fin d) :
          embedLocalOperator (d := d) L N hLN i B σ (e.symm (τ, u)) =
            B (MPSTensor.extractWindow L i σ) τ *
              (if (e σ).2 = u then 1 else 0) := by
        have h := congrFun (congrFun
          (reindex_embedLocalOperator_windowComplement (d := d) L N hLN i B)
          (e σ)) (τ, u)
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
          Matrix.one_apply] at h
        rw [e.symm_apply_apply] at h
        rw [show (e σ).1 = MPSTensor.extractWindow L i σ from rfl] at h
        exact h
      simp_rw [hentry]
      rw [Finset.sum_eq_single (e σ).2]
      · simp [hreplace]
      · intro u _ hu
        rw [if_neg (Ne.symm hu), mul_zero, zero_mul]
      · simp

private theorem cyclicWindowsDisjoint_of_not_overlap {N L : ℕ} (hLN : L ≤ N)
    {i j : Fin N} (hij : ¬ MPSTensor.cyclicWindowsOverlap N L i j) :
    ∀ k : Fin N,
      ((k.val + N - i.val) % N < L) →
        ((k.val + N - j.val) % N < L) → False := by
  intro k hki hkj
  apply hij
  refine ⟨k, ?_, ?_⟩
  · exact (MPSTensor.mem_cyclicWindowSupport_iff hLN i k).mpr hki
  · exact (MPSTensor.mem_cyclicWindowSupport_iff hLN j k).mpr hkj

private theorem extractWindow_replaceWindow_of_not_cyclicWindowsOverlap
    {N L : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : ¬ MPSTensor.cyclicWindowsOverlap N L i j)
    (σ : Fin N → Fin d) (τ : Fin L → Fin d) :
    MPSTensor.extractWindow L i (MPSTensor.replaceWindow L hLN j σ τ) =
      MPSTensor.extractWindow L i σ := by
  funext r
  unfold MPSTensor.extractWindow MPSTensor.replaceWindow
  have hi : (((i.val + r.val) % N + N - i.val) % N) < L := by
    rw [MPSTensor.offset_mod_eq i.isLt (Nat.lt_of_lt_of_le r.isLt hLN)]
    exact r.isLt
  have hnotj : ¬ (((i.val + r.val) % N + N - j.val) % N < L) := by
    intro hj
    exact cyclicWindowsDisjoint_of_not_overlap hLN hij
      ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ hi hj
  rw [dif_neg hnotj]

private theorem replaceWindow_commute_of_not_cyclicWindowsOverlap
    {N L : ℕ} (hLN : L ≤ N) {i j : Fin N}
    (hij : ¬ MPSTensor.cyclicWindowsOverlap N L i j)
    (σ : Fin N → Fin d) (α β : Fin L → Fin d) :
    MPSTensor.replaceWindow L hLN j (MPSTensor.replaceWindow L hLN i σ α) β =
      MPSTensor.replaceWindow L hLN i (MPSTensor.replaceWindow L hLN j σ β) α := by
  funext k
  have hdisjoint := cyclicWindowsDisjoint_of_not_overlap hLN hij
  by_cases hi : ((k.val + N - i.val) % N < L)
  · have hnotj : ¬ ((k.val + N - j.val) % N < L) := fun hj => hdisjoint k hi hj
    simp [MPSTensor.replaceWindow, hi, hnotj]
  · by_cases hj : ((k.val + N - j.val) % N < L)
    · simp [MPSTensor.replaceWindow, hi, hj]
    · simp [MPSTensor.replaceWindow, hi, hj]

/-- Operators embedded into disjoint cyclic windows commute.

The hypothesis is precisely that the two cyclic supports have no common site.
No positivity, idempotency, or relation between the two local matrices is
required.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1571--1593. -/
theorem embedLocalOperator_commute_of_not_cyclicWindowsOverlap
    (L N : ℕ) (hLN : L ≤ N) {i j : Fin N}
    (hij : ¬ MPSTensor.cyclicWindowsOverlap N L i j)
    (B C : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    embedLocalOperator (d := d) L N hLN i B *
        embedLocalOperator (d := d) L N hLN j C =
      embedLocalOperator (d := d) L N hLN j C *
        embedLocalOperator (d := d) L N hLN i B := by
  apply Matrix.mulVec_injective
  funext v σ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [embedLocalOperator_mulVec_apply, embedLocalOperator_mulVec_apply]
  simp_rw [embedLocalOperator_mulVec_apply]
  simp_rw [extractWindow_replaceWindow_of_not_cyclicWindowsOverlap
    (d := d) hLN hij]
  simp_rw [extractWindow_replaceWindow_of_not_cyclicWindowsOverlap
    (d := d) hLN (fun h ↦ hij ((MPSTensor.cyclicWindowsOverlap_comm N L j i).mp h))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro α _
  rw [replaceWindow_commute_of_not_cyclicWindowsOverlap (d := d) hLN hij]
  ring

/-- Chain-level commuting-form data for the simple-MPDO theorem.

The current structure stores the translation-invariant two-site factor `B` together
with chain-level commutativity of its translated copies. The intended
nearest-neighbor support is encoded by `embedLocalOperator`; no separate
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
      embedLocalOperator (d := d) 2 N hN i bond
        * embedLocalOperator (d := d) 2 N hN j bond
      = embedLocalOperator (d := d) 2 N hN j bond
          * embedLocalOperator (d := d) 2 N hN i bond

namespace CommutingFormData

variable {N : ℕ}

/-- The translated copy of the local bond operator at site `i`. -/
noncomputable def bondAt (data : CommutingFormData d N) (i : Fin N) :
    ChainOperator d N :=
  embedLocalOperator (d := d) 2 N data.hN i data.bond

@[simp] theorem bondAt_apply (data : CommutingFormData d N) (i : Fin N)
    (σ τ : Fin N → Fin d) :
    data.bondAt i σ τ =
      if AgreesOutsideWindow (d := d) 2 data.hN i σ τ then
        data.bond (MPSTensor.extractWindow 2 i σ) (MPSTensor.extractWindow 2 i τ)
      else 0 :=
  rfl

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

/-- A witness for a single-bond commuting-product presentation at chain length
`N`. This auxiliary condition has no explicit outer sector decomposition.

Source comparison: arXiv:1606.00608, Definition 4.8, lines 829--850. The
source GSNNCH condition is defined separately below. -/
structure CommutingBondProductData (d N : ℕ) where
  /-- The underlying positive commuting bond. -/
  form : CommutingFormData d N
  /-- The positive scalar multiplying the bond product. -/
  normalization : ℝ
  /-- Strict positivity of the scalar multiplying the bond product. -/
  normalization_pos : 0 < normalization

namespace CommutingBondProductData

variable {N : ℕ}

/-- The chain operator represented by a single commuting bond. -/
noncomputable def state (data : CommutingBondProductData d N) : ChainOperator d N :=
  (data.normalization : ℂ) • data.form.product

/-- A single-bond witness realizes its represented chain operator. -/
theorem realizes_form_state (data : CommutingBondProductData d N) :
    data.form.Realizes data.state :=
  ⟨data.normalization, data.normalization_pos, rfl⟩

end CommutingBondProductData

/-- The chain-level single-bond commuting-product condition. -/
def HasCommutingBondProductAt {d N : ℕ} (ρ : ChainOperator d N) : Prop :=
  ∃ data : CommutingBondProductData d N, ρ = data.state

/-- Every chain generated by the MPO tensor has a single-bond
commuting-product presentation. -/
def HasCommutingBondProduct (M : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 2 ≤ N → HasCommutingBondProductAt (mpo M N)

namespace CommutingFormData

variable {N : ℕ}

/-- Adjoin a positive normalization to a commuting-form witness. -/
def toCommutingBondProductData
    (data : CommutingFormData d N) (c : ℝ) (hc : 0 < c) :
    CommutingBondProductData d N where
  form := data
  normalization := c
  normalization_pos := hc

/-- Any commuting-form realization yields a single-bond product witness. -/
theorem hasCommutingBondProductAt_of_realizes (data : CommutingFormData d N)
    {ρ : ChainOperator d N} (hρ : data.Realizes ρ) : HasCommutingBondProductAt ρ := by
  rcases hρ with ⟨c, hc, hρ⟩
  refine ⟨data.toCommutingBondProductData c hc, ?_⟩
  simpa [CommutingBondProductData.state, toCommutingBondProductData] using hρ

end CommutingFormData

/-- A chain operator has a single-bond product presentation exactly when it
has a commuting-form realization. -/
theorem hasCommutingBondProductAt_iff_exists_commutingForm
    {d N : ℕ} (ρ : ChainOperator d N) :
    HasCommutingBondProductAt ρ ↔
      ∃ data : CommutingFormData d N, data.Realizes ρ := by
  constructor
  · rintro ⟨data, rfl⟩
    exact ⟨data.form, data.realizes_form_state⟩
  · rintro ⟨data, hρ⟩
    exact data.hasCommutingBondProductAt_of_realizes hρ

/-- A global commuting form gives a single-bond product witness at every
chain length. -/
theorem hasCommutingBondProduct_of_hasCommutingForm {M : MPOTensor d D}
    (hM : HasCommutingForm M) : HasCommutingBondProduct M := by
  intro N hN
  obtain ⟨data, hdata⟩ := hM N hN
  exact data.hasCommutingBondProductAt_of_realizes hdata

/-- Single-bond witnesses at every chain length give a global commuting
form. -/
theorem hasCommutingForm_of_hasCommutingBondProduct {M : MPOTensor d D}
    (hM : HasCommutingBondProduct M) : HasCommutingForm M := fun N hN ↦
  (hasCommutingBondProductAt_iff_exists_commutingForm (mpo M N)).mp (hM N hN)

/-- The two presentations of the single-bond commuting-product condition are
equivalent. -/
theorem hasCommutingBondProduct_iff_hasCommutingForm (M : MPOTensor d D) :
    HasCommutingBondProduct M ↔ HasCommutingForm M :=
  ⟨hasCommutingForm_of_hasCommutingBondProduct,
    hasCommutingBondProduct_of_hasCommutingForm⟩

/-- The single-bond commuting-product condition together with the
doubled-index transfer identity. -/
def HasCommutingBondProductWithZCL (M : MPOTensor d D) : Prop :=
  HasCommutingBondProduct M ∧ IsZCL M

/-- The single-bond condition with doubled-index transfer idempotence is
equivalent to a commuting form with the same idempotence condition. -/
theorem hasCommutingBondProductWithZCL_iff_hasCommutingForm_and_isZCL
    (M : MPOTensor d D) :
    HasCommutingBondProductWithZCL M ↔ HasCommutingForm M ∧ IsZCL M := by
  rw [HasCommutingBondProductWithZCL,
    hasCommutingBondProduct_iff_hasCommutingForm]

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
    embedLocalOperator (d := d) 2 N hN ⟨0, by omega⟩ (bond x) *
        embedLocalOperator (d := d) 2 N hN ⟨1, by omega⟩ (bond x) =
      embedLocalOperator (d := d) 2 N hN ⟨1, by omega⟩ (bond x) *
        embedLocalOperator (d := d) 2 N hN ⟨0, by omega⟩ (bond x)

namespace GSNNCHData

variable {N : ℕ}

/-- The translate `τ_i(B^(x))` of a sector bond. -/
noncomputable def bondAt (data : GSNNCHData d N)
    (x : Fin data.sectorCount) (i : Fin N) : ChainOperator d N :=
  embedLocalOperator (d := d) 2 N data.hN i (data.bond x)

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
  simp [unnormalizedState, sectorProduct, bondAt, ofCommutingFormData,
    CommutingFormData.product, CommutingFormData.bondAt]

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

/-- Every single-bond commuting-product presentation is a one-sector source
GSNNCH presentation.

Source comparison: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
theorem hasGSNNCHFormAt_of_hasCommutingBondProductAt
    {ρ : ChainOperator d N} (hρ : HasCommutingBondProductAt ρ) :
    HasGSNNCHFormAt ρ := by
  rw [hasCommutingBondProductAt_iff_exists_commutingForm] at hρ
  obtain ⟨data, hdata⟩ := hρ
  exact data.hasGSNNCHFormAt_of_realizes hdata

/-- A global single-bond commuting-product presentation gives the one-sector
instance of the explicit source sector form at every chain length.

Source comparison: arXiv:1606.00608, Definition 4.8, lines 829--850. -/
theorem hasGSNNCHForm_of_hasCommutingBondProduct
    {M : MPOTensor d D} (hM : HasCommutingBondProduct M) :
    HasGSNNCHForm M := fun N hN ↦
  hasGSNNCHFormAt_of_hasCommutingBondProductAt (hM N hN)

end MPOTensor
