/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SelectedMiddleMPOFamily
import TNLean.MPS.AreaLaw.IntervalMPOTransfer
import TNLean.MPS.AreaLaw.TraceIntervalTransfer
import TNLean.MPS.AreaLaw.RegionalMiddleFactors
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.RetainedCoreFamilies
import TNLean.MPS.AreaLaw.SelectedCoefficientDecomposition
import TNLean.Algebra.TwoMarkerMiddleFactors
import TNLean.MPS.AreaLaw.IntervalSymmDiff
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.SymmDiff

/-!
# A common prescribed-middle family over finite sampling nodes

The selected middle intervals and the prescribed central interval have a
nonempty overlap under the original two-window geometry. Moving the middle
factors to the prescribed interval multiplies their number by at most the
fourth-power configuration count of the window half-width.

A finite supplied family of ordinary weights gives a dependent sum of the
canonical node families. The resulting middle operators are fixed before
the supported exterior pair and every array of polynomial coefficients.
All terms share the general square-derived open bond bound in increasing
site order. The low-frequency cardinal estimate is a separate numerical
consequence.

The family theorem requires positive local dimension, while virtual
dimension zero and degree zero are retained. The statement concerns the
supplied sampling nodes; coefficient recovery and the sharper bond and
computational estimates of the cited proposition remain separate.

## References

Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The selected and prescribed middle intervals satisfy the bounds for the
increasing-coordinate interval transport, with a nonempty overlap. All
inequalities follow from the original two-window assumptions. Supporting
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
theorem selected_middle_fixed_interval_bounds
    {L a b ell : ℕ}
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) :
    a + p.val + 1 ≤ b + s.val + 1 ∧
      b + s.val + 1 ≤ L ∧
      a + ell ≤ b + ell + 1 ∧
      b + ell + 1 ≤ L ∧
      max (a + p.val + 1) (a + ell) <
        min (b + s.val + 1) (b + ell + 1) := by
  have hp := p.isLt
  have hs := s.isLt
  omega

/-- The selected middle and the central prescribed interval differ at no
more than twice the window half-width. The same nonempty regional core lies
inside both intervals. This is geometric support for changing intervals in
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
private theorem selected_middle_central_interval_geometry
    {L a b ell : ℕ}
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) :
    let E := interval L (a + p.val + 1) (b + s.val + 1)
    let J := interval L (a + ell) (b + ell + 1)
    let K := interval L (a + 2 * ell) (b + 1)
    (E \ J).card + (J \ E).card ≤ 2 * ell ∧
      K ⊆ E ∧ K ⊆ J ∧ K.Nonempty := by
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let J := interval L (a + ell) (b + ell + 1)
  let K := interval L (a + 2 * ell) (b + 1)
  have hp := p.isLt
  have hs := s.isLt
  have hdisjoint : Disjoint (E \ J) (J \ E) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1
  have hcount : (E \ J).card + (J \ E).card ≤ 2 * ell := by
    calc
      (E \ J).card + (J \ E).card = ((E \ J) ∪ (J \ E)).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ 2 * ell := by
        simpa only [Fin.val_zero, Nat.add_zero, Finset.symmDiff_def] using
          card_two_window_middle_symmDiff_le (L := L) (a := a) (b := b) p s (0 : Fin 2)
  have hKE : K ⊆ E := interval_mono (by omega) (by omega)
  have hKJ : K ⊆ J := interval_mono (by omega) (by omega)
  have hstart : a + 2 * ell < L := by omega
  have hKnonempty : K.Nonempty :=
    ⟨⟨a + 2 * ell, hstart⟩, mem_interval.mpr ⟨le_rfl, Nat.lt_succ_of_le hab⟩⟩
  exact ⟨hcount, hKE, hKJ, hKnonempty⟩

/-- Transferring at most twice the window half-width sites multiplies a
family cardinality by at most q to the power four times that half-width.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333. -/
private theorem card_changingMiddle_configuration_index_le
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (A B : Finset V) {q ell : ℕ} (hq : 1 ≤ q)
    (hAB : A.card + B.card ≤ 2 * ell) :
    Fintype.card (ι × ((A → Fin q) × (A → Fin q)) ×
      ((B → Fin q) × (B → Fin q))) ≤ Fintype.card ι * q ^ (4 * ell) := by
  calc
    Fintype.card (ι × ((A → Fin q) × (A → Fin q)) ×
        ((B → Fin q) × (B → Fin q))) =
        Fintype.card ι * ((q ^ A.card * q ^ A.card) *
          (q ^ B.card * q ^ B.card)) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    _ = Fintype.card ι * q ^ (A.card + A.card + (B.card + B.card)) := by
      rw [← pow_add, ← pow_add, ← pow_add]
    _ = Fintype.card ι * q ^ (2 * (A.card + B.card)) := by
      have h : A.card + A.card + (B.card + B.card) = 2 * (A.card + B.card) := by
        rw [two_mul]
        ac_rfl
      rw [h]
    _ ≤ Fintype.card ι * q ^ (4 * ell) := by
      have hexp : 2 * (A.card + B.card) ≤ 4 * ell := by
        calc
          2 * (A.card + B.card) ≤ 2 * (2 * ell) := Nat.mul_le_mul_left 2 hAB
          _ = 4 * ell := by rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (pow_le_pow_right' hq hexp)

/-- Under the original two-window geometry, the prescribed middle interval
has one fixed MPO family for all exterior coefficient families. The overlap
and all endpoint bounds are derived, rather than supplied as extra
hypotheses. The number of operators grows by at most q^(4 ell), and each
individual open-boundary bond bound becomes max(1,D_t). Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1332–1333; this does not assert the
source-sharp bond bound or algorithmic conclusion. -/
private theorem selected_middle_fixed_mpo_family
    {L a b ell q : ℕ} {ι : Type*} [Fintype ι]
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) (hq : 0 < q)
    (V : ι → Matrix
      (FiniteProduct.Configuration (fun _ : Fin L ↦ Fin q)
        (interval L (a + p.val + 1) (b + s.val + 1)))
      (FiniteProduct.Configuration (fun _ : Fin L ↦ Fin q)
        (interval L (a + p.val + 1) (b + s.val + 1))) ℂ)
    (D : ι → ℕ)
    (hV : ∀ t,
      let eE := intervalShiftOrderIso
        ((selected_middle_fixed_interval_bounds hab hb p s).1)
        ((selected_middle_fixed_interval_bounds hab hb p s).2.1)
      IsOpenMPS ((b + s.val + 1) - (a + p.val + 1)) (q * q) (D t) (fun x ↦
        V t (fun z ↦ (finProdFinEquiv.symm (x (eE.symm z))).1)
          (fun z ↦ (finProdFinEquiv.symm (x (eE.symm z))).2))) :
    let β := fun _ : Fin L ↦ Fin q
    let E := interval L (a + p.val + 1) (b + s.val + 1)
    let J := interval L (a + ell) (b + ell + 1)
    let A := E \ J
    let B := J \ E
    let I := ι × (FiniteProduct.Configuration β A × FiniteProduct.Configuration β A) ×
      (FiniteProduct.Configuration β B × FiniteProduct.Configuration β B)
    let W := FiniteProduct.changingRegionalMiddleFamily β E J V
    let eJ := intervalShiftOrderIso
      ((selected_middle_fixed_interval_bounds hab hb p s).2.2.1)
      ((selected_middle_fixed_interval_bounds hab hb p s).2.2.2.1)
    Fintype.card I ≤ Fintype.card ι * q ^ (4 * ell) ∧
      (∀ r : I, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
          (max 1 (D r.1)) (fun x ↦
        W r (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).1)
          (fun z ↦ (finProdFinEquiv.symm (x (eJ.symm z))).2))) ∧
      ∀ M : ι → Matrix (FiniteProduct.Configuration β Eᶜ)
          (FiniteProduct.Configuration β Eᶜ) ℂ,
        ∃ Mnew : I → Matrix (FiniteProduct.Configuration β Jᶜ)
            (FiniteProduct.Configuration β Jᶜ) ℂ,
          (∑ t, M t ⊗ₖ V t).submatrix
            ((FiniteProduct.splitEquiv β E).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv β E).trans (Equiv.prodComm _ _)) =
          (∑ r, Mnew r ⊗ₖ W r).submatrix
            ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
            ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)) := by
  have hbounds := selected_middle_fixed_interval_bounds hab hb p s
  obtain ⟨_hcard, hW, hglobal⟩ :=
    changingRegionalMiddleFamily_mpo_and_global_decomposition hq
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1 hbounds.2.2.2.2.le V D hV
  have hsites := (selected_middle_central_interval_geometry hab hb p s).1
  have hcard := card_changingMiddle_configuration_index_le (ι := ι)
    (interval L (a + p.val + 1) (b + s.val + 1) \
      interval L (a + ell) (b + ell + 1))
    (interval L (a + ell) (b + ell + 1) \
      interval L (a + p.val + 1) (b + s.val + 1))
    (Nat.succ_le_iff.mpr hq) hsites
  exact ⟨hcard, hW, hglobal⟩

/-- One common family on the prescribed middle interval for the actual
fixed-frequency coefficients. The selected crossings, ordinary weights and
supplied middle tensors are fixed before this family; the supported exterior
Hamiltonians and polynomial weights are supplied afterwards. The family is
exactly the canonical change of interval of the common natural family.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333;
the degree-specific general open-boundary estimate is retained, without a
source-sharp bond bound or algorithmic assertion. -/
private noncomputable def actualCommonFixedMiddleMPOFamilyStatement
    {L q ell a b B : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (_hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (_hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) (_hq : 0 < q)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ)
    (z : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℂ)
    (k i j : ℕ) : Prop :=
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let Nnat := (b + s.val + 1) - (a + p.val + 1)
  let aNat := (a + 2 * ell + 1) - (a + p.val + 1)
  let Lnat := b - (a + 2 * ell + 1)
  let eE := intervalShiftOrderIso
    (show a + p.val + 1 ≤ b + s.val + 1 by have hp := p.isLt; omega)
    (show b + s.val + 1 ≤ L by have hs := s.isLt; omega)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega)
    (show b + 1 ≤ L by have hs := s.isLt; omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
    (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
  let RetDim := Fintype.card (MPOTensor.actualAffineRetainedConfig Nnat Lnat q aNat)
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.1
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.2.1
  let oldBound := Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
    (k + 1) * RetDim ^ 2
  ∃ (n : ℕ) (deg : Fin n → Fin (k + 1))
    (V : Fin n → Matrix (Fin Nnat → Fin q) (Fin Nnat → Fin q) ℂ),
    let β := fun _ : Fin L ↦ Fin q
    let Vphys := fun r ↦ (V r).submatrix (fun σ : E → Fin q ↦ σ ∘ eE)
      (fun σ : E → Fin q ↦ σ ∘ eE)
    let I := Fin n ×
      (FiniteProduct.Configuration β (E \ J) × FiniteProduct.Configuration β (E \ J)) ×
      (FiniteProduct.Configuration β (J \ E) × FiniteProduct.Configuration β (J \ E))
    let W := FiniteProduct.changingRegionalMiddleFamily β E J Vphys
    Fintype.card I ≤ oldBound * q ^ (4 * ell) ∧
      (∀ r : I, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        (max 1 ((B ^ (deg r.1).val) ^ 2)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      (∀ r : I,
        ∃ Cr : Matrix (Fin (B ^ (deg r.1).val)) (Fin (B ^ (deg r.1).val)) ℂ,
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q (B ^ (deg r.1).val),
          (W r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        let Dphys := ∑ t ∈ O, z t • F t
        ∀ cPoly : Fin (k + 1) → ℂ,
          ∃ Mnew : I → Matrix (FiniteProduct.Configuration β Jᶜ)
              (FiniteProduct.Configuration β Jᶜ) ℂ,
            (∑ r : Fin (k + 1),
              cPoly r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j) =
                (∑ r, Mnew r ⊗ₖ W r).submatrix
                  ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
                  ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))

/-- The actual coefficient family admits a single decomposition over the
prescribed middle and its actual complement. The original two-window
hypotheses imply all interval and overlap bounds internally. The canonical
middle family is chosen before every supported exterior Hamiltonian and
polynomial weight. Its cardinality is at most the previous common-family
bound times `q ^ (4 * ell)`, and a term of degree `t` has open-boundary bound
`max 1 ((B ^ t) ^ 2)`. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333; no complete source proposition, sharp bond
estimate or running-time bound is asserted. -/
private theorem exists_common_fixed_middle_twoMarkerCoefficient_mpo_family
    {L q ell a b B : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) (hq : 0 < q)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ)
    (z : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℂ)
    (k i j : ℕ) :
    actualCommonFixedMiddleMPOFamilyStatement
      (L := L) (q := q) (ell := ell) (a := a) (b := b) (B := B)
      WL WR hleft hright hab hb p s hq Acore C0 z k i j := by
  classical
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let T := interval L 0 (a + p.val + 1)
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let hTE : Disjoint T E := disjoint_interval_interval (L := L) 0 _ _
  let Nnat := (b + s.val + 1) - (a + p.val + 1)
  let aNat := (a + 2 * ell + 1) - (a + p.val + 1)
  let Lnat := b - (a + 2 * ell + 1)
  let eE := intervalShiftOrderIso
    (show a + p.val + 1 ≤ b + s.val + 1 by have hp := p.isLt; omega)
    (show b + s.val + 1 ≤ L by have hs := s.isLt; omega)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega)
    (show b + 1 ≤ L by have hs := s.isLt; omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
    (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
  let RetDim := Fintype.card (MPOTensor.actualAffineRetainedConfig Nnat Lnat q aNat)
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.1
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.2.1
  let oldBound := Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
    (k + 1) * RetDim ^ 2
  obtain ⟨n, deg, V, hcount, hV, htrace, hdecomp⟩ :=
    exists_common_physical_twoMarkerCoefficient_mpo_family
      WL WR hleft hright hab hb p s Acore C0 z k i j
  let β := fun _ : Fin L ↦ Fin q
  let Vphys := fun r ↦ (V r).submatrix (fun σ : E → Fin q ↦ σ ∘ eE)
    (fun σ : E → Fin q ↦ σ ∘ eE)
  let I := Fin n ×
    (FiniteProduct.Configuration β (E \ J) × FiniteProduct.Configuration β (E \ J)) ×
    (FiniteProduct.Configuration β (J \ E) × FiniteProduct.Configuration β (J \ E))
  let W := FiniteProduct.changingRegionalMiddleFamily β E J Vphys
  have hcancel (σ : Fin Nnat → Fin q) : (σ ∘ eE.symm) ∘ eE = σ := by
    funext v
    exact congrArg σ (eE.symm_apply_apply v)
  have hread (r : Fin n) (σ τ : Fin Nnat → Fin q) :
      Vphys r (σ ∘ eE.symm) (τ ∘ eE.symm) = V r σ τ := by
    change V r ((σ ∘ eE.symm) ∘ eE) ((τ ∘ eE.symm) ∘ eE) = _
    rw [hcancel σ, hcancel τ]
  have hVphys (r : Fin n) :
      IsOpenMPS Nnat (q * q) ((B ^ (deg r).val) ^ 2) (fun w ↦ Vphys r
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eE.symm v))).1)
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eE.symm v))).2)) := by
    have hf :
        (fun w : Fin Nnat → Fin (q * q) ↦ Vphys r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eE.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eE.symm v))).2)) =
        (fun w : Fin Nnat → Fin (q * q) ↦ V r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2)) := by
      funext w
      exact hread r
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2)
    rw [hf]
    exact hV r
  obtain ⟨hcard, hW, hglobal⟩ := selected_middle_fixed_mpo_family
    hab hb p s hq Vphys (fun r ↦ (B ^ (deg r).val) ^ 2) hVphys
  have hTracePhys (r : Fin n) :
      ∃ Cr : Matrix (Fin (B ^ (deg r).val)) (Fin (B ^ (deg r).val)) ℂ,
      ∃ Ar : Fin Nnat → MPOTensor q (B ^ (deg r).val),
        (Vphys r).submatrix (fun σ z ↦ σ (eE.symm z))
          (fun σ z ↦ σ (eE.symm z)) = MPOTensor.traceChainOperator Ar Cr := by
    obtain ⟨Cr, Ar, hAr⟩ := htrace r
    refine ⟨Cr, Ar, ?_⟩
    ext σ τ
    exact (hread r σ τ).trans (congrFun (congrFun hAr σ) τ)
  have hbounds := selected_middle_fixed_interval_bounds hab hb p s
  obtain ⟨_hTraceCard, hTraceW, _hTraceGlobal⟩ :=
    changingRegionalMiddleFamily_trace_and_global_decomposition hq
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1 hbounds.2.2.2.2.le
      Vphys (fun r ↦ B ^ (deg r).val) hTracePhys
  have hcard' : Fintype.card I ≤ n * q ^ (4 * ell) := by
    simpa only [Fintype.card_fin] using hcard
  have hcountNew : Fintype.card I ≤ oldBound * q ^ (4 * ell) :=
    hcard'.trans (Nat.mul_le_mul_right (q ^ (4 * ell)) hcount)
  refine ⟨n, deg, V, hcountNew, hW, hTraceW, ?_⟩
  intro PL PR hPL hPR F Dphys cPoly
  obtain ⟨B_out, hB_out⟩ := hdecomp PL PR hPL hPR cPoly
  let X := ∑ r : Fin (k + 1),
    cPoly r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j
  obtain ⟨M, hM⟩ := exists_regional_exterior_of_natural_threeSplit_decomposition
    T E hTE eE.toEquiv X V B_out hB_out
  obtain ⟨Mnew, hnew⟩ := hglobal M
  exact ⟨Mnew, hM.trans hnew⟩

/-- The common-family bound after passage to the prescribed interval has an
explicit low-frequency estimate. The additional matrix-unit labels number
at most `q ^ (4 * ell)`. Positivity of the window length follows
from the selected crossing index. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333; this is a cardinal estimate alone and makes
no assertion about a sharp bond dimension or running time. -/
theorem actual_common_fixed_middle_mpo_card_low_frequency_le
    {L a b ell q k i j n : ℕ}
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (hi : i ≤ k / (2 * ell)) (hj : j ≤ k / (2 * ell))
    (hcount : n ≤ Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
      (k + 1) * Fintype.card (MPOTensor.actualAffineRetainedConfig
        ((b + s.val + 1) - (a + p.val + 1))
        (b - (a + 2 * ell + 1)) q
        ((a + 2 * ell + 1) - (a + p.val + 1))) ^ 2 * q ^ (4 * ell)) :
    n ≤ (q * k) ^ (24 * ell + 4 * (k / ell)) := by
  let oldBound := Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
    (k + 1) * Fintype.card (MPOTensor.actualAffineRetainedConfig
      ((b + s.val + 1) - (a + p.val + 1))
      (b - (a + 2 * ell + 1)) q
      ((a + 2 * ell + 1) - (a + p.val + 1))) ^ 2
  have hell : 1 ≤ ell := by
    have hp := p.isLt
    omega
  have hold : oldBound ≤ (q * (k + 1)) ^ (8 * ell + 2 * (i + j) + 2) :=
    actual_common_physical_mpo_card_le (n := oldBound)
      hab hb p s (by omega) hk (le_refl _)
  have hlow : oldBound ≤ (q * k) ^ (20 * ell + 4 * (k / ell)) :=
    actual_common_physical_mpo_card_low_frequency_le hq hk hell hi hj hold
  have hbase : q ≤ q * k := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hk
  calc
    n ≤ oldBound * q ^ (4 * ell) := hcount
    _ ≤ (q * k) ^ (20 * ell + 4 * (k / ell)) * (q * k) ^ (4 * ell) :=
      Nat.mul_le_mul hlow (Nat.pow_le_pow_left hbase _)
    _ = (q * k) ^ (24 * ell + 4 * (k / ell)) := by
      rw [← pow_add]
      congr 1
      omega

/-- The degree-specific bound after changing the middle interval is at most a
single bound for all degrees up to `k`. The maximum retains zero virtual
dimensions and degree zero. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333; the exponent is the general square bound,
not the source-sharp virtual dimension. -/
private theorem max_one_degree_square_le_uniform {B t k : ℕ} (ht : t ≤ k) :
    max 1 ((B ^ t) ^ 2) ≤ (max 1 B) ^ (2 * k) := by
  have hpos : 0 < max 1 B := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 B)
  have hpow : B ^ t ≤ (max 1 B) ^ k :=
    (Nat.pow_le_pow_left (le_max_right 1 B) t).trans (Nat.pow_le_pow_right hpos ht)
  refine max_le (Nat.one_le_pow (2 * k) (max 1 B) hpos) ?_
  calc
    (B ^ t) ^ 2 ≤ ((max 1 B) ^ k) ^ 2 := Nat.pow_le_pow_left hpow 2
    _ = (max 1 B) ^ (2 * k) := by
      rw [← Nat.pow_mul, Nat.mul_comm k 2]

/-- Every degree-specific middle factor has the same coarse open-boundary
bound when its degree is at most `k`. Only the existing internal-cut-rank
criterion is used to enlarge the bound; the represented coefficient function
is unchanged. Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1311–1333; no sharp virtual dimension or complexity estimate is asserted. -/
private theorem IsOpenMPS.uniform_middle_degree_bound {N q B t k : ℕ}
    {ψ : (Fin N → Fin q) → ℂ}
    (hψ : IsOpenMPS N q (max 1 ((B ^ t) ^ 2)) ψ) (ht : t ≤ k) :
    IsOpenMPS N q ((max 1 B) ^ (2 * k)) ψ := by
  let Φ : EuclideanSpace ℂ (Fin N → Fin q) := WithLp.toLp 2 ψ
  have hΦ : IsOpenMPS N q (max 1 ((B ^ t) ^ 2)) (fun x ↦ Φ x) := hψ
  apply isOpenMPS_of_internal_cutMatrix_rank_le Φ
  intro c hc0 hcN
  exact (hΦ.rank_cutMatrix_le hc0 hcN).trans (max_one_degree_square_le_uniform ht)

/-- The finite union of the actual fixed-middle families is common to all
supported exterior Hamiltonians and all polynomial coefficient arrays. Its
carrier is the dependent sum of the canonical node carriers. The cardinal
bound grows by the number of nodes, while every term has the common bound
`(max 1 B) ^ (2 * k)`, including zero virtual dimension and degree zero.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333;
no interpolation identity, complete source proposition, sharp bond estimate
or running-time bound is asserted. -/
theorem exists_common_fixed_middle_grid_mpo_family
    {ζ : Type*} [Fintype ζ] {L q ell a b B : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) (hq : 0 < q)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ)
    (z : ζ → ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℂ)
    (k i j : ℕ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let Nnat := (b + s.val + 1) - (a + p.val + 1)
  let aNat := (a + 2 * ell + 1) - (a + p.val + 1)
  let Lnat := b - (a + 2 * ell + 1)
  let eE := intervalShiftOrderIso
    (show a + p.val + 1 ≤ b + s.val + 1 by have hp := p.isLt; omega)
    (show b + s.val + 1 ≤ L by have hs := s.isLt; omega)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega)
    (show b + 1 ≤ L by have hs := s.isLt; omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
    (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
  let RetDim := Fintype.card (MPOTensor.actualAffineRetainedConfig Nnat Lnat q aNat)
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.1
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.2.1
  let oldBound := Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
    (k + 1) * RetDim ^ 2
  ∃ (n : ζ → ℕ) (_deg : (u : ζ) → Fin (n u) → Fin (k + 1))
    (V : (u : ζ) → Fin (n u) → Matrix (Fin Nnat → Fin q) (Fin Nnat → Fin q) ℂ),
    let β := fun _ : Fin L ↦ Fin q
    let Vphys := fun (u : ζ) r ↦ (V u r).submatrix
      (fun σ : E → Fin q ↦ σ ∘ eE) (fun σ : E → Fin q ↦ σ ∘ eE)
    let I := fun u : ζ ↦ Fin (n u) ×
      (FiniteProduct.Configuration β (E \ J) × FiniteProduct.Configuration β (E \ J)) ×
      (FiniteProduct.Configuration β (J \ E) × FiniteProduct.Configuration β (J \ E))
    let W := fun u : ζ ↦ FiniteProduct.changingRegionalMiddleFamily β E J (Vphys u)
    let Iall := Σ u : ζ, I u
    let Wall := fun r : Iall ↦ W r.1 r.2
    Fintype.card Iall ≤ Fintype.card ζ * oldBound * q ^ (4 * ell) ∧
      (∀ r : Iall, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ Wall r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      (∀ r : Iall, ∃ D : ℕ, D ≤ (max 1 B) ^ k ∧
        ∃ Cr : Matrix (Fin D) (Fin D) ℂ,
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q D,
          (Wall r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        let Dphys := fun u : ζ ↦ ∑ t ∈ O, z u t • F t
        ∀ c : ζ → Fin (k + 1) → ℂ,
          ∃ M : Iall → Matrix (FiniteProduct.Configuration β Jᶜ)
              (FiniteProduct.Configuration β Jᶜ) ℂ,
            (∑ u : ζ, ∑ r : Fin (k + 1),
              c u r • twoMarkerCoefficient (Dphys u) (WL p) (WR s) r.val i j) =
                (∑ r, M r ⊗ₖ Wall r).submatrix
                  ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
                  ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)) := by
  classical
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let Nnat := (b + s.val + 1) - (a + p.val + 1)
  let aNat := (a + 2 * ell + 1) - (a + p.val + 1)
  let Lnat := b - (a + 2 * ell + 1)
  let eE := intervalShiftOrderIso
    (show a + p.val + 1 ≤ b + s.val + 1 by have hp := p.isLt; omega)
    (show b + s.val + 1 ≤ L by have hs := s.isLt; omega)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega)
    (show b + 1 ≤ L by have hs := s.isLt; omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
    (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
  let RetDim := Fintype.card (MPOTensor.actualAffineRetainedConfig Nnat Lnat q aNat)
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.1
    (selected_middle_fixed_interval_bounds hab hb p s).2.2.2.1
  let oldBound := Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
    (k + 1) * RetDim ^ 2
  have hfamily (u : ζ) := exists_common_fixed_middle_twoMarkerCoefficient_mpo_family
    WL WR hleft hright hab hb p s hq Acore C0 (z u) k i j
  choose n deg V hcard hW hTrace hdecomp using hfamily
  let β := fun _ : Fin L ↦ Fin q
  let Vphys := fun (u : ζ) r ↦ (V u r).submatrix
    (fun σ : E → Fin q ↦ σ ∘ eE) (fun σ : E → Fin q ↦ σ ∘ eE)
  let I := fun u : ζ ↦ Fin (n u) ×
    (FiniteProduct.Configuration β (E \ J) × FiniteProduct.Configuration β (E \ J)) ×
    (FiniteProduct.Configuration β (J \ E) × FiniteProduct.Configuration β (J \ E))
  let W := fun u : ζ ↦ FiniteProduct.changingRegionalMiddleFamily β E J (Vphys u)
  let Iall := Σ u : ζ, I u
  let Wall := fun r : Iall ↦ W r.1 r.2
  have hcountAll : Fintype.card Iall ≤ Fintype.card ζ * oldBound * q ^ (4 * ell) := by
    calc
      Fintype.card Iall = ∑ u : ζ, Fintype.card (I u) := Fintype.card_sigma
      _ ≤ ∑ _u : ζ, oldBound * q ^ (4 * ell) := by
        apply Finset.sum_le_sum
        intro u _hu
        exact hcard u
      _ = Fintype.card ζ * oldBound * q ^ (4 * ell) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.cast_id, Nat.mul_assoc]
  have hWall (r : Iall) :
      IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ Wall r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2)) := by
    exact (hW r.1 r.2).uniform_middle_degree_bound
      (Nat.le_of_lt_succ (deg r.1 r.2.1).isLt)
  have hTraceAll (r : Iall) : ∃ D : ℕ, D ≤ (max 1 B) ^ k ∧
      ∃ Cr : Matrix (Fin D) (Fin D) ℂ,
      ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q D,
        (Wall r).submatrix (fun σ z ↦ σ (eJ.symm z))
          (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr := by
    obtain ⟨Cr, Ar, hAr⟩ := hTrace r.1 r.2
    refine ⟨B ^ (deg r.1 r.2.1).val, ?_, Cr, Ar, hAr⟩
    have hpos : 0 < max 1 B := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 B)
    exact (Nat.pow_le_pow_left (le_max_right 1 B) _).trans
      (Nat.pow_le_pow_right hpos (Nat.le_of_lt_succ (deg r.1 r.2.1).isLt))
  refine ⟨n, deg, V, hcountAll, hWall, hTraceAll, ?_⟩
  intro PL PR hPL hPR F Dphys c
  choose M hM using fun u : ζ ↦ hdecomp u PL PR hPL hPR (c u)
  refine ⟨(fun r : Iall ↦ M r.1 r.2), ?_⟩
  calc
    (∑ u : ζ, ∑ r : Fin (k + 1),
      c u r • twoMarkerCoefficient (Dphys u) (WL p) (WR s) r.val i j) =
        ∑ u : ζ, (∑ r : I u, M u r ⊗ₖ W u r).submatrix
          ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
          ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)) := by
      apply Finset.sum_congr rfl
      intro u _hu
      exact hM u
    _ = _ := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.submatrix_apply, Fintype.sum_sigma]
      rfl

end TNLean.MPS.AreaLaw

end
