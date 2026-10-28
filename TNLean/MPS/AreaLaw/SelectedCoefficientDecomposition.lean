/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SelectedMiddleData
import TNLean.Algebra.TwoMarkerMiddleFactors
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Prescribed middle factors of selected two-marker coefficients

The two exterior regions are grouped together while the selected middle
region is kept as the other tensor factor. The ordinary interpolation
weights enter the middle sum, and the two selected crossings remain
unweighted.

The two windows, central operator, weights, degree and crossing frequencies
determine one prescribed middle family. It is retained for every supported
pair of exterior bulk operators and every scalar combination of degrees
through the supplied cutoff. Only the exterior coefficient matrices depend
on these later choices.

## References

Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The two exterior tensor factors are grouped together, with the middle
factor retained as the second tensor factor. This only rearranges the
three regional configuration types; no sites within a region are permuted.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
def exteriorMiddleEquiv (l m n : Type*) :
    ((l × m) × n) ≃ ((l × n) × m) :=
  (Equiv.prodAssoc l m n).trans
    ((Equiv.prodCongr (Equiv.refl l) (Equiv.prodComm m n)).trans
      (Equiv.prodAssoc l n m).symm)

open Classical in
/-- Regrouping the three regions gives the ordinary tensor sum and preserves
the prescribed middle factors of both crossings.
ALVV, arXiv:1602.08828v2, equation H-mid-cut, lines 810–821,
and Proposition 5.7, lines 1324–1333. -/
private theorem three_region_reindex_prescribed_factors
    {l m n : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]
    {rU rV : ℕ}
    (HL : Matrix l l ℂ) (HM : Matrix m m ℂ) (HR : Matrix n n ℂ)
    (AL : Fin rU → Matrix l l ℂ) (UM : Fin rU → Matrix m m ℂ)
    (VM : Fin rV → Matrix m m ℂ) (BR : Fin rV → Matrix n n ℂ) :
    let e := exteriorMiddleEquiv l m n
    let D := (HL ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix n n ℂ) +
      ((1 : Matrix l l ℂ) ⊗ₖ HM) ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix (l × m) (l × m) ℂ) ⊗ₖ HR
    let U := (∑ z, AL z ⊗ₖ UM z) ⊗ₖ (1 : Matrix n n ℂ)
    let V := ((1 : Matrix l l ℂ) ⊗ₖ (∑ z, VM z ⊗ₖ BR z)).reindex
      (Equiv.prodAssoc l m n).symm (Equiv.prodAssoc l m n).symm
    D.reindex e e =
        (HL ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix l l ℂ) ⊗ₖ HR) ⊗ₖ
            (1 : Matrix m m ℂ) +
          (1 : Matrix (l × n) (l × n) ℂ) ⊗ₖ HM ∧
      U.reindex e e = ∑ z, (AL z ⊗ₖ (1 : Matrix n n ℂ)) ⊗ₖ UM z ∧
      V.reindex e e = ∑ z, ((1 : Matrix l l ℂ) ⊗ₖ BR z) ⊗ₖ VM z := by
  intro e D U V
  refine ⟨?_, ?_, ?_⟩ <;>
    ext ⟨⟨a, c⟩, b⟩ ⟨⟨a', c'⟩, b'⟩ <;>
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> by_cases hc : c = c' <;>
    simp [e, D, U, V, exteriorMiddleEquiv, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.sum_apply,
      Finset.mul_sum, ha, hb, hc, mul_comm, add_right_comm]

/-- A ring homomorphism commutes with extracting the two marked coefficients.
The order of every noncommutative product is retained.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem map_twoMarkerCoefficient
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (D U V : R) (r i j : ℕ) :
    f (twoMarkerCoefficient D U V r i j) =
      twoMarkerCoefficient (f D) (f U) (f V) r i j := by
  let F : Polynomial (Polynomial R) :=
    Polynomial.C (Polynomial.C D + Polynomial.C V * Polynomial.X) +
      Polynomial.C (Polynomial.C U) * Polynomial.X
  let G : Polynomial (Polynomial S) :=
    Polynomial.C (Polynomial.C (f D) + Polynomial.C (f V) * Polynomial.X) +
      Polynomial.C (Polynomial.C (f U)) * Polynomial.X
  have hFG : F.map (Polynomial.mapRingHom f) = G := by
    simp only [F, G, Polynomial.map_add, Polynomial.map_C,
      Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_X]
  have hpow : (F ^ r).map (Polynomial.mapRingHom f) = G ^ r := by
    rw [Polynomial.map_pow, hFG]
  have hcoeff := congrArg
    (fun P : Polynomial (Polynomial S) ↦ (P.coeff i).coeff j) hpow
  simpa only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, F, G,
    twoMarkerCoefficient] using hcoeff

open Classical in
/-- Regrouping commutes with a scalar sum of the two marked coefficients.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem reindex_sum_twoMarkerCoefficient
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β)
    (D U V : Matrix α α ℂ) (k i j : ℕ) (c : Fin (k + 1) → ℂ) :
    (∑ r : Fin (k + 1), c r • twoMarkerCoefficient D U V r.val i j).reindex e e =
      ∑ r : Fin (k + 1), c r •
        twoMarkerCoefficient (D.reindex e e) (U.reindex e e) (V.reindex e e) r.val i j := by
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
      (∑ r : Fin (k + 1), c r • twoMarkerCoefficient D U V r.val i j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul]
  exact congrArg (fun X ↦ c r • X)
    (map_twoMarkerCoefficient (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom D U V r.val i j)

open Classical in
/-- All scalar combinations through degree k are sums with the same prescribed middle
products. Only its two exterior factors are combined.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333.
The family depends on HM, UM, VM and the degree and frequencies, and is
independent of HL, HR, AL, BR and the scalar coefficients c. -/
private theorem exists_sum_three_region_twoMarkerCoefficient_decomposition_with_decidable
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] {rU rV : ℕ}
    (HL : Matrix l l ℂ) (HM : Matrix m m ℂ) (HR : Matrix n n ℂ)
    (AL : Fin rU → Matrix l l ℂ) (UM : Fin rU → Matrix m m ℂ)
    (VM : Fin rV → Matrix m m ℂ) (BR : Fin rV → Matrix n n ℂ)
    (k i j : ℕ) (c : Fin (k + 1) → ℂ) :
    let e := exteriorMiddleEquiv l m n
    let D := (HL ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix n n ℂ) +
      ((1 : Matrix l l ℂ) ⊗ₖ HM) ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix (l × m) (l × m) ℂ) ⊗ₖ HR
    let U := (∑ z, AL z ⊗ₖ UM z) ⊗ₖ (1 : Matrix n n ℂ)
    let V := ((1 : Matrix l l ℂ) ⊗ₖ (∑ z, VM z ⊗ₖ BR z)).reindex
      (Equiv.prodAssoc l m n).symm (Equiv.prodAssoc l m n).symm
    ∃ B : TwoMarkerMiddleIndex k i j rU rV → Matrix (l × n) (l × n) ℂ,
      (∑ r : Fin (k + 1), c r • twoMarkerCoefficient D U V r.val i j).reindex e e =
        ∑ p, B p ⊗ₖ twoMarkerMiddleFactor HM UM VM p := by
  intro e D U V
  obtain ⟨hD, hU, hV⟩ := three_region_reindex_prescribed_factors HL HM HR AL UM VM BR
  obtain ⟨B, hB⟩ := exists_sum_twoMarkerCoefficient_decomposition
    (HL ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix l l ℂ) ⊗ₖ HR) HM
    (fun z ↦ AL z ⊗ₖ (1 : Matrix n n ℂ)) UM
    (fun z ↦ (1 : Matrix l l ℂ) ⊗ₖ BR z) VM k i j c
  refine ⟨B, Eq.trans ?_ hB⟩
  have htrans := reindex_sum_twoMarkerCoefficient e D U V k i j c
  rw [hD, hU, hV] at htrans
  exact htrans

/-- One physical middle family works for all supported exterior bulk terms
and all scalar polynomial coefficients. The ordinary interpolation weights
are retained, while the two selected crossings are unweighted, as in QICLean's
weighted-frequency coefficient identity. ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem exists_physical_twoMarkerCoefficient_prescribed_middle_decomposition
    {L q ℓ a b : ℕ}
    (WL WR : Fin (2 * ℓ) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ))
    (M : Matrix ((interval L (a + 2 * ℓ) (b + 1)) → Fin q)
      ((interval L (a + 2 * ℓ) (b + 1)) → Fin q) ℂ)
    (z : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℂ)
    (k i j : ℕ) :
    let K := interval L (a + 2 * ℓ) (b + 1)
    let T := interval L 0 (a + p.val + 1)
    let E := interval L (a + p.val + 1) (b + s.val + 1)
    let hTE : Disjoint T E := disjoint_interval_interval (L := L) 0 _ _
    let g := threeSplit q T E hTE
    let e := exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)
    let Z := interval L (a + 2 * ℓ + 1) b
    let C : Finset E := Finset.univ.filter (fun x : E ↦ x.val ∉ Z)
    let hKE : K ⊆ E := (core_and_strict_core_subset_selected_middle
      (L := L) (a := a) (b := b) p s).1
    let ME := QuantumCircuit.embedOp (fun x : K ↦ (⟨x.val, hKE x.property⟩ : E)) M
    let Pmid := QuantumCircuit.embedOp (Subtype.val : K → Fin L) M
    let O : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :=
      (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
    let N := fun (e₀ : E) (t : Fin (q * q)) ↦
      QuantumCircuit.embedOp (fun _ : Fin 1 ↦ e₀)
        (Matrix.single
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm t).1)
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm t).2) (1 : ℂ))
    ∃ (eL eR : E) (A Kz : Matrix (E → Fin q) (E → Fin q) ℂ),
      eL.val.val = a + p.val + 1 ∧ eR.val.val = b + s.val ∧
      A = z (Sum.inr 1) • ME + Kz ∧ Entropy.IsSupportedOn Kz C ∧
      (∀ t, Entropy.IsSupportedOn (N eL t) C) ∧
      (∀ t, Entropy.IsSupportedOn (N eR t) C) ∧
      let Psi := fun f : TwoMarkerMiddleIndex k i j (q * q) (q * q) ↦
        twoMarkerMiddleFactor A (N eL) (N eR) f
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ℓ) L) →
        let F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        let Dphys := ∑ t ∈ O, z t • F t
        ∀ c : Fin (k + 1) → ℂ,
          ∃ B : TwoMarkerMiddleIndex k i j (q * q) (q * q) →
              Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
                ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ,
            (∑ r : Fin (k + 1),
                c r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j).reindex
                (g.trans e) (g.trans e) =
              ∑ f, B f ⊗ₖ Psi f := by
  classical
  intro K T E hTE g e Z C hKE ME Pmid O N
  obtain ⟨eL, eR, HM, UL, VR, AL, BR, heL, heR, _hactual, hUL, hVR,
      hAL, hBR, hNL, hNR, hweighted, hlate⟩ :=
    exists_physical_selected_window_fixed_middle_data
      WL WR hleft hright hab hb p s M
  let A : Matrix (E → Fin q) (E → Fin q) ℂ := ∑ t ∈ O, z t • HM t
  obtain ⟨Kz, hA, hKz⟩ := hweighted z
  refine ⟨eL, eR, A, Kz, heL, heR, hA, hKz, hNL, hNR, ?_⟩
  intro Psi PL PR hPL hPR F Dphys c
  obtain ⟨HL, HR, hlocal, _hLmid, _hRmid⟩ := hlate PL PR hPL hPR
  let Lz : Matrix (T → Fin q) (T → Fin q) ℂ := ∑ t ∈ O, z t • HL t
  let Rz : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ :=
    ∑ t ∈ O, z t • HR t
  let D₀ := (Lz ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
        (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ A) ⊗ₖ
        (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
      (1 : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ Rz
  let U₀ := (∑ t, AL t ⊗ₖ N eL t) ⊗ₖ
    (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)
  let V₀ := ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ
      (∑ t, N eR t ⊗ₖ BR t)).reindex
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm
  have hD : Dphys.reindex g g = D₀ := by
    calc
      _ = ∑ t ∈ O, z t • (F t).submatrix g.symm g.symm := by
        ext x y
        simp only [Dphys, Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.sum_apply, Matrix.smul_apply]
      _ = ∑ t ∈ O, z t •
          ((HL t ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM t) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR t) := by
        refine Finset.sum_congr rfl fun t ht ↦ ?_
        have htr : t ≠ Sum.inl (Sum.inr s) := (Finset.mem_erase.mp ht).1
        have htl : t ≠ Sum.inl (Sum.inl p) :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        rw [hlocal t htl htr]
      _ = D₀ := by
        let fullConfig := ((T → Fin q) × (E → Fin q)) × (↥(T ∪ E)ᶜ → Fin q)
        let outer : Matrix ((T → Fin q) × (E → Fin q))
            ((T → Fin q) × (E → Fin q)) ℂ →ₗ[ℂ] Matrix fullConfig fullConfig ℂ :=
          (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)).flip
            (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)
        let leftMap : Matrix (T → Fin q) (T → Fin q) ℂ →ₗ[ℂ]
            Matrix fullConfig fullConfig ℂ :=
          outer.comp ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)).flip
            (1 : Matrix (E → Fin q) (E → Fin q) ℂ))
        let middleMap : Matrix (E → Fin q) (E → Fin q) ℂ →ₗ[ℂ]
            Matrix fullConfig fullConfig ℂ :=
          outer.comp ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ))
            (1 : Matrix (T → Fin q) (T → Fin q) ℂ))
        let rightMap : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ →ₗ[ℂ]
            Matrix fullConfig fullConfig ℂ :=
          (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ))
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ)
        change (∑ t ∈ O, z t • (leftMap (HL t) + middleMap (HM t) + rightMap (HR t))) =
          leftMap (∑ t ∈ O, z t • HL t) + middleMap (∑ t ∈ O, z t • HM t) +
            rightMap (∑ t ∈ O, z t • HR t)
        simp only [smul_add, Finset.sum_add_distrib, map_sum, map_smul]
  have hU : (WL p).reindex g g = U₀ := by
    change (WL p).submatrix g.symm g.symm = _
    rw [hUL, hAL]
  have hV : (WR s).reindex g g = V₀ := by
    change (WR s).submatrix g.symm g.symm = _
    rw [hVR, hBR]
  obtain ⟨B, hB⟩ := exists_sum_three_region_twoMarkerCoefficient_decomposition_with_decidable
    Lz A Rz AL (N eL) (N eR) BR k i j c
  change (∑ r : Fin (k + 1), c r • twoMarkerCoefficient D₀ U₀ V₀ r.val i j).reindex e e =
    ∑ f, B f ⊗ₖ twoMarkerMiddleFactor A (N eL) (N eR) f at hB
  have hfirst := reindex_sum_twoMarkerCoefficient g Dphys (WL p) (WR s) k i j c
  rw [hD, hU, hV] at hfirst
  refine ⟨B, ?_⟩
  calc
    (∑ r : Fin (k + 1), c r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j).reindex
        (g.trans e) (g.trans e) =
      ((∑ r : Fin (k + 1), c r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j).reindex
        g g).reindex e e := by
      ext x y
      rfl
    _ = (∑ r : Fin (k + 1), c r • twoMarkerCoefficient D₀ U₀ V₀ r.val i j).reindex e e := by
      rw [hfirst]
    _ = ∑ f, B f ⊗ₖ Psi f := hB

end TNLean.MPS.AreaLaw

end
