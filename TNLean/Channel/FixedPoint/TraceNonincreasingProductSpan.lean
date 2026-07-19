/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.MaximalSupportBasic
import TNLean.Channel.FixedPoint.MeanErgodicAdjoint
import TNLean.Channel.FixedPoint.DirectSumBlockRetraction

/-!
# Trace preservation from fixed product generators

A positive trace-nonincreasing endomorphism is trace preserving when a
positive-length product family of its fixed points spans the identity.  The
mean-ergodic image of the identity has maximal support among fixed points.
Every product of fixed generators remains on that support; spanning the
identity therefore makes the mean-ergodic fixed point faithful.  The positive
trace-loss functional must then vanish.

This supplies the channel hypothesis used silently for the transported
vertical-sector composites in arXiv:1606.00608, Appendix C.4.  Lines
1974--1980 identify the fixed contraction generators, and lines 1980--1995
place them in the spanning argument.

## Main results

* `IsPositiveMap.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span`
* `IsPositiveMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span`

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.3 and
  Proposition 6.9.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.4,
  lines 1974--1980 and 1980--1995.
-/

open Filter Function Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {D : ℕ}

open Kraus

/-- A positive trace-nonincreasing endomorphism has a positive-definite fixed
point when the identity lies in the span of positive-length products of a
fixed family.

No product is assumed to be fixed.  The fixed factors lie on the support of
the mean-ergodic image of the identity, so their products do as well.  The
product-span hypothesis forces this support to be the identity.

This is the channel-hypothesis step used at arXiv:1606.00608, Appendix C.4.
Lines 1974--1980 supply the fixed contraction factors; lines 1980--1995
supply their spanning context. -/
private theorem
    IsPositiveMap.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span_fin
    {J : Type*}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T)
    (V : J → Matrix (Fin D) (Fin D) ℂ) (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, T (V j) = V j)
    (hOne : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J =>
        (List.ofFn fun t => V (x t)).prod)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosDef ∧ T ρ = ρ := by
  classical
  let hbounded := hT.hasBoundedOrbits_of_traceNonincreasing hTNI
  let ρ := LinearMap.meanErgodicProjection (𝕜 := ℂ)
    (E := Matrix (Fin D) (Fin D) ℂ) T hbounded 1
  obtain ⟨hρ, hρfixed, hMaxSupport⟩ :=
    hT.exists_maximalSupport_fixedPoint_of_hasBoundedOrbits hbounded
  let Q := stationaryProj hρ
  have hQidem : Q * Q = Q := (isOrthogonalProjection_stationaryProj hρ).2
  have hVsupport (j : J) : Q * V j * Q = V j := hMaxSupport _ (hFixed j)
  have hVleft (j : J) : Q * V j = V j := by
    calc
      Q * V j = Q * (Q * V j * Q) := by rw [hVsupport j]
      _ = (Q * Q) * V j * Q := by simp [Matrix.mul_assoc]
      _ = Q * V j * Q := by rw [hQidem]
      _ = V j := hVsupport j
  have hVright (j : J) : V j * Q = V j := by
    calc
      V j * Q = (Q * V j * Q) * Q := by rw [hVsupport j]
      _ = Q * V j * (Q * Q) := by simp [Matrix.mul_assoc]
      _ = Q * V j * Q := by rw [hQidem]
      _ = V j := hVsupport j
  have hProdAbsorb (l : List J) (hl : l ≠ []) :
      Q * (l.map V).prod = (l.map V).prod ∧
        (l.map V).prod * Q = (l.map V).prod := by
    induction l with
    | nil => exact (hl rfl).elim
    | cons a l ih =>
        constructor
        · simp only [List.map_cons, List.prod_cons]
          rw [← Matrix.mul_assoc, hVleft a]
        · cases l with
          | nil => simpa using hVright a
          | cons b l =>
              have ihtail := (ih (by simp)).2
              simp only [List.map_cons, List.prod_cons] at ihtail ⊢
              calc
                (V a * (V b * (List.map V l).prod)) * Q =
                    V a * ((V b * (List.map V l).prod) * Q) :=
                  Matrix.mul_assoc _ _ _
                _ = V a * (V b * (List.map V l).prod) := by rw [ihtail]
  have hProductSupport (x : Fin L → J) :
      Q * (List.ofFn fun t => V (x t)).prod * Q =
        (List.ofFn fun t => V (x t)).prod := by
    have hne : List.ofFn x ≠ [] := by
      intro hempty
      have hlen := congrArg List.length hempty
      simp only [List.length_ofFn, List.length_nil] at hlen
      omega
    have habsorb := hProdAbsorb (List.ofFn x) hne
    rw [List.map_ofFn] at habsorb
    have hfun : V ∘ x = fun t => V (x t) := rfl
    rw [hfun] at habsorb
    calc
      Q * (List.ofFn fun t => V (x t)).prod * Q =
          (List.ofFn fun t => V (x t)).prod * Q := by rw [habsorb.1]
      _ = (List.ofFn fun t => V (x t)).prod := habsorb.2
  have hOneSupport : Q * (1 : Matrix (Fin D) (Fin D) ℂ) * Q = 1 := by
    exact Submodule.span_induction (p := fun X _ => Q * X * Q = X)
      (fun Y hY => by
        obtain ⟨x, rfl⟩ := hY
        exact hProductSupport x)
      (by simp)
      (fun X Y _ _ hX hY => by
        rw [Matrix.mul_add, Matrix.add_mul, hX, hY])
      (fun c X _ hX => by
        rw [Matrix.mul_smul, Matrix.smul_mul, hX])
      hOne
  have hQone : Q = 1 := by
    simpa [hQidem] using hOneSupport
  have hρposDef : ρ.PosDef := hρ.posDef_of_supportProj_eq_one hQone
  exact ⟨ρ, hρposDef, hρfixed⟩

/-- A positive trace-nonincreasing endomorphism of a finite matrix algebra has
a positive-definite fixed point when the identity lies in the span of
positive-length products of a fixed family.

No product is assumed to be fixed. The maximal-support fixed point contains
every fixed factor, hence every positive-length product of those factors. The
spanning hypothesis makes its support the whole matrix algebra.

This is the faithful fixed-point step used in arXiv:1606.00608, Appendix C.4,
lines 1980--1995, before applying the density-block classification of the
fixed-point space. -/
theorem IsPositiveMap.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span
    {n J : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T)
    (V : J → Matrix n n ℂ) (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, T (V j) = V j)
    (hOne : (1 : Matrix n n ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J =>
        (List.ofFn fun t => V (x t)).prod)) :
    ∃ ρ : Matrix n n ℂ, ρ.PosDef ∧ T ρ = ρ := by
  classical
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let Φ := Matrix.reindexLinearEquiv ℂ ℂ e e
  let TFin := Matrix.reindexEndomorphism e T
  let VFin : J → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    fun j => Matrix.reindex e e (V j)
  have hTFin : IsPositiveMap TFin :=
    Matrix.IsPositiveMap.reindexEndomorphism hT e
  have hTNIFin : IsTraceNonincreasingMap TFin :=
    Matrix.IsTraceNonincreasingMap.reindexEndomorphism hTNI e
  have hreindex_symm (A : Matrix n n ℂ) :
      Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
    simpa only [Matrix.coe_reindexLinearEquiv,
      Matrix.symm_reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply A
  have hFixedFin (j : J) : TFin (VFin j) = VFin j := by
    change Matrix.reindex e e
        (T (Matrix.reindex e.symm e.symm (Matrix.reindex e e (V j)))) =
      Matrix.reindex e e (V j)
    rw [hreindex_symm, hFixed]
  have hreindexProd (l : List J) :
      Matrix.reindex e e (l.map V).prod = (l.map VFin).prod := by
    induction l with
    | nil =>
        ext i j
        simp [Matrix.reindex_apply, Matrix.one_apply]
    | cons a l ih =>
        simp only [List.map_cons, List.prod_cons]
        calc
          Matrix.reindex e e (V a * (l.map V).prod) =
              Matrix.reindex e e (V a) * Matrix.reindex e e (l.map V).prod :=
            (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e _ _).symm
          _ = VFin a * (l.map VFin).prod := by rw [ih]
  let productSpanFin := Submodule.span ℂ
    (Set.range fun x : Fin L → J => (List.ofFn fun t => VFin (x t)).prod)
  have hOneFin :
      (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) ∈
        productSpanFin := by
    have hReindexOne : Matrix.reindex e e (1 : Matrix n n ℂ) = 1 := by
      simpa only [List.map_nil, List.prod_nil] using hreindexProd ([] : List J)
    rw [← hReindexOne]
    exact Submodule.span_induction (p := fun X _ =>
        Matrix.reindex e e X ∈ productSpanFin)
      (fun X hX => by
        obtain ⟨x, rfl⟩ := hX
        apply Submodule.subset_span
        refine ⟨x, ?_⟩
        have hprod := hreindexProd (List.ofFn x)
        rw [List.map_ofFn, List.map_ofFn] at hprod
        have hfun : V ∘ x = fun t => V (x t) := rfl
        have hfunFin : VFin ∘ x = fun t => VFin (x t) := rfl
        simpa only [hfun, hfunFin] using hprod.symm)
      (by
        change Φ 0 ∈ productSpanFin
        rw [map_zero]
        exact Submodule.zero_mem productSpanFin)
      (fun X Y _ _ hX hY => by
        change Φ (X + Y) ∈ productSpanFin
        rw [map_add]
        exact Submodule.add_mem productSpanFin hX hY)
      (fun c X _ hX => by
        change Φ (c • X) ∈ productSpanFin
        rw [_root_.map_smul]
        exact Submodule.smul_mem productSpanFin c hX)
      hOne
  obtain ⟨ρFin, hρFin, hρFinFixed⟩ :=
    hTFin.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span_fin
      hTNIFin VFin L hL hFixedFin hOneFin
  let ρ := Φ.symm ρFin
  have hρ : ρ.PosDef := by
    exact hρFin.reindex e.symm
  have hρFixed : T ρ = ρ := by
    have hΦρ : Φ ρ = ρFin := Φ.apply_symm_apply ρFin
    apply Φ.injective
    calc
      Φ (T ρ) = TFin (Φ ρ) := by
        change Matrix.reindex e e (T ρ) = Matrix.reindex e e
          (T (Matrix.reindex e.symm e.symm (Matrix.reindex e e ρ)))
        rw [hreindex_symm]
      _ = Φ ρ := by rw [hΦρ, hρFinFixed]
  exact ⟨ρ, hρ, hρFixed⟩

/-- A positive trace-nonincreasing endomorphism of a finite matrix algebra is
trace preserving when the identity lies in the span of positive-length
products of a fixed family.

This coordinate-free finite-index form is obtained from the preceding
`Fin`-indexed argument by simultaneous matrix reindexing.  In
arXiv:1606.00608, Appendix C.4, lines 1974--1980 supply the fixed factors to
which this criterion is applied. -/
theorem IsPositiveMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span
    {n J : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T)
    (V : J → Matrix n n ℂ) (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, T (V j) = V j)
    (hOne : (1 : Matrix n n ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J =>
        (List.ofFn fun t => V (x t)).prod)) :
    IsTracePreservingMap T := by
  obtain ⟨ρ, hρposDef, hρfixed⟩ :=
    hT.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span
      hTNI V L hL hFixed hOne
  let gap : Matrix n n ℂ := 1 - Matrix.traceAdjointMap T 1
  have hAdjointOne : (Matrix.traceAdjointMap T 1).PosSemidef :=
    IsPositiveMap.traceAdjointMap hT 1 Matrix.PosSemidef.one
  have hGapHermitian : gap.IsHermitian := by
    exact Matrix.IsHermitian.sub Matrix.isHermitian_one hAdjointOne.isHermitian
  have hGap : gap.PosSemidef := by
    apply Matrix.PosSemidef.of_forall_trace_mul_nonneg hGapHermitian
    intro X hX
    have hloss : 0 ≤ Matrix.trace X - Matrix.trace (T X) :=
      sub_nonneg.mpr (hTNI X hX)
    simpa only [gap, Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul,
      Matrix.trace_traceAdjointMap_mul] using hloss
  have hGapTrace : Matrix.trace (ρ * gap) = 0 := by
    calc
      Matrix.trace (ρ * gap) = Matrix.trace (gap * ρ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ρ - Matrix.trace (T ρ) := by
        simp only [gap, Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul,
          Matrix.trace_traceAdjointMap_mul]
      _ = 0 := by rw [hρfixed, sub_self]
  have hGapZero : gap = 0 :=
    Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hGap hρposDef hGapTrace
  change 1 - Matrix.traceAdjointMap T 1 = 0 at hGapZero
  have hAdjointOneEq : Matrix.traceAdjointMap T 1 = 1 :=
    (sub_eq_zero.mp hGapZero).symm
  intro X
  calc
    Matrix.trace (T X) = Matrix.trace (1 * T X) := by simp
    _ = Matrix.trace (Matrix.traceAdjointMap T 1 * X) :=
      (Matrix.trace_traceAdjointMap_mul T 1 X).symm
    _ = Matrix.trace X := by rw [hAdjointOneEq]; simp
