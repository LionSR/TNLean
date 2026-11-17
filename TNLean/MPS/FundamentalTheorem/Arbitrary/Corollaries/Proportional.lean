/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.ArbitraryTensor
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.EventualEquality
import TNLean.MPS.SharedInfra.Scaling
import QICLean.Channel.Peripheral.Conjugation
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.WeightedSums
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.GaugeConversions
import TNLean.MPS.Periodic.Overlap.NonzeroSubfamily
import TNLean.MPS.Periodic.ScaledNormalization
import TNLean.MPS.Periodic.StateVectorDecomposition

/-!
# The proportional theorem for arbitrary tensors

Let `A`, `B` be arbitrary tensors with reductions onto admissible families `(C s)_{s ∈ S}` and
`(C' t)_{t ∈ T}`, and suppose that for every large `N` there is `c_N ≠ 0` with
`V_N(A) = c_N V_N(B)`. Then:

* (a) the two tensors have the same classes of factors: every `C s` is gauge related to a nonzero
  multiple of some `C' t`, and every `C' t` to a nonzero multiple of some `C s`;
* (b) matched factors have the same period, and if both are normalized to transfer-operator
  spectral radius one the scalar has modulus one;
* (c) if `c_N = λ ^ N`, the factors of `A` and of `λ • B` correspond along a bijection, up to
  gauge.

Multiplicities and weights are not determined in general: `C ⊕ 2C` and `C` are proportional with
`c_N = 1 + 2 ^ N`. The theorem assumes neither a canonical form, nor normalization, nor
non-repeated blocks.

## Main results

* `MPSTensor.forall_exists_isGaugeRelated_smul_of_eventuallyNonzeroProportionalMPV₂`.
* `MPSTensor.IsSpectrallyPeriodic.period_eq_of_isGaugeRelated_smul`: matched factors have the same
  period.
* `MPSTensor.norm_eq_one_of_isGaugeRelated_smul`: the scalar has modulus one.
* `MPSTensor.exists_equiv_isGaugeRelated_smul_of_eventually_mpv_eq_pow_mul`.

## Implementation notes

(a) is proved in four steps: the blocks of both tensors are grouped into classes (equal
up to a nonzero scalar and a gauge), one periodic left-canonical representative is chosen per
class, the states of the representatives whose period divides `N` are linearly independent for
large `N`, and a nonempty power sum of nonzero numbers does not vanish for all large exponents.
(b) uses that a gauge relation conjugates the transfer maps and that the transfer spectral radius
scales by `‖c‖ ^ 2`. (c) is the eventual-equality theorem applied to `A` and `λ • B`, followed by
the existence of reductions and the uniqueness of the factors.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, `thm:bd`, and
  Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, Theorem 2.10: the normalized,
  non-repeated special case.
-/

open scoped Matrix Matrix.Norms.Operator

namespace MPSTensor

variable {d : ℕ}

/-- The transfer map of a tensor gauge related to `A` is conjugate to the transfer map of `A`,
by the linear equivalence `Z ↦ Y Z Yᴴ` of the two matrix spaces. -/
private theorem exists_transferMap_eq_conj_of_isGaugeRelated {D₁ D₂ : ℕ}
    {A : MPSTensor d D₁} {A' : MPSTensor d D₂} (h : IsGaugeRelated A A') :
    ∃ e : Matrix (Fin D₁) (Fin D₁) ℂ ≃ₗ[ℂ] Matrix (Fin D₂) (Fin D₂) ℂ,
      Kraus.transferMap A' = e.conj (Kraus.transferMap A) := by
  obtain ⟨X, Y, hXY, hYX, hint⟩ := h
  have hXYh : Yᴴ * Xᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hXY, Matrix.conjTranspose_one]
  have hYXh : Xᴴ * Yᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hYX, Matrix.conjTranspose_one]
  have hA' : ∀ i, A' i = Y * A i * X := fun i => by
    rw [Matrix.mul_assoc, hint, ← Matrix.mul_assoc, hYX, Matrix.one_mul]
  let e : Matrix (Fin D₁) (Fin D₁) ℂ ≃ₗ[ℂ] Matrix (Fin D₂) (Fin D₂) ℂ :=
    { toFun := fun Z => Y * Z * Yᴴ
      invFun := fun W => X * W * Xᴴ
      map_add' := fun Z Z' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c Z => by simp
      left_inv := fun Z => by
        simp only [← Matrix.mul_assoc]
        rw [hXY, Matrix.one_mul, Matrix.mul_assoc, hXYh, Matrix.mul_one]
      right_inv := fun W => by
        simp only [← Matrix.mul_assoc]
        rw [hYX, Matrix.one_mul, Matrix.mul_assoc, hYXh, Matrix.mul_one] }
  refine ⟨e, LinearMap.ext fun W => ?_⟩
  rw [LinearEquiv.conj_apply]
  change Kraus.transferMap A' W = Y * Kraus.transferMap A (X * W * Xᴴ) * Yᴴ
  simp only [Kraus.transferMap_apply]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA', Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The transfer spectral radius is invariant under conjugation by a linear equivalence of matrix
spaces. -/
private theorem spectralRadius_toContinuousLinearMap_conj {D₁ D₂ : ℕ}
    (e : Matrix (Fin D₁) (Fin D₁) ℂ ≃ₗ[ℂ] Matrix (Fin D₂) (Fin D₂) ℂ)
    (f : Matrix (Fin D₁) (Fin D₁) ℂ →ₗ[ℂ] Matrix (Fin D₁) (Fin D₁) ℂ) :
    spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D₂) (Fin D₂) ℂ))
        (e.conj f)) =
      spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₁) ℂ)) f) := by
  have h1 := AlgEquiv.spectrum_eq
    (Module.End.toContinuousLinearMap (Matrix (Fin D₂) (Fin D₂) ℂ)) (e.conj f)
  have h2 := AlgEquiv.spectrum_eq
    (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₁) ℂ)) f
  have h3 : spectrum ℂ (e.conj f) = spectrum ℂ f := AlgEquiv.spectrum_eq (e.conjAlgEquiv ℂ) f
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
  rw [h1, h2, h3]

/-- The transfer spectral radius of `c • A` is `‖c‖ ^ 2` times that of `A`, at positive bond
dimension. -/
private theorem spectralRadius_transferMap_smul_of_ne_zero {D : ℕ} (hD : D ≠ 0) (c : ℂ)
    (A : MPSTensor d D) :
    spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap (d := d) (D := D) (c • A))) =
      (‖c‖₊ : ENNReal) ^ 2 * spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (Kraus.transferMap (d := d) (D := D) A)) := by
  have : Nonempty (Fin D) := ⟨⟨0, Nat.pos_of_ne_zero hD⟩⟩
  by_cases hc : c = 0
  · subst hc
    have h0 : Kraus.transferMap (d := d) (D := D) ((0 : ℂ) • A) = 0 :=
      LinearMap.ext fun X => by simp
    rw [h0, map_zero, spectrum.spectralRadius_zero]
    simp
  · exact spectralRadius_transferMap_smul c hc A

/-- A complex number whose squared norm is one, read in `ℝ≥0∞`, has norm one. -/
private theorem norm_eq_one_of_coe_nnnorm_sq_eq_one {c : ℂ} (h : (‖c‖₊ : ENNReal) ^ 2 = 1) :
    ‖c‖ = 1 := by
  have h' : ‖c‖₊ ^ 2 = 1 := by exact_mod_cast h
  have h'' : ‖c‖ ^ 2 = 1 := by
    rw [← coe_nnnorm, ← NNReal.coe_pow, h', NNReal.coe_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).mp h''

/-- A repeated-block relation, read across an equality of bond dimensions, is a gauge relation
with a nonzero scalar. -/
theorem exists_ne_zero_isGaugeRelated_smul_of_repeatedBlocks_cast {D₁ D₂ : ℕ}
    (hdim : D₁ = D₂) {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) A) B) :
    ∃ ξ : ℂ, ξ ≠ 0 ∧ IsGaugeRelated A (ξ • B) := by
  subst hdim
  obtain ⟨ξ, Y, hξ, hY⟩ := h
  simp only [cast_eq] at hY
  refine ⟨ξ, fun h0 => by rw [h0, norm_zero] at hξ; exact zero_ne_one hξ,
    (Y : Matrix (Fin D₁) (Fin D₁) ℂ), ((Y⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ),
    by simp, by simp, fun i => ?_⟩
  rw [hY i, Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    Units.inv_mul, Matrix.mul_one]

/-- **Class decomposition.** A finite family of admissible blocks is written, up to gauge and a
nonzero scalar for each block, over a pairwise non-repeated family of periodic blocks; blocks
written over the same periodic block are gauge related up to a nonzero scalar. -/
theorem exists_periodic_class_decomposition {U : Type*} [Finite U] {DU : U → ℕ}
    (CU : ∀ u, MPSTensor d (DU u)) (hirr : ∀ u, Matrix.IsIrreducibleAction (CU u))
    (hlet : ∀ u, ∃ i, CU u i ≠ 0) :
    ∃ (g : ℕ) (dim : Fin g → ℕ) (R : ∀ j, MPSTensor d (dim j)) (per : Fin g → ℕ)
      (cls : U → Fin g) (lam : U → ℂ),
      (∀ j, IsPeriodic (per j) (R j)) ∧
      (∀ i j, i ≠ j → ∀ hdim : dim i = dim j,
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (R i)) (R j)) ∧
      (∀ u, lam u ≠ 0) ∧
      (∀ u N (σ : Fin N → Fin d), mpv (CU u) σ = lam u ^ N * mpv (R (cls u)) σ) ∧
      (∀ u v, cls u = cls v → ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (CU u) (c • CU v)) := by
  classical
  have : Fintype U := Fintype.ofFinite U
  let rel : U → U → Prop := fun u v => ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (CU u) (c • CU v)
  have hrefl : ∀ u, rel u u := fun u =>
    ⟨1, one_ne_zero, by rw [one_smul]; exact IsGaugeRelated.refl _⟩
  have hsymm : ∀ {u v}, rel u v → rel v u := by
    rintro u v ⟨c, hc, h⟩
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    have h1 := h.smul c⁻¹
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
    exact h1.symm
  have htrans : ∀ {u v w}, rel u v → rel v w → rel u w := by
    rintro u v w ⟨c, hc, h⟩ ⟨c', hc', h'⟩
    refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
    have h1 := h'.smul c
    rw [smul_smul] at h1
    exact h.trans h1
  let st : Setoid U := ⟨rel, ⟨hrefl, hsymm, htrans⟩⟩
  let eQ : Quotient st ≃ Fin (Fintype.card (Quotient st)) := Fintype.equivFin _
  let rep : Fin (Fintype.card (Quotient st)) → U := fun j => (eQ.symm j).out
  have hfam : ∀ j, ∃ (B : MPSTensor d (DU (rep j))) (ζ : ℂ) (m : ℕ), ζ ≠ 0 ∧
      GaugeEquiv (fun i => ζ • CU (rep j) i) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv (CU (rep j)) σ) ∧
      IsPeriodic m B := by
    intro j
    have hNZ : NeZero (DU (rep j)) := by
      refine ⟨fun h0 => ?_⟩
      obtain ⟨i, hi⟩ := hlet (rep j)
      exact hi (Matrix.ext fun a _ => absurd a.2 (by omega))
    exact exists_leftCanonical_periodic_scale_of_irreducible
      (Kraus.isIrreducibleFamily_of_isIrreducibleAction _ (hirr (rep j))) (hlet (rep j))
  choose R ζ per hζ hgauge hmpvR hper using hfam
  let cls : U → Fin (Fintype.card (Quotient st)) := fun u => eQ (Quotient.mk st u)
  have hrel_rep : ∀ u, rel u (rep (cls u)) := fun u => by
    have h1 : rep (cls u) = (Quotient.mk st u).out := by
      simp only [rep, cls, Equiv.symm_apply_apply]
    rw [h1]
    exact hsymm (Quotient.exact (Quotient.out_eq (Quotient.mk st u)))
  choose c hc hcrel using hrel_rep
  refine ⟨_, fun j => DU (rep j), R, per, cls, fun u => c u / ζ (cls u), hper, ?_,
    fun u => div_ne_zero (hc u) (hζ _), ?_, ?_⟩
  · intro i j hij hdim hrep
    obtain ⟨ξ, hξ, hRR⟩ := exists_ne_zero_isGaugeRelated_smul_of_repeatedBlocks_cast hdim hrep
    have hi : IsGaugeRelated (ζ i • CU (rep i)) (R i) :=
      isGaugeRelated_iff_gaugeEquiv.mpr (hgauge i)
    have hj : IsGaugeRelated (R j) (ζ j • CU (rep j)) :=
      (isGaugeRelated_iff_gaugeEquiv.mpr (hgauge j)).symm
    have h1 := (hi.trans (hRR.trans (hj.smul ξ))).smul (ζ i)⁻¹
    simp only [smul_smul, inv_mul_cancel₀ (hζ i), one_smul] at h1
    have hr : rel (rep i) (rep j) := ⟨_, by simp [hξ, hζ], h1⟩
    have hq : Quotient.mk st (rep i) = Quotient.mk st (rep j) := Quotient.sound hr
    simp only [rep, Quotient.out_eq] at hq
    exact hij (eQ.symm.injective hq)
  · intro u N σ
    rw [hmpvR]
    simp only [mpv_eq, coeff_eq]
    rw [(hcrel u).trace_evalWord_eq, trace_evalWord_smul, List.length_ofFn, div_pow]
    have := hζ (cls u)
    field_simp
  · intro u v huv
    have hu : rel u (rep (cls u)) := ⟨c u, hc u, hcrel u⟩
    have hv : rel v (rep (cls v)) := ⟨c v, hc v, hcrel v⟩
    rw [← huv] at hv
    exact htrans hu (hsymm hv)

/-- Summing a family of blocks written over periodic blocks, fiber by fiber. -/
theorem sum_fiber_pow_mul_mpv_eq_sum {V : Type*} [Fintype V] {g : ℕ} {dim : Fin g → ℕ}
    (R : ∀ j, MPSTensor d (dim j)) {DV : V → ℕ} (CV : ∀ v, MPSTensor d (DV v))
    (cls : V → Fin g) (lam : V → ℂ)
    (hmpv : ∀ v N (σ : Fin N → Fin d), mpv (CV v) σ = lam v ^ N * mpv (R (cls v)) σ)
    {N : ℕ} (σ : Fin N → Fin d) :
    ∑ j, (∑ v ∈ Finset.univ.filter (fun v => cls v = j), lam v ^ N) * mpv (R j) σ =
      ∑ v, mpv (CV v) σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ cls (fun v => mpv (CV v) σ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hmpv, (Finset.mem_filter.mp hv).2]

/-- **Coefficient extraction.** At a length where the states of the periodic blocks whose period
divides it are linearly independent, a vanishing combination of all the block states has zero
coefficient at each of those blocks. -/
theorem coeff_eq_zero_of_forall_sum_mul_mpv_eq_zero {g : ℕ} {dim : Fin g → ℕ}
    (R : ∀ j, MPSTensor d (dim j)) (per : Fin g → ℕ) (hper : ∀ j, IsPeriodic (per j) (R j))
    {N : ℕ} (hLI : LinearIndependent ℂ
      (fun j : {j : Fin g // per j ∣ N} => mpvState (d := d) (R ↑j) N))
    (a : Fin g → ℂ) (h : ∀ σ : Fin N → Fin d, ∑ j, a j * mpv (R j) σ = 0)
    (j : Fin g) (hj : per j ∣ N) : a j = 0 := by
  classical
  have hSum : ∑ j, a j • mpvState (d := d) (R j) N = 0 := by
    ext σ
    simpa using h σ
  have hFilter : ∀ x : Fin g, x ∈ Finset.univ.filter (fun x => per x ∣ N) ↔ per x ∣ N := by
    intro x; simp
  have hDrop : ∑ x ∈ Finset.univ.filter (fun x => per x ∣ N),
      a x • mpvState (d := d) (R x) N = 0 := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    · exact hSum
    · intro x _ hx
      have hnd : ¬ per x ∣ N := by simpa using hx
      have hzero : mpvState (d := d) (R x) N = 0 := by
        ext σ
        simpa using pgvwc07_stateVector_eq_zero_of_not_dvd (R x) (hper x) hnd σ
      rw [hzero, smul_zero]
  have hSubtype : ∑ k : {x : Fin g // per x ∣ N}, a ↑k • mpvState (d := d) (R ↑k) N = 0 :=
    (Finset.sum_subtype (Finset.univ.filter (fun x => per x ∣ N)) hFilter
      (fun x => a x • mpvState (d := d) (R x) N)).symm.trans hDrop
  exact Fintype.linearIndependent_iff.mp hLI (fun k => a ↑k) hSubtype ⟨j, hj⟩

/-- The states of a tensor at a positive length are the sums of the states of the blocks of a
reduction, summed over the subtype of the block set. -/
theorem mpv_eq_sum_coe_sort_of_multiBlockCompression {ι : Type*} [DecidableEq ι]
    {DB : ℕ} {D : ι → ℕ} {S : Finset ι} {C : ∀ s, MPSTensor d (D s)} {B : MPSTensor d DB}
    (P : MultiBlockCompression B S C) {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin d) :
    mpv B σ = ∑ s : {s // s ∈ S}, mpv (C s.1) σ := by
  have hne : List.ofFn σ ≠ [] := by
    intro h0
    have h1 := congrArg List.length h0
    rw [List.length_ofFn, List.length_nil] at h1
    omega
  simp only [mpv_eq, coeff_eq]
  rw [P.trace_evalWord_eq_sum _ hne]
  exact (Finset.sum_coe_sort S (fun s => Matrix.trace (Kraus.evalWord (C s) (List.ofFn σ)))).symm

/-- **Classes of factors for proportional states, one direction.** Under eventual nonzero
proportionality, every factor of the first tensor is gauge related to a nonzero multiple of a factor
of the second. -/
private theorem forall_exists_isGaugeRelated_smul_of_eventually_core {DA DB : ℕ}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ} {S : Finset ι}
    {T : Finset κ} {C : ∀ s, MPSTensor d (D s)} {C' : ∀ t, MPSTensor d (D' t)}
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    (P : MultiBlockCompression A S C) (Q : MultiBlockCompression B T C')
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t ∈ T, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ T, ∃ i, C' t i ≠ 0)
    (h : EventuallyNonzeroProportionalMPV₂ A B) :
    ∀ s ∈ S, ∃ t ∈ T, ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (C s) (c • C' t) := by
  classical
  intro s0 hs0
  by_contra hno
  push Not at hno
  -- All blocks of both tensors in one finite family.
  let U := {s // s ∈ S} ⊕ {t // t ∈ T}
  let DU : U → ℕ := Sum.elim (fun s => D s.1) (fun t => D' t.1)
  let CU : ∀ u, MPSTensor d (DU u) := fun u =>
    match u with
    | Sum.inl s => C s.1
    | Sum.inr t => C' t.1
  have hirrU : ∀ u, Matrix.IsIrreducibleAction (CU u) := by
    rintro (s | t)
    exacts [hirr s.1 s.2, hirr' t.1 t.2]
  have hletU : ∀ u, ∃ i, CU u i ≠ 0 := by
    rintro (s | t)
    exacts [hlet s.1 s.2, hlet' t.1 t.2]
  obtain ⟨g, dim, R, per, cls, lam, hper, hnonrep, hlam, hmpv, hcls⟩ :=
    exists_periodic_class_decomposition CU hirrU hletU
  obtain ⟨N₁, hN₁⟩ := periodicBasis_nonzero_subfamily_eventuallyLinearlyIndependent R per hper
    hnonrep
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  set j0 := cls (Sum.inl ⟨s0, hs0⟩) with hj0
  set p := per j0 with hp
  have hppos : 0 < p := (hper j0).period_pos
  -- No block of the second tensor lies in the class of `C s0`.
  have hnoT : ∀ t : {t // t ∈ T}, cls (Sum.inr t) ≠ j0 := by
    intro t ht
    obtain ⟨c, hc, hg⟩ := hcls (Sum.inl ⟨s0, hs0⟩) (Sum.inr t) ht.symm
    exact hno t.1 t.2 c hc hg
  -- The class coefficient of `C s0` vanishes along the multiples of the period.
  have hF : ∀ m, N₀ + N₁ + 1 ≤ m →
      ∑ s ∈ Finset.univ.filter (fun s : {s // s ∈ S} => cls (Sum.inl s) = j0),
        lam (Sum.inl s) ^ (p * m) = 0 := by
    intro m hm
    set N := p * m with hN
    have hmN : m ≤ N := Nat.le_mul_of_pos_left m hppos
    obtain ⟨c, -, hAB⟩ := hN₀ N (by omega)
    let F : Fin g → ℂ := fun j =>
      ∑ s ∈ Finset.univ.filter (fun s : {s // s ∈ S} => cls (Sum.inl s) = j),
        lam (Sum.inl s) ^ N
    let G : Fin g → ℂ := fun j =>
      ∑ t ∈ Finset.univ.filter (fun t : {t // t ∈ T} => cls (Sum.inr t) = j),
        lam (Sum.inr t) ^ N
    have hcomb : ∀ σ : Fin N → Fin d, ∑ j, (F j - c * G j) * mpv (R j) σ = 0 := by
      intro σ
      have hA' := sum_fiber_pow_mul_mpv_eq_sum R (fun s : {s // s ∈ S} => C s.1)
        (fun s => cls (Sum.inl s)) (fun s => lam (Sum.inl s)) (fun s => hmpv (Sum.inl s)) σ
      have hB' := sum_fiber_pow_mul_mpv_eq_sum R (fun t : {t // t ∈ T} => C' t.1)
        (fun t => cls (Sum.inr t)) (fun t => lam (Sum.inr t)) (fun t => hmpv (Sum.inr t)) σ
      have hNpos : 0 < N := by omega
      rw [← mpv_eq_sum_coe_sort_of_multiBlockCompression P hNpos] at hA'
      rw [← mpv_eq_sum_coe_sort_of_multiBlockCompression Q hNpos] at hB'
      have hsplit : ∑ j, (F j - c * G j) * mpv (R j) σ =
          ∑ j, F j * mpv (R j) σ - c * ∑ j, G j * mpv (R j) σ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit]
      change ∑ j, (∑ s ∈ Finset.univ.filter (fun s : {s // s ∈ S} => cls (Sum.inl s) = j),
          lam (Sum.inl s) ^ N) * mpv (R j) σ - c * ∑ j, (∑ t ∈ Finset.univ.filter
            (fun t : {t // t ∈ T} => cls (Sum.inr t) = j), lam (Sum.inr t) ^ N) *
              mpv (R j) σ = 0
      rw [hA', hB', hAB σ, sub_self]
    have h0 := coeff_eq_zero_of_forall_sum_mul_mpv_eq_zero R per hper (hN₁ N (by omega))
      (fun j => F j - c * G j) hcomb j0 (dvd_mul_right p m)
    have hG : G j0 = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      exact absurd (Finset.mem_filter.mp ht).2 (hnoT t)
    simp only [hG, mul_zero, sub_zero] at h0
    exact h0
  -- A nonempty power sum of nonzero numbers cannot vanish for all large exponents.
  let Λ : Multiset ℂ :=
    (Finset.univ.filter (fun s : {s // s ∈ S} => cls (Sum.inl s) = j0)).val.map
      (fun s => lam (Sum.inl s) ^ p)
  have hΛ0 : (0 : ℂ) ∉ Λ := by
    intro hmem
    obtain ⟨s, -, hs⟩ := Multiset.mem_map.mp hmem
    exact pow_ne_zero p (hlam (Sum.inl s)) hs
  have hΛ : Λ = 0 := by
    refine Multiset.eq_zero_of_notMem_zero_of_forall_sum_map_pow_eq_zero hΛ0
      ⟨N₀ + N₁ + 1, fun m hm => ?_⟩
    rw [← hF m hm, Multiset.map_map]
    simp only [Function.comp_def, ← pow_mul]
    rfl
  have hmem : (⟨s0, hs0⟩ : {s // s ∈ S}) ∈
      Finset.univ.filter (fun s : {s // s ∈ S} => cls (Sum.inl s) = j0) := by
    simp [hj0]
  have : lam (Sum.inl ⟨s0, hs0⟩) ^ p ∈ Λ := Multiset.mem_map_of_mem _ hmem
  rw [hΛ] at this
  simp at this



/-- **Classes of factors for proportional states.** If the states of two arbitrary tensors are
eventually proportional with nonzero constants, every factor of either tensor is gauge related to a
nonzero multiple of a factor of the other. -/
theorem forall_exists_isGaugeRelated_smul_of_eventuallyNonzeroProportionalMPV₂ {DA DB : ℕ}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ} {S : Finset ι}
    {T : Finset κ} {C : ∀ s, MPSTensor d (D s)} {C' : ∀ t, MPSTensor d (D' t)}
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    (hP : Nonempty (MultiBlockCompression A S C)) (hQ : Nonempty (MultiBlockCompression B T C'))
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t ∈ T, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ T, ∃ i, C' t i ≠ 0)
    (h : EventuallyNonzeroProportionalMPV₂ A B) :
    (∀ s ∈ S, ∃ t ∈ T, ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (C s) (c • C' t)) ∧
      ∀ t ∈ T, ∃ s ∈ S, ∃ c : ℂ, c ≠ 0 ∧ IsGaugeRelated (C' t) (c • C s) := by
  obtain ⟨P⟩ := hP
  obtain ⟨Q⟩ := hQ
  exact ⟨forall_exists_isGaugeRelated_smul_of_eventually_core P Q hirr hlet hirr' hlet' h,
    forall_exists_isGaugeRelated_smul_of_eventually_core Q P hirr' hlet' hirr hlet h.symm⟩

/-- **Periods of matched factors.** If `C` is gauge related to `c • C'`, then any normalizations `a
• C` and `a' • C'` that are spectrally periodic have the same period: the period is an invariant of
the class of a factor. -/
theorem IsSpectrallyPeriodic.period_eq_of_isGaugeRelated_smul {D₁ D₂ m m' : ℕ}
    {C : MPSTensor d D₁} {C' : MPSTensor d D₂} {a a' c : ℂ}
    (hC : IsSpectrallyPeriodic m (a • C)) (hC' : IsSpectrallyPeriodic m' (a' • C'))
    (h : IsGaugeRelated C (c • C')) : m = m' := by
  have hD₂ : D₂ ≠ 0 := hC'.bondDim_ne_zero
  have ha' : a' ≠ 0 := by
    intro ha'
    have h1 := hC'.spectral_radius_one
    rw [spectralRadius_transferMap_smul_of_ne_zero hD₂, ha'] at h1
    simp at h1
  have hg : IsGaugeRelated (a • C) ((a * c / a') • (a' • C')) := by
    have h1 := h.smul a
    rwa [smul_smul, (div_mul_cancel₀ (a * c) ha').symm, mul_smul] at h1
  obtain ⟨e, he⟩ := exists_transferMap_eq_conj_of_isGaugeRelated hg
  have hr := spectralRadius_toContinuousLinearMap_conj e (Kraus.transferMap (a • C))
  rw [← he, spectralRadius_transferMap_smul_of_ne_zero hD₂, hC'.spectral_radius_one,
    hC.spectral_radius_one, mul_one] at hr
  have hb := norm_eq_one_of_coe_nnnorm_sq_eq_one hr
  have hper := peripheralEigenvalues_conj_cross e (Kraus.transferMap (a • C))
  rw [← he, show Kraus.transferMap (d := d) (D := D₂) ((a * c / a') • (a' • C')) =
      Kraus.transferMap (d := d) (D := D₂) (a' • C') from
      transferMap_smul_eq_of_norm_eq_one _ _ hb, hC'.peripheral_eq, hC.peripheral_eq] at hper
  exact (period_eq_of_setOf_pow_eq_one hC'.period_pos hC.period_pos hper).symm

/-- **Modulus of the scalar.** If the transfer maps of `C` and `C'` have spectral radius one and `C`
is gauge related to `c • C'`, then `‖c‖ = 1`. -/
theorem norm_eq_one_of_isGaugeRelated_smul {D₁ D₂ : ℕ} {C : MPSTensor d D₁}
    {C' : MPSTensor d D₂} {c : ℂ}
    (hC : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₁) ℂ))
        (Kraus.transferMap (d := d) (D := D₁) C)) = 1)
    (hC' : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D₂) (Fin D₂) ℂ))
        (Kraus.transferMap (d := d) (D := D₂) C')) = 1)
    (h : IsGaugeRelated C (c • C')) : ‖c‖ = 1 := by
  have hD₂ : D₂ ≠ 0 := matrix_dim_ne_zero_of_spectralRadius_eq_one _ hC'
  obtain ⟨e, he⟩ := exists_transferMap_eq_conj_of_isGaugeRelated h
  have hr := spectralRadius_toContinuousLinearMap_conj e (Kraus.transferMap C)
  rw [← he, spectralRadius_transferMap_smul_of_ne_zero hD₂, hC', hC, mul_one] at hr
  exact norm_eq_one_of_coe_nnnorm_sq_eq_one hr

/-- **Factors for states proportional by a power.** If `V_N(A) = λ ^ N V_N(B)` for every large `N`,
with `λ ≠ 0`, the factors of `A` correspond to those of `B` along a bijection, each gauge related to
`λ` times its partner. -/
theorem exists_equiv_isGaugeRelated_smul_of_eventually_mpv_eq_pow_mul {DA DB : ℕ}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ} {S : Finset ι}
    {T : Finset κ} {C : ∀ s, MPSTensor d (D s)} {C' : ∀ t, MPSTensor d (D' t)}
    {A : MPSTensor d DA} {B : MPSTensor d DB}
    (hP : Nonempty (MultiBlockCompression A S C)) (hQ : Nonempty (MultiBlockCompression B T C'))
    (hirr : ∀ s ∈ S, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s ∈ S, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t ∈ T, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t ∈ T, ∃ i, C' t i ≠ 0)
    {lam : ℂ} (hlam : lam ≠ 0)
    (h : ∀ᶠ N in Filter.atTop, ∀ σ : Fin N → Fin d, mpv A σ = lam ^ N * mpv B σ) :
    ∃ τ : {s // s ∈ S} ≃ {t // t ∈ T}, ∀ s, IsGaugeRelated (C s.1) (lam • C' (τ s).1) := by
  classical
  obtain ⟨P⟩ := hP
  obtain ⟨Q⟩ := hQ
  have hirrl : ∀ t ∈ T, Matrix.IsIrreducibleAction (lam • C' t) := fun t ht =>
    isIrreducibleAction_smul (hirr' t ht) hlam
  have hletl : ∀ t ∈ T, ∃ i, (lam • C' t) i ≠ 0 := fun t ht =>
    exists_smul_apply_ne_zero (hlet' t ht) hlam
  obtain ⟨Q', -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction T
    (fun t => lam • C' t) hirrl hletl (lam • B) fun w hw => by
      rw [trace_evalWord_smul, Q.trace_evalWord_eq_sum w hw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => (trace_evalWord_smul lam (C' t) w).symm
  have hsame : SameMPV₂Pos A (lam • B) := by
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h
    refine sameMPV₂Pos_of_forall_le_length_trace_evalWord_eq N₁ fun w hw => ?_
    have h1 := hN₁ w.length hw w.get
    simp only [mpv_eq, coeff_eq, List.ofFn_get] at h1
    rw [h1, trace_evalWord_smul]
  obtain ⟨-, τ, hτ⟩ :=
    P.z_sub_z_eq_and_exists_equiv_isGaugeRelated_of_sameMPV₂Pos Q' hirr hlet hirrl hletl hsame
  exact ⟨τ, hτ⟩

end MPSTensor
