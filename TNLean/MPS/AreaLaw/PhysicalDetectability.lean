/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.DetectabilityLemma
import QICLean.Analysis.ComplementProdKernel
import QICLean.Analysis.ProjectionGeometry
import TNLean.Algebra.GappedGroundState
import TNLean.Circuit.EntropySupport
import TNLean.MPS.AreaLaw.Basic

/-!
# Detectability for a physical nearest-neighbour projection chain

The even and odd products are formed from the actual supported bond
projections. Their commutation and noncommutation count follow from the
chain geometry. This supports ALVV, arXiv:1602.08828v2, `def:DLO`,
`lem:dl` and `lem:dl-converse`, lines 1496–1537.

The local terms are orthogonal projections, exactly as assumed in
`def:DLO`. This is the source's case after its range-projection reduction
at lines 1457–1460. The reduction from arbitrary positive contractions is proved in
`PhysicalRangeDetectability.lean`. The regional truncated-Hamiltonian
conclusions are separate.
-/

open Matrix
open scoped BigOperators InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

private noncomputable def parityTerm
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (p k : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  if hk : k < L - 1 then
    if k % 2 = p then Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (h ⟨k, hk⟩) else 0
  else 0

/-- The product of the complements on one parity of the physical bond starts.
With sites numbered from one, parity zero comprises the odd source terms.
ALVV, arXiv:1602.08828v2, `def:DLO`, lines 1496–1501. -/
noncomputable def physicalParityProduct
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (p : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  ContinuousLinearMap.complementProd (parityTerm h p) (L - 1)

/-- The actual even-then-odd detectability operator; the odd source terms act
first. ALVV, arXiv:1602.08828v2, `def:DLO`, lines 1496–1501. -/
noncomputable def physicalDetectability
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  physicalParityProduct h 1 * physicalParityProduct h 0

private theorem commute_bonds_of_separated
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (i j : Fin (L - 1)) (hsep : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (h i) (h j) := by
  refine QuantumCircuit.commute_of_mem_supportedOperators ?_
    (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i))
    (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs j))
  rw [Set.disjoint_left]
  intro x hx hy
  change x ∈ interval L i.val (i.val + 2) at hx
  change x ∈ interval L j.val (j.val + 2) at hy
  rw [mem_interval] at hx hy
  omega

private noncomputable def orderedTerm
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (k : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  if k < L - 1 then parityTerm h 0 k else parityTerm h 1 (k - (L - 1))

private def orderedPosition (m r : ℕ) : ℕ := if r % 2 = 0 then r else m + r

private theorem exists_bond_of_orderedTerm_ne_zero
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    {k : ℕ} (hk : k < 2 * (L - 1)) (hne : orderedTerm h k ≠ 0) :
    ∃ i : Fin (L - 1), k = orderedPosition (L - 1) i.val ∧
      orderedTerm h k = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (h i) := by
  by_cases hkm : k < L - 1
  · have hp : k % 2 = 0 := by
      by_contra hp
      exact hne (by simp [orderedTerm, parityTerm, hkm, hp])
    refine ⟨⟨k, hkm⟩, ?_, ?_⟩
    · simp [orderedPosition, hp]
    · simp [orderedTerm, parityTerm, hkm, hp]
  · have hsub : k - (L - 1) < L - 1 := by omega
    have hp : (k - (L - 1)) % 2 = 1 := by
      by_contra hp
      exact hne (by simp [orderedTerm, parityTerm, hkm, hsub, hp])
    refine ⟨⟨k - (L - 1), hsub⟩, ?_, ?_⟩
    · simp only [orderedPosition, hp, one_ne_zero, ↓reduceIte]
      omega
    · simp [orderedTerm, parityTerm, hkm, hsub, hp]

open scoped Classical in
private theorem orderedTerm_noncommutation_count
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) :
    ∀ i < 2 * (L - 1),
      ((Finset.range (2 * (L - 1))).filter
        (fun j ↦ j ≠ i ∧ ¬Commute (orderedTerm h i) (orderedTerm h j))).card ≤ 2 := by
  intro i hi
  by_cases hz : orderedTerm h i = 0
  · simp [hz, Commute.zero_left]
  obtain ⟨r, _hrpos, hreq⟩ := exists_bond_of_orderedTerm_ne_zero h hi hz
  have hsub : ((Finset.range (2 * (L - 1))).filter
      (fun j ↦ j ≠ i ∧ ¬Commute (orderedTerm h i) (orderedTerm h j))) ⊆
      {orderedPosition (L - 1) (r.val - 1), orderedPosition (L - 1) (r.val + 1)} := by
    intro j hj
    obtain ⟨hjrange, _hji, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨s, hspos, hseq⟩ := exists_bond_of_orderedTerm_ne_zero h
      (Finset.mem_range.mp hjrange) (fun hz ↦ hc (by simp [hz, Commute.zero_right]))
    have hn : ¬Commute (h r) (h s) := by
      intro hrs
      apply hc
      rw [hreq, hseq]
      exact hrs.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
    have hadj : s.val = r.val - 1 ∨ s.val = r.val + 1 := by
      by_contra hnbr
      have hne : r.val ≠ s.val := by
        intro heq
        exact hn (by rw [Fin.ext heq])
      exact hn (commute_bonds_of_separated h hs r s (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hadj with hadj | hadj
    · exact Or.inl (hspos.trans (congrArg (orderedPosition (L - 1)) hadj))
    · exact Or.inr (hspos.trans (congrArg (orderedPosition (L - 1)) hadj))
  refine (Finset.card_le_card hsub).trans ?_
  have hc := Finset.card_pair_eq_one_or_two
    (a := orderedPosition (L - 1) (r.val - 1))
    (b := orderedPosition (L - 1) (r.val + 1))
  omega

private theorem parityTerm_isStarProjection
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i)) (p k : ℕ) :
    IsStarProjection (parityTerm h p k) := by
  unfold parityTerm
  split_ifs with hk hkpar
  · exact (hp ⟨k, hk⟩).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
  · exact IsStarProjection.zero _
  · exact IsStarProjection.zero _

private theorem orderedTerm_isStarProjection
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i)) (k : ℕ) :
    IsStarProjection (orderedTerm h k) := by
  unfold orderedTerm
  split_ifs
  · exact parityTerm_isStarProjection h hp _ _
  · exact parityTerm_isStarProjection h hp _ _

private theorem parityTerm_commute
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p i j : ℕ) :
    Commute (parityTerm h p i) (parityTerm h p j) := by
  by_cases hi : i < L - 1
  · by_cases hj : j < L - 1
    · by_cases hip : i % 2 = p
      · by_cases hjp : j % 2 = p
        · by_cases hij : i = j
          · subst j
            exact Commute.refl _
          have hsep : i + 1 < j ∨ j + 1 < i := by omega
          simpa only [parityTerm, dite_eq_left hi, dite_eq_left hj,
            ite_eq_left hip, ite_eq_left hjp] using
            (commute_bonds_of_separated h hs ⟨i, hi⟩ ⟨j, hj⟩ hsep).map
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        · simp [parityTerm, hj, hjp, Commute.zero_right]
      · simp [parityTerm, hi, hip, Commute.zero_left]
    · simp [parityTerm, hj, Commute.zero_right]
  · simp [parityTerm, hi, Commute.zero_left]

private theorem complementProd_orderedTerm
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    ContinuousLinearMap.complementProd (orderedTerm h) (2 * (L - 1)) =
      physicalDetectability h := by
  have hfirst : ∀ n ≤ L - 1,
      ContinuousLinearMap.complementProd (orderedTerm h) n =
        ContinuousLinearMap.complementProd (parityTerm h 0) n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [ContinuousLinearMap.complementProd_succ, ContinuousLinearMap.complementProd_succ,
        ih (by omega)]
      congr 1
      simp only [orderedTerm, ite_eq_left (show n < L - 1 by omega)]
  have hsecond : ∀ n,
      ContinuousLinearMap.complementProd (orderedTerm h) ((L - 1) + n) =
        ContinuousLinearMap.complementProd (parityTerm h 1) n *
          ContinuousLinearMap.complementProd (parityTerm h 0) (L - 1) := by
    intro n
    induction n with
    | zero => simpa using hfirst (L - 1) le_rfl
    | succ n ih =>
      rw [Nat.add_succ, ContinuousLinearMap.complementProd_succ, ih,
        ContinuousLinearMap.complementProd_succ, mul_assoc]
      congr 2
      simp [orderedTerm]
  simpa only [two_mul, physicalDetectability, physicalParityProduct] using hsecond (L - 1)

private theorem sum_parityTerm
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ k ∈ Finset.range (L - 1), parityTerm h 0 k) +
      (∑ k ∈ Finset.range (L - 1), parityTerm h 1 k) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) := by
  rw [← Finset.sum_add_distrib, Finset.sum_range, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hp : i.val % 2 = 0
  · simp [parityTerm, i.isLt, hp]
  · have hp1 : i.val % 2 = 1 := by omega
    simp [parityTerm, i.isLt, hp1]

private theorem sum_orderedTerm
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ k ∈ Finset.range (2 * (L - 1)), orderedTerm h k) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) := by
  rw [two_mul, Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range (L - 1), orderedTerm h k) =
      ∑ k ∈ Finset.range (L - 1), parityTerm h 0 k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp only [orderedTerm, ite_eq_left (Finset.mem_range.mp hk)]
  have hsecond : (∑ k ∈ Finset.range (L - 1), orderedTerm h ((L - 1) + k)) =
      ∑ k ∈ Finset.range (L - 1), parityTerm h 1 k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    simp [orderedTerm]
  rw [hfirst, hsecond]
  exact sum_parityTerm h

/-- The actual product on one parity is an orthogonal projection. Its
commutation is derived from physical support. ALVV, arXiv:1602.08828v2,
`def:DLO` and `def:HLeven-odd`, lines 1475–1501. -/
theorem physicalParityProduct_isStarProjection
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (p : ℕ) :
    IsStarProjection (physicalParityProduct h p) :=
  ContinuousLinearMap.isStarProjection_complementProd
    (parityTerm_isStarProjection h hp p) (parityTerm_commute h hs p) (L - 1)

/-- The fixed vectors of an actual parity product are precisely the vectors
annihilated by its selected physical bonds. This assertion requires no
commutativity or support hypothesis. ALVV, arXiv:1602.08828v2,
`def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and 1543–1550. -/
theorem physicalParityProduct_apply_eq_self_iff
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i)) (p : ℕ)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    physicalParityProduct h p x = x ↔
      ∀ i : Fin (L - 1), i.val % 2 = p →
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (h i) x = 0 := by
  rw [physicalParityProduct, ContinuousLinearMap.complementProd_apply_eq_self_iff
    (parityTerm_isStarProjection h hp p)]
  constructor
  · intro hx i hi
    simpa only [parityTerm, dite_eq_left i.isLt, ite_eq_left hi] using hx i.val i.isLt
  · intro hx k hk
    by_cases hkp : k % 2 = p
    · simpa only [parityTerm, dite_eq_left hk, ite_eq_left hkp] using hx ⟨k, hk⟩ hkp
    · simp only [parityTerm, dite_eq_left hk, ite_eq_right hkp, _root_.zero_apply]

/-- The converse estimate for the actual physical even/odd product, for
every unit vector. The constant three strengthens the stated constant four.
ALVV, arXiv:1602.08828v2, `lem:dl-converse`, lines 1528–1537. -/
theorem one_sub_three_mul_le_norm_sq_physicalDetectability
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1) :
    1 - 3 * (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (∑ i, h i) x⟫_ℂ).re ≤ ‖physicalDetectability h x‖ ^ 2 := by
  have hconv := ContinuousLinearMap.one_sub_three_mul_le_norm_sq_complementProd_comp
    (parityTerm_isStarProjection h hp 1) (parityTerm_commute h hs 1)
    (parityTerm_isStarProjection h hp 0) (parityTerm_commute h hs 0)
    (L - 1) (L - 1) hx
  rw [add_comm (∑ k ∈ Finset.range (L - 1), parityTerm h 1 k), sum_parityTerm] at hconv
  exact hconv

/-- The energy decrease estimate for the actual physical even/odd product.
Each bond has at most two noncommuting neighbours, derived from support.
ALVV, arXiv:1602.08828v2, `lem:dl`, lines 1508–1519. -/
theorem re_inner_physicalDetectability_le
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    (⟪physicalDetectability h x,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (∑ i, h i) (physicalDetectability h x)⟫_ℂ).re ≤
      4 * (‖x‖ ^ 2 - ‖physicalDetectability h x‖ ^ 2) := by
  have hDL := ContinuousLinearMap.re_inner_sum_complementProd_le
    (orderedTerm_isStarProjection h hp) (orderedTerm_noncommutation_count h hs) x
  rw [complementProd_orderedTerm, sum_orderedTerm] at hDL
  norm_num at hDL
  simpa only [map_sum, _root_.sum_apply] using hDL

private theorem bond_apply_eq_zero_of_sum
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i)) {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) z = 0)
    (i : Fin (L - 1)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (h i) z = 0 := by
  refine ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
    (fun j ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (h j)).toLinearMap)
    (fun j ↦ ContinuousLinearMap.IsStarProjection.isSymmetricProjection
      ((hp j).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)))) ?_ i
  simpa only [map_sum, _root_.sum_apply, LinearMap.sum_apply,
    ContinuousLinearMap.coe_coe] using hz

/-- Each parity product fixes every vector in the actual Hamiltonian kernel.
ALVV, arXiv:1602.08828v2, `def:DLO` and the frustration-free condition,
lines 1457–1460 and 1496–1501. No uniqueness is required. -/
theorem physicalParityProduct_fixes_kernel
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i)) {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) z = 0)
    (p : ℕ) : physicalParityProduct h p z = z := by
  apply (physicalParityProduct_apply_eq_self_iff h hp p z).mpr
  intro i _
  exact bond_apply_eq_zero_of_sum h hp hz i

/-- The actual detectability operator fixes the entire original ground kernel.
ALVV, arXiv:1602.08828v2, `def:DLO`, lines 1496–1501. -/
theorem physicalDetectability_fixes_kernel
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i)) {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) z = 0) :
    physicalDetectability h z = z := by
  change physicalParityProduct h 1 (physicalParityProduct h 0 z) = z
  rw [physicalParityProduct_fixes_kernel h hp hz, physicalParityProduct_fixes_kernel h hp hz]

/-- The physical detectability operator preserves the inner product with
every ground-kernel vector, hence preserves the kernel's orthogonal complement.
ALVV, arXiv:1602.08828v2, the use of `lem:dl` in `thm:FF-tH`, lines 1562–1568.
This assertion does not assume that the kernel is one-dimensional. -/
theorem inner_physicalDetectability_eq
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) z = 0)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) : ⟪z, physicalDetectability h x⟫_ℂ = ⟪z, x⟫_ℂ := by
  change ⟪z, physicalParityProduct h 1 (physicalParityProduct h 0 x)⟫_ℂ = ⟪z, x⟫_ℂ
  rw [← ContinuousLinearMap.IsStarProjection.inner_apply_left
    (physicalParityProduct_isStarProjection h hp hs 1), physicalParityProduct_fixes_kernel h hp hz]
  rw [← ContinuousLinearMap.IsStarProjection.inner_apply_left
    (physicalParityProduct_isStarProjection h hp hs 0), physicalParityProduct_fixes_kernel h hp hz]

/-- A gap above the frustration-free ground vector contracts the orthogonal
complement under the actual physical detectability operator. The estimate
uses squared norms and retains the full denominator, with no upper bound on
the gap. ALVV, arXiv:1602.08828v2, `lem:dl` and its application in `thm:FF-tH`,
lines 1508–1519 and 1562–1568. -/
theorem norm_sq_physicalDetectability_le_of_gappedGroundState
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    {Gamma x : EuclideanSpace ℂ (Fin L → Fin q)} {gamma : ℝ}
    (hgs : Matrix.IsGappedGroundState (∑ i, h i) 0 Gamma gamma)
    (hgamma : 0 < gamma) (hx : ‖x‖ = 1) (horth : ⟪Gamma, x⟫_ℂ = 0) :
    ‖physicalDetectability h x‖ ^ 2 ≤ 4 / (4 + gamma) := by
  have hGamma : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (∑ i, h i) Gamma = 0 := by
    simpa only [Complex.ofReal_zero, zero_smul] using hgs.2.1
  have horth' : ⟪Gamma, physicalDetectability h x⟫_ℂ = 0 :=
    (inner_physicalDetectability_eq h hp hs hGamma x).trans horth
  have hgap := hgs.2.2.gap_le (physicalDetectability h x)
  rw [horth', norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
    zero_mul, sub_zero] at hgap
  have henergy := re_inner_physicalDetectability_le h hp hs x
  rw [hx, one_pow] at henergy
  rw [le_div_iff₀ (show 0 < 4 + gamma by linarith only [hgamma])]
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at hgap
  simp only [ContinuousLinearMap.coe_coe] at hgap
  nlinarith only [hgap, henergy]

end TNLean.MPS.AreaLaw
