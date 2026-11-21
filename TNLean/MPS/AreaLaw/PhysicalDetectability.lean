/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.DetectabilityLemma
import QICLean.Analysis.ComplementProdKernel
import QICLean.Analysis.ComplementProdPartition
import QICLean.Analysis.ProjectionGeometry
import QICLean.ManyBody.Hamiltonian.Models
import TNLean.Algebra.MatrixHermitianSum
import TNLean.Circuit.SiteEmbedding
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.RegionUnion
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Hamiltonian.GroundSpace

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

open ManyBody (interval mem_interval)

open Matrix

open ManyBody (IsGapped groundSpace)
open scoped BigOperators InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

private noncomputable def parityTerm
    (Φ : ManyBody.BondInteraction L q) (p k : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  if hk : k < L - 1 then
    if k % 2 = p then Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (Φ.term ⟨k, hk⟩) else 0
  else 0

/-- The product of the complements on one parity of the physical bond starts.
With sites numbered from one, parity zero comprises the odd source terms.
ALVV, arXiv:1602.08828v2, `def:DLO`, lines 1496–1501. -/
noncomputable def physicalParityProduct
    (Φ : ManyBody.BondInteraction L q) (p : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  ContinuousLinearMap.complementProd (parityTerm Φ p) (L - 1)

/-- The actual even-then-odd detectability operator; the odd source terms act
first. ALVV, arXiv:1602.08828v2, `def:DLO`, lines 1496–1501. -/
noncomputable def physicalDetectability
    (Φ : ManyBody.BondInteraction L q) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  physicalParityProduct Φ 1 * physicalParityProduct Φ 0

private theorem commute_bonds_of_separated
    (Φ : ManyBody.BondInteraction L q)
    (i j : Fin (L - 1)) (hsep : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (Φ.term i) (Φ.term j) := by
  refine ManyBody.commute_of_mem_supportedOperators_of_disjoint (Φ.mem i) (Φ.mem j) ?_
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_interval] at hx hy
  omega

private noncomputable def orderedTerm
    (Φ : ManyBody.BondInteraction L q) (k : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
  if k < L - 1 then parityTerm Φ 0 k else parityTerm Φ 1 (k - (L - 1))

private def orderedPosition (m r : ℕ) : ℕ := if r % 2 = 0 then r else m + r

private theorem exists_bond_of_orderedTerm_ne_zero
    (Φ : ManyBody.BondInteraction L q)
    {k : ℕ} (hk : k < 2 * (L - 1)) (hne : orderedTerm Φ k ≠ 0) :
    ∃ i : Fin (L - 1), k = orderedPosition (L - 1) i.val ∧
      orderedTerm Φ k = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Φ.term i) := by
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
    (Φ : ManyBody.BondInteraction L q) :
    ∀ i < 2 * (L - 1),
      ((Finset.range (2 * (L - 1))).filter
        (fun j ↦ j ≠ i ∧ ¬Commute (orderedTerm Φ i) (orderedTerm Φ j))).card ≤ 2 := by
  intro i hi
  by_cases hz : orderedTerm Φ i = 0
  · simp [hz, Commute.zero_left]
  obtain ⟨r, _hrpos, hreq⟩ := exists_bond_of_orderedTerm_ne_zero Φ hi hz
  have hsub : ((Finset.range (2 * (L - 1))).filter
      (fun j ↦ j ≠ i ∧ ¬Commute (orderedTerm Φ i) (orderedTerm Φ j))) ⊆
      {orderedPosition (L - 1) (r.val - 1), orderedPosition (L - 1) (r.val + 1)} := by
    intro j hj
    obtain ⟨hjrange, _hji, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨s, hspos, hseq⟩ := exists_bond_of_orderedTerm_ne_zero Φ
      (Finset.mem_range.mp hjrange) (fun hz ↦ hc (by simp [hz, Commute.zero_right]))
    have hn : ¬Commute (Φ.term r) (Φ.term s) := by
      intro hrs
      apply hc
      rw [hreq, hseq]
      exact hrs.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
    have hadj : s.val = r.val - 1 ∨ s.val = r.val + 1 := by
      by_contra hnbr
      have hne : r.val ≠ s.val := by
        intro heq
        exact hn (by rw [Fin.ext heq])
      exact hn (commute_bonds_of_separated Φ r s (by omega))
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
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (p k : ℕ) :
    IsStarProjection (parityTerm Φ p k) := by
  unfold parityTerm
  split_ifs with hk hkpar
  · exact (hp ⟨k, hk⟩).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
  · exact IsStarProjection.zero _
  · exact IsStarProjection.zero _

private theorem orderedTerm_isStarProjection
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (k : ℕ) :
    IsStarProjection (orderedTerm Φ k) := by
  unfold orderedTerm
  split_ifs
  · exact parityTerm_isStarProjection Φ hp _ _
  · exact parityTerm_isStarProjection Φ hp _ _

private theorem parityTerm_commute
    (Φ : ManyBody.BondInteraction L q) (p i j : ℕ) :
    Commute (parityTerm Φ p i) (parityTerm Φ p j) := by
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
            (commute_bonds_of_separated Φ ⟨i, hi⟩ ⟨j, hj⟩ hsep).map
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
        · simp [parityTerm, hj, hjp, Commute.zero_right]
      · simp [parityTerm, hi, hip, Commute.zero_left]
    · simp [parityTerm, hj, Commute.zero_right]
  · simp [parityTerm, hi, Commute.zero_left]

private theorem complementProd_orderedTerm
    (Φ : ManyBody.BondInteraction L q) :
    ContinuousLinearMap.complementProd (orderedTerm Φ) (2 * (L - 1)) =
      physicalDetectability Φ := by
  have hfirst : ∀ n ≤ L - 1,
      ContinuousLinearMap.complementProd (orderedTerm Φ) n =
        ContinuousLinearMap.complementProd (parityTerm Φ 0) n := by
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
      ContinuousLinearMap.complementProd (orderedTerm Φ) ((L - 1) + n) =
        ContinuousLinearMap.complementProd (parityTerm Φ 1) n *
          ContinuousLinearMap.complementProd (parityTerm Φ 0) (L - 1) := by
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
    (Φ : ManyBody.BondInteraction L q) :
    (∑ k ∈ Finset.range (L - 1), parityTerm Φ 0 k) +
      (∑ k ∈ Finset.range (L - 1), parityTerm Φ 1 k) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian := by
  rw [← Finset.sum_add_distrib, Finset.sum_range, ManyBody.Interaction.hamiltonian, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hp : i.val % 2 = 0
  · simp [parityTerm, i.isLt, hp]
  · have hp1 : i.val % 2 = 1 := by omega
    simp [parityTerm, i.isLt, hp1]

private theorem sum_orderedTerm
    (Φ : ManyBody.BondInteraction L q) :
    (∑ k ∈ Finset.range (2 * (L - 1)), orderedTerm Φ k) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian := by
  rw [two_mul, Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range (L - 1), orderedTerm Φ k) =
      ∑ k ∈ Finset.range (L - 1), parityTerm Φ 0 k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp only [orderedTerm, ite_eq_left (Finset.mem_range.mp hk)]
  have hsecond : (∑ k ∈ Finset.range (L - 1), orderedTerm Φ ((L - 1) + k)) =
      ∑ k ∈ Finset.range (L - 1), parityTerm Φ 1 k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    simp [orderedTerm]
  rw [hfirst, hsecond]
  exact sum_parityTerm Φ

/-- A physical parity product splits over any selection of its bonds.
Commutativity follows from the original nearest-neighbour supports; no
projection hypothesis is needed for this algebraic identity. ALVV,
arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and 1543–1550. -/
theorem physicalParityProduct_partition
    (Φ : ManyBody.BondInteraction L q)
    (s : Fin (L - 1) → Prop) [DecidablePred s] (p : ℕ) :
    physicalParityProduct Φ p =
      physicalParityProduct (Φ.restrict s) p * physicalParityProduct (Φ.restrict (¬ s ·)) p := by
  classical
  let t (k : ℕ) : Prop := if hk : k < L - 1 then s ⟨k, hk⟩ else False
  have heq := ContinuousLinearMap.complementProd_partition (parityTerm_commute Φ p)
    t (L - 1)
  have hu : (fun k ↦ if t k then parityTerm Φ p k else 0) = parityTerm (Φ.restrict s) p := by
    funext k
    unfold parityTerm
    split_ifs <;> simp_all [t]
  have hv : (fun k ↦ if t k then 0 else parityTerm Φ p k) =
      parityTerm (Φ.restrict (¬ s ·)) p := by
    funext k
    unfold parityTerm
    split_ifs <;> simp_all [t]
  simpa only [physicalParityProduct, hu, hv] using heq

/-- The actual product on one parity is an orthogonal projection. Its
commutation is derived from physical support. ALVV, arXiv:1602.08828v2,
`def:DLO` and `def:HLeven-odd`, lines 1475–1501. -/
theorem physicalParityProduct_isStarProjection
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (p : ℕ) :
    IsStarProjection (physicalParityProduct Φ p) :=
  ContinuousLinearMap.isStarProjection_complementProd
    (parityTerm_isStarProjection Φ hp p) (parityTerm_commute Φ p) (L - 1)

/-- The fixed vectors of an actual parity product are precisely the vectors
annihilated by its selected physical bonds. This assertion requires no
commutativity or support hypothesis. ALVV, arXiv:1602.08828v2,
`def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and 1543–1550. -/
theorem physicalParityProduct_apply_eq_self_iff
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (p : ℕ)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    physicalParityProduct Φ p x = x ↔
      ∀ i : Fin (L - 1), i.val % 2 = p →
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Φ.term i) x = 0 := by
  rw [physicalParityProduct, ContinuousLinearMap.complementProd_apply_eq_self_iff
    (parityTerm_isStarProjection Φ hp p)]
  constructor
  · intro hx i hi
    simpa only [parityTerm, dite_eq_left i.isLt, ite_eq_left hi] using hx i.val i.isLt
  · intro hx k hk
    by_cases hkp : k % 2 = p
    · simpa only [parityTerm, dite_eq_left hk, ite_eq_left hkp] using hx ⟨k, hk⟩ hkp
    · simp only [parityTerm, dite_eq_left hk, ite_eq_right hkp, _root_.zero_apply]

/-- The two complementary parity masses are bounded by the actual physical
energy. The vector need not be normalized. ALVV, arXiv:1602.08828v2,
`lem:dl-converse` and `thm:FF-tH`, lines 1528–1550. -/
theorem sum_norm_sq_sub_physicalParityProduct_le
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i))
    (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖x - physicalParityProduct Φ 0 x‖ ^ 2 +
      ‖x - physicalParityProduct Φ 1 x‖ ^ 2 ≤
        (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          Φ.hamiltonian x⟫_ℂ).re := by
  have h0 := ContinuousLinearMap.norm_sq_sub_norm_sq_complementProd_le
    (parityTerm_isStarProjection Φ hp 0) (parityTerm_commute Φ 0) x (L - 1)
  have h1 := ContinuousLinearMap.norm_sq_sub_norm_sq_complementProd_le
    (parityTerm_isStarProjection Φ hp 1) (parityTerm_commute Φ 1) x (L - 1)
  have hpy (p : ℕ) := ContinuousLinearMap.IsStarProjection.norm_sq_eq
    (physicalParityProduct_isStarProjection Φ hp p) x
  have hsum :
      (⟪x, (∑ k ∈ Finset.range (L - 1), parityTerm Φ 0 k) x⟫_ℂ).re +
        (⟪x, (∑ k ∈ Finset.range (L - 1), parityTerm Φ 1 k) x⟫_ℂ).re =
          (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
            Φ.hamiltonian x⟫_ℂ).re := by
    simpa only [_root_.add_apply, inner_add_right, Complex.add_re] using
      congrArg (fun A : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ]
        EuclideanSpace ℂ (Fin L → Fin q) ↦ (⟪x, A x⟫_ℂ).re) (sum_parityTerm Φ)
  simp only [physicalParityProduct, RCLike.re_to_complex] at h0 h1 hpy ⊢
  linarith only [h0, h1, hpy 0, hpy 1, hsum]

/-- The converse estimate for the actual physical even/odd product, for
every unit vector. The constant three strengthens the stated constant four.
ALVV, arXiv:1602.08828v2, `lem:dl-converse`, lines 1528–1537. -/
theorem one_sub_three_mul_le_norm_sq_physicalDetectability
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i))
    {x : EuclideanSpace ℂ (Fin L → Fin q)} (hx : ‖x‖ = 1) :
    1 - 3 * (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      Φ.hamiltonian x⟫_ℂ).re ≤ ‖physicalDetectability Φ x‖ ^ 2 := by
  have hconv := ContinuousLinearMap.one_sub_three_mul_le_norm_sq_complementProd_comp
    (parityTerm_isStarProjection Φ hp 1) (parityTerm_commute Φ 1)
    (parityTerm_isStarProjection Φ hp 0) (parityTerm_commute Φ 0)
    (L - 1) (L - 1) hx
  rw [add_comm (∑ k ∈ Finset.range (L - 1), parityTerm Φ 1 k), sum_parityTerm] at hconv
  exact hconv

/-- The energy decrease estimate for the actual physical even/odd product.
Each bond has at most two noncommuting neighbours, derived from support.
ALVV, arXiv:1602.08828v2, `lem:dl`, lines 1508–1519. -/
theorem re_inner_physicalDetectability_le
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    (⟪physicalDetectability Φ x,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        Φ.hamiltonian (physicalDetectability Φ x)⟫_ℂ).re ≤
      4 * (‖x‖ ^ 2 - ‖physicalDetectability Φ x‖ ^ 2) := by
  have hDL := ContinuousLinearMap.re_inner_sum_complementProd_le
    (orderedTerm_isStarProjection Φ hp) (orderedTerm_noncommutation_count Φ) x
  rw [complementProd_orderedTerm, sum_orderedTerm] at hDL
  norm_num at hDL
  simpa only [map_sum, _root_.sum_apply] using hDL

private theorem bond_apply_eq_zero_of_sum
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian z = 0)
    (i : Fin (L - 1)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Φ.term i) z = 0 := by
  refine ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
    (fun j ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (Φ.term j)).toLinearMap)
    (fun j ↦ ContinuousLinearMap.IsStarProjection.isSymmetricProjection
      ((hp j).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)))) ?_ i
  simpa only [ManyBody.Interaction.hamiltonian, map_sum, _root_.sum_apply, LinearMap.sum_apply,
    ContinuousLinearMap.coe_coe] using hz

/-- Each parity product fixes every vector in the actual Hamiltonian kernel.
ALVV, arXiv:1602.08828v2, `def:DLO` and the frustration-free condition,
lines 1457–1460 and 1496–1501. No uniqueness is required. -/
theorem physicalParityProduct_fixes_kernel
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian z = 0)
    (p : ℕ) : physicalParityProduct Φ p z = z := by
  apply (physicalParityProduct_apply_eq_self_iff Φ hp p z).mpr
  intro i _
  exact bond_apply_eq_zero_of_sum Φ hp hz i

/-- The actual detectability operator fixes the entire original ground kernel.
ALVV, arXiv:1602.08828v2, `def:DLO`, lines 1496–1501. -/
theorem physicalDetectability_fixes_kernel
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i)) {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian z = 0) :
    physicalDetectability Φ z = z := by
  change physicalParityProduct Φ 1 (physicalParityProduct Φ 0 z) = z
  rw [physicalParityProduct_fixes_kernel Φ hp hz, physicalParityProduct_fixes_kernel Φ hp hz]

/-- The physical detectability operator preserves the inner product with
every ground-kernel vector, hence preserves the kernel's orthogonal complement.
ALVV, arXiv:1602.08828v2, the use of `lem:dl` in `thm:FF-tH`, lines 1562–1568.
This assertion does not assume that the kernel is one-dimensional. -/
theorem inner_physicalDetectability_eq
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i))
    {z : EuclideanSpace ℂ (Fin L → Fin q)}
    (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian z = 0)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) : ⟪z, physicalDetectability Φ x⟫_ℂ = ⟪z, x⟫_ℂ := by
  change ⟪z, physicalParityProduct Φ 1 (physicalParityProduct Φ 0 x)⟫_ℂ = ⟪z, x⟫_ℂ
  rw [← ContinuousLinearMap.IsStarProjection.inner_apply_left
    (physicalParityProduct_isStarProjection Φ hp 1), physicalParityProduct_fixes_kernel Φ hp hz]
  rw [← ContinuousLinearMap.IsStarProjection.inner_apply_left
    (physicalParityProduct_isStarProjection Φ hp 0), physicalParityProduct_fixes_kernel Φ hp hz]

/-- A gap above the frustration-free ground vector contracts the orthogonal
complement under the actual physical detectability operator. The estimate
uses squared norms and retains the full denominator, with no upper bound on
the gap. ALVV, arXiv:1602.08828v2, `lem:dl` and its application in `thm:FF-tH`,
lines 1508–1519 and 1562–1568. -/
theorem norm_sq_physicalDetectability_le_of_gappedGroundState
    (Φ : ManyBody.BondInteraction L q)
    (hp : ∀ i, IsStarProjection (Φ.term i))
    {Gamma x : EuclideanSpace ℂ (Fin L → Fin q)} {gamma : ℝ}
    (hΩ : ‖Gamma‖ = 1) (hgap : IsGapped Φ.hamiltonian 0 gamma)
    (hspan : groundSpace Φ.hamiltonian 0 = Submodule.span ℂ {Gamma})
    (hgamma : 0 < gamma) (hx : ‖x‖ = 1) (horth : ⟪Gamma, x⟫_ℂ = 0) :
    ‖physicalDetectability Φ x‖ ^ 2 ≤ 4 / (4 + gamma) := by
  have hGamma : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      Φ.hamiltonian Gamma = 0 := by
    have h0 := ManyBody.mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Gamma)
    rw [Complex.ofReal_zero, zero_smul] at h0
    exact h0
  have horth' : ⟪Gamma, physicalDetectability Φ x⟫_ℂ = 0 :=
    (inner_physicalDetectability_eq Φ hp hGamma x).trans horth
  have hH : Φ.hamiltonian.IsHermitian := Matrix.isHermitian_sum _ fun i _ ↦ (hp i).isSelfAdjoint
  have hgap := (hgap.posSemidef_sub_smul_one hH hΩ hspan).gap_le (physicalDetectability Φ x)
  rw [horth', norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
    zero_mul, sub_zero] at hgap
  have henergy := re_inner_physicalDetectability_le Φ hp x
  rw [hx, one_pow] at henergy
  rw [le_div_iff₀ (show 0 < 4 + gamma by linarith only [hgamma])]
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at hgap
  simp only [ContinuousLinearMap.coe_coe] at hgap
  nlinarith only [hgap, henergy]

end TNLean.MPS.AreaLaw
