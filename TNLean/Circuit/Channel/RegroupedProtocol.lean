/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.SiteBlocking
import TNLean.Circuit.Channel.OnsiteRegisterEncoding
import TNLean.Circuit.Channel.DimensionBoundedConversion

/-!
# Regrouping local channel protocols

This is an internal comparison for enlarged-site channels, motivated by the blocking
argument in arXiv:2103.13367v3, Appendix E. It does not compare enlarged-site gates with
fixed physical ports or establish the source's phase classification. See
`docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

The seam matching on six sites becomes a triangle after grouping pairs. Thus a direct
matching schedule on the blocks needs three colors in general, even though the original
gates are disjoint. This is an obstruction to that schedule, not to every alternative
implementation of the channel.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

open Fin.CommRing

noncomputable section

variable {M k d e : ℕ}

/-- Three colors for a cyclic sequence of bonds: alternate along the path and reserve
the closing bond. For an even number of sites the closing bond uses the odd color. -/
def regroupColor (M : ℕ) (j : Fin M) : Fin 3 :=
  if j.val + 1 = M ∧ M % 2 = 1 then 2 else ⟨j.val % 2, by omega⟩

/-- An even ring uses only the first two colors. -/
theorem regroupColor_lt_two (hM : M % 2 = 0) (j : Fin M) :
    (regroupColor M j).val < 2 := by
  simp [regroupColor, hM]
  omega

private theorem val_add_one [NeZero M] (j : Fin M) :
    (j + 1).val = if j.val + 1 = M then 0 else j.val + 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  rw [Fin.val_add_one]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- Bonds of one color are pairwise disjoint, including the periodic seam and the
one- and two-site rings. -/
theorem regroupColor_pairwiseDisjoint [NeZero M] (c : Fin 3) :
    {j : Fin M | regroupColor M j = c}.PairwiseDisjoint ringBond := by
  intro i hi j hj hij
  have hcolor : regroupColor M i = regroupColor M j := hi.trans hj.symm
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hnext : ∀ a b : Fin M, a ≠ b → regroupColor M a = regroupColor M b → a + 1 ≠ b := by
    intro a b hab hc hn
    have hv := congrArg Fin.val hn
    rw [val_add_one] at hv
    have hvab : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hc' := congrArg Fin.val hc
    simp only [regroupColor] at hc'
    split_ifs at hc' <;> simp at hc' <;>
      split_ifs at hv <;> omega
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hij (hx.symm.trans hy)
  · exact hnext j i hij.symm hcolor.symm (hy.symm.trans hx)
  · exact hnext i j hij hcolor (hx.symm.trans hy)
  · exact hij (add_right_cancel (hx.symm.trans hy))

/-- The seam bonds at positions 1, 3 and 5 are a matching on six sites. -/
theorem sixSite_seam_matching :
    ({1, 3, 5} : Set (Fin 6)).PairwiseDisjoint ringBond := by
  simp only [Set.PairwiseDisjoint, Set.Pairwise, Set.disjoint_left, mem_ringBond,
    Set.mem_insert_iff, Set.mem_singleton_iff, Function.onFun]
  decide

/-- Their images after grouping pairs cannot be put in two whole-block matching
layers. This only concerns a direct partition of the three triangle edges. -/
theorem threeBlock_seams_no_two_colors :
    ¬ ∃ c : Fin 3 → Fin 2, ∀ i j, i ≠ j → c i = c j →
      Disjoint (ringBond i) (ringBond j) := by
  simp only [Set.disjoint_left, mem_ringBond]
  decide

/-- The actual blocking map sends the six-site seam matching to the three triangle
bonds. This connects the obstruction above to grouping consecutive pairs. -/
theorem sixSite_seam_block_image (j : Fin 3) :
    siteBlock (M := 3) (k := 2) '' ringBond (⟨2 * j.val + 1, by omega⟩ : Fin 6) =
      ringBond j := by
  simp only [ringBond, Set.image_pair]
  fin_cases j <;> ext x <;> fin_cases x <;> decide

/-- Every original nearest-neighbor bond lies in its left block and the next block. -/
theorem ringBond_subset_preimage_siteBlock [NeZero M] [NeZero k] (i : Fin (M * k)) :
    ringBond i ⊆ siteBlock ⁻¹' ringBond (siteBlock i) := by
  rintro x (rfl | rfl)
  · exact Or.inl rfl
  · change siteBlock (i + 1) = siteBlock i ∨ siteBlock (i + 1) = siteBlock i + 1
    apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    change (i + 1).val / k = i.val / k ∨ (i + 1).val / k = (siteBlock i + 1).val
    have hik : i.val / k < M := (siteBlock i).isLt
    have hk := Nat.pos_of_ne_zero (NeZero.ne k)
    have hstep : (i.val + 1) / k = i.val / k ∨ (i.val + 1) / k = i.val / k + 1 := by
      rw [Nat.succ_div]
      split_ifs <;> omega
    rw [val_add_one, val_add_one]
    change (if i.val + 1 = M * k then 0 else i.val + 1) / k = i.val / k ∨
      (if i.val + 1 = M * k then 0 else i.val + 1) / k =
        if i.val / k + 1 = M then 0 else i.val / k + 1
    by_cases hseam : i.val + 1 = M * k
    · have hq : (i.val + 1) / k = M := by rw [hseam, Nat.mul_div_cancel _ hk]
      have hlast : i.val / k + 1 = M := by omega
      simp [hseam, hlast]
    · have hlt : (i.val + 1) / k < M :=
        (Nat.div_lt_iff_lt_mul hk).mpr (by omega)
      simp only [ite_eq_right hseam]
      rcases hstep with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [ite_eq_right (by omega)]; exact h)

private theorem supportedKraus_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set ι} {F G : Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)}
    (hF : ∃ r, ∃ A : Fin r → Matrix (ι → Fin d) (ι → Fin d) ℂ,
      F = rectangularKrausMap A ∧ (∑ a, (A a)ᴴ * A a = 1) ∧
        ∀ a, A a ∈ supportedOperators d S)
    (hG : ∃ r, ∃ A : Fin r → Matrix (ι → Fin d) (ι → Fin d) ℂ,
      G = rectangularKrausMap A ∧ (∑ a, (A a)ᴴ * A a = 1) ∧
        ∀ a, A a ∈ supportedOperators d S) :
    ∃ r, ∃ A : Fin r → Matrix (ι → Fin d) (ι → Fin d) ℂ,
      F * G = rectangularKrausMap A ∧ (∑ a, (A a)ᴴ * A a = 1) ∧
        ∀ a, A a ∈ supportedOperators d S := by
  obtain ⟨r, A, rfl, hA, hsA⟩ := hF
  obtain ⟨s, B, rfl, hB, hsB⟩ := hG
  let C (a : Fin (r * s)) := A (finProdFinEquiv.symm a).1 * B (finProdFinEquiv.symm a).2
  refine ⟨r * s, C, ?_, ?_, fun a => mul_mem_supportedOperators (hsA _) (hsB _)⟩
  · apply LinearMap.ext
    intro X
    change (∑ a, A a * (∑ b, B b * X * (B b)ᴴ) * (A a)ᴴ) = _
    change _ = ∑ a, C a * X * (C a)ᴴ
    rw [← finProdFinEquiv.sum_comp]
    simp only [C, Equiv.symm_apply_apply, Fintype.sum_prod_type,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rw [← finProdFinEquiv.sum_comp]
    simp only [C, Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.conjTranspose_mul]
    rw [Finset.sum_comm]
    rw [← hB]
    refine Finset.sum_congr rfl fun b _ => ?_
    have step : ∑ a, (B b)ᴴ * (A a)ᴴ * (A a * B b) =
        (B b)ᴴ * ((∑ a, (A a)ᴴ * A a) * B b) := by
      simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_assoc]
    rw [step, hA, Matrix.one_mul]

private theorem supportedKraus_noncommProd {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (F : α → Module.End ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ))
    (hc : (s : Set α).Pairwise (Function.onFun Commute F)) (S : Set ι)
    (hF : ∀ i ∈ s, ∃ r, ∃ A : Fin r → Matrix (ι → Fin d) (ι → Fin d) ℂ,
      F i = rectangularKrausMap A ∧ (∑ a, (A a)ᴴ * A a = 1) ∧
        ∀ a, A a ∈ supportedOperators d S) :
    ∃ r, ∃ A : Fin r → Matrix (ι → Fin d) (ι → Fin d) ℂ,
      s.noncommProd F hc = rectangularKrausMap A ∧ (∑ a, (A a)ᴴ * A a = 1) ∧
        ∀ a, A a ∈ supportedOperators d S := by
  refine Finset.noncommProd_induction s F hc
    (fun G => ∃ r, ∃ A : Fin r → Matrix (ι → Fin d) (ι → Fin d) ℂ,
      G = rectangularKrausMap A ∧ (∑ a, (A a)ᴴ * A a = 1) ∧
        ∀ a, A a ∈ supportedOperators d S)
    (fun _ _ => supportedKraus_mul) ?_ hF
  refine ⟨1, fun _ => 1, ?_, by simp, fun _ => one_mem_supportedOperators _⟩
  apply LinearMap.ext
  intro X
  change X = ∑ _ : Fin 1, 1 * X * 1ᴴ
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem noncommProd_fibers {α β H : Type*} [DecidableEq β]
    [Monoid H] (s : Finset α) (F : α → H)
    (hc : (s : Set α).Pairwise (Function.onFun Commute F)) (f : α → β) (t : Finset β) :
    ∃ ht : (t : Set β).Pairwise (Function.onFun Commute
        (fun j => (s.filter (f · = j)).noncommProd F
        (hc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))))),
      t.noncommProd (fun j => (s.filter (f · = j)).noncommProd F
        (hc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))) ht =
      (s.filter (f · ∈ t)).noncommProd F
        (hc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))) := by
  classical
  have hcomm (i j : β) : Commute
      ((s.filter (f · = i)).noncommProd F
        (hc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))))
      ((s.filter (f · = j)).noncommProd F
        (hc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))) := by
    apply Finset.noncommProd_commute
    intro b hb
    apply Commute.symm
    apply Finset.noncommProd_commute
    intro a ha
    exact hc.forall₂ (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp ha).1
  refine ⟨fun _ _ _ _ _ => hcomm _ _, ?_⟩
  induction t using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, Finset.filter_false]; rfl
  | @insert j t hj ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj, ih]
    have hset : s.filter (f · ∈ insert j t) = s.filter (f · = j) ∪ s.filter (f · ∈ t) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      tauto
    have hdis : Disjoint (s.filter (f · = j)) (s.filter (f · ∈ t)) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact hj ((Finset.mem_filter.mp ha).2 ▸ (Finset.mem_filter.mp hb).2)
    symm
    exact (Finset.noncommProd_congr hset (fun _ _ => rfl) _).trans
      (Finset.noncommProd_union_of_disjoint hdis F _)

/-- Regroup a channel with possibly different input and output dimensions by the actual
computational-basis blocking equivalences. -/
def regroupChannel (M k : ℕ)
    (F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ) :
    Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ →ₗ[ℂ]
      Matrix (Fin M → Fin (e ^ k)) (Fin M → Fin (e ^ k)) ℂ :=
  (blockSites M k e).toLinearMap ∘ₗ F ∘ₗ (blockSites M k d).symm.toLinearMap

private def regroupEnd (M k d : ℕ) :
    Module.End ℂ (Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ) →*
      Module.End ℂ (Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ) :=
  (blockSites M k d).toLinearEquiv.conjRingEquiv.toMonoidHom

private theorem regroupEnd_kraus
    {r : ℕ} (A : Fin r → Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ) :
    regroupEnd M k d (rectangularKrausMap A) =
      rectangularKrausMap (fun a => blockSites M k d (A a)) := by
  apply LinearMap.ext
  intro X
  change blockSites M k d (∑ a, A a * (blockSites M k d).symm X * (A a)ᴴ) = _
  rw [map_sum]
  change _ = ∑ a, blockSites M k d (A a) * X * (blockSites M k d (A a))ᴴ
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  rfl

/-- Blocking intertwines the constructed map with the original map on every operator. -/
theorem regroupChannel_blockSites
    (F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ) :
    regroupChannel M k F ∘ₗ (blockSites M k d).toLinearMap =
      (blockSites M k e).toLinearMap ∘ₗ F := by
  apply LinearMap.ext
  intro X
  exact congrArg (fun Y => blockSites M k e (F Y)) ((blockSites M k d).symm_apply_apply X)

private theorem regroupChannel_comp {f : ℕ}
    (F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ)
    (G : Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin f) (Fin (M * k) → Fin f) ℂ) :
    regroupChannel M k (G ∘ₗ F) = regroupChannel M k G ∘ₗ regroupChannel M k F := by
  apply LinearMap.ext
  intro X
  simp [regroupChannel]

private def blockMatrixEquiv (k d : ℕ) :
    Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ ≃ₐ[ℂ]
      Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ finFunctionFinEquiv

namespace OnsiteChannel

private def inBlock (Φ : OnsiteChannel d e (Fin (M * k))) (j : Fin M) :
    OnsiteChannel d e (Fin k) where
  r t := Φ.r (finProdFinEquiv (j, t))
  kraus t := Φ.kraus (finProdFinEquiv (j, t))
  sum_kraus _ := Φ.sum_kraus _

/-- The product of the original onsite channels inside each block. Both the input and
output local dimension are allowed to vary, as in the original protocol. -/
def regroup (Φ : OnsiteChannel d e (Fin (M * k))) :
    OnsiteChannel (d ^ k) (e ^ k) (Fin M) :=
  ofSiteMaps (fun j => (blockMatrixEquiv k e).toLinearMap ∘ₗ (Φ.inBlock j).map ∘ₗ
      (blockMatrixEquiv k d).symm.toLinearMap) (fun j =>
    isKrausCPTP_comp
      (isKrausCPTP_comp (equivReindexMap_isKrausCPTP finFunctionFinEquiv.symm)
        (Φ.inBlock j).map_isKrausCPTP)
      (equivReindexMap_isKrausCPTP finFunctionFinEquiv))

/-- The concrete grouped onsite channel equals conjugation of the original global
channel on all operators, including correlated inputs. -/
theorem regroup_map (Φ : OnsiteChannel d e (Fin (M * k))) :
    Φ.regroup.map = regroupChannel M k Φ.map := by
  have hprod (A : Fin (M * k) → Matrix (Fin d) (Fin d) ℂ) :
      Φ.regroup.map (blockSites M k d (rectKronecker A)) =
        blockSites M k e (Φ.map (rectKronecker A)) := by
    rw [blockSites_rectKronecker, map_rectKronecker, map_rectKronecker,
      blockSites_rectKronecker]
    congr 1
    funext j
    simp only [regroup, ofSiteMaps_siteMap, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    change blockMatrixEquiv k e ((Φ.inBlock j).map
      ((blockMatrixEquiv k d).symm (blockMatrixEquiv k d
        (rectKronecker (fun t => A (finProdFinEquiv (j, t))))))) = _
    rw [AlgEquiv.symm_apply_apply, map_rectKronecker]
    rfl
  apply LinearMap.ext
  intro X
  obtain ⟨Y, rfl⟩ := (blockSites M k d).surjective X
  change Φ.regroup.map (blockSites M k d Y) =
    blockSites M k e (Φ.map ((blockSites M k d).symm (blockSites M k d Y)))
  rw [AlgEquiv.symm_apply_apply]
  change (Φ.regroup.map ∘ₗ (blockSites M k d).toLinearMap) Y =
    ((blockSites M k e).toLinearMap ∘ₗ Φ.map) Y
  exact LinearMap.eqOn_span' (by rintro _ ⟨A, _, rfl⟩; exact hprod A)
    (mem_supportedOperators_univ Y)

end OnsiteChannel

namespace ChannelLayer

set_option backward.isDefEq.respectTransparency false in
/-- A layer on the original ring has an exact implementation by three actual matching
layers on the grouped ring. If the number of blocks is even, two layers suffice.
Internal gates are bundled with the outgoing block bond and included in this bound. -/
theorem exists_regrouped_layers [NeZero M] [NeZero k] (L : ChannelLayer d (M * k)) :
    ∃ Ls : List (ChannelLayer (d ^ k) M),
      Ls.length ≤ (if M % 2 = 0 then 2 else 3) ∧
        channelCircuitMap Ls = regroupChannel M k L.map := by
  classical
  let F := fun i => regroupEnd M k d (L.gateMap i)
  have hc : (L.bonds : Set (Fin (M * k))).Pairwise (Function.onFun Commute F) :=
    fun _ hi _ hj _ => (L.gateMap_commute.forall₂ hi hj).map (regroupEnd M k d)
  let H := fun j : Fin M => (L.bonds.filter (siteBlock · = j)).noncommProd F
    (hc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
  have hH (j : Fin M) : ∃ r, ∃ A : Fin r →
      Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ,
      H j = rectangularKrausMap A ∧ (∑ a, (A a)ᴴ * A a = 1) ∧
        ∀ a, A a ∈ supportedOperators (d ^ k) (ringBond j) := by
    apply supportedKraus_noncommProd
    intro i hi
    obtain ⟨hi, hij⟩ := Finset.mem_filter.mp hi
    refine ⟨L.r i, fun a => blockSites M k d (L.kraus i a), regroupEnd_kraus _, ?_, ?_⟩
    · change (∑ a, blockSites M k d ((L.kraus i a)ᴴ) *
        blockSites M k d (L.kraus i a)) = 1
      simp only [← map_mul, ← map_sum, L.sum_kraus i hi, map_one]
    · intro a
      apply blockSites_mem_supportedOperators
      apply supportedOperators_mono _ (L.kraus_mem_supportedOperators i hi a)
      simpa only [hij] using ringBond_subset_preimage_siteBlock i
  choose r A hA hnorm hs using hH
  obtain ⟨hHc, hHeq⟩ := noncommProd_fibers L.bonds F hc siteBlock (Finset.univ : Finset (Fin M))
  change (Finset.univ.noncommProd H hHc) = _ at hHeq
  simp only [Finset.mem_univ, Finset.filter_true] at hHeq
  have hHeq' : Finset.univ.noncommProd H hHc = regroupChannel M k L.map := by
    rw [hHeq]
    exact (Finset.map_noncommProd L.bonds L.gateMap L.gateMap_commute
      (regroupEnd M k d)).symm
  let Λ (c : Fin 3) : ChannelLayer (d ^ k) M :=
    { bonds := Finset.univ.filter (regroupColor M · = c)
      r := r
      kraus := A
      kraus_mem_supportedOperators := fun j _ a => hs j a
      sum_kraus := fun j _ => hnorm j
      pairwiseDisjoint := fun i hi j hj hij =>
        regroupColor_pairwiseDisjoint c (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2 hij }
  have hΛ (c : Fin 3) : (Λ c).map =
      (Finset.univ.filter (regroupColor M · = c)).noncommProd H
        (hHc.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))) := by
    apply Finset.noncommProd_congr rfl
    intro j _
    exact (hA j).symm
  obtain ⟨hCc, hCeq⟩ := noncommProd_fibers Finset.univ H hHc (regroupColor M)
    (Finset.univ : Finset (Fin 3))
  simp only [Finset.mem_univ, Finset.filter_true] at hCeq
  rw [hHeq'] at hCeq
  have huniv : (Finset.univ : Finset (Fin 3)) = ([0, 1, 2] : List (Fin 3)).toFinset := by decide
  simp only [huniv] at hCeq
  rw [Finset.noncommProd_toFinset ([0, 1, 2] : List (Fin 3)) _ _ (by decide)] at hCeq
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← hΛ] at hCeq
  by_cases hEven : M % 2 = 0
  · have hΛtwo : (Λ 2).map = 1 := by
      have hempty : (Finset.univ.filter (regroupColor M · = 2)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro j _ hj
        have hlt := regroupColor_lt_two hEven j
        rw [hj] at hlt
        exact (by decide : ¬ (2 : Fin 3).val < 2) hlt
      change (Λ 2).bonds.noncommProd _ _ = 1
      change (Finset.univ.filter (regroupColor M · = 2)).noncommProd _ _ = 1
      simp only [hempty, Finset.noncommProd_empty]
    refine ⟨[Λ 1, Λ 0], by simp [hEven], ?_⟩
    simpa only [channelCircuitMap, hΛtwo, mul_one, one_mul] using hCeq
  · refine ⟨[Λ 2, Λ 1, Λ 0], by simp [hEven], ?_⟩
    simpa only [channelCircuitMap, one_mul, mul_assoc] using hCeq

end ChannelLayer

namespace IsDimensionBoundedLocalChannelProtocol

private theorem append_layers {N B T d e : ℕ} [NeZero N]
    {F : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T F) (Ls : List (ChannelLayer e N)) :
    IsDimensionBoundedLocalChannelProtocol B (T + Ls.length) (channelCircuitMap Ls ∘ₗ F) := by
  induction Ls generalizing T F with
  | nil => exact h
  | cons L Ls ih =>
    have hi := ih (h.layer L)
    rw [List.length_cons, show T + (Ls.length + 1) = T + 1 + Ls.length by omega]
    exact hi

/-- Grouping a dimension-bounded protocol raises its dimension budget to `B ^ k`.
The constructed protocol has depth at most `2T` for an even number of blocks and `3T`
in general. All intermediate onsite dimensions, including ancillas, are retained. -/
theorem exists_regrouped [NeZero M] [NeZero k] {B T : ℕ}
    {F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T F) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsDimensionBoundedLocalChannelProtocol (B ^ k) S (regroupChannel M k F) := by
  induction h with
  | onsite Φ hd he =>
    refine ⟨0, by omega, ?_⟩
    rw [← OnsiteChannel.regroup_map]
    exact .onsite Φ.regroup ⟨Nat.pow_pos hd.1, Nat.pow_le_pow_left hd.2 k⟩
      ⟨Nat.pow_pos he.1, Nat.pow_le_pow_left he.2 k⟩
  | @layer e T F h L ih =>
    obtain ⟨S, hS, hreg⟩ := ih
    obtain ⟨Ls, hLs, heq⟩ := L.exists_regrouped_layers
    refine ⟨S + Ls.length, ?_, ?_⟩
    · calc S + Ls.length ≤ (if M % 2 = 0 then 2 else 3) * T +
          (if M % 2 = 0 then 2 else 3) := Nat.add_le_add hS hLs
        _ = (if M % 2 = 0 then 2 else 3) * (T + 1) := by rw [Nat.mul_add, Nat.mul_one]
    · rw [regroupChannel_comp, ← heq]
      exact hreg.append_layers Ls
  | onsite_comp h Φ hf ih =>
    obtain ⟨S, hS, hreg⟩ := ih
    refine ⟨S, hS, ?_⟩
    rw [regroupChannel_comp, ← OnsiteChannel.regroup_map]
    exact hreg.onsite_comp Φ.regroup ⟨Nat.pow_pos hf.1, Nat.pow_le_pow_left hf.2 k⟩

end IsDimensionBoundedLocalChannelProtocol

/-- Exact regrouping of an arbitrary positive-input protocol, allowing its onsite
registers to change dimension. The equality is between linear maps on all operators. -/
theorem IsLocalChannelProtocol.exists_regrouped [NeZero M] [NeZero k] {T : ℕ}
    {F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    (h : IsLocalChannelProtocol T F) (hd : 0 < d) :
    ∃ S, S ≤ (if M % 2 = 0 then 2 else 3) * T ∧
      IsLocalChannelProtocol S (regroupChannel M k F) := by
  obtain ⟨B, hB⟩ := h.exists_dimension_bound hd
  obtain ⟨S, hS, hreg⟩ := hB.exists_regrouped
  exact ⟨S, hS, hreg.toIsLocalChannelProtocol⟩

/-- The exact regrouping identity also holds with any untouched external reference. -/
theorem regroupChannel_blockSites_reference {δ : Type*}
    (F : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ) :
    tensorMapIdLM (δ := δ) (regroupChannel M k F) ∘ₗ
        tensorMapIdLM (blockSites M k d).toLinearMap =
      tensorMapIdLM (blockSites M k e).toLinearMap ∘ₗ tensorMapIdLM F := by
  simpa only [tensorMapIdLM_comp] using
    congrArg (tensorMapIdLM (δ := δ)) (regroupChannel_blockSites F)

/-- An unblocked conversion followed by a blocked conversion composes with the actual
regrouping overhead on the first depth and additive depth for the second conversion. -/
theorem IsLocalChannelConversion.then_blocked [NeZero M] [NeZero k] {f T U : ℕ}
    {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin (M * k) → Fin e) (Fin (M * k) → Fin e) ℂ}
    {τ : Matrix (Fin M → Fin f) (Fin M → Fin f) ℂ}
    (h₁ : IsLocalChannelConversion T ρ σ)
    (h₂ : IsBlockedLocalChannelConversion k U σ τ) (hd : 0 < d) :
    IsBlockedLocalChannelConversion k ((if M % 2 = 0 then 2 else 3) * T + U) ρ τ := by
  obtain ⟨T', hT, F, hF, hρ⟩ := h₁
  obtain ⟨U', hU, G, hG, hσ⟩ := h₂
  obtain ⟨S, hS, hreg⟩ := hF.exists_regrouped hd
  refine ⟨S + U', Nat.add_le_add (hS.trans (Nat.mul_le_mul_left _ hT)) hU,
    G ∘ₗ regroupChannel M k F, hreg.comp hG, ?_⟩
  change G (regroupChannel M k F (blockSites M k d ρ)) = τ
  have hmap := LinearMap.congr_fun (regroupChannel_blockSites F) ρ
  change regroupChannel M k F (blockSites M k d ρ) = blockSites M k e (F ρ) at hmap
  rw [hmap, hρ]
  exact hσ

private def oneSiteMatrixEquiv (q : ℕ) :
    Matrix (Fin 1 → Fin q) (Fin 1 → Fin q) ℂ ≃ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.funUnique (Fin 1) (Fin q))

private theorem oneSiteMatrixEquiv_rectKronecker
    (A : Fin 1 → Matrix (Fin d) (Fin d) ℂ) :
    oneSiteMatrixEquiv d (rectKronecker A) = A 0 := by
  ext a b
  simp [oneSiteMatrixEquiv, Matrix.reindexAlgEquiv, Matrix.reindex_apply, rectKronecker_apply]

private theorem exists_oneSite_onsite
    {F : Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin 1 → Fin e) (Fin 1 → Fin e) ℂ} (hF : IsKrausCPTP F) :
    ∃ Φ : OnsiteChannel d e (Fin 1), Φ.map = F := by
  let G := (oneSiteMatrixEquiv e).toLinearMap ∘ₗ F ∘ₗ (oneSiteMatrixEquiv d).symm.toLinearMap
  have hG : IsKrausCPTP G := isKrausCPTP_comp
    (isKrausCPTP_comp (equivReindexMap_isKrausCPTP (Equiv.funUnique (Fin 1) (Fin d)).symm) hF)
    (equivReindexMap_isKrausCPTP (Equiv.funUnique (Fin 1) (Fin e)))
  let Φ := OnsiteChannel.ofSiteMaps (fun _ : Fin 1 => G) (fun _ => hG)
  refine ⟨Φ, ?_⟩
  apply LinearMap.ext
  intro X
  apply LinearMap.eqOn_span' (s := {Z | ∃ A : Fin 1 → Matrix (Fin d) (Fin d) ℂ,
    (∀ i ∉ (Set.univ : Set (Fin 1)), A i = 1) ∧ Z = rectKronecker A})
  · rintro _ ⟨A, _, rfl⟩
    apply (oneSiteMatrixEquiv e).injective
    rw [OnsiteChannel.map_rectKronecker, oneSiteMatrixEquiv_rectKronecker]
    simp only [Φ, OnsiteChannel.ofSiteMaps_siteMap]
    change G (A 0) = oneSiteMatrixEquiv e (F (rectKronecker A))
    change oneSiteMatrixEquiv e (F ((oneSiteMatrixEquiv d).symm (A 0))) = _
    rw [← oneSiteMatrixEquiv_rectKronecker A, AlgEquiv.symm_apply_apply]
  · exact mem_supportedOperators_univ X

/-- With one block the entire regrouped channel is onsite and costs zero depth.
This holds for arbitrary finite Kraus channels, independently of their original depth. -/
theorem regroupChannel_oneBlock_depth_zero
    {F : Matrix (Fin (1 * k) → Fin d) (Fin (1 * k) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (1 * k) → Fin e) (Fin (1 * k) → Fin e) ℂ} (hF : IsKrausCPTP F) :
    IsLocalChannelProtocol 0 (regroupChannel 1 k F) := by
  have hG : IsKrausCPTP (regroupChannel 1 k F) :=
    isKrausCPTP_comp (isKrausCPTP_comp blockSites_symm_isKrausCPTP hF) blockSites_isKrausCPTP
  obtain ⟨Φ, hΦ⟩ := exists_oneSite_onsite hG
  rw [← hΦ]
  exact .onsite Φ

end

end QuantumCircuit
