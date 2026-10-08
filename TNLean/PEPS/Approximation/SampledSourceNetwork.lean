/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.SourceGaussianLaw
import TNLean.PEPS.Approximation.DistributedOperatorContraction
import TNLean.PEPS.Approximation.EffectReplacementSources

/-!
# Sampled source factors and participant-pair labels

At each original source occurrence and ordered ket–bra branch pair, the two
sampled matrices use one Gaussian array and one common sample index. Their
Kronecker-product average is the actual sampled source matrix.

The common prepared source slots are equivalent, by their actual endpoints,
to unordered pairs of distinct gate participants. This equivalence extends to
all source occurrences and preserves their gate, endpoint set and sample
assignment. If every participating gate has at most `M` branches, each common
density label has at most `M ^ 2` values, while each sample label has `k` values.
Consequently every constructed virtual alphabet has cardinality at most
`max (M ^ 2) k`. Private dimensions and Schmidt ranks do not enter this bound.

These results do not identify the chronological sampled physical density
with a contraction of party-local tensors. That further identity requires
constructing the local chronological matrix products, including private
preparations, intermediate memories and final partial traces. Gates with no
participating parties contribute scalars and require no sample edges.

## References

- OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2, `04-compression.tex:233–251`,
  `279–309` and `565–588`.
  [Pinned source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex).
  The proofs are independently written from the mathematical source.
-/

noncomputable section
open QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate Kronecker
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The left endpoint operator retains the original source occurrence, the ordered
ket–bra branch pair, and the shared sample index. Source: polynomial-PEPS,
`04-compression.tex:279–309`. -/
def sampledEndpointLeft (e : sourceLocations w)
    (ξζ : branchLabels w e.1 × branchLabels w e.1) (j : Fin k)
    (ω : SourceGaussianSamples w k) :
    Matrix (Fin (sourceDims w e).1) (Fin (sourceDims w e).1) ℂ :=
  ambientSourceU k (lam e ξζ.1) (lam e ξζ.2) (E e ξζ.1) (E e ξζ.2)
    j (ω e ξζ)

/-- The right endpoint uses the conjugate of precisely the same Gaussian array
and the same sample index as the left endpoint. Source: polynomial-PEPS,
`04-compression.tex:279–309`. -/
def sampledEndpointRight (e : sourceLocations w)
    (ξζ : branchLabels w e.1 × branchLabels w e.1) (j : Fin k)
    (ω : SourceGaussianSamples w k) :
    Matrix (Fin (sourceDims w e).2) (Fin (sourceDims w e).2) ℂ :=
  ambientSourceV k (lam e ξζ.1) (lam e ξζ.2) (F e ξζ.1) (F e ξζ.2)
    j (ω e ξζ)

/-- The actual sampled source is the average of its two endpoint factors;
the factorization follows from the constructed matrices. Source: polynomial-PEPS,
`04-compression.tex:279–309`. -/
theorem sampledSourceMatrix_eq_endpoint_average (e : sourceLocations w)
    (ξ ζ : branchLabels w e.1) (ω : SourceGaussianSamples w k) :
    sampledSourceMatrix w k lam E F e ξ ζ ω =
      (k : ℂ)⁻¹ • ∑ j : Fin k,
        sampledEndpointLeft w k lam E e (ξ, ζ) j ω ⊗ₖ
          sampledEndpointRight w k lam F e (ξ, ζ) j ω := rfl

/-- The ordered density label has the square of the actual branch cardinality.
Source: polynomial-PEPS, `04-compression.tex:565–573`. -/
theorem card_densityBranchLabels (g : w.gateLocations) :
    Fintype.card (branchLabels w g × branchLabels w g) =
      (Fintype.card (branchLabels w g)) ^ 2 := by
  simp only [Fintype.card_prod, pow_two]

/-- The unordered party pair of an actual common source slot. Source:
polynomial-PEPS, `04-compression.tex:233–251` and `568–573`. -/
def sourcePairAt (g : w.gateLocations) (i : Fin (w.slotCount g)) : Sym2 P :=
  Sym2.mk (w.endpoints ⟨g, i⟩).1 (w.endpoints ⟨g, i⟩).2

/-- Distinct common slots of one gate have distinct unordered endpoint pairs.
Source: polynomial-PEPS, `04-compression.tex:233–251` and `568–573`. -/
theorem sourcePairAt_injective (g : w.gateLocations) :
    Function.Injective (w.sourcePairAt g) := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv => cases g with
    | inl g => exact ihw g
    | inr g => exact ihv g
  | localMap => exact nomatch g
  | @gate C ι _ _ owner a b c G tail =>
      intro i j h
      change Sym2.map owner ((G.slots.get i).partyPair) =
        Sym2.map owner ((G.slots.get j).partyPair) at h
      have hi : i.val < (G.slots.map PairSource.partyPair).length := by
        simpa only [List.length_map, slotCount] using i.isLt
      have hj : j.val < (G.slots.map PairSource.partyPair).length := by
        simpa only [List.length_map, slotCount] using j.isLt
      have hp := Sym2.map.injective owner.injective h
      change G.slots[i.val].partyPair = G.slots[j.val].partyPair at hp
      have heq := G.pair_nodup.injective_get (a₁ := ⟨i.val, hi⟩) (a₂ := ⟨j.val, hj⟩)
        (by simpa only [List.get_eq_getElem, List.getElem_map] using hp)
      exact Fin.ext (congrArg (fun x : Fin (G.slots.map PairSource.partyPair).length ↦ x.val) heq)
  | swap => exact nomatch g
  | frame r w ih => exact ih g

open TNLean.PEPS.Approximation
variable [DecidableEq P]

/-- An actual slot is an admissible participant-pair sample label. Source:
polynomial-PEPS, `04-compression.tex:233–251` and `568–573`. -/
def sourceSlotPair (g : w.gateLocations) (i : Fin (w.slotCount g)) :
    {pair : Sym2 P // pair ∈ pairSampleLabels (w.participants g)} :=
  ⟨w.sourcePairAt g i, (mk_mem_pairSampleLabels _ _ _).mpr
    ⟨(w.endpoints_mem_participants ⟨g, i⟩).1,
      (w.endpoints_mem_participants ⟨g, i⟩).2, w.endpoints_ne ⟨g, i⟩⟩⟩

/-- The source-slot map is a bijection onto the gate's actual pair-sample labels.
Source: polynomial-PEPS, `04-compression.tex:233–251` and `568–573`. -/
theorem sourceSlotPair_bijective (g : w.gateLocations) :
    Function.Bijective (w.sourceSlotPair g) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨fun i j h ↦ w.sourcePairAt_injective g (congrArg Subtype.val h),
    by simp only [Fintype.card_fin, Fintype.card_coe, slotCount_eq_choose,
      card_pairSampleLabels]⟩

/-- The common source slots and the unordered participant-pair sample labels
are equivalent by the actual endpoint map. Source: polynomial-PEPS,
`04-compression.tex:233–251` and `568–573`. -/
def sourceSlotPairEquiv (g : w.gateLocations) :
    Fin (w.slotCount g) ≃
      {pair : Sym2 P // pair ∈ pairSampleLabels (w.participants g)} :=
  Equiv.ofBijective (w.sourceSlotPair g) (w.sourceSlotPair_bijective g)

/-- The equivalence records precisely the unordered pair of actual endpoints.
Source: polynomial-PEPS, `04-compression.tex:568–573`. -/
theorem sourceSlotPairEquiv_endpoints (g : w.gateLocations) (i : Fin (w.slotCount g)) :
    (w.sourceSlotPairEquiv g i).val =
      Sym2.mk (w.endpoints ⟨g, i⟩).1 (w.endpoints ⟨g, i⟩).2 := rfl

local instance : DecidableEq w.gateLocations := Classical.decEq _

/-- Every actual source location is exactly one gate-tagged sample edge.
This construction does not choose a star root or require nonempty gates.
Source: polynomial-PEPS, `04-compression.tex:568–573`. -/
def sourceSampleEquiv : w.sourceLocations ≃
    DistributedOperatorContraction.Sample (Finset.univ : Finset w.gateLocations)
      w.participants where
  toFun e := ⟨⟨e.1, Finset.mem_univ _⟩, w.sourceSlotPairEquiv e.1 e.2⟩
  invFun s := ⟨s.1.val, (w.sourceSlotPairEquiv s.1.val).symm s.2⟩
  left_inv := by
    rintro ⟨g, i⟩
    simp only [Equiv.symm_apply_apply]
    rfl
  right_inv := by
    rintro ⟨⟨g, hg⟩, s⟩
    simp only [Equiv.apply_symm_apply]

/-- The gate occurrence is preserved by the sample-edge equivalence.
Source: polynomial-PEPS, `04-compression.tex:568–573`. -/
theorem sourceSampleEquiv_gate (e : w.sourceLocations) :
    (w.sourceSampleEquiv e).1.val = e.1 := rfl

/-- Sample-edge locality is precisely locality of the actual source endpoints.
Source: polynomial-PEPS, `04-compression.tex:568–573` and `581–588`. -/
theorem sourceSampleEquiv_parties (e : w.sourceLocations) :
    (w.sourceSampleEquiv e).2.val.toFinset =
      {(w.endpoints e).1, (w.endpoints e).2} := by
  exact Sym2.toFinset_mk_eq

/-- Sample assignments on actual sources reindex onto the constructed pair edges.
Source: polynomial-PEPS, `04-compression.tex:568–573`. -/
def sourceSampleIndices (j : w.sourceLocations → Fin k) :
    DistributedOperatorContraction.Sample (Finset.univ : Finset w.gateLocations)
      w.participants → Fin k :=
  j ∘ w.sourceSampleEquiv.symm

/-- Reindexing preserves the literal shared sample at each actual source.
Source: polynomial-PEPS, `04-compression.tex:568–573`. -/
theorem sourceSampleIndices_apply (j : w.sourceLocations → Fin k)
    (e : w.sourceLocations) :
    w.sourceSampleIndices k j (w.sourceSampleEquiv e) = j e := by
  simp only [sourceSampleIndices, Function.comp_apply, Equiv.symm_apply_apply]

omit [DecidableEq P] in
/-- A bound on actual ket branch cardinalities gives the square bound on the
common ordered ket–bra labels. Source: polynomial-PEPS,
`04-compression.tex:267–278` and `565–573`. -/
theorem card_densityBranchLabels_le (g : w.gateLocations) (M : ℕ)
    (hM : Fintype.card (w.branchLabels g) ≤ M) :
    Fintype.card (w.branchLabels g × w.branchLabels g) ≤ M ^ 2 := by
  simpa only [Fintype.card_prod, pow_two] using Nat.mul_le_mul hM hM

/-- The constructed virtual alphabets depend only on actual branch counts and
the number of samples, independently of private or Schmidt dimensions.
Source: polynomial-PEPS, `04-compression.tex:565–588`. -/
theorem card_sourceNetworkAlphabet_le (gates : Finset w.gateLocations)
    (root : w.gateLocations → P) (M : ℕ)
    (hM : ∀ g ∈ gates, Fintype.card (w.branchLabels g) ≤ M)
    (e : DistributedOperatorContraction.Link gates w.participants root) :
    Fintype.card (DistributedOperatorContraction.alphabet gates w.participants root
      (fun g ↦ w.branchLabels g × w.branchLabels g) k e) ≤ max (M ^ 2) k :=
  DistributedOperatorContraction.card_alphabet_le gates w.participants root
    (fun g ↦ w.branchLabels g × w.branchLabels g) k (M ^ 2)
    (fun g hg ↦ w.card_densityBranchLabels_le g M (hM g hg)) e

end TNLean.PEPS.PairEffect.SourceCircuit
