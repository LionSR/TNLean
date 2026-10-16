/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ComparatorBounds


/-!
# Upper and lower norm comparisons from an auxiliary pair

The norm comparisons of Proposition 8.1 for a finite product system. A unit ground
vector of a positive gapped Hamiltonian, a physical target `X` and a typical Schmidt
set of `X` determine one sequence of common auxiliary labels. The projected vectors
`pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k}` are nonzero, symmetric, of norm at most one,
exact mean-energy eigenvectors, and carry the same label on both auxiliary systems.
For every finite collection of nested status partitions, every weight `0 < a ≤ a₀`
and every mean tree, the inverse-power norm of the band product satisfies the rough
and sharp upper and lower comparisons, with remainders uniform in the tree, its
terminal probabilities and the symmetric coordinates. The entropy identity and the
nonnegativity of the pre-comparison entropy expression hold exactly.

The rough upper bound uses the nested prefix data; the rough lower bound uses neither
the prefix data nor the marginal moment data; both sharp bounds use the marginal moment
data and `a ≤ c / √𝓑`, and the sharp upper bound uses no prefix data. The rough
constant is universal, the sharp constant depends only on `C₀`, and the threshold `c`
depends only on `c₀`. The lower comparisons hold for every symmetric vector of norm at
most one carrying the common label on both auxiliary systems, in particular for
`pre_k`, with one remainder for all of them.

The physical sites carry arbitrary finite local spaces. The proof assembles the
general comparisons of QICLean for the actual band product; the band factorization of
the mean-tree root is the commuting-band factorization of the leaves.

## Main definitions

* `TNLean.PEPS.AreaLaw.Scan.Comparators.ComparatorsStatement`: Proposition 8.1, with the
  data of `TNLean.PEPS.AreaLaw.Scan.ComparatorData`.

## Main result

* `TNLean.PEPS.AreaLaw.Scan.Comparators.comparatorsStatement`: Proposition 8.1 holds.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Proposition 8.1 (`prop:comparators`), `07-comparators.tex`, lines 125–214, with the
standing data of lines 13–123. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proofs are written from the
manuscript; no Lean declaration of the accompanying development is reused.
-/

noncomputable section

open Filter Topology Matrix TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  symmDiff
namespace TNLean.PEPS.AreaLaw.Scan.Comparators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

open Classical in
/-- **Proposition 8.1** (`prop:comparators`, `07-comparators.tex`, lines 125–214).

There are an absolute `a₀ > 0` and a universal rough constant `C`, and for all `C₀, c₀ > 0`
a sharp constant `C'` and a threshold `c > 0`, with the following property. Let `Ω` be the
unit ground vector, with energy `E₀` and gap `g > 0`, of a positive Hamiltonian `H` on a
finite product system (lines 15–19), let `X` be a physical target and `E` a typical Schmidt
set of width `w` (`comparator:typical-set`). Put `d_* = |E|`, `z = ∑_{i ∈ E} p_i` and
`S' = -∑_{i ∈ E} p'_i log p'_i`. There are common auxiliary labels `λ_k` such that
`pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k} ∈ 𝒮_k` is nonzero, has norm at most one, is a
physical mean-energy eigenvector of eigenvalue `E₀` and has label `λ_k` on both `C` and `R`
(`comparator:prevector`, lines 131–142). The labels precede the statuses and the weight.

The entropy identity `comparator:entropy-identity` holds for every physical partition
(lines 198–202). For every finite status family obeying `comparator:nesting`,
`g^pre_{j,g} ≥ 0` (line 181), and for every `0 < a ≤ a₀`, with `t = a/2`, `s = 1/4` and
`W = aK` (lines 99–100), every mean tree with metrics `comparator:metrics`, `N = ‖𝓜^{-s} ξ‖`
and `E_def = (⟨v, H̄ v⟩ - E₀)/g` for `v = 𝓜^{-s} ξ / N` (lines 143–153):

* the rough upper bound `comparator:rough-upper` for `ξ = pre_k` holds under the prefix
  data (lines 154–161);
* the rough lower bound `comparator:rough-lower` holds for every `0 < τ < 1/2`, without
  the prefix or moment data (lines 162–169);
* under the moment data and `a ≤ c/√𝓑`, the sharp upper bound `comparator:sharp-upper` for
  `ξ = pre_k` holds without the prefix data, and the sharp lower bound
  `comparator:sharp-lower` holds for every `0 < τ < 1/2` (lines 171–197).

Every remainder `o_k(1)` is one sequence tending to zero, chosen with the physical system,
the auxiliary dimensions, the status family, `a` and the respective data fixed, and uniform
over the tree, its terminal probabilities, the isometric coordinates `Z` of the symmetric
space and, for the lower bounds, over every symmetric vector `ξ` of norm at most one with
label `λ_k` on both `C` and `R`, which includes `pre_k` (lines 205–213). The maximum
`g_max` is taken over the bands and the labels occurring at the leaves of the tree; since
`g^pre ≥ 0`, inserting `0` changes it only for `K = 0`. -/
def ComparatorsStatement : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 < C ∧
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ → ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → Type) [∀ v, Fintype (β v)]
    [∀ v, DecidableEq (β v)] (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ)
    (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (E₀ gap : ℝ),
    H.PosSemidef → IsGappedGroundState H E₀ Ω gap → 0 < gap →
  ∀ (X : Finset ι) (E : Finset (FiniteProduct.Configuration β X)) (w : ℝ),
    IsTypicalSchmidtSet β Ω X E w →
    let p := (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues
    let S := FiniteProduct.entropy β Ω
    let z := ∑ i ∈ E, p i
    let d := E.card
    let S' := ∑ i ∈ E, Real.negMulLog (p i / z)
    let Hbar := fun k : ℕ ↦ globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k
    let Psym := fun k : ℕ ↦ symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k)
    let LC := fun (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) ↦
      labelProj (subsystemPerm k (siteSpace β d) {some none}) l
    let LR := fun (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) ↦
      labelProj (subsystemPerm k (siteSpace β d) {none}) l
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let pre := prevector β Ω d ell k
        pre ≠ 0 ∧ ‖pre‖ ≤ 1 ∧ Psym k *ᵥ pre = pre ∧ Hbar k *ᵥ pre = (E₀ : ℂ) • pre.ofLp ∧
          LC k (ell k) *ᵥ pre = pre ∧ LR k (ell k) *ᵥ pre = pre) ∧
      (∀ U Y V : Finset ι, Disjoint X U → Disjoint X Y → Disjoint X V → Disjoint U Y →
        Disjoint U V → Disjoint Y V → X ∪ U ∪ Y ∪ V = Finset.univ →
        2 * S X + (S (X ∪ U) + S V - S Y) - (S U + S (U ∪ Y) - S Y) =
          FiniteProduct.mutualInformation β Ω X V +
            FiniteProduct.mutualInformation β Ω X (Y ∪ V)) ∧
      ∀ (St : Type) [Fintype St] [DecidableEq St] (K : ℕ) (U Y V : St → Fin K → Finset ι),
        IsStatusFamily X U Y V →
        let gpre := fun j l ↦ S (X ∪ U j l) + S (V j l) - S (Y j l)
        let gpost := fun j l ↦ S (U j l) + S (U j l ∪ Y j l) - S (Y j l)
        (∀ j l, 0 ≤ gpre j l) ∧
        ∀ a : ℝ, 0 < a → a ≤ a₀ →
        let s : ℝ := 1 / 4
        let t := a / 2
        let W := a * K
        let avg := fun (T : MeanTree St) (f : St → Fin K → ℝ) ↦
          (1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * f j l
        (∀ (R : Finset (Finset ι)) (Bsh Bexc : ℝ), IsPrefixData β Ω X U Y R Bsh Bexc →
          ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
            ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ T : MeanTree St,
              let N := ‖toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
              0 < N ∧ -Real.log (N ^ 2) / k ≤
                2 * Real.log d - Real.log z + 2 * s * W * (2 * Bsh / z + 2 * Bexc) + ρ k) ∧
        (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
          ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
            Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ (T : MeanTree St)
            (ξ : EuclideanSpace ℂ (Config k (siteSpace β d))), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
            Psym k *ᵥ ξ = ξ → LC k (ell k) *ᵥ ξ = ξ → LR k (ell k) *ᵥ ξ = ξ →
            let w := toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
              (toEuclideanLin Zᴴ ξ)
            let N := ‖w‖
            let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
            let Edef := ((star v ⬝ᵥ (Hbar k *ᵥ v)).re - E₀) / gap
            0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
              2 * s * W * (2 * S' - C * (τ * Real.log d + Real.binEntropy τ / a) -
                  C * (Edef / τ) * S') - ρ k ≤ -Real.log (N ^ 2) / k) ∧
        (∀ B : ℝ, IsMarginalMomentData β Ω X U Y V C₀ c₀ B → a ≤ c / Real.sqrt B →
          (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
            ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ T : MeanTree St,
              let N := ‖toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
              0 < N ∧ -Real.log (N ^ 2) / k ≤
                2 * Real.log d - Real.log z +
                  2 * s * W * (avg T gpost + C' * (a * B + |Real.log z| / a)) + ρ k) ∧
          (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
            ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ (T : MeanTree St)
              (ξ : EuclideanSpace ℂ (Config k (siteSpace β d))), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
              Psym k *ᵥ ξ = ξ → LC k (ell k) *ᵥ ξ = ξ → LR k (ell k) *ᵥ ξ = ξ →
              let gmax := (insert (0 : ℝ) ((Finset.univ : Finset (T.labels.toFinset × Fin K)).image
                fun x ↦ gpre x.1.val x.2)).max' (Finset.insert_nonempty _ _)
              let w := toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ ξ)
              let N := ‖w‖
              let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
              let Edef := ((star v ⬝ᵥ (Hbar k *ᵥ v)).re - E₀) / gap
              0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
                2 * s * W * (2 * S' + (1 - τ) * avg T gpre -
                    C' * (τ * Real.log d + Real.binEntropy τ / a + a * B) -
                    C' * (Edef / τ) * (S' + gmax)) - ρ k ≤ -Real.log (N ^ 2) / k))

/-- **Proposition 8.1** (`prop:comparators`, `07-comparators.tex`, lines 125–214) holds,
with `a₀ = 1/10`, rough constant `4`, sharp constant `4 + 25 C₀` and threshold `c = c₀/10`. -/
theorem comparatorsStatement : ComparatorsStatement := by
  refine ⟨1 / 10, by norm_num, 4, by norm_num, fun C₀ c₀ hC₀ hc₀ ↦
    ⟨c₀ / 10, 4 + 25 * C₀, by positivity, by positivity, ?_⟩⟩
  intro ι _ _ β _ _ H Ω E₀ gap hHpos hgs hgap_pos X E w htyp p S z d S' Hbar Psym LC LR
  obtain ⟨hΩ, hE, hgapM⟩ := isGappedGroundState_iff.mp hgs
  have hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass
      E := htyp.mass_pos
  have : NeZero d := ⟨htyp.nonempty.card_pos.ne'⟩
  have : NeZero E.card := ⟨htyp.nonempty.card_pos.ne'⟩
  have : ∀ v, Nonempty (β v) := fun v ↦ by
    by_contra hv
    rw [not_nonempty_iff] at hv
    have h0 : Ω = 0 := by
      ext x
      exact (hv.false (x v)).elim
    simp [h0] at hΩ
  obtain ⟨ell, hpre, hmass, hdim⟩ := exists_prevector_labels β H Ω E₀ hΩ hE X E hz
  rw [vonNeumannEntropy_compressedTypicalPureState_eq_sum β Ω X E hz] at hdim
  have hS' : 0 ≤ S' := Finset.sum_nonneg fun i hi ↦ Real.negMulLog_nonneg
    (div_nonneg ((FiniteProduct.reducedPure_posSemidef β Ω X).eigenvalues_nonneg i) hz.le)
    ((div_le_one hz).mpr (Finset.single_le_sum (fun j _ ↦
      (FiniteProduct.reducedPure_posSemidef β Ω X).eigenvalues_nonneg j) hi))
  refine ⟨ell, hpre, fun U Y V hXU hXY hXV hUY hUV hYV hc ↦
    FiniteProduct.auxiliaryPair_entropyIdentity β Ω X U Y V hXU hXY hXV hUY hUV hYV hc, ?_⟩
  intro St _ _ K U Y V hfam gpre gpost
  refine ⟨fun j l ↦ FiniteProduct.auxiliaryPair_pre_nonneg β Ω hΩ X (U j l) (Y j l) (V j l)
    (hfam.disjoint_XY j l) (hfam.disjoint_XV j l) (hfam.disjoint_UY j l)
    (hfam.disjoint_UV j l) (hfam.disjoint_YV j l) (hfam.cover j l), ?_⟩
  intro a ha ha₀ s t W avg
  refine ⟨fun R Bsh Bexc hR ↦ exists_rough_upper β Ω hΩ X E hz ell hmass U Y V hfam a ha
      R Bsh Bexc hR,
    exists_rough_lower β H Ω E₀ gap hgapM hΩ hgap_pos ell S' hS' hdim X U Y V hfam a ha
      (by linarith), fun B hmom hac ↦ ?_⟩
  have hB : 0 < Real.sqrt B := Real.sqrt_pos.mpr (zero_lt_one.trans_le hmom.one_le)
  have h10 : 10 * a ≤ c₀ / Real.sqrt B := by
    rw [div_right_comm] at hac
    linarith
  exact ⟨exists_sharp_upper β Ω hΩ X E hz ell hmass U Y V hfam C₀ c₀ B (4 + 25 * C₀)
      (by linarith) (by linarith) hmom a ha (by linarith) (by linarith),
    exists_sharp_lower β H Ω E₀ gap hgapM hΩ hgap_pos ell S' hS' hdim X U Y V hfam
      C₀ c₀ B (4 + 25 * C₀) hC₀.le (by linarith) (by linarith) hmom a ha h10 (by linarith)⟩

end TNLean.PEPS.AreaLaw.Scan.Comparators
