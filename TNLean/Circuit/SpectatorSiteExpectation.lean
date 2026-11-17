/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteEmbedding
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.RegionUnion
import QICLean.ManyBody.Sites.Twirl
import QICLean.Algebra.L2OpNormReindex

/-!
# Site expectations with an untouched spectator

A finite spectator `Aux` is one more site of the system: the sites are `Option ι`, the
physical sites `some i` carry `Fin q` and the site `none` carries `Aux`. The spectator
expectation onto the retained physical sites `K` is the region expectation of this system
onto `K` together with the spectator site, written in the coordinates
`(ι → Fin q) × Aux`. It acts on the physical matrix indices of each spectator block, it is
contractive in the matrix `L²` operator norm, and its localization error is bounded by the
sum of physical on-site commutator bounds, independently of the spectator dimension. No
Hermiticity assumption is imposed on the operator being averaged.

The set `K` consists of the retained physical sites. Averaging over a set `Q`
of physical sites therefore means taking `K = Qᶜ`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–139, especially the averaging argument before
`eq:amplification-shell-oscillation`, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
formalized from the manuscript; no upstream Lean proof text is reused.

## Main definitions

* `QuantumCircuit.spectatorBasis` — the basis types of the physical sites and the spectator.
* `QuantumCircuit.spectatorConfigEquiv` — configurations of this system as pairs of a
  physical configuration and a spectator label.
* `QuantumCircuit.spectatorSiteExpectation` — the region expectation onto the retained
  physical sites and the spectator.

## Main results

* `QuantumCircuit.spectatorSiteExpectation_apply` — the spectator expectation applies the
  region expectation of the physical sites to each spectator block.
* `QuantumCircuit.norm_spectatorSiteExpectation_le`,
  `QuantumCircuit.norm_sub_spectatorSiteExpectation_le` — contraction and the localization
  error through on-site commutators, from `ManyBody.norm_regionExpectation_le` and
  `ManyBody.norm_sub_regionExpectation_le`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix ManyBody
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit

universe u

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Aux : Type u} [Fintype Aux] [DecidableEq Aux]

/-! ### The system of physical sites and one spectator site -/

/-- The basis types of the sites `Option ι`: the physical sites `some i` carry `Fin q`, and
the spectator site `none` carries `Aux`. Source: area law, `09-amplification.tex`,
lines 111–121 (operators acting on the physical sites and on spectators). The physical labels
are lifted to the universe of `Aux`. -/
abbrev spectatorBasis (q : ℕ) (Aux : Type u) : Option ι → Type u
  | none => Aux
  | some _ => ULift (Fin q)

instance spectatorBasis.instFintype : ∀ o : Option ι, Fintype (spectatorBasis q Aux o)
  | none => inferInstanceAs (Fintype Aux)
  | some _ => inferInstanceAs (Fintype (ULift (Fin q)))

instance spectatorBasis.instDecidableEq : ∀ o : Option ι, DecidableEq (spectatorBasis q Aux o)
  | none => inferInstanceAs (DecidableEq Aux)
  | some _ => inferInstanceAs (DecidableEq (ULift (Fin q)))

/-- A configuration of the physical sites and the spectator is a physical configuration
together with a spectator label. -/
def spectatorConfigEquiv (q : ℕ) (ι : Type*) (Aux : Type u) :
    Config (spectatorBasis (ι := ι) q Aux) ≃ (ι → Fin q) × Aux where
  toFun x := (fun i ↦ (x (some i)).down, x none)
  invFun p o := match o with
    | none => p.2
    | some i => ULift.up (p.1 i)
  left_inv x := by funext o; cases o <;> rfl
  right_inv _ := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype Aux] [DecidableEq Aux] in
@[simp] theorem spectatorConfigEquiv_symm_apply_none (p : (ι → Fin q) × Aux) :
    (spectatorConfigEquiv q ι Aux).symm p none = p.2 := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype Aux] [DecidableEq Aux] in
@[simp] theorem spectatorConfigEquiv_symm_apply_some (p : (ι → Fin q) × Aux) (i : ι) :
    (spectatorConfigEquiv q ι Aux).symm p (some i) = ULift.up (p.1 i) := rfl

/-- The physical sites outside `K` are the sites of the enlarged system outside `K` and the
spectator. -/
def spectatorComplEquiv (K : Finset ι) :
    {i // i ∉ K} ≃ {o : Option ι // o ∉ Finset.insertNone K} where
  toFun i := ⟨some i.1, fun h ↦ i.2 (Finset.some_mem_insertNone.mp h)⟩
  invFun o := ⟨o.1.get (Option.ne_none_iff_isSome.mp fun h ↦ o.2 (h ▸ Finset.none_mem_insertNone)),
    fun h ↦ o.2 (by
      obtain ⟨o, ho⟩ := o
      cases o with
      | none => exact Finset.none_mem_insertNone
      | some i => exact Finset.some_mem_insertNone.mpr h)⟩
  left_inv _ := rfl
  right_inv o := by
    obtain ⟨o, ho⟩ := o
    cases o with
    | none => exact absurd Finset.none_mem_insertNone ho
    | some i => rfl

/-! ### The spectator expectation -/

/-- The spectator expectation onto the retained physical sites `K`: the region expectation of
the system of physical sites and the spectator onto `K` and the spectator site, in the
coordinates `(ι → Fin q) × Aux`. Source: area law, `09-amplification.tex`, lines 111–121,
including the sentence about operators acting on spectators. -/
noncomputable def spectatorSiteExpectation (q : ℕ) (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ :=
  reindex (spectatorConfigEquiv q ι Aux) (spectatorConfigEquiv q ι Aux)
    (regionExpectation (Finset.insertNone K)
      (reindex (spectatorConfigEquiv q ι Aux).symm (spectatorConfigEquiv q ι Aux).symm B))

/-- The spectator expectation applies the region expectation of the physical sites to each
spectator block. Source: area law, `09-amplification.tex`, lines 111–121. -/
theorem spectatorSiteExpectation_apply (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (σ τ : ι → Fin q) (a b : Aux) :
    spectatorSiteExpectation q K B (σ, a) (τ, b) =
      regionExpectation K (Matrix.of fun σ' τ' ↦ B (σ', a) (τ', b)) σ τ := by
  set e := spectatorConfigEquiv q ι Aux
  let φ : ComplConfig (spectatorBasis (ι := ι) q Aux) (Finset.insertNone K) ≃
      ComplConfig (fun _ : ι ↦ Fin q) K :=
    (Equiv.piCongrLeft (fun o : {o : Option ι // o ∉ Finset.insertNone K} ↦
      spectatorBasis q Aux o.1) (spectatorComplEquiv K)).symm.trans
      (Equiv.piCongrRight fun _ ↦ Equiv.ulift)
  have hφ (y) (i : {i // i ∉ K}) : φ y i = (y (spectatorComplEquiv K i)).down := rfl
  have hcard : Fintype.card (ComplConfig (spectatorBasis (ι := ι) q Aux) (Finset.insertNone K)) =
      Fintype.card (ComplConfig (fun _ : ι ↦ Fin q) K) := Fintype.card_congr φ
  have hagree : (∀ o ∉ Finset.insertNone K, e.symm (σ, a) o = e.symm (τ, b) o) ↔
      ∀ i ∉ K, σ i = τ i := by
    refine ⟨fun h i hi ↦ congrArg ULift.down
      (h (some i) fun h' ↦ hi (Finset.some_mem_insertNone.mp h')), ?_⟩
    rintro h (_ | i) hi
    · exact absurd Finset.none_mem_insertNone hi
    · exact congrArg ULift.up (h i fun h' ↦ hi (Finset.some_mem_insertNone.mpr h'))
  have hglue (ρ : (ι → Fin q) × Aux) (y) :
      e ((cutEquiv _ (Finset.insertNone K)).symm ((cutEquiv _ (Finset.insertNone K) (e.symm ρ)).1,
          y)) = ((cutEquiv (fun _ : ι ↦ Fin q) K).symm ((cutEquiv _ K ρ.1).1, φ y), ρ.2) := by
    refine Prod.ext (funext fun i ↦ ?_) ?_
    · by_cases hi : i ∈ K
      · change ((cutEquiv (spectatorBasis q Aux) (Finset.insertNone K)).symm _ (some i)).down =
          (cutEquiv (fun _ : ι ↦ Fin q) K).symm _ i
        rw [cutEquiv_symm_apply_mem _ _ (Finset.some_mem_insertNone.mpr hi),
          cutEquiv_symm_apply_mem _ _ hi]
        rfl
      · change ((cutEquiv (spectatorBasis q Aux) (Finset.insertNone K)).symm _ (some i)).down =
          (cutEquiv (fun _ : ι ↦ Fin q) K).symm _ i
        rw [cutEquiv_symm_apply_not_mem _ _ (fun h ↦ hi (Finset.some_mem_insertNone.mp h)),
          cutEquiv_symm_apply_not_mem _ _ hi, hφ]
        rfl
    · change (cutEquiv (spectatorBasis q Aux) (Finset.insertNone K)).symm _ none = ρ.2
      rw [cutEquiv_symm_apply_mem _ _ Finset.none_mem_insertNone]
      rfl
  rw [spectatorSiteExpectation, reindex_apply, submatrix_apply, regionExpectation_apply,
    regionExpectation_apply, hcard]
  congr 1
  by_cases h : ∀ i ∉ K, σ i = τ i
  · rw [ite_eq_left (hagree.mpr h), ite_eq_left h]
    refine Fintype.sum_equiv φ _ _ fun y ↦ ?_
    simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Matrix.of_apply]
    rw [hglue (σ, a) y, hglue (τ, b) y]
  · rw [ite_eq_right (mt hagree.mp h), ite_eq_right h]

/-- On a simple tensor, only the physical factor is averaged. In particular,
this formula preserves arbitrary, possibly non-Hermitian spectator operators.
Source: area law, `09-amplification.tex`, lines 111–121. -/
theorem spectatorSiteExpectation_kronecker (K : Finset ι)
    (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Matrix Aux Aux ℂ) :
    spectatorSiteExpectation q K (A ⊗ₖ S) = regionExpectation K A ⊗ₖ S := by
  ext ⟨σ, a⟩ ⟨τ, b⟩
  have hblock : (Matrix.of fun σ' τ' => (A ⊗ₖ S) (σ', a) (τ', b)) = S a b • A := by
    ext σ' τ'
    simp [Matrix.kroneckerMap_apply, mul_comm]
  rw [spectatorSiteExpectation_apply, hblock, regionExpectation_smul]
  simp [Matrix.kroneckerMap_apply, mul_comm]

/-- An operator acting only on the spectator is fixed by every physical site
expectation. Source: area law, `09-amplification.tex`, lines 111–121. -/
@[simp] theorem spectatorSiteExpectation_one_kronecker (K : Finset ι)
    (S : Matrix Aux Aux ℂ) :
    spectatorSiteExpectation q K ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S) =
      (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S := by
  rw [spectatorSiteExpectation_kronecker, regionExpectation_one]

/-- The averaged operator commutes with every physical operator supported
outside `K`, with the spectator left untouched. Source: area law,
`09-amplification.tex`, lines 113–121 (the result commutes with the algebra on
the averaged set). -/
theorem spectatorSiteExpectation_commute (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    {U : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hU : U ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Kᶜ) :
    Commute (spectatorSiteExpectation q K B) (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) := by
  change spectatorSiteExpectation q K B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) =
    (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * spectatorSiteExpectation q K B
  ext ⟨σ, a⟩ ⟨τ, b⟩
  have h := congrArg (fun M : Matrix (ι → Fin q) (ι → Fin q) ℂ => M σ τ)
    (ManyBody.commute_of_mem_supportedOperators_of_disjoint
        (regionExpectation_mem_supportedOperators K (Matrix.of fun σ' τ' => B (σ', a) (τ', b))) hU
        disjoint_compl_right).eq
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_ite, ite_mul, spectatorSiteExpectation_apply] using h

/-- Retaining every physical site gives the identity map, even in the presence
of a spectator. Source: area law, `09-amplification.tex`, lines 101 and 111–121. -/
@[simp] theorem spectatorSiteExpectation_univ
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q Finset.univ B = B := by
  ext ⟨σ, a⟩ ⟨τ, b⟩
  rw [spectatorSiteExpectation_apply, regionExpectation_of_mem_supportedOperators
    (by rw [supportedOperators_univ]; trivial)]
  rfl

/-- The site expectation is a contraction after tensoring with the identity on
any finite spectator. Source: area law, `09-amplification.tex`, lines 111–121.
The norm is the matrix `L²` operator norm. -/
theorem norm_spectatorSiteExpectation_le (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorSiteExpectation q K B‖ ≤ ‖B‖ :=
  (l2_opNorm_reindex_le_equiv _ _).trans <| (norm_regionExpectation_le _).trans
    (l2_opNorm_reindex_le_equiv _ _)

/-- An operator on the enlarged system supported on one physical site `some i` is a physical
operator supported on `{i}`, tensored with the identity on the spectator; it is unitary when
the operator is. -/
private theorem exists_kronecker_one_of_mem_supportedOperators_some {i : ι}
    {U : Matrix (Config (spectatorBasis (ι := ι) q Aux))
      (Config (spectatorBasis (ι := ι) q Aux)) ℂ}
    (hU : U ∈ ManyBody.supportedOperators (spectatorBasis (ι := ι) q Aux) {some i})
    (hUu : U ∈ unitary (Matrix (Config (spectatorBasis (ι := ι) q Aux))
      (Config (spectatorBasis (ι := ι) q Aux)) ℂ)) :
    ∃ U₀ ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({i} : Finset ι),
        U₀ ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) ∧
      reindex (spectatorConfigEquiv q ι Aux) (spectatorConfigEquiv q ι Aux) U =
        U₀ ⊗ₖ (1 : Matrix Aux Aux ℂ) := by
  set e := spectatorConfigEquiv q ι Aux
  rcases isEmpty_or_nonempty Aux with hAux | hAux
  · exact ⟨1, (one_mem (ManyBody.supportedOperators _ _)), one_mem _, Subsingleton.elim _ _⟩
  obtain ⟨a₀⟩ := hAux
  let U₀ : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
    Matrix.of fun σ τ ↦ U (e.symm (σ, a₀)) (e.symm (τ, a₀))
  have hfac : reindex e e U = U₀ ⊗ₖ (1 : Matrix Aux Aux ℂ) := by
    ext ⟨σ, a⟩ ⟨τ, b⟩
    rw [reindex_apply, submatrix_apply, kroneckerMap_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl, mul_one]
      refine ManyBody.apply_eq_of_mem_supportedOperators hU (fun v hv ↦ ?_) (fun v hv ↦ ?_)
        fun v hv ↦ ?_
      · rw [Finset.mem_singleton.mp hv]; rfl
      · rw [Finset.mem_singleton.mp hv]; rfl
      · cases v with
        | none => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
        | some j => exact Iff.rfl
    · rw [ite_eq_right hab, mul_zero]
      exact ManyBody.apply_eq_zero_of_mem_supportedOperators hU (v := none)
        (fun h ↦ by simp at h) hab
  have hU₀ : U₀ ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({i} : Finset ι) := by
    refine ⟨fun σ τ ⟨j, hj, hne⟩ ↦ ?_,
      fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
    · exact ManyBody.apply_eq_zero_of_mem_supportedOperators hU (v := some j)
        (fun h ↦ hj (Finset.mem_singleton.mpr (Option.some_injective _
          (Finset.mem_singleton.mp h)))) fun h ↦ hne (congrArg ULift.down h)
    · refine (ManyBody.mem_supportedOperators_iff.mp hU).2 _ _ _ _ (fun v hv ↦ ?_) (fun v hv ↦ ?_)
        (fun v hv ↦ ?_) fun v hv ↦ ?_
      · rw [Finset.mem_singleton.mp hv]
        exact congrArg ULift.up (h1 i (Finset.mem_singleton_self i))
      · rw [Finset.mem_singleton.mp hv]
        exact congrArg ULift.up (h2 i (Finset.mem_singleton_self i))
      · cases v with
        | none => rfl
        | some j => exact congrArg ULift.up (h3 j fun h ↦ hv (Finset.mem_singleton.mpr
            (congrArg some (Finset.mem_singleton.mp h))))
      · cases v with
        | none => rfl
        | some j => exact congrArg ULift.up (h4 j fun h ↦ hv (Finset.mem_singleton.mpr
            (congrArg some (Finset.mem_singleton.mp h))))
  have hmul (M N : Matrix (Config (spectatorBasis (ι := ι) q Aux))
      (Config (spectatorBasis (ι := ι) q Aux)) ℂ) :
      reindex e e M * reindex e e N = reindex e e (M * N) := by
    simp only [reindex_apply, submatrix_mul_equiv]
  have hunit : reindex e e U ∈ unitary (Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) := by
    rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_reindex, hmul, hmul,
      ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hUu, Unitary.mul_star_self_of_mem hUu]
    simp [reindex_apply]
  refine ⟨U₀, hU₀, ?_, hfac⟩
  rw [hfac] at hunit
  have h1 := Unitary.star_mul_self_of_mem hunit
  have h2 := Unitary.mul_star_self_of_mem hunit
  simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul] at h1 h2
  have hcancel {M : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hM : M ⊗ₖ (1 : Matrix Aux Aux ℂ) = 1) :
      M = 1 := by
    ext σ τ
    have := congrFun (congrFun hM (σ, a₀)) (τ, a₀)
    simpa [kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff] using this
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  exact ⟨hcancel h1, hcancel h2⟩

/-- Averaging outside `K` changes an arbitrary operator by at most the sum of
its physical on-site commutator bounds. Every test unitary acts as the identity
on the spectator, and the estimate has no spectator dimension factor. Source:
area law, `09-amplification.tex`, lines 111–121, the averaging argument before
`eq:amplification-shell-oscillation`. -/
theorem norm_sub_spectatorSiteExpectation_le (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (ε : ι → ℝ)
    (hε : ∀ y ∉ K, ∀ U ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({y} : Finset ι),
      U ∈ unitary (Matrix (ι → Fin q) (ι → Fin q) ℂ) →
        ‖B * (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ ≤ ε y) :
    ‖B - spectatorSiteExpectation q K B‖ ≤ ∑ y ∈ Kᶜ, ε y := by
  set e := spectatorConfigEquiv q ι Aux
  set B' := reindex e.symm e.symm B
  have hB : B = reindex e e B' := by simp [B']
  have hdiff : B - spectatorSiteExpectation q K B =
      reindex e e (B' - regionExpectation (Finset.insertNone K) B') := by
    conv_lhs => rw [hB]
    ext x y
    simp [spectatorSiteExpectation, B', Matrix.sub_apply, e]
  have hsum : ∑ o ∈ (Finset.insertNone K)ᶜ, Option.elim o 0 ε = ∑ y ∈ Kᶜ, ε y := by
    have hc : (Finset.insertNone K)ᶜ = Kᶜ.map Function.Embedding.some := by
      ext o
      cases o <;> simp
    rw [hc, Finset.sum_map]
    rfl
  rw [hdiff, ← hsum]
  refine (l2_opNorm_reindex_le_equiv _ _).trans (norm_sub_regionExpectation_le _ _ _ ?_)
  intro o ho U hU hUu
  cases o with
  | none => exact absurd Finset.none_mem_insertNone ho
  | some i =>
    obtain ⟨U₀, hU₀, hU₀u, hfac⟩ := exists_kronecker_one_of_mem_supportedOperators_some hU hUu
    have hi : i ∉ K := fun h ↦ ho (Finset.some_mem_insertNone.mpr h)
    calc ‖B' * U - U * B'‖ = ‖reindex e e (B' * U - U * B')‖ :=
          (l2_opNorm_reindex_equiv _ _).symm
      _ = ‖B * (U₀ ⊗ₖ (1 : Matrix Aux Aux ℂ)) - (U₀ ⊗ₖ (1 : Matrix Aux Aux ℂ)) * B‖ := by
          rw [← hfac, hB]
          simp only [e, reindex_apply, submatrix_sub, submatrix_mul_equiv]
          rfl
      _ ≤ ε i := hε i hi U₀ hU₀ hU₀u

end QuantumCircuit
