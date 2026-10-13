/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.RestrictedMixedPhysicalTrace
import TNLean.PEPS.Approximation.NoneSourceWordScalar
import TNLean.PEPS.Approximation.SampledEndpointExteriorIdentity
import TNLean.PEPS.Approximation.SelectedFamilyPhysicalBasis
import QICLean.Channel.PartialTrace

/-!
# The actual exterior scalar in a sampled local trace

The exterior restriction of the prepared source word is multiplication by the
original empty-gate scalar. The sampled endpoint word is the identity on this
empty memory. Arbitrary orthonormal input and output coordinates therefore
give the same reduced exterior matrix, equal to the squared modulus of that
scalar times the identity on the singleton physical coordinate. No scalar is
cancelled, and no additional physical register is introduced.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267 and 565–588.
-/

noncomputable section
open scoped Matrix ComplexConjugate
namespace TNLean.PEPS.PairEffect

private theorem restrict_eval_heq_of_selector_eq {Q : Type} {f g : Q → Bool}
    (h : f = g) {a b : Layout Q} (w : Word a b) (hs : w.sources = []) :
    HEq (w.restrict f hs).eval (w.restrict g hs).eval := by
  cases h
  rfl

private theorem restrict_none_eval_heq_isNone {Q : Type} {a b : Layout (Option Q)}
    (w : Word a b) (hs : w.sources = []) :
    HEq (w.restrict (partySelector none) hs).eval (w.restrict Option.isNone hs).eval := by
  have h : partySelector (none : Option Q) = Option.isNone := by
    funext q
    cases q <;> simp [partySelector]
  exact restrict_eval_heq_of_selector_eq h w hs

private theorem empty_memory_mixed_partialTrace
    {Q I J : Type} [Fintype I] [Fintype J] {a b : Layout Q}
    (ha : a = []) (hb : b = [])
    (B : OrthonormalBasis I ℂ (Mem a))
    (C : OrthonormalBasis (PUnit × J) ℂ (Mem b))
    (A T : Mem a →L[ℂ] Mem b) (U : Mem a →L[ℂ] Mem a) (α β : ℂ)
    (hA : HEq A (α • ContinuousLinearMap.id ℂ ℂ))
    (hT : HEq T (β • ContinuousLinearMap.id ℂ ℂ))
    (hU : HEq U (ContinuousLinearMap.id ℂ ℂ)) :
    Matrix.partialTraceRight
        (Matrix.of (fun row col ↦ C.repr (A (B col)) row) *
          Matrix.of (fun row col ↦ B.repr (U (B col)) row) *
          (Matrix.of (fun row col ↦ C.repr (T (B col)) row))ᴴ) =
      (α * conj β) • (1 : Matrix PUnit PUnit ℂ) := by
  classical
  cases ha
  cases hb
  rw [eq_of_heq hA, eq_of_heq hT, eq_of_heq hU]
  let V := C.toBasis.toMatrix B
  have hScalar (γ : ℂ) :
      Matrix.of (fun row col ↦ C.repr ((γ • ContinuousLinearMap.id ℂ ℂ) (B col)) row) =
        γ • V := by
    ext row col
    change C.repr (γ • B col) row = γ • C.toBasis.repr (B col) row
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    exact congrArg (fun x : EuclideanSpace ℂ (PUnit × J) ↦ x row)
      (map_smul C.repr γ (B col))
  have hIdentity : Matrix.of (fun row col ↦
      B.repr ((ContinuousLinearMap.id ℂ ℂ) (B col)) row) = (1 : Matrix I I ℂ) := by
    have hself : B.toBasis.toMatrix B = (1 : Matrix I I ℂ) := by
      change B.toBasis.toMatrix B.toBasis = 1
      exact Module.Basis.toMatrix_self B.toBasis
    ext row col
    have h := congrArg (fun M : Matrix I I ℂ ↦ M row col) hself
    simpa only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      Matrix.of_apply, ContinuousLinearMap.id_apply] using h
  have hV : V * Vᴴ = 1 := C.toMatrix_orthonormalBasis_self_mul_conjTranspose B
  have hJ : Fintype.card J = 1 := by
    simpa only [Module.finrank_self, Fintype.card_prod, Fintype.card_punit, one_mul] using
      (Module.finrank_eq_card_basis C.toBasis).symm
  rw [hScalar, hScalar, hIdentity, Matrix.mul_one, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, hV, smul_smul,
    Matrix.partialTraceRight_smul, Matrix.partialTraceRight_one, hJ]
  simp only [Nat.cast_one, one_smul, Complex.star_def]

/-- The coordinate trace for words on empty memories is computed before the
actual retained layouts are substituted. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 574–579. -/
private theorem empty_memory_words_mixed_partialTrace
    {Q I J : Type} [Fintype I] [Fintype J] {a b : Layout Q}
    (ha : a = []) (hb : b = [])
    (B : OrthonormalBasis I ℂ (Mem a))
    (C : OrthonormalBasis (PUnit × J) ℂ (Mem b))
    (u t : Word a b) (v : Word a a) (α β : ℂ)
    (hA : HEq u.eval (α • ContinuousLinearMap.id ℂ ℂ))
    (hT : HEq t.eval (β • ContinuousLinearMap.id ℂ ℂ))
    (hU : HEq v.eval (ContinuousLinearMap.id ℂ ℂ)) :
    Matrix.partialTraceRight
        (Matrix.of (fun row col ↦ C.repr (u.eval (B col)) row) *
          Matrix.of (fun row col ↦ B.repr (v.eval (B col)) row) *
          (Matrix.of (fun row col ↦ C.repr (t.eval (B col)) row))ᴴ) =
      (α * conj β) • (1 : Matrix PUnit PUnit ℂ) := by
  exact empty_memory_mixed_partialTrace ha hb B C u.eval t.eval v.eval α β hA hT hU

/-- The selected mixed trace equality in its original coordinates. This
reducible abbreviation retains the literal matrix expression while allowing
the words and layouts to be substituted before that expression is unfolded.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 574–579. -/
private abbrev emptyPartyTraceIdentity
    {Q I J : Type} [Fintype I] [Fintype J] (q : Q) {a b : Layout Q}
    (u t : Word a b) (v : Word a a)
    (hu : u.sources = []) (ht : t.sources = []) (hv : v.sources = [])
    (B : OrthonormalBasis I ℂ (Mem (Layout.atParty q a)))
    (C : OrthonormalBasis (PUnit × J) ℂ (Mem (Layout.atParty q b))) (α β : ℂ) : Prop :=
  restrictedMixedPhysicalTrace (partySelector q) u t v hu ht hv B C =
    (α * conj β) • (1 : Matrix PUnit PUnit ℂ)

/-- The selected coordinate trace is formed for arbitrary source-free words
before the actual source and endpoint words are substituted. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 574–579. -/
private theorem empty_party_words_mixed_partialTrace
    {Q I J : Type} [Fintype I] [Fintype J] (q : Q) {a b : Layout Q}
    (u t : Word a b) (v : Word a a)
    (hu : u.sources = []) (ht : t.sources = []) (hv : v.sources = [])
    (ha : Layout.atParty q a = []) (hb : Layout.atParty q b = [])
    (B : OrthonormalBasis I ℂ (Mem (Layout.atParty q a)))
    (C : OrthonormalBasis (PUnit × J) ℂ (Mem (Layout.atParty q b))) (α β : ℂ)
    (hA : HEq (u.restrict (partySelector q) hu).eval
      (α • ContinuousLinearMap.id ℂ ℂ))
    (hT : HEq (t.restrict (partySelector q) ht).eval
      (β • ContinuousLinearMap.id ℂ ℂ))
    (hU : HEq (v.restrict (partySelector q) hv).eval
      (ContinuousLinearMap.id ℂ ℂ)) :
    emptyPartyTraceIdentity q u t v hu ht hv B C α β := by
  classical
  have h := empty_memory_words_mixed_partialTrace
    (a := Layout.atParty q a) (b := Layout.atParty q b) ha hb B C
    (u.restrict (partySelector q) hu) (t.restrict (partySelector q) ht)
    (v.restrict (partySelector q) hv) α β hA hT hU
  rw [matrix_repr_eval_eq_toMatrix B B (v.restrict (partySelector q) hv).eval] at h
  simpa only [emptyPartyTraceIdentity, restrictedMixedPhysicalTrace] using h

namespace SourceCircuit
variable {P : Type} {a b : Layout P}

/-- The actual exterior source input is empty. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 246–267 and 565–588. -/
private theorem actualSourceInput_none_eq_nil (w : SourceCircuit a b) :
    Layout.atParty none (w.allResidualSourceLayout ++ []) = [] := by
  change Layout.restrict (partySelector none) (w.allResidualSourceLayout ++ []) = []
  rw [partySelector_none, Layout.restrict_append, restrict_allResidualSourceLayout_isNone,
    Layout.restrict_nil, List.nil_append]

/-- The actual exterior source word has its original scalar in the party
selector. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 246–267 and 565–588. -/
private theorem partialSourceWord_none_eval_heq_scalar
    (w : SourceCircuit a b) (ψ : ProductInput a) (ξ : Choices (fun _ : P ↦ true) w) :
    HEq ((w.partialSourceWord ψ ξ).restrict (partySelector none)
      (sources_partialSourceWord w ψ ξ)).eval
      (w.emptyGateScalar • ContinuousLinearMap.id ℂ ℂ) := by
  exact (restrict_none_eval_heq_isNone (w.partialSourceWord ψ ξ)
    (sources_partialSourceWord w ψ ξ)).trans
      (restrict_partialSourceWord_all_eval_heq_emptyGateScalar w ψ ξ)

/-- The sampled exterior input is the identity in the party selector.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267 and 565–588. -/
private theorem sampledEndpointInputWord_party_none_eval_heq_id
    (w : SourceCircuit a b) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k) :
    HEq ((sampledEndpointInputWord w k lam L R ξ ζ j ω).restrict (partySelector none)
      (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).eval
      (ContinuousLinearMap.id ℂ ℂ) := by
  exact (restrict_none_eval_heq_isNone (sampledEndpointInputWord w k lam L R ξ ζ j ω)
    (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).trans
      (sampledEndpointInputWord_none_eval_heq_id w k lam L R ξ ζ j ω)

/-- The actual exterior sampled mixed trace is the original empty-gate scalar
times its complex conjugate, in the canonical singleton physical coordinate.
The input and output orthonormal bases, ket and bra choices, and original joint
sample are arbitrary. No normalization or nonvanishing is required.
The conclusion uses a reducible abbreviation of the literal selected mixed
trace equality, with the same words, coordinates and scalar.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–139,
246–267 and 565–588. -/
theorem partialSourceWord_sampled_none_partialTrace_eq_scalar
    (w : SourceCircuit a b) (ψ : ProductInput a) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k)
    {I J : Type} [Fintype I] [Fintype J]
    (B : OrthonormalBasis I ℂ
      (Mem (Layout.atParty none (w.allResidualSourceLayout ++ []))))
    (C : OrthonormalBasis (PUnit × J) ℂ
      (Mem (Layout.atParty none (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)))) :
    emptyPartyTraceIdentity
      (Q := Option {p : P // (fun _ : P ↦ true) p = true}) (I := I) (J := J)
      (a := w.allResidualSourceLayout ++ [])
      (b := Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b) none
      (w.partialSourceWord ψ ξ) (w.partialSourceWord ψ ζ)
      (sampledEndpointInputWord w k lam L R ξ ζ j ω)
      (sources_partialSourceWord w ψ ξ) (sources_partialSourceWord w ψ ζ)
      (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω) B C
      w.emptyGateScalar w.emptyGateScalar := by
  classical
  have hξ := partialSourceWord_none_eval_heq_scalar w ψ ξ
  have hζ := partialSourceWord_none_eval_heq_scalar w ψ ζ
  have hU := sampledEndpointInputWord_party_none_eval_heq_id w k lam L R ξ ζ j ω
  have ha := actualSourceInput_none_eq_nil w
  have hb := Layout.atParty_none_mapOwner_all b
  exact empty_party_words_mixed_partialTrace
    (Q := Option {p : P // (fun _ : P ↦ true) p = true}) (I := I) (J := J)
    (a := w.allResidualSourceLayout ++ [])
    (b := Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b) none
    (w.partialSourceWord ψ ξ) (w.partialSourceWord ψ ζ)
    (sampledEndpointInputWord w k lam L R ξ ζ j ω)
    (sources_partialSourceWord w ψ ξ) (sources_partialSourceWord w ψ ζ)
    (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω) ha hb B C
    w.emptyGateScalar w.emptyGateScalar hξ hζ hU

end SourceCircuit
end TNLean.PEPS.PairEffect
