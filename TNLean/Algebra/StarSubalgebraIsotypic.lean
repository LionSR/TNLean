/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraSchur

/-!
# Grouping the irreducible pieces of a star-subalgebra by isomorphism type

Continuing the structure theory of *Quantum Channels & Operations* (Wolf 2012), Chapter 6,
towards Theorem 6.14, this file groups the
mutually orthogonal irreducible pieces produced by the orthogonal decomposition according
to their isomorphism type. Two irreducible invariant subspaces have the same type when
there is a nonzero operator that carries one into the other and commutes there with the
subalgebra; Schur's lemma upgrades any such nonzero operator to an isomorphism of one piece
onto the other.

The same-type relation is reflexive, symmetric, and transitive, and is characterized by the
existence of an isomorphism between the two pieces. Pieces of different types are forced to be
orthogonal: the orthogonal projection onto one piece is itself an operator commuting with
the subalgebra, so Schur's lemma makes it either an isomorphism onto the other piece, giving
the same type, or zero, placing the first piece in the orthogonal complement of the second.

## Main definitions

* `StarSubalgebra.IsIntertwiner` -- an operator carrying one invariant subspace into another
  and commuting on the source with every member of the subalgebra.
* `StarSubalgebra.SameIsotype` -- two invariant subspaces are of the same type when some
  operator carrying the first into the second, and commuting there with the subalgebra, is
  nonzero on the first.

## Main results

* `StarSubalgebra.sameIsotype_iff_exists_isomorphism` -- on irreducible pieces, having the
  same type is the same as the existence of an operator that is an isomorphism of the first
  piece onto the second and commutes with the subalgebra.
* `StarSubalgebra.sameIsotype_refl` -- an irreducible piece has the same type as itself.
* `StarSubalgebra.sameIsotype_symm` -- the same-type relation on irreducible pieces is
  symmetric.
* `StarSubalgebra.sameIsotype_trans` -- the same-type relation on irreducible pieces is
  transitive.
* `StarSubalgebra.starProjection_toEuclideanLin_comm` -- the orthogonal projection onto an
  invariant subspace commutes with every member of the subalgebra.
* `StarSubalgebra.isOrtho_of_not_sameIsotype` -- two irreducible pieces that do not have the
  same type are orthogonal.

## Remaining gap: isotypic decomposition and unitary change of basis

The same-type relation and the orthogonality of pieces of different types are established
here. The full theorem additionally collects the pieces of a single type into an isotypic
component, equips each component with a tensor identification of the form "matrix block on
the multiplicity space", and assembles a single unitary change of basis. Those steps are not
formalized here.
-/

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- An operator from one invariant subspace into another for a star-subalgebra `S` of complex
matrices: a complex-linear operator on Euclidean space that carries `p` into `q` and, on `p`,
commutes with every member of the subalgebra. See *Quantum Channels & Operations*
(Wolf 2012), Chapter 6, towards Theorem 6.14. -/
def IsIntertwiner (p q : Submodule ℂ (EuclideanSpace ℂ n))
    (f : Module.End ℂ (EuclideanSpace ℂ n)) : Prop :=
  Submodule.map f p ≤ q ∧
    ∀ A ∈ S, ∀ x ∈ p, f (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A (f x)

/-- Two invariant subspaces `p` and `q` of a star-subalgebra `S` of complex matrices are of
the same type when there is an operator carrying `p` into `q`, commuting on `p` with every
member of the subalgebra, that is not zero on `p`. On irreducible pieces Schur's lemma makes
any such operator an isomorphism of `p` onto `q`. See *Quantum Channels & Operations*
(Wolf 2012), Chapter 6, towards Theorem 6.14. -/
def SameIsotype (p q : Submodule ℂ (EuclideanSpace ℂ n)) : Prop :=
  ∃ f : Module.End ℂ (EuclideanSpace ℂ n), S.IsIntertwiner p q f ∧ ¬ ∀ x ∈ p, f x = 0

omit [Fintype n] [DecidableEq n] in
/-- If the image of `p` under `f` is a nonzero subspace, then `f` is not zero on `p`. -/
private theorem not_forall_apply_eq_zero_of_map_ne_bot
    {p : Submodule ℂ (EuclideanSpace ℂ n)} {f : Module.End ℂ (EuclideanSpace ℂ n)}
    (hne : Submodule.map f p ≠ ⊥) : ¬ ∀ x ∈ p, f x = 0 := by
  intro hzero
  refine hne (eq_bot_iff.mpr ?_)
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  rw [hzero x hx]
  exact Submodule.zero_mem _

/-- On irreducible pieces of a star-subalgebra of complex matrices, two pieces have the same
type exactly when some operator commuting with the subalgebra is an isomorphism of the first
piece onto the second: injective on the source with image exactly the target. The forward
direction upgrades a nonzero intertwiner via Schur's lemma; the reverse direction notes that
an isomorphism onto a nonzero target cannot vanish on the source. See
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem sameIsotype_iff_exists_isomorphism {p q : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsIrreducibleSubspace p) (hq : S.IsIrreducibleSubspace q) :
    S.SameIsotype p q ↔
      ∃ f : Module.End ℂ (EuclideanSpace ℂ n),
        S.IsIntertwiner p q f ∧ Set.InjOn f p ∧ Submodule.map f p = q := by
  constructor
  · rintro ⟨f, hf, hne⟩
    rcases S.intertwiner_zero_or_isomorphism hp hq hf.1 hf.2 with hzero | ⟨hinj, heq⟩
    · exact absurd hzero hne
    · exact ⟨f, hf, hinj, heq⟩
  · rintro ⟨f, hf, _, heq⟩
    exact ⟨f, hf, not_forall_apply_eq_zero_of_map_ne_bot (heq ▸ hq.2.1)⟩

/-- An irreducible piece of a star-subalgebra of complex matrices has the same type as
itself: the identity operator carries the piece into itself, commutes with the subalgebra,
and is nonzero there since the piece is nonzero. See *Quantum Channels & Operations*
(Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem sameIsotype_refl {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsIrreducibleSubspace p) : S.SameIsotype p p := by
  refine ⟨LinearMap.id, ⟨(Submodule.map_id p).le, fun _ _ _ _ => rfl⟩, ?_⟩
  obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff p).mp hp.2.1
  exact fun hzero => hxne (hzero x hx)

/-- The same-type relation on irreducible pieces of a star-subalgebra of complex matrices is
transitive: composing an isomorphism of `p` onto `q` with an isomorphism of `q` onto `r`
gives an isomorphism of `p` onto `r` that commutes with the subalgebra. See
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem sameIsotype_trans {p q r : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsIrreducibleSubspace p) (hq : S.IsIrreducibleSubspace q)
    (hr : S.IsIrreducibleSubspace r) (hpq : S.SameIsotype p q) (hqr : S.SameIsotype q r) :
    S.SameIsotype p r := by
  obtain ⟨f, hf, _, hfeq⟩ := (S.sameIsotype_iff_exists_isomorphism hp hq).mp hpq
  obtain ⟨g, hg, _, hgeq⟩ := (S.sameIsotype_iff_exists_isomorphism hq hr).mp hqr
  have hmapr : Submodule.map (g.comp f) p = r := by rw [Submodule.map_comp, hfeq, hgeq]
  refine ⟨g.comp f, ⟨hmapr.le, fun A hA x hx => ?_⟩,
    not_forall_apply_eq_zero_of_map_ne_bot (hmapr ▸ hr.2.1)⟩
  have hfx : f x ∈ q := hfeq ▸ Submodule.mem_map_of_mem hx
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hf.2 A hA x hx, hg.2 A hA (f x) hfx]

/-- The orthogonal projection onto an invariant subspace of a star-subalgebra of complex
matrices commutes with every member of the subalgebra. Writing a vector as the sum of its
projection and its orthogonal part, each member sends the projection into the subspace and
the orthogonal part into the orthogonal complement, which is invariant as well; so applying
the member and then projecting recovers the projected-then-applied vector. See
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem starProjection_toEuclideanLin_comm {q : Submodule ℂ (EuclideanSpace ℂ n)}
    (hq : S.IsInvariantSubspace q) {A : Matrix n n ℂ} (hA : A ∈ S)
    (x : EuclideanSpace ℂ n) :
    q.starProjection (Matrix.toEuclideanLin A x) =
      Matrix.toEuclideanLin A (q.starProjection x) := by
  have hqinv : q ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A) := hq A hA
  have hqperp : qᗮ ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A) :=
    S.orthogonal_mem_invtSubmodule hq A hA
  have hmem_q : Matrix.toEuclideanLin A (q.starProjection x) ∈ q :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := Matrix.toEuclideanLin A)).mp hqinv
      _ (q.starProjection_apply_mem x)
  have hmem_qperp : Matrix.toEuclideanLin A (qᗮ.starProjection x) ∈ qᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := Matrix.toEuclideanLin A)).mp hqperp
      _ (qᗮ.starProjection_apply_mem x)
  refine Submodule.eq_starProjection_of_mem_orthogonal' hmem_q hmem_qperp ?_
  have hdecomp : x = q.starProjection x + qᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal_val]; abel
  conv_lhs => rw [hdecomp]
  rw [map_add]

/-- Two irreducible pieces of a star-subalgebra of complex matrices that do not have the same
type are orthogonal. The orthogonal projection onto the second piece, viewed as an operator,
commutes with the subalgebra and carries the first piece into the second, so Schur's lemma
makes it either an isomorphism, giving the same type, or zero on the first piece, which means
the first piece lies in the orthogonal complement of the second. See
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem isOrtho_of_not_sameIsotype {p q : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsIrreducibleSubspace p) (hq : S.IsIrreducibleSubspace q)
    (h : ¬ S.SameIsotype p q) : p ⟂ q := by
  set Pq : Module.End ℂ (EuclideanSpace ℂ n) := q.starProjection.toLinearMap
  have hmap : Submodule.map Pq p ≤ q :=
    Submodule.map_le_iff_le_comap.mpr fun x _ => q.starProjection_apply_mem x
  have hcomm : ∀ A ∈ S, ∀ x ∈ p,
      Pq (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A (Pq x) :=
    fun A hA x _ => S.starProjection_toEuclideanLin_comm hq.1 hA x
  rcases S.intertwiner_zero_or_isomorphism hp hq hmap hcomm with hzero | ⟨hinj, heq⟩
  · rw [Submodule.isOrtho_iff_le]
    intro x hx
    have hx0 : (q.orthogonalProjectionOnto x : EuclideanSpace ℂ n) = 0 := hzero x hx
    exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mp (Submodule.coe_eq_zero.mp hx0)
  · refine absurd ?_ h
    exact (S.sameIsotype_iff_exists_isomorphism hp hq).mpr ⟨Pq, ⟨hmap, hcomm⟩, hinj, heq⟩

/-- The same-type relation on irreducible pieces of a star-subalgebra of complex matrices is
symmetric: an isomorphism of `p` onto `q` has an inverse, built by projecting onto `q`,
inverting on the subspace, and including back into `p`, which is an isomorphism of `q` onto
`p` commuting with the subalgebra. See *Quantum Channels & Operations* (Wolf 2012),
Chapter 6, towards Theorem 6.14. -/
theorem sameIsotype_symm {p q : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsIrreducibleSubspace p) (hq : S.IsIrreducibleSubspace q)
    (h : S.SameIsotype p q) : S.SameIsotype q p := by
  obtain ⟨f, hf, hfinj, hfeq⟩ := (S.sameIsotype_iff_exists_isomorphism hp hq).mp h
  -- `f` restricts to a linear bijection of `p` onto `q`.
  have hf_mem : ∀ x ∈ p, f x ∈ q := fun x hx => hfeq ▸ Submodule.mem_map_of_mem hx
  have hf₀_bij : Function.Bijective (f.restrict hf_mem) := by
    refine ⟨fun a b hab => Subtype.ext (hfinj a.2 b.2 ?_), fun y => ?_⟩
    · exact congrArg Subtype.val hab
    · have hy : (y : EuclideanSpace ℂ n) ∈ Submodule.map f p := by rw [hfeq]; exact y.2
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  set e : p ≃ₗ[ℂ] q := LinearEquiv.ofBijective (f.restrict hf_mem) hf₀_bij
  have hf_symm : ∀ w : q, f (e.symm w : EuclideanSpace ℂ n) = (w : EuclideanSpace ℂ n) :=
    fun w => congrArg Subtype.val (e.apply_symm_apply w)
  -- The inverse operator: project onto `q`, invert, and include into `p`.
  set g : Module.End ℂ (EuclideanSpace ℂ n) :=
    p.subtype.comp (e.symm.toLinearMap.comp q.orthogonalProjectionOnto.toLinearMap) with hg
  have hg_mem_q : ∀ w (hw : w ∈ q), g w = (e.symm ⟨w, hw⟩ : EuclideanSpace ℂ n) := by
    intro w hw
    have hself : q.orthogonalProjectionOnto w = ⟨w, hw⟩ :=
      q.orthogonalProjectionOnto_mem_subspace_eq_self ⟨w, hw⟩
    simp only [hg, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hself,
      LinearEquiv.coe_coe, Submodule.subtype_apply]
  refine ⟨g, ⟨Submodule.map_le_iff_le_comap.mpr fun w hw => ?_, fun A hA w hw => ?_⟩, ?_⟩
  · rw [Submodule.mem_comap, hg_mem_q w hw]
    exact (e.symm ⟨w, hw⟩).2
  · -- `g` commutes on `q` with every member, by applying the injective `f` to both sides.
    have hAw : Matrix.toEuclideanLin A w ∈ q :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Matrix.toEuclideanLin A)).mp (hq.1 A hA) w hw
    have hey : (e.symm ⟨w, hw⟩ : EuclideanSpace ℂ n) ∈ p := (e.symm ⟨w, hw⟩).2
    have hmem2 : Matrix.toEuclideanLin A (e.symm ⟨w, hw⟩ : EuclideanSpace ℂ n) ∈ p :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Matrix.toEuclideanLin A)).mp (hp.1 A hA) _ hey
    rw [hg_mem_q (Matrix.toEuclideanLin A w) hAw, hg_mem_q w hw]
    refine hfinj (e.symm ⟨Matrix.toEuclideanLin A w, hAw⟩).2 hmem2 ?_
    rw [hf_symm ⟨Matrix.toEuclideanLin A w, hAw⟩, hf.2 A hA _ hey, hf_symm ⟨w, hw⟩]
  · -- `g` is nonzero on `q`, since `q` is a nonzero subspace.
    obtain ⟨w, hw, hwne⟩ := (Submodule.ne_bot_iff q).mp hq.2.1
    refine fun hzero => hwne ?_
    have hgw : (e.symm ⟨w, hw⟩ : EuclideanSpace ℂ n) = 0 := by
      rw [← hg_mem_q w hw]; exact hzero w hw
    have h2 : (⟨w, hw⟩ : q) = 0 := by
      rw [← e.apply_symm_apply ⟨w, hw⟩, Submodule.coe_eq_zero.mp hgw, map_zero]
    exact congrArg Subtype.val h2

end StarSubalgebra
