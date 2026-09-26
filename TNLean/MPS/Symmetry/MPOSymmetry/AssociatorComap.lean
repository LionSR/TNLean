/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# Restricting a group of matrix product operators along a homomorphism

Let `g ↦ O_g` be a family of matrix product operator tensors indexed by a group `G` and let
`f : H →* G` be a group homomorphism. The family `a ↦ O_{f a}` is indexed by `H`. If the
first family is a normal representation of `G`, the second is a normal representation of `H`,
and every choice of fusion tensors of the first restricts to one of the second. The anomaly
three-cochain of the restricted fusion tensors is the restriction of the anomaly three-cochain,
`ω_H(a,b,c) = ω(f a, f b, f c)`.

Since the class of `ω` does not depend on the fusion tensors (arXiv:2502.20257,
`eq:omegagauge`), any choice of fusion tensors of a restriction computes the gauge-invariant
products `ω(g, 1, g) ω(g, g, g) ⋯` of the ambient family at the elements of the image. For
instance, the anomaly class of a representation of `ℤ₂ × ℤ₂` can be probed on its three
subgroups of order two.

## Main definitions

* `MPOTensor.GroupFamily.comap`: the restricted family `a ↦ O_{f a}`.
* `MPOTensor.GroupFamily.FusionData.comap`: the restricted fusion tensors.

## Main results

* `MPOTensor.GroupFamily.IsNormalRepresentation.comap`: restriction preserves normal
  representations.
* `MPOTensor.GroupFamily.FusionData.omega_comap`: the anomaly three-cochain of the restricted
  fusion tensors is the restriction of the anomaly three-cochain.
* `MPOTensor.GroupFamily.FusionData.cyclicInvariant_omega_map`,
  `MPOTensor.GroupFamily.FusionData.cyclicInvariant_omega_map_of_comap_eq`: the cyclic
  invariant of the anomaly three-cochain at `f a` is computed by any choice of fusion tensors
  of the restriction, or of any family equal to it.

## References

- [arXiv:2502.20257](https://arxiv.org/abs/2502.20257) -- Franco Rubio, Bochniak, Cirac,
  *Symmetry defects and gauging for quantum states with matrix product unitary symmetries*,
  `main.tex` lines 1403--1546 (fusion tensors, the three-cocycle `ω` and its gauge freedom).
-/

open scoped Matrix Kronecker
open TNLean.Algebra

namespace MPOTensor.GroupFamily

variable {G H : Type*} [Group G] [Group H] {d : ℕ}

/-- **Restriction along a homomorphism**: the family `a ↦ O_{f a}` indexed by `H`. -/
def comap (F : GroupFamily G d) (f : H →* G) : GroupFamily H d where
  bondDim a := F.bondDim (f a)
  bondDim_pos a := F.bondDim_pos (f a)
  tensor a := F.tensor (f a)

omit [Group H] in
/-- Two families with the same bond dimensions and the same tensors are equal. -/
theorem ext_of_heq {F F' : GroupFamily H d} (hb : F.bondDim = F'.bondDim)
    (ht : ∀ a, HEq (F.tensor a) (F'.tensor a)) : F = F' := by
  obtain ⟨b, hbpos, t⟩ := F
  obtain ⟨b', hbpos', t'⟩ := F'
  obtain rfl : b = b' := hb
  obtain rfl : t = t' := funext fun a ↦ eq_of_heq (ht a)
  rfl

variable {F : GroupFamily G d}

/-- The restriction of a normal representation along a homomorphism is a normal
representation.

Source: arXiv:2502.20257, lines 1403--1407 (the representation law), applied to the elements
of the image. -/
theorem IsNormalRepresentation.comap (hF : F.IsNormalRepresentation) (f : H →* G) :
    (F.comap f).IsNormalRepresentation where
  isNormal a := hF.isNormal (f a)
  operator_mul a b N hN := by
    change mpo (F.tensor (f a)) N * mpo (F.tensor (f b)) N = mpo (F.tensor (f (a * b))) N
    rw [hF.operator_mul _ _ N hN, map_mul]

/-- The bond identification of the restricted family is that of the ambient family at the
images. -/
theorem castMat_comap (f : H →* G) {a b : H} (e : a = b) :
    (F.comap f).castMat e = F.castMat (congrArg f e) := rfl

namespace FusionData

/-- **Restriction of fusion tensors**: the fusion tensors of the pair `(f a, f b)`, with the
bond space of `f a * f b` identified with that of `f (a * b)`.

Source: arXiv:2502.20257, equations `eq:fusion_1` and `eq:fusion_2`, `main.tex`
lines 1403--1497, for the pairs of the image. -/
noncomputable def comap (fd : FusionData F) (f : H →* G) : FusionData (F.comap f) where
  V a b := F.castMat (map_mul f a b).symm * fd.V (f a) (f b)
  W a b := fd.W (f a) (f b) * F.castMat (map_mul f a b)
  isReduction a b := isReduction_castMat (fd.isReduction (f a) (f b)) (map_mul f a b).symm

variable (fd : FusionData F) (f : H →* G)

/-- The left boundary of the tree fusing `a` with `b` first, for the restricted fusion
tensors, is the ambient one up to the identification of bond spaces. -/
theorem comap_leftV (a b c : H) :
    (fd.comap f).leftV a b c =
      F.castMat (by simp only [map_mul] : f a * f b * f c = f (a * b * c)) *
        fd.leftV (f a) (f b) (f c) := by
  change F.castMat (map_mul f (a * b) c).symm * fd.V (f (a * b)) (f c) *
      kronId (F.castMat (map_mul f a b).symm * fd.V (f a) (f b)) (F.bondDim (f c)) = _
  rw [Matrix.mul_assoc, V_mul_kronId_castMat, castMat_mul_castMat_assoc]
  rfl

/-- The left boundary of the tree fusing `b` with `c` first, for the restricted fusion
tensors, is the ambient one up to the identification of bond spaces. -/
theorem comap_rightV (a b c : H) :
    (fd.comap f).rightV a b c =
      F.castMat (by simp only [map_mul] : f a * f b * f c = f (a * b * c)) *
        fd.rightV (f a) (f b) (f c) := by
  change F.castMat (congrArg f (mul_assoc a b c).symm) *
      (F.castMat (map_mul f a (b * c)).symm * fd.V (f a) (f (b * c)) *
        idKron (F.bondDim (f a)) (F.castMat (map_mul f b c).symm * fd.V (f b) (f c)) *
        mulTensorAssocInvMatrix (F.bondDim (f a)) (F.bondDim (f b)) (F.bondDim (f c))) = _
  rw [rightV, Matrix.mul_assoc (F.castMat _) (fd.V _ _), V_mul_idKron_castMat]
  simp only [Matrix.mul_assoc, castMat_mul_castMat_assoc]

/-- **The anomaly three-cochain of restricted fusion tensors is the restriction of the
anomaly three-cochain**: `ω_H(a,b,c) = ω(f a, f b, f c)`.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines 1506--1535, for
the triples of the image. -/
theorem omega_comap (hF : F.IsNormalRepresentation) :
    (fd.comap f).omega = ScalarThreeCochain.comap f fd.omega := by
  funext a b c
  have h : (fd.comap f).IsAssociator a b c (fd.omega (f a) (f b) (f c)) := by
    unfold IsAssociator
    rw [comap_leftV, comap_rightV]
    exact (isAssociator_omega hF (f a) (f b) (f c)).mul_left _
  exact Units.ext (eq_omega_of_isAssociator (hF.comap f) h).symm

/-- **Cyclic invariants from a restriction**: if `a ^ n = 1`, the gauge-invariant product
`∏_{k < n} ω(g, g^k, g)` of the anomaly three-cochain at `g = f a` equals that of any choice of
fusion tensors of the restriction along `f` at `a`.

Source: arXiv:2502.20257, `eq:omegagauge` and the sentence following it, `main.tex`
lines 1541--1546 (independence of the class from the fusion tensors). -/
theorem cyclicInvariant_omega_map (hF : F.IsNormalRepresentation)
    (fdH : (F.comap f).FusionData) {a : H} {n : ℕ} (ha : a ^ n = 1) :
    ScalarThreeCochain.cyclicInvariant fd.omega (f a) n =
      ScalarThreeCochain.cyclicInvariant fdH.omega a n := by
  rw [(omega_cohomologousTo (hF.comap f) (fd.comap f) fdH).cyclicInvariant_eq ha,
    omega_comap fd f hF]
  simp only [ScalarThreeCochain.cyclicInvariant, ScalarThreeCochain.comap_apply, map_pow]

/-- `cyclicInvariant_omega_map` for a family `F'` equal to the restriction along `f`, for
instance a family indexed by `H` whose tensors are written out explicitly. -/
theorem cyclicInvariant_omega_map_of_comap_eq (hF : F.IsNormalRepresentation)
    {F' : GroupFamily H d} (hF' : F.comap f = F') (fd' : F'.FusionData) {a : H} {n : ℕ}
    (ha : a ^ n = 1) :
    ScalarThreeCochain.cyclicInvariant fd.omega (f a) n =
      ScalarThreeCochain.cyclicInvariant fd'.omega a n := by
  subst hF'
  exact cyclicInvariant_omega_map fd f hF fd' ha

end FusionData

end MPOTensor.GroupFamily
