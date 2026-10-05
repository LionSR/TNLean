/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.PBCGroupProjector
import TNLean.Algebra.ScalarThreeCocycleCyclicTwoExamples

/-!
# Regression tests for the periodic group projector

The tests retain the incoming/outgoing orientation of the source's modified zipper,
check the nonempty-word condition on periodic support, and exhibit an off-support
component over the nontrivial group Z₂ where the unprojected zipper is false.
-/

noncomputable section

open TNLean.Algebra MPOTensor MPOTensor.GroupCocycle
-- These regressions intentionally inspect declaration and kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix

variable {G : Type} [Group G] {n : ℕ} (e : G ≃ Fin n)

example (h : G) : fusionProjector e h * fusionProjector e h = fusionProjector e h :=
  fusionProjector_mul_self e h

example (h : G) : (fusionProjector e h)ᴴ = fusionProjector e h :=
  fusionProjector_conjTranspose e h

example (ω : ScalarThreeCochain G) (g h : G) :
    fusionW e ω g h * fusionV e ω g h = fusionProjector e h :=
  fusionW_mul_fusionV e ω g h

example (ω : ScalarThreeCochain G) (g h : G) (i j : Fin n) :
    mulTensor (tensor e ω g) (tensor e ω h) i j * fusionProjector e h =
      mulTensor (tensor e ω g) (tensor e ω h) i j :=
  mulTensor_mul_fusionProjector e ω g h i j

example {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h : G) (i j : Fin n) :
    fusionProjector e h * mulTensor (tensor e ω g) (tensor e ω h) i j =
      fusionW e ω g h * tensor e ω (g * h) i j * fusionV e ω g h :=
  fusionProjector_mul_mulTensor hω g h i j

example {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h : G) (i j : Fin n) :
    fusionProjector e h * mulTensor (tensor e ω g) (tensor e ω h) i j * fusionW e ω g h =
      fusionW e ω g h * tensor e ω (g * h) i j :=
  fusionProjector_mul_mulTensor_mul_fusionW hω g h i j

example {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h : G) (w : List (Fin (n * n))) :
    fusionProjector e h *
        Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w =
      fusionW e ω g h * Kraus.evalWord (tensor e ω (g * h)).toMPSTensor w * fusionV e ω g h :=
  fusionProjector_mul_evalWord hω g h w

-- Empty-word factorization is exactly P = W V, without the cocycle equation.
example (ω : ScalarThreeCochain G) (g h : G) :
    fusionProjector e h *
        Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor [] =
      fusionW e ω g h * Kraus.evalWord (tensor e ω (g * h)).toMPSTensor [] * fusionV e ω g h := by
  simpa only [Kraus.evalWord_nil, Matrix.mul_one] using
    (fusionW_mul_fusionV e ω g h).symm

example (ω : ScalarThreeCochain G) (g h : G) (w : List (Fin (n * n))) (hw : w ≠ []) :
    Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w *
        fusionProjector e h =
      Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w :=
  evalWord_mul_fusionProjector ω g h w hw

example (ω : ScalarThreeCochain G) (g h : G) (w : List (Fin (n * n))) (hw : w ≠ []) :
    Matrix.trace (fusionProjector e h *
        Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w) =
      Matrix.trace (Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w) :=
  trace_fusionProjector_mul_evalWord ω g h w hw

example {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (g h : G) (w : List (Fin (n * n))) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord (mulTensor (tensor e ω g) (tensor e ω h)).toMPSTensor w) =
      Matrix.trace (Kraus.evalWord (tensor e ω (g * h)).toMPSTensor w) :=
  trace_evalWord_mulTensor_eq hω g h w hw

example [Nontrivial G] (ω : ScalarThreeCochain G) (g h : G) :
    ∃ i j, mulTensor (tensor e ω g) (tensor e ω h) i j * fusionW e ω g h ≠
      fusionW e ω g h * tensor e ω (g * h) i j :=
  exists_mulTensor_mul_fusionW_ne ω g h

example [Nontrivial G] (ω : ScalarThreeCochain G) (g h : G) :
    ∃ i j, mulTensor (tensor e ω g) (tensor e ω h) i j ≠
      fusionW e ω g h * tensor e ω (g * h) i j * fusionV e ω g h :=
  exists_mulTensor_ne_fusionW_mul_tensor_mul_fusionV ω g h

-- The generic normalized identity tensor is not a normal representation tensor.
example [Nontrivial G] {ω : ScalarThreeCochain G} (hn : ScalarThreeCochain.IsNormalized ω) :
    ¬ Kraus.IsNormal (tensor e ω 1).toMPSTensor :=
  not_isNormal_tensor_one e hn

local notation "e₂" => (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ Fin 2)
local notation "ω₀" => (fun _ _ _ ↦ 1 : ScalarThreeCochain (Multiplicative (ZMod 2)))

-- At g = h = e, physical letter (0,0), incoming pair (1,0), and fused outgoing
-- label 0, the two sides of the unprojected right zipper are 1 and 0.
example :
    (mulTensor (tensor e₂ ω₀ 1) (tensor e₂ ω₀ 1) 0 0 * fusionW e₂ ω₀ 1 1)
      (finProdFinEquiv (1, 0)) 0 = 1 := by
  simp [mul_fusionW_apply, pairLabel, mulTensor_tensor_apply]

example :
    (fusionW e₂ ω₀ 1 1 * tensor e₂ ω₀ 1 0 0) (finProdFinEquiv (1, 0)) 0 = 0 := by
  simp [fusionW_mul_apply]

-- The support projector on Z₂ has diagonal (1,0,0,1), so it is not the full identity.
example : fusionProjector e₂ 1 (finProdFinEquiv (1, 0)) (finProdFinEquiv (1, 0)) = 0 := by
  simp [fusionProjector_apply]

example : fusionProjector e₂ 1 ≠ 1 := by
  intro heq
  have hentry := congrArg (fun M ↦ M (finProdFinEquiv (1, 0)) (finProdFinEquiv (1, 0))) heq
  simpa [fusionProjector_apply] using hentry

-- The same failure occurs for the nontrivial three-cocycle and nonidentity elements.
example :
    ∃ i j, mulTensor
        (tensor e₂ (ScalarThreeCochain.cyclicTwoCocycle 1) (Multiplicative.ofAdd 1))
        (tensor e₂ (ScalarThreeCochain.cyclicTwoCocycle 1) (Multiplicative.ofAdd 1)) i j *
          fusionW e₂ (ScalarThreeCochain.cyclicTwoCocycle 1)
            (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1) ≠
      fusionW e₂ (ScalarThreeCochain.cyclicTwoCocycle 1)
          (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1) *
        tensor e₂ (ScalarThreeCochain.cyclicTwoCocycle 1)
          (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1) i j :=
  exists_mulTensor_mul_fusionW_ne _ _ _
