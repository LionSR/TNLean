/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGraphInsertedSurplus
import TNLean.PEPS.RegularTwoByTwoGraphCoordinates
import TNLean.PEPS.TorusInsertedGraphNetwork
import TNLean.PEPS.TorusTwoByTwoTwistedGeometry

/-!
# Native regular insertions in bundled graph coordinates

Arbitrary physical tensors and oriented inserted bonds retain their actual
coefficients under native-to-graph coordinates and under the identification of
two regular labels with one distinguished label and a one-coordinate surplus
register. Native orientation reversals invert regular group labels in both the
single-bond and bundled representations.

Source: SCP10, arXiv:1001.3807, lines 1840–1909 and 1515–1525.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS

section Graph
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable {P : V → Type*}

omit [DecidableEq X] [DecidableEq Y] in
/-- Bijectively reindexing both endpoints and the incident site labels leaves
the actual inserted contraction unchanged. Source: SCP10, the coordinate
identifications in the blocking construction, lines 1840–1909. -/
theorem graphInsertedBondNetwork_equiv (E : X ≃ Y)
    (B : Edge Γ → Matrix X X ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ) (σ : (v : V) → P v) :
    graphInsertedBondNetwork (fun f x y => B f (E.symm x) (E.symm y))
        (fun v η s => a v (fun f => E.symm (η f)) s) σ =
      graphInsertedBondNetwork B a σ := by
  classical
  let F := (Equiv.refl (Edge Γ)).arrowCongr (E.prodCongr E)
  unfold graphInsertedBondNetwork
  rw [← F.sum_comp]
  simp only [F, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply,
    Function.comp_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext f
  by_cases hf : f.1.1.1 = v <;> simp [graphSiteBondEndpointEquiv, hf]

end Graph

section Torus
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "TG" => torusGraph width height
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Native and graph contractions agree for arbitrary site-dependent physical
alphabets and inserted matrices. Source: SCP10, the two-by-two geometry and
oriented insertions, lines 1888–1909 and 1515–1525. -/
theorem graphInsertedBondNetwork_torusIncidentFamily {Q : TV → Type*}
    (a : (v : TV) → (Fin 4 → X) → Q v → ℂ)
    (Oh Ov : TV → Matrix X X ℂ) (σ : (v : TV) → Q v) :
    graphInsertedBondNetwork (torusGraphBondMatrix Oh Ov) (torusIncidentFamily a) σ =
      torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) Oh Ov := by
  classical
  let E := Fintype.equivFin TV
  let A (t r b l : X) (i : Fin (Fintype.card TV)) : ℂ :=
    a (E.symm i) ![t, r, b, l] (σ (E.symm i))
  have hA (v : TV) (t r b l : X) :
      A t r b l (E v) = a v ![t, r, b, l] (σ v) :=
    congrArg (fun w => a w ![t, r, b, l] (σ w)) (E.symm_apply_apply v)
  have h := torusBondNetwork_eq_graphInsertedBondNetwork A Oh Ov E
  have hc (v : TV) (η : IncidentEdge TG v → X) :
      ![η (torusTopLeg v), η (torusRightLeg v),
        η (torusDownLeg v), η (torusLeftLeg v)] =
        fun i => η (torusIncidentLeg v i) := by
    funext i
    fin_cases i <;> rfl
  simpa only [graphInsertedBondNetwork, torusNativeIncidentSite, hA, hc,
    torusIncidentFamily] using h.symm

omit [DecidableEq X] in
/-- The actual blocked graph contraction is unchanged by expressing each
paired virtual bond as a distinguished label and a Unit-indexed surplus.
Source: SCP10, the paired boundaries in lines 1888–1906. -/
theorem graphInsertedBondNetwork_twoByTwoBundledGraphSite {P : Type*}
    (a : FV → (Fin 4 → X) → P → ℂ)
    (B : Edge TG → Matrix (X × X) (X × X) ℂ) (σ : TV → Fin 4 → P) :
    graphInsertedBondNetwork
        (fun e x y => B e (pairUnitBundleEquiv.symm x) (pairUnitBundleEquiv.symm y))
        (twoByTwoBundledGraphSite a) σ =
      graphInsertedBondNetwork B (twoByTwoGraphSite a) σ :=
  graphInsertedBondNetwork_equiv pairUnitBundleEquiv B (twoByTwoGraphSite a) σ

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Native group insertions expressed on ordered graph edges. Every reversed
edge, including a periodic seam, carries the inverse group label.
Source: SCP10, oriented insertions, lines 1515–1525. -/
def torusGraphRegularLabels (uh uv : TV → G) (e : Edge TG) : G :=
  match torusEdgeEquiv.symm e with
  | .inl v => if e.1.1 = v then uh v else (uh v)⁻¹
  | .inr v => if e.1.1 = v then (uv v)⁻¹ else uv v

/-- The inverse in the ordered group label is exactly the transpose required
by the native matrix contraction. Source: SCP10, lines 1515–1525. -/
theorem torusGraphBondMatrix_leftRegular (uh uv : TV → G) :
    torusGraphBondMatrix (fun v => leftRegularMatrix G (uh v))
        (fun v => leftRegularMatrix G (uv v)) =
      fun e => leftRegularMatrix G (torusGraphRegularLabels uh uv e) := by
  have ht (g : G) : (leftRegularMatrix G g).transpose = leftRegularMatrix G g⁻¹ := by
    ext x y
    simp only [Matrix.transpose_apply, leftRegularMatrix_apply,
      eq_inv_mul_iff_mul_eq, eq_comm]
  funext e
  cases he : torusEdgeEquiv.symm e <;>
    simp only [torusGraphBondMatrix, torusGraphRegularLabels, he] <;>
    split_ifs <;> first | rfl | exact ht _

/-- The bundled representation has exactly the same ordered group labels as
one regular bond; native orientation does not twist any relative register.
Source: SCP10, lines 1840–1873 and 1515–1525. -/
theorem torusGraphBondMatrix_regularBundle (K : Type*) [Fintype K] [DecidableEq K]
    (uh uv : TV → G) :
    torusGraphBondMatrix (fun v => regularBundleMatrix K (uh v))
        (fun v => regularBundleMatrix K (uv v)) =
      fun e => regularBundleMatrix K (torusGraphRegularLabels uh uv e) := by
  funext e
  cases he : torusEdgeEquiv.symm e <;>
    simp only [torusGraphBondMatrix, torusGraphRegularLabels, he] <;>
    split_ifs <;> first | rfl | exact regularBundleMatrix_transpose K _


/-- The ordered-edge labels of the two native periodic seams. Horizontal
seams carry h and downward vertical seams carry g, with inverses precisely
where ordered graph orientation reverses the native arrow.
Source: SCP10, Definition 5.6, lines 1515–1525. -/
def torusClosureRegularLabels (g h : G) : Edge TG → G :=
  torusGraphRegularLabels (fun v => if v.1 + 1 = 0 then h else 1)
    (fun v => if v.2 + 1 = 0 then g else 1)

omit [Fintype G] [DecidableEq G] in
private theorem torusGraphBondMatrix_closure_eq_labels
    (U : G →* Matrix X X ℂ) (ht : ∀ g, (U g).transpose = U g⁻¹) (g h : G) :
    torusGraphBondMatrix (torusHorizontalClosure U h) (torusVerticalClosure U g) =
      fun e : Edge TG => U (torusClosureRegularLabels g h e) := by
  funext e
  cases he : torusEdgeEquiv.symm e <;>
    simp only [torusGraphBondMatrix, torusHorizontalClosure, torusVerticalClosure,
      torusClosureRegularLabels, torusGraphRegularLabels, he] <;>
    split_ifs <;> simp only [ht, inv_one, map_one, Matrix.transpose_one]

/-- Original native regular closures are the literal inserted graph
contractions on the same oriented seam labels, for any physical alphabet.
Source: SCP10, Definition 5.6 and lines 1515–1525. -/
theorem graphInsertedBondNetwork_torusClosureRegularLabels {P : Type*}
    (a : (Fin 4 → G) → P → ℂ) (g h : G) (σ : TV → P) :
    graphInsertedBondNetwork (fun e => leftRegularMatrix G (torusClosureRegularLabels g h e))
        (torusIncidentFamily (fun _ => a)) σ =
      torusGClosure (leftRegularMatrix G) (fun t r b l => a ![t, r, b, l]) g h σ := by
  have ht (x : G) : (leftRegularMatrix G x).transpose = leftRegularMatrix G x⁻¹ := by
    ext y z
    simp only [Matrix.transpose_apply, leftRegularMatrix_apply,
      eq_inv_mul_iff_mul_eq, eq_comm]
  rw [torusGClosure, ← graphInsertedBondNetwork_torusIncidentFamily,
    torusGraphBondMatrix_closure_eq_labels _ ht]

/-- The permutation on two regular labels is the same matrix as the
one-coordinate regular bundle, including its exact row and column indices.
Source: SCP10, the two-bond construction, lines 1840–1873. -/
theorem regularBundleMatrix_unit_eq_paired (g : G) (x y : G × (Unit → G)) :
    regularBundleMatrix Unit g x y = pairedLeftRegularMatrix G g
      (pairUnitBundleEquiv.symm x) (pairUnitBundleEquiv.symm y) := by
  rw [regularBundleMatrix_apply, pairedLeftRegularMatrix_apply]
  have he : pairUnitBundleEquiv.symm (g • y) =
      (g * (pairUnitBundleEquiv.symm y).1, g * (pairUnitBundleEquiv.symm y).2) := rfl
  simp only [← he, Equiv.apply_eq_iff_eq]

/-- Actual fine native closures equal the contraction of the genuine four-site
blocked tensors on the paired coarse graph. The same seam label acts on both
regular bond labels, with all native transposes retained as inverse labels.
No commutation or physical-state factorization hypothesis is used.
Source: SCP10, the geometric step of Observation 6.6 and Definition 5.6,
lines 1888–1909 and 1515–1525. -/
theorem torusGClosure_leftRegular_eq_twoByTwoBundledGraphSite {P : Type*}
    (a : (Fin 4 → G) → P → ℂ) (g h : G) (σ : FV → P) :
    torusGClosure (leftRegularMatrix G) (fun t r b l => a ![t, r, b, l]) g h σ =
      graphInsertedBondNetwork
        (fun e => regularBundleMatrix Unit (torusClosureRegularLabels g h e))
        (twoByTwoBundledGraphSite (fun _ => a)) (twoByTwoPhysicalEquiv σ) := by
  have hfour (α : Fin 4 → G) : ![α 0, α 1, α 2, α 3] = α := by
    funext i
    fin_cases i <;> rfl
  have hgeo := torusGClosure_leftRegular_eq_twoByTwoBlocked
    (fun t r b l => a ![t, r, b, l]) g h σ
  simp only [hfour] at hgeo
  rw [hgeo, torusGClosure]
  rw [← graphInsertedBondNetwork_torusIncidentFamily]
  have ht (x : G) :
      (pairedLeftRegularMatrix G x).transpose = pairedLeftRegularMatrix G x⁻¹ := by
    ext y z
    simp only [Matrix.transpose_apply, pairedLeftRegularMatrix_apply]
    change (if z = x • y then (1 : ℂ) else 0) =
      if y = x⁻¹ • z then 1 else 0
    simp only [eq_inv_smul_iff, eq_comm]
  rw [torusGraphBondMatrix_closure_eq_labels _ ht]
  have hB : (fun e : Edge TG => regularBundleMatrix Unit (torusClosureRegularLabels g h e)) =
      fun e x y => pairedLeftRegularMatrix G (torusClosureRegularLabels g h e)
        (pairUnitBundleEquiv.symm x) (pairUnitBundleEquiv.symm y) := by
    funext e x y
    exact regularBundleMatrix_unit_eq_paired _ _ _
  rw [hB, graphInsertedBondNetwork_twoByTwoBundledGraphSite]
  rfl

end Torus
end TNLean.PEPS
