/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoMarkerMiddleFactors
import TNLean.MPS.AreaLaw.ThreeRegionSupport
import TNLean.Lattice.RegionSplit
import Mathlib.Data.Matrix.Basis
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fixed middle data for two selected windows

The selected middle interval contains the supplied central operator and
has at most four times the window half-width outside the strict core.
The actual crossings have product decompositions with the literal one-site
matrix units at the two middle endpoints.

The middle factors and these crossing decompositions are chosen from the
two windows and the central operator before the exterior bulk operators.
Every weighted ordinary middle sum is the corresponding multiple of the
canonically placed central operator plus a collar-supported remainder.

The geometry may place the two selected endpoints at the same site.
Zero local dimension is included whenever the stated configuration data
exist. No commutativity or matrix product representation is assumed.

## References

Supporting locality algebra for ALVV, arXiv:1602.08828v2,
equation H-mid-cut, lines 810–821, and Proposition 5.7, lines 1324–1333.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The original central support and its strict interior lie in every selected
middle interval. ALVV, arXiv:1602.08828v2, equation H-mid-cut, lines 810–821. -/
theorem core_and_strict_core_subset_selected_middle {L a b ℓ : ℕ}
    (p s : Fin (2 * ℓ)) :
    interval L (a + 2 * ℓ) (b + 1) ⊆
        interval L (a + p.val + 1) (b + s.val + 1) ∧
      interval L (a + 2 * ℓ + 1) b ⊆
        interval L (a + p.val + 1) (b + s.val + 1) := by
  have hp := p.isLt
  constructor <;> exact interval_mono (by omega) (by omega)

/-- The selected middle interval outside the strict core is the union of the
left and right collars. They may overlap at one site when the windows touch.
ALVV, arXiv:1602.08828v2, equation H-mid-cut, lines 810–821. -/
private theorem selected_middle_sdiff_strict_core_eq_collars {L a b ℓ : ℕ}
    (hab : a + 2 * ℓ ≤ b) (p s : Fin (2 * ℓ)) :
    interval L (a + p.val + 1) (b + s.val + 1) \
        interval L (a + 2 * ℓ + 1) b =
      interval L (a + p.val + 1) (a + 2 * ℓ + 1) ∪
        interval L b (b + s.val + 1) := by
  have hp := p.isLt
  have hs := s.isLt
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, mem_interval]
  omega

/-- The two selected collars have at most four times the window half-width
in total, without imposing disjointness. ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem card_selected_middle_sdiff_strict_core_le {L a b ℓ : ℕ}
    (hab : a + 2 * ℓ ≤ b) (p s : Fin (2 * ℓ)) :
    (interval L (a + p.val + 1) (b + s.val + 1) \
      interval L (a + 2 * ℓ + 1) b).card ≤ 4 * ℓ := by
  rw [selected_middle_sdiff_strict_core_eq_collars hab p s]
  calc
    _ ≤ (interval L (a + p.val + 1) (a + 2 * ℓ + 1)).card +
        (interval L b (b + s.val + 1)).card := Finset.card_union_le _ _
    _ ≤ (a + 2 * ℓ + 1 - (a + p.val + 1)) + (b + s.val + 1 - b) :=
      Nat.add_le_add (card_interval_le _ _) (card_interval_le _ _)
    _ ≤ 4 * ℓ := by
      have hp := p.isLt
      have hs := s.isLt
      omega

/-- The middle endpoint of the selected left crossing edge is its only site
in the selected middle interval. This is the left-hand counterpart of the
right intersection in the two-cut support classification. ALVV,
arXiv:1602.08828v2, equation H-mid-cut, lines 810–821. -/
private theorem interval_left_edge_inter_middle {L u v : ℕ}
    (huv : u < v) (hv : v + 1 < L) :
    interval L u (u + 2) ∩ interval L (u + 1) (v + 1) =
      {⟨u + 1, by omega⟩} := by
  ext x
  simp only [Finset.mem_inter, mem_interval, Finset.mem_singleton, Fin.ext_iff]
  omega

/-- An embedding whose image lies in E factors through the canonical inclusion
of E and gives the same actual regional operator in threeSplit coordinates.
No injectivity of the original placement is needed. Supporting locality algebra
for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem embedOp_into_middle_submatrix_threeSplit
    {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] {q : ℕ}
    (T E : Finset V) (hTE : Disjoint T E)
    (e : κ → V) (hE : ∀ j, e j ∈ E)
    (M : Matrix (κ → Fin q) (κ → Fin q) ℂ) :
    (QuantumCircuit.embedOp e M).submatrix
        (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ
        QuantumCircuit.embedOp (fun j ↦ (⟨e j, hE j⟩ : E)) M) ⊗ₖ
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
  classical
  let eE : κ → E := fun j ↦ ⟨e j, hE j⟩
  have hplace : QuantumCircuit.embedOp (Subtype.val : E → V)
      (QuantumCircuit.embedOp eE M) = QuantumCircuit.embedOp e M := by
    simpa only [Function.comp_def, eE] using
      QuantumCircuit.embedOp_embedOp (f := (Subtype.val : E → V))
        Subtype.val_injective eE M
  rw [← hplace]
  exact embedOp_subtype_val_submatrix_threeSplit T E hTE
    (QuantumCircuit.embedOp eE M)

end TNLean.MPS.AreaLaw

namespace QuantumCircuit

/-- Every operator supported at one designated site belongs to the span of the
fixed embedded one-site matrix units, indexed by `Fin (q * q)`.
The family depends only on the site and the local dimension, not on the operator.
This is supporting locality algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. No positive-dimension premise is required. -/
private theorem mem_span_embedOp_single_of_isSupportedOn_singleton
    {E : Type*} [Fintype E] [DecidableEq E] {q : ℕ} (e₀ : E)
    (W : Matrix (E → Fin q) (E → Fin q) ℂ)
    (hW : Entropy.IsSupportedOn (n := fun _ : E ↦ q) W {e₀}) :
    let N : Fin (q * q) → Matrix (E → Fin q) (E → Fin q) ℂ := fun z ↦
      embedOp (fun _ : Fin 1 ↦ e₀)
        (Matrix.single
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).1)
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).2) (1 : ℂ))
    W ∈ Submodule.span ℂ (Set.range N) := by
  classical
  intro N
  by_cases hq : q = 0
  · subst q
    have hzero : W = 0 := by
      ext x y
      exact Fin.elim0 (x e₀)
    rw [hzero]
    exact Submodule.zero_mem _
  · let e : Fin 1 → E := fun _ ↦ e₀
    let S : Finset E := {e₀}
    let σ₀ : E → Fin q := fun _ ↦ ⟨0, Nat.pos_of_ne_zero hq⟩
    obtain ⟨K, hK⟩ := hW.exists_localLift σ₀
    let X : Matrix (Fin 1 → Fin q) (Fin 1 → Fin q) ℂ :=
      fun x y ↦ K (fun _ ↦ x 0) (fun _ ↦ y 0)
    have hX : W = embedOp e X := by
      rw [hK]
      ext σ τ
      rw [Entropy.localLift_apply, embedOp_apply]
      have hagree : AgreeOff e σ τ ↔ ∀ v ∉ S, σ v = τ v := by
        constructor
        · intro h v hv
          apply h v
          intro j
          have hv' : v ≠ e₀ := by simpa only [S, Finset.mem_singleton] using hv
          exact Ne.symm hv'
        · intro h v hv
          apply h v
          have hv' : e₀ ≠ v := hv 0
          simpa only [S, Finset.mem_singleton] using Ne.symm hv'
      change (if ∀ v ∉ S, σ v = τ v then
        K (fun v ↦ σ v.val) (fun v ↦ τ v.val) else 0) =
        if AgreeOff e σ τ then X (σ ∘ e) (τ ∘ e) else 0
      simp only [hagree]
      split_ifs
      · change K (fun v ↦ σ v.val) (fun v ↦ τ v.val) =
          K (fun _ ↦ σ e₀) (fun _ ↦ τ e₀)
        congr 1
        · exact funext fun v ↦ congrArg σ (Finset.mem_singleton.mp v.property)
        · exact funext fun v ↦ congrArg τ (Finset.mem_singleton.mp v.property)
      · rfl
    let Φ : Matrix (Fin 1 → Fin q) (Fin 1 → Fin q) ℂ →ₗ[ℂ]
        Matrix (E → Fin q) (E → Fin q) ℂ :=
      { toFun := embedOp e
        map_add' := embedOp_add e
        map_smul' := embedOp_smul e }
    rw [hX]
    change Φ X ∈ Submodule.span ℂ (Set.range N)
    rw [Matrix.matrix_eq_sum_single X, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_sum]
    apply Submodule.sum_mem
    intro j _
    have hsingle : Matrix.single i j (X i j) =
        (X i j) • Matrix.single i j (1 : ℂ) := by
      simp
    rw [hsingle, map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨finProdFinEquiv (i 0, j 0), ?_⟩
    have hi : (fun _ : Fin 1 ↦ i 0) = i :=
      funext fun t ↦ congrArg i (Subsingleton.elim _ _)
    have hj : (fun _ : Fin 1 ↦ j 0) = j :=
      funext fun t ↦ congrArg j (Subsingleton.elim _ _)
    simp only [N]
    rw [Equiv.symm_apply_apply]
    change embedOp e (Matrix.single (fun _ : Fin 1 ↦ i 0)
        (fun _ : Fin 1 ↦ j 0) (1 : ℂ)) = embedOp e (Matrix.single i j (1 : ℂ))
    rw [hi, hj]

end QuantumCircuit

namespace TNLean.MPS.AreaLaw

/-- The actual left crossing retains a prescribed singleton-supported middle
family. The site and support inclusion are geometric data, not assumptions
on a new Schmidt decomposition. Supporting locality algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem exists_left_crossing_factors_with_fixed_middle_units
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (T E D : Finset V) (hTE : Disjoint T E)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : Entropy.IsSupportedOn (n := fun _ : V ↦ q) P D)
    (UL : Matrix ((T → Fin q) × (E → Fin q))
      ((T → Fin q) × (E → Fin q)) ℂ)
    (hUL : P.submatrix (threeSplit q T E hTE).symm
        (threeSplit q T E hTE).symm =
      UL ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ))
    (e₀ : E)
    (hDE : Finset.univ.filter (fun e : E ↦ e.val ∈ D) ⊆ {e₀}) :
    let N : Fin (q * q) → Matrix (E → Fin q) (E → Fin q) ℂ := fun z ↦
      QuantumCircuit.embedOp (fun _ : Fin 1 ↦ e₀)
        (Matrix.single
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).1)
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).2) (1 : ℂ))
    ∃ A : Fin (q * q) → Matrix (T → Fin q) (T → Fin q) ℂ,
      UL = ∑ z, A z ⊗ₖ N z := by
  classical
  intro N
  apply Matrix.exists_left_factors_of_operatorBlock_mem_span UL N
  intro a b
  have hblock :=
    (operatorBlock_isSupportedOn_of_threeSplit_left T E D hTE P hP UL hUL a b).mono hDE
  exact QuantumCircuit.mem_span_embedOp_single_of_isSupportedOn_singleton
    e₀ (Matrix.operatorBlock UL a b) hblock

/-- The actual right crossing retains the same literal singleton-unit form
as its left, middle-region factors. The tensor association is unchanged.
Supporting locality algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem exists_right_crossing_factors_with_fixed_middle_units
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (T E D : Finset V) (hTE : Disjoint T E)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : Entropy.IsSupportedOn (n := fun _ : V ↦ q) P D)
    (VR : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (hVR : P.submatrix (threeSplit q T E hTE).symm
        (threeSplit q T E hTE).symm =
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm)
    (e₀ : E)
    (hDE : Finset.univ.filter (fun e : E ↦ e.val ∈ D) ⊆ {e₀}) :
    let N : Fin (q * q) → Matrix (E → Fin q) (E → Fin q) ℂ := fun z ↦
      QuantumCircuit.embedOp (fun _ : Fin 1 ↦ e₀)
        (Matrix.single
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).1)
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).2) (1 : ℂ))
    ∃ B : Fin (q * q) →
        Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ,
      VR = ∑ z, N z ⊗ₖ B z := by
  classical
  intro N
  apply Matrix.exists_right_factors_of_left_blocks_mem_span VR N
  intro a b
  have hblock :=
    (leftBlock_isSupportedOn_of_threeSplit_right T E D hTE P hP VR hVR a b).mono hDE
  exact QuantumCircuit.mem_span_embedOp_single_of_isSupportedOn_singleton
    e₀ (fun x y : E → Fin q ↦ VR (x, a) (y, b)) hblock

/-- Regional factors chosen for the two windows and central bulk remain valid
when arbitrary supported exterior bulk operators are supplied afterwards.
Every exterior component of every bulk label is overwritten, while the middle
array and all exterior window components are retained. This is supporting
locality algebra for ALVV, arXiv:1602.08828v2, equation `H-mid-cut`,
lines 810–821, and Proposition 5.7, lines 1324–1333. -/
private theorem exists_threeSplit_two_window_late_exterior
    {V : Type*} [Fintype V] [DecidableEq V] {q ℓ : ℕ}
    (T E : Finset V) (hTE : Disjoint T E) (p s : Fin (2 * ℓ))
    (WL WR : Fin (2 * ℓ) → Matrix (V → Fin q) (V → Fin q) ℂ)
    (Pmid : Matrix (V → Fin q) (V → Fin q) ℂ)
    (HL₀ : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (T → Fin q) (T → Fin q) ℂ)
    (HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (E → Fin q) (E → Fin q) ℂ)
    (HR₀ : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) :
    let g := threeSplit q T E hTE
    let F₀ : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
        Matrix (V → Fin q) (V → Fin q) ℂ :=
      Sum.elim (Sum.elim WL WR) (fun j : Fin 3 ↦ if j = 1 then Pmid else 0)
    (∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
      (F₀ r).submatrix g.symm g.symm =
        (HL₀ r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
            (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
          ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
            (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
          (1 : Matrix ((T → Fin q) × (E → Fin q))
            ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR₀ r) →
    HM (Sum.inr 0) = 0 → HM (Sum.inr 2) = 0 →
    HL₀ (Sum.inr 1) = 0 → HR₀ (Sum.inr 1) = 0 →
    ∀ (PL PR : Matrix (V → Fin q) (V → Fin q) ℂ),
      PL ∈ supportedOperators q (T : Set V) →
      PR ∈ supportedOperators q ((T ∪ E)ᶜ : Set V) →
      let F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
          Matrix (V → Fin q) (V → Fin q) ℂ :=
        Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
      ∃ (HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
          Matrix (T → Fin q) (T → Fin q) ℂ)
        (HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
          Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ),
        (∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
          (F r).submatrix g.symm g.symm =
            (HL r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
                (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
              ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
                (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
              (1 : Matrix ((T → Fin q) × (E → Fin q))
                ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR r) ∧
        (∀ r : Fin (2 * ℓ) ⊕ Fin (2 * ℓ), HL (Sum.inl r) = HL₀ (Sum.inl r)) ∧
        (∀ r : Fin (2 * ℓ) ⊕ Fin (2 * ℓ), HR (Sum.inl r) = HR₀ (Sum.inl r)) ∧
        HR (Sum.inr 0) = 0 ∧ HL (Sum.inr 2) = 0 ∧
        HL (Sum.inr 1) = 0 ∧ HR (Sum.inr 1) = 0 := by
  classical
  intro g F₀ hlocal hMleft hMright hLmid hRmid PL PR hPL hPR F
  obtain ⟨BL, hBL⟩ := exists_threeSplit_eq_kronecker_one_kronecker_one
    (ι := V) (q := q) (T := T) (E := E) (D := (T : Set V)) (A := PL)
    hTE (Set.Subset.rfl) hPL
  obtain ⟨BR, hBR⟩ := exists_threeSplit_eq_one_kronecker
    (ι := V) (q := q) (T := T) (E := E)
    (D := ((T ∪ E)ᶜ : Set V)) (A := PR) hTE
    (by simpa only [Finset.coe_compl, Finset.coe_union] using
      (Set.Subset.rfl : ((T : Set V) ∪ (E : Set V))ᶜ ⊆
        ((T : Set V) ∪ (E : Set V))ᶜ)) hPR
  have hF₀mid : F₀ (Sum.inr 1) = Pmid := by
    change (if (1 : Fin 3) = 1 then Pmid else 0) = Pmid
    exact ite_eq_left rfl
  have hmid : Pmid.submatrix g.symm g.symm =
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM (Sum.inr 1)) ⊗ₖ
        (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
    have h := hlocal (Sum.inr 1) (by intro h; cases h) (by intro h; cases h)
    rw [hF₀mid, hLmid, hRmid] at h
    simpa only [Matrix.zero_kronecker, Matrix.kronecker_zero, zero_add, add_zero] using h
  let HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (T → Fin q) (T → Fin q) ℂ :=
    Sum.elim (fun r ↦ HL₀ (Sum.inl r)) (fun j ↦ if j = 0 then BL else 0)
  let HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ :=
    Sum.elim (fun r ↦ HR₀ (Sum.inl r)) (fun j ↦ if j = 2 then BR else 0)
  have hHLleft : HL (Sum.inr 0) = BL := by
    change (if (0 : Fin 3) = 0 then BL else 0) = BL
    exact ite_eq_left rfl
  have hHLmid : HL (Sum.inr 1) = 0 := by
    change (if (1 : Fin 3) = 0 then BL else 0) = 0
    exact ite_eq_right (by decide)
  have hHLright : HL (Sum.inr 2) = 0 := by
    change (if (2 : Fin 3) = 0 then BL else 0) = 0
    exact ite_eq_right (by decide)
  have hHRleft : HR (Sum.inr 0) = 0 := by
    change (if (0 : Fin 3) = 2 then BR else 0) = 0
    exact ite_eq_right (by decide)
  have hHRmid : HR (Sum.inr 1) = 0 := by
    change (if (1 : Fin 3) = 2 then BR else 0) = 0
    exact ite_eq_right (by decide)
  have hHRright : HR (Sum.inr 2) = BR := by
    change (if (2 : Fin 3) = 2 then BR else 0) = BR
    exact ite_eq_left rfl
  have hFleft : F (Sum.inr 0) = PL := rfl
  have hFmid : F (Sum.inr 1) = Pmid := rfl
  have hFright : F (Sum.inr 2) = PR := rfl
  refine ⟨HL, HR, ?_, ?_, ?_, hHRleft, hHLright, hHLmid, hHRmid⟩
  · intro r hru hrv
    rcases r with r | j
    · exact hlocal (Sum.inl r) hru hrv
    · have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl | rfl
      · rw [hFleft, hHLleft, hHRleft, hMleft]
        simpa only [Matrix.kronecker_zero, Matrix.zero_kronecker, add_zero] using hBL
      · rw [hFmid, hHLmid, hHRmid]
        simpa only [Matrix.zero_kronecker, Matrix.kronecker_zero, zero_add, add_zero] using hmid
      · rw [hFright, hHLright, hHRright, hMright]
        simpa only [Matrix.zero_kronecker, Matrix.kronecker_zero, zero_add] using hBR
  · intro r
    rfl
  · intro r
    rfl

/-- Both selected crossing supports meet the retained middle in their literal
boundary points, and both points lie outside the strict core. All site and
interval bounds are derived from the original two-window hypotheses.
ALVV, arXiv:1602.08828v2, equation H-mid-cut and Proposition 5.7,
lines 810–821 and 1324–1333. -/
private theorem exists_selected_middle_collar_endpoints {L a b ℓ : ℕ}
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) :
    let u := a + p.val
    let v := b + s.val
    let E := interval L (u + 1) (v + 1)
    let Z := interval L (a + 2 * ℓ + 1) b
    let C : Finset E := Finset.univ.filter (fun x : E ↦ x.val ∉ Z)
    ∃ eL eR : E,
      eL.val.val = u + 1 ∧ eR.val.val = v ∧
      Finset.univ.filter (fun x : E ↦ x.val ∈ interval L u (u + 2)) ⊆ {eL} ∧
      Finset.univ.filter (fun x : E ↦ x.val ∈ interval L v (v + 2)) ⊆ {eR} ∧
      eL ∈ C ∧ eR ∈ C := by
  classical
  intro u v E Z C
  have hp := p.isLt
  have hs := s.isLt
  have huv : u < v := by
    dsimp [u, v]
    omega
  have hv : v + 1 < L := by
    dsimp [v]
    omega
  let l : Fin L := ⟨u + 1, by omega⟩
  let r : Fin L := ⟨v, by omega⟩
  have hlE : l ∈ E := by
    apply mem_interval.mpr
    change u + 1 ≤ u + 1 ∧ u + 1 < v + 1
    omega
  have hrE : r ∈ E := by
    apply mem_interval.mpr
    change u + 1 ≤ v ∧ v < v + 1
    omega
  let eL : E := ⟨l, hlE⟩
  let eR : E := ⟨r, hrE⟩
  have hpullback {D : Finset (Fin L)} (e : E) (hDE : D ∩ E = {e.val}) :
      Finset.univ.filter (fun x : E ↦ x.val ∈ D) ⊆ {e} := by
    intro x hx
    apply Finset.mem_singleton.mpr
    apply Subtype.ext
    have hxDE : x.val ∈ D ∩ E :=
      Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hx).2, x.property⟩
    rw [hDE] at hxDE
    exact Finset.mem_singleton.mp hxDE
  have hleft : interval L u (u + 2) ∩ E = {eL.val} :=
    interval_left_edge_inter_middle (L := L) huv hv
  have hright : interval L v (v + 2) ∩ E = {eR.val} :=
    (interval_edge_classification_of_lt (L := L) huv hv).2.2.2.1
  refine ⟨eL, eR, rfl, rfl, hpullback eL hleft, hpullback eR hright, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    have hbound := (mem_interval.mp hmem).1
    change a + 2 * ℓ + 1 ≤ u + 1 at hbound
    dsimp [u] at hbound
    omega
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    have hbound := (mem_interval.mp hmem).2
    change v < b at hbound
    dsimp [v] at hbound
    omega

/-- The actual core and the two windows determine fixed selected middle
and crossing factors. All supported exterior bulk operators are quantified
after these choices. The core is placed by the literal site inclusions;
no physical-site ordering or matrix product hypothesis is supplied.
ALVV, arXiv:1602.08828v2, equation H-mid-cut, lines 810–821, and
Proposition 5.7, lines 1324–1333. -/
theorem exists_physical_selected_window_fixed_middle_data
    {L q ℓ a b : ℕ}
    (WL WR : Fin (2 * ℓ) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ))
    (M : Matrix ((interval L (a + 2 * ℓ) (b + 1)) → Fin q)
      ((interval L (a + 2 * ℓ) (b + 1)) → Fin q) ℂ) :
    let K := interval L (a + 2 * ℓ) (b + 1)
    let T := interval L 0 (a + p.val + 1)
    let E := interval L (a + p.val + 1) (b + s.val + 1)
    let hTE : Disjoint T E := disjoint_interval_interval (L := L) 0 _ _
    let g := threeSplit q T E hTE
    let Z := interval L (a + 2 * ℓ + 1) b
    let C : Finset E := Finset.univ.filter (fun x : E ↦ x.val ∉ Z)
    let hKE : K ⊆ E := (core_and_strict_core_subset_selected_middle
      (L := L) (a := a) (b := b) p s).1
    let ME := QuantumCircuit.embedOp (fun x : K ↦ (⟨x.val, hKE x.property⟩ : E)) M
    let Pmid := QuantumCircuit.embedOp (Subtype.val : K → Fin L) M
    let O : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :=
      (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
    let N := fun (e₀ : E) (z : Fin (q * q)) ↦
      QuantumCircuit.embedOp (fun _ : Fin 1 ↦ e₀)
        (Matrix.single
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).1)
          (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).2) (1 : ℂ))
    ∃ (eL eR : E)
      (HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
        Matrix (E → Fin q) (E → Fin q) ℂ)
      (UL : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ)
      (VR : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
        ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
      (AL : Fin (q * q) → Matrix (T → Fin q) (T → Fin q) ℂ)
      (BR : Fin (q * q) →
        Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ),
      eL.val.val = a + p.val + 1 ∧ eR.val.val = b + s.val ∧
      HM (Sum.inr 1) = ME ∧
      (WL p).submatrix g.symm g.symm = UL ⊗ₖ
        (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) ∧
      (WR s).submatrix g.symm g.symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm ∧
      UL = ∑ z, AL z ⊗ₖ N eL z ∧
      VR = ∑ z, N eR z ⊗ₖ BR z ∧
      (∀ z, Entropy.IsSupportedOn (n := fun _ : E ↦ q) (N eL z) C) ∧
      (∀ z, Entropy.IsSupportedOn (n := fun _ : E ↦ q) (N eR z) C) ∧
      (∀ z : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℂ,
        ∃ Kz : Matrix (E → Fin q) (E → Fin q) ℂ,
          (∑ i ∈ O, z i • HM i) = z (Sum.inr 1) • ME + Kz ∧
            Entropy.IsSupportedOn (n := fun _ : E ↦ q) Kz C) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ℓ) L) →
        let F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∃ (HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
            Matrix (T → Fin q) (T → Fin q) ℂ)
          (HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
            Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ),
          (∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
            (F r).submatrix g.symm g.symm =
              (HL r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
                  (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
                ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
                  (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
                (1 : Matrix ((T → Fin q) × (E → Fin q))
                  ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR r) ∧
          HL (Sum.inr 1) = 0 ∧ HR (Sum.inr 1) = 0 := by
  classical
  intro K T E hTE g Z C hKE ME Pmid O N
  obtain ⟨eL, eR, heL, heR, hDEL, hDER, heLC, heRC⟩ :=
    exists_selected_middle_collar_endpoints hab hb p s
  let F₀ : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    Sum.elim (Sum.elim WL WR) (fun j : Fin 3 ↦ if j = 1 then Pmid else 0)
  have hF₀left : F₀ (Sum.inr 0) = 0 := by
    change (if (0 : Fin 3) = 1 then Pmid else 0) = 0
    exact ite_eq_right (by decide)
  have hF₀middle : F₀ (Sum.inr 1) = Pmid := by
    change (if (1 : Fin 3) = 1 then Pmid else 0) = Pmid
    exact ite_eq_left rfl
  have hF₀right : F₀ (Sum.inr 2) = 0 := by
    change (if (2 : Fin 3) = 1 then Pmid else 0) = 0
    exact ite_eq_right (by decide)
  have hFleft : ∀ r, F₀ (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)) := by
    intro r
    change WL r ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L))
    exact mem_supportedOperators_of_isSupportedOn (hleft r)
  have hFright : ∀ r, F₀ (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)) := by
    intro r
    change WR r ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L))
    exact mem_supportedOperators_of_isSupportedOn (hright r)
  have hFleftBulk : F₀ (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)) := by
    rw [hF₀left]
    exact Submodule.zero_mem _
  have hPmid : Pmid ∈ supportedOperators q (K : Set (Fin L)) :=
    TNLean.Lattice.siteLift_mem_supportedOperators K M
  have hFmiddleBulk : F₀ (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)) := by
    rw [hF₀middle]
    exact hPmid
  have hFrightBulk : F₀ (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)) := by
    rw [hF₀right]
    exact Submodule.zero_mem _
  obtain ⟨HL₀, HM, HR₀, UL, VR, hlocal₀, hUL₀, hVR₀, _hULrank, _hVRrank,
      hMleftBulk, hMrightBulk, hLmiddleZero, hRmiddleZero, hLzero, hRzero, hLsupp, hRsupp⟩ :=
    exists_threeSplit_two_window_factors_with_collars F₀ hFleft hFright hFleftBulk hFmiddleBulk
      hFrightBulk hab hb p s
  have hUL : (WL p).submatrix g.symm g.symm = UL ⊗ₖ
      (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
    exact hUL₀
  have hVR : (WR s).submatrix g.symm g.symm =
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm := by
    exact hVR₀
  have hmiddle : HM (Sum.inr 1) = ME := by
    apply eq_of_threeSplit_middle_lift_eq T E eL
    have hchosen : Pmid.submatrix g.symm g.symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM (Sum.inr 1)) ⊗ₖ
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
      have h := hlocal₀ (Sum.inr 1) (by intro h; cases h) (by intro h; cases h)
      rw [hF₀middle, hLmiddleZero, hRmiddleZero] at h
      simpa only [Matrix.zero_kronecker, Matrix.kronecker_zero, zero_add, add_zero] using h
    have hcanonical := embedOp_into_middle_submatrix_threeSplit T E hTE
      (Subtype.val : K → Fin L) (fun x ↦ hKE x.property) M
    exact hchosen.symm.trans hcanonical
  obtain ⟨AL, hAL⟩ := exists_left_crossing_factors_with_fixed_middle_units
    T E (interval L (a + p.val) (a + p.val + 2)) hTE (WL p) (hleft p) UL hUL eL hDEL
  obtain ⟨BR, hBR⟩ := exists_right_crossing_factors_with_fixed_middle_units
    T E (interval L (b + s.val) (b + s.val + 2)) hTE (WR s) (hright s) VR hVR eR hDER
  have hNsupport (e₀ : E) (he₀ : e₀ ∈ C) (z : Fin (q * q)) :
      Entropy.IsSupportedOn (n := fun _ : E ↦ q) (N e₀ z) C := by
    have hinj : Function.Injective (fun _ : Fin 1 ↦ e₀) :=
      fun _ _ _ ↦ Subsingleton.elim _ _
    have hmem : N e₀ z ∈ supportedOperators q (({e₀} : Finset E) : Set E) := by
      simpa only [N, Set.range_const, Finset.coe_singleton] using
        QuantumCircuit.embedOp_mem_supportedOperators hinj
          (Matrix.single
            (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).1)
            (fun _ : Fin 1 ↦ (finProdFinEquiv.symm z).2) (1 : ℂ))
    exact (isSupportedOn_of_mem_supportedOperators (S := {e₀}) hmem).mono
      (Finset.singleton_subset_iff.mpr he₀)
  have hweighted : ∀ z : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℂ,
      ∃ Kz : Matrix (E → Fin q) (E → Fin q) ℂ,
        (∑ i ∈ O, z i • HM i) = z (Sum.inr 1) • ME + Kz ∧
          Entropy.IsSupportedOn (n := fun _ : E ↦ q) Kz C := by
    intro z
    obtain ⟨Kz, hKz, hKsupport⟩ :=
      exists_weighted_ordinary_middle_eq_central_add_supported HM p s z C
        hMleftBulk hMrightBulk hLzero (fun r _ ↦ hLsupp r) hRzero (fun r _ ↦ hRsupp r)
    exact ⟨Kz, by simpa only [hmiddle] using hKz, hKsupport⟩
  refine ⟨eL, eR, HM, UL, VR, AL, BR, heL, heR, hmiddle, hUL, hVR,
    hAL, hBR, hNsupport eL heLC, hNsupport eR heRC, hweighted, ?_⟩
  intro PL PR hPL hPR F
  have hPLT : PL ∈ supportedOperators q (T : Set (Fin L)) :=
    supportedOperators_mono
      (Finset.coe_subset.mpr (interval_mono (by omega) (by omega)))
      (mem_supportedOperators_of_isSupportedOn hPL)
  have hPRU : PR ∈ supportedOperators q ((T ∪ E)ᶜ : Set (Fin L)) := by
    apply supportedOperators_mono ?_ (mem_supportedOperators_of_isSupportedOn hPR)
    intro x hx
    have hx' := mem_interval.mp hx
    change ¬(x ∈ T ∨ x ∈ E)
    simp only [T, E, mem_interval]
    have hp := p.isLt
    have hs := s.isLt
    omega
  obtain ⟨HL, HR, hlocal, _hLwindows, _hRwindows, _hRleftBulk, _hLrightBulk, hLmid, hRmid⟩ :=
    exists_threeSplit_two_window_late_exterior T E hTE p s WL WR Pmid HL₀ HM HR₀
      hlocal₀ hMleftBulk hMrightBulk hLmiddleZero hRmiddleZero PL PR hPLT hPRU
  exact ⟨HL, HR, hlocal, hLmid, hRmid⟩

end TNLean.MPS.AreaLaw

end
