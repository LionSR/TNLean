/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.RetainedCoreFamilies
import TNLean.MPS.AreaLaw.SelectedCoefficientDecomposition
import TNLean.MPS.AreaLaw.SelectedMiddleData
import TNLean.MPS.AreaLaw.TraceCoreSlices
import TNLean.Algebra.TwoMarkerMiddleFactors
import QICLean.Entropy.LocalLift
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.List.OfFn

/-!
# Common matrix product families for selected two-marker coefficients

The windows, actual core tensors, selected crossings and ordinary scalar
weights determine one family of middle operators in increasing interval
coordinates. The family is chosen before the supported exterior operators
and before every scalar combination of degrees through the fixed cutoff.
The selected crossing operators themselves remain unweighted.

Each ordered middle word is expanded using the same supplied core tensors
and one retained complement. Its summands carry the general square open
bond bound. The family count is bounded separately, with an additional
coarse estimate in the low-frequency range.

The statements include zero local and virtual dimensions whenever their
configuration data exist. No source-sharp virtual dimension, computational
cost or complete proposition is asserted.

## References

Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Expand every ordinary run into repeated affine steps, retaining each
marker in its original position. ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private def twoMarkerMiddleSteps {R : Type*} {k i j rU rV : ℕ}
    (K : R) (c : ℂ) (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex k i j rU rV) : List (R × ℂ) :=
  (List.ofFn (fun h : Fin (i + j) ↦
    List.replicate (p.1.2 h.castSucc).val (K, c) ++
      [(Sum.elim U V (p.1.1 h), 0)])).flatten ++
    List.replicate (p.1.2 (Fin.last (i + j))).val (K, c)

/-- The deterministic list has the original word length and evaluates to
that exact ordered middle factor under any pointwise placement f.
No homomorphism property of f is required. ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem twoMarkerMiddleSteps_spec
    {R S : Type*} [Semiring S] [Algebra ℂ S] {k i j rU rV : ℕ}
    (f : R → S) (H : S) (K : R) (c : ℂ)
    (U : Fin rU → R) (V : Fin rV → R)
    (p : TwoMarkerMiddleIndex k i j rU rV) :
    let steps := twoMarkerMiddleSteps K c U V p
    steps.length = (∑ h, (p.1.2 h).val) + i + j ∧
      steps.length ≤ k ∧
      (steps.map (fun x ↦ f x.1 + x.2 • H)).prod =
        twoMarkerMiddleFactor (c • H + f K) (f ∘ U) (f ∘ V) p := by
  intro steps
  have hlen : steps.length = (∑ h, (p.1.2 h).val) + i + j := by
    change (twoMarkerMiddleSteps K c U V p).length = _
    simp only [twoMarkerMiddleSteps, List.length_append, List.length_flatten,
      List.map_ofFn, Function.comp_def, List.length_replicate,
      List.length_singleton, List.sum_ofFn, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id,
      mul_one]
    rw [Fin.sum_univ_castSucc (fun h : Fin (i + j + 1) ↦ (p.1.2 h).val)]
    omega
  refine ⟨hlen, ?_, ?_⟩
  · rw [hlen]
    exact p.2.2.2
  · have hrun : f K + c • H = c • H + f K := add_comm _ _
    have hmarker (w : Fin rU ⊕ Fin rV) :
        f (Sum.elim U V w) = Sum.elim (f ∘ U) (f ∘ V) w := by
      cases w <;> rfl
    have hchunk (t : ℕ) (W : R) :
        ((List.replicate t (K, c) ++ [(W, 0)]).map
          (fun x : R × ℂ ↦ f x.1 + x.2 • H)).prod =
        (c • H + f K) ^ t * f W := by
      simp only [List.map_append, List.prod_append, List.map_replicate,
        List.prod_replicate, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, zero_smul, add_zero, mul_one, hrun]
    change ((twoMarkerMiddleSteps K c U V p).map
      (fun x : R × ℂ ↦ f x.1 + x.2 • H)).prod = _
    rw [twoMarkerMiddleSteps, List.map_append, List.prod_append,
      List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn]
    simp only [Function.comp_def]
    simp_rw [hchunk, hmarker]
    rw [List.map_replicate, List.prod_replicate, hrun]
    rfl

end TNLean.MPS.AreaLaw

namespace Entropy

/-- Every supported operator is an actual local lift, including when the
full configuration space is empty. Supporting locality algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem IsSupportedOn.exists_eq_localLift
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    {C : Finset V} {X : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hX : IsSupportedOn X C) :
    ∃ XC : Matrix (RegionConfig n C) (RegionConfig n C) ℂ,
      X = localLift C XC := by
  classical
  by_cases h : Nonempty (SiteConfig n)
  · exact hX.exists_localLift (Classical.choice h)
  · refine ⟨0, ?_⟩
    ext σ τ
    exact False.elim (h ⟨σ⟩)

end Entropy

namespace TNLean.MPS.AreaLaw

/-- Supported collar factors have retained representatives chosen once for
all degrees and existing middle indices. Their affine steps evaluate to the
original ordered middle factor. The explicit matrix equality instance keeps
its word algebra fixed. ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
private theorem exists_localLift_twoMarkerMiddleSteps
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    [DecidableEq (Entropy.SiteConfig n)] {rU rV : ℕ}
    (C : Finset V)
    (H K : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ) (c : ℂ)
    (U : Fin rU → Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ)
    (W : Fin rV → Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ)
    (hK : Entropy.IsSupportedOn K C)
    (hU : ∀ t, Entropy.IsSupportedOn (U t) C)
    (hW : ∀ t, Entropy.IsSupportedOn (W t) C) :
    ∃ (KC : Matrix (Entropy.RegionConfig n C) (Entropy.RegionConfig n C) ℂ)
      (UC : Fin rU → Matrix (Entropy.RegionConfig n C) (Entropy.RegionConfig n C) ℂ)
      (WC : Fin rV → Matrix (Entropy.RegionConfig n C) (Entropy.RegionConfig n C) ℂ),
      K = Entropy.localLift C KC ∧
      (∀ t, U t = Entropy.localLift C (UC t)) ∧
      (∀ t, W t = Entropy.localLift C (WC t)) ∧
      ∀ (k i j : ℕ) (p : TwoMarkerMiddleIndex k i j rU rV),
        let steps := twoMarkerMiddleSteps KC c UC WC p
        steps.length ≤ k ∧
          (steps.map (fun x ↦ Entropy.localLift C x.1 + x.2 • H)).prod =
            twoMarkerMiddleFactor (c • H + K) U W p := by
  classical
  obtain ⟨KC, hKC⟩ := hK.exists_eq_localLift
  have hUret : ∀ t, ∃ X, U t = Entropy.localLift C X :=
    fun t ↦ (hU t).exists_eq_localLift
  have hWret : ∀ t, ∃ X, W t = Entropy.localLift C X :=
    fun t ↦ (hW t).exists_eq_localLift
  choose UC hUC using hUret
  choose WC hWC using hWret
  refine ⟨KC, UC, WC, hKC, hUC, hWC, ?_⟩
  intro k i j p steps
  let f : Matrix (Entropy.RegionConfig n C) (Entropy.RegionConfig n C) ℂ →
      Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ := Entropy.localLift C
  have hspec := twoMarkerMiddleSteps_spec f H KC c UC WC p
  have hfK : f KC = K := hKC.symm
  have hfU : f ∘ UC = U := funext fun t ↦ (hUC t).symm
  have hfW : f ∘ WC = W := funext fun t ↦ (hWC t).symm
  refine ⟨hspec.2.1, ?_⟩
  have heval := hspec.2.2
  rw [hfK, hfU, hfW] at heval
  exact heval

end TNLean.MPS.AreaLaw

namespace MPOTensor

open TNLean.MPS.AreaLaw

/-- Every supplied ordered affine word admits a finite matrix product
operator decomposition in the original site order. The family has exactly
(length+1) times the square of the retained configuration dimension terms;
its term of degree t has the general open bond bound (B^t)^2.
Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. This bound does not establish the paper's sharper estimate. -/
private theorem exists_finite_actual_natural_affine_family {T L q B : ℕ}
    (Afull : Fin T → MPOTensor q B) (C : Matrix (Fin B) (Fin B) ℂ)
    (a : ℕ) (ha : a + L ≤ T)
    (steps : List (Matrix (actualAffineRetainedConfig T L q a)
      (actualAffineRetainedConfig T L q a) ℂ × ℂ)) :
    let n := (steps.length + 1) * Fintype.card (actualAffineRetainedConfig T L q a) ^ 2
    ∃ (t : Fin n → Fin (steps.length + 1))
      (V : Fin n → Matrix (Fin T → Fin q) (Fin T → Fin q) ℂ),
      (∀ r, IsOpenMPS T (q * q) ((B ^ (t r).val) ^ 2) (fun w ↦ V r
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
        (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2))) ∧
      (steps.map (fun z : Matrix (actualAffineRetainedConfig T L q a)
          (actualAffineRetainedConfig T L q a) ℂ × ℂ ↦
        (z.1 ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)).submatrix
          (retainedIntervalEquiv a ha).symm (retainedIntervalEquiv a ha).symm +
        z.2 • (Matrix.of fun σ τ : Fin T → Fin q ↦ Matrix.trace
          (C * (List.ofFn (fun v : Fin T ↦ Afull v (σ v) (τ v))).prod)))).prod =
          ∑ r, V r := by
  intro n
  let R : Fin B × Fin B → Matrix (actualAffineRetainedConfig T L q a)
      (actualAffineRetainedConfig T L q a) ℂ := fun ab η θ ↦
    actualRetainedIntervalClosing Afull C a ha η θ ab.2 ab.1
  let Ainterval : Fin L → MPOTensor q B :=
    fun v ↦ Afull ⟨a + v.val, by omega⟩
  obtain ⟨t, _, _, V, _, hV, hprod⟩ :=
    exists_finite_natural_retained_core_family a ha R steps Ainterval
  exact ⟨t, V, hV, (prod_actual_natural_affine_eq Afull C a ha steps).trans hprod⟩

end MPOTensor

namespace TNLean.MPS.AreaLaw

/-- Every existing ordered middle word built from the actual supplied regional
MPO and collar-supported factors has a finite MPO decomposition in increasing
selected-interval coordinates. If its word length is d, the decomposition has
exactly (d+1) times the square of the retained configuration dimension terms.
The term of degree t has the general open bond bound (B^t)^2. This supporting
result for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333, does not
assert the source's sharper bond estimate or its algorithmic bound. -/
private noncomputable def actualSelectedMiddleWordStatement
    {L a b ell q B rU rV : ℕ}
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell))
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) (zmid : ℂ) : Prop :=
    let cE := a + p.val + 1
    let dE := b + s.val + 1
    let E := interval L cE dE
    let Z := interval L (a + 2 * ell + 1) b
    let C : Finset E := Finset.univ.filter (fun x : E ↦ x.val ∉ Z)
    let N := dE - cE
    let aNat := (a + 2 * ell + 1) - cE
    let Lnat := b - (a + 2 * ell + 1)
    let eK := intervalShiftOrderIso
      (show a + 2 * ell ≤ b + 1 by omega)
      (show b + 1 ≤ L by have hs := s.isLt; omega)
    let eE := intervalShiftOrderIso
      (show cE ≤ dE by have hp := p.isLt; omega)
      (show dE ≤ L by have hs := s.isLt; omega)
    let inc := fun x : ↥(interval L (a + 2 * ell) (b + 1)) ↦
      (⟨x.val, mem_interval.mpr (by
        have hx := mem_interval.mp x.property
        have hp := p.isLt
        constructor <;> omega)⟩ : E)
    let Mphys := QuantumCircuit.embedOp eK
      (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
        Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
    let ME := QuantumCircuit.embedOp inc Mphys
    ∀ (K : Matrix (E → Fin q) (E → Fin q) ℂ)
      (U : Fin rU → Matrix (E → Fin q) (E → Fin q) ℂ)
      (W : Fin rV → Matrix (E → Fin q) (E → Fin q) ℂ),
      Entropy.IsSupportedOn K C →
      (∀ t, Entropy.IsSupportedOn (U t) C) →
      (∀ t, Entropy.IsSupportedOn (W t) C) →
      ∀ (k i j : ℕ) (pIndex : TwoMarkerMiddleIndex k i j rU rV),
        ∃ d : ℕ, d = (∑ h, (pIndex.1.2 h).val) + i + j ∧ d ≤ k ∧
          let n := (d + 1) *
            Fintype.card (MPOTensor.actualAffineRetainedConfig N Lnat q aNat) ^ 2
          ∃ (t : Fin n → Fin (d + 1))
            (V : Fin n → Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ),
            (∀ r, IsOpenMPS N (q * q) ((B ^ (t r).val) ^ 2) (fun w ↦ V r
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
              (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2))) ∧
            (twoMarkerMiddleFactor (zmid • ME + K) U W pIndex).submatrix
              (fun σ : Fin N → Fin q ↦ σ ∘ eE.symm)
              (fun σ : Fin N → Fin q ↦ σ ∘ eE.symm) = ∑ r, V r

/-- Finite MPO families for the supplied selected-middle word.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem exists_actual_selected_middle_word_mpo_family
    {L a b ell q B rU rV : ℕ}
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell))
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) (zmid : ℂ) :
    actualSelectedMiddleWordStatement (L := L) (a := a) (b := b) (ell := ell)
      (q := q) (B := B) (rU := rU) (rV := rV) hab hb p s Acore C0 zmid := by
  classical
  let cE := a + p.val + 1
  let dE := b + s.val + 1
  let E := interval L cE dE
  let Z := interval L (a + 2 * ell + 1) b
  let C : Finset E := Finset.univ.filter (fun x : E ↦ x.val ∉ Z)
  let N := dE - cE
  let aNat := (a + 2 * ell + 1) - cE
  let Lnat := b - (a + 2 * ell + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega)
    (show b + 1 ≤ L by have hs := s.isLt; omega)
  let eE := intervalShiftOrderIso
    (show cE ≤ dE by have hp := p.isLt; omega)
    (show dE ≤ L by have hs := s.isLt; omega)
  let inc := fun x : ↥(interval L (a + 2 * ell) (b + 1)) ↦
    (⟨x.val, mem_interval.mpr (by
      have hx := mem_interval.mp x.property
      have hp := p.isLt
      constructor <;> omega)⟩ : E)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
  let ME := QuantumCircuit.embedOp inc Mphys
  intro K U W hK hU hW
  have hp := p.isLt
  have hs := s.isLt
  have hcd : cE ≤ dE := by dsimp only [cE, dE]; omega
  have hd : dE ≤ L := by dsimp only [dE]; omega
  have hcu : cE ≤ a + 2 * ell + 1 := by dsimp only [cE]; omega
  have hud : a + 2 * ell + 1 ≤ dE := by dsimp only [dE]; omega
  have hvd : b ≤ dE := by dsimp only [dE]; omega
  have ha : aNat + Lnat ≤ N :=
    intervalShift_subinterval_length_le hcu hud hvd
  have hC : ∀ r : Fin N,
      r ∈ Finset.univ.filter (fun v : Fin N ↦
        ¬(aNat ≤ v.val ∧ v.val < aNat + Lnat)) ↔ eE r ∈ C := by
    intro r
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (not_congr (intervalShiftOrderIso_mem_subinterval
      (u := a + 2 * ell + 1) (v := b) hcd hd hcu r)).symm
  let eConf : (E → Fin q) ≃ (Fin N → Fin q) :=
    Equiv.arrowCongr eE.toEquiv.symm (Equiv.refl (Fin q))
  let natPull := Matrix.reindexAlgEquiv ℂ ℂ eConf
  have hnatPull (X : Matrix (E → Fin q) (E → Fin q) ℂ) :
      natPull X = X.submatrix
        (fun σ : Fin N → Fin q ↦ σ ∘ eE.symm)
        (fun σ : Fin N → Fin q ↦ σ ∘ eE.symm) := rfl
  have hca : cE ≤ a + 2 * ell := by dsimp only [cE]; omega
  have hcore : a + 2 * ell ≤ b + 1 := by omega
  have hbd : b + 1 ≤ dE := by dsimp only [dE]; omega
  have hpad : (a + 2 * ell - cE) + ((b + 1) - (a + 2 * ell)) ≤ N := by
    dsimp only [N]
    omega
  let Afull : Fin N → MPOTensor q B :=
    MPOTensor.identityExtendInterval Acore (a + 2 * ell - cE) hpad
  let Hnat : Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ :=
    Matrix.of fun σ τ ↦ Matrix.trace
      (C0 * (List.ofFn (fun v ↦ Afull v (σ v) (τ v))).prod)
  have hME : natPull ME = Hnat := by
    exact MPOTensor.trace_identityExtendInterval_nested_natural
      hca hcore hbd hd Acore C0
  let place := fun X : Matrix (MPOTensor.actualAffineRetainedConfig N Lnat q aNat)
      (MPOTensor.actualAffineRetainedConfig N Lnat q aNat) ℂ ↦
    (X ⊗ₖ (1 : Matrix (Fin Lnat → Fin q) (Fin Lnat → Fin q) ℂ)).submatrix
      (retainedIntervalEquiv aNat ha).symm (retainedIntervalEquiv aNat ha).symm
  have htransport : ∀ X : Matrix (Entropy.RegionConfig (fun _ : E ↦ q) C)
      (Entropy.RegionConfig (fun _ : E ↦ q) C) ℂ,
      ∃ Xret : Matrix (MPOTensor.actualAffineRetainedConfig N Lnat q aNat)
          (MPOTensor.actualAffineRetainedConfig N Lnat q aNat) ℂ,
        natPull (Entropy.localLift C X) = place Xret := by
    intro X
    exact exists_retainedMatrix_of_physical_localLift eE.toEquiv aNat ha C hC X
  choose g hg using htransport
  obtain ⟨KC, UC, WC, _hKC, _hUC, _hWC, hsteps⟩ :=
    exists_localLift_twoMarkerMiddleSteps C ME K zmid U W hK hU hW
  intro k i j pIndex
  let stepsPhys := twoMarkerMiddleSteps KC zmid UC WC pIndex
  let stepsNat := stepsPhys.map (fun z ↦ (g z.1, z.2))
  have hstep := hsteps k i j pIndex
  have hlength := (twoMarkerMiddleSteps_spec (Entropy.localLift C)
    ME KC zmid UC WC pIndex).1
  have hlengthNat : stepsNat.length = (∑ h, (pIndex.1.2 h).val) + i + j := by
    simpa only [stepsNat, List.length_map] using hlength
  have hbound : stepsNat.length ≤ k := by
    simpa only [stepsNat, List.length_map] using hstep.1
  have hproduct : natPull (twoMarkerMiddleFactor (zmid • ME + K) U W pIndex) =
      (stepsNat.map (fun z ↦ place z.1 + z.2 • Hnat)).prod := by
    calc
      natPull (twoMarkerMiddleFactor (zmid • ME + K) U W pIndex) =
          natPull ((stepsPhys.map
            (fun x ↦ Entropy.localLift C x.1 + x.2 • ME)).prod) :=
        congrArg natPull hstep.2.symm
      _ = ((stepsPhys.map
            (fun x ↦ Entropy.localLift C x.1 + x.2 • ME)).map natPull).prod :=
        map_list_prod natPull _
      _ = (stepsNat.map (fun z ↦ place z.1 + z.2 • Hnat)).prod := by
        apply congrArg List.prod
        simp only [stepsNat, List.map_map]
        apply List.map_congr_left
        intro x _hx
        change natPull (Entropy.localLift C x.1 + x.2 • ME) =
          place (g x.1) + x.2 • Hnat
        rw [map_add, map_smul, hg, hME]
  obtain ⟨t, V, hV, hsum⟩ :=
    MPOTensor.exists_finite_actual_natural_affine_family Afull C0 aNat ha stepsNat
  refine ⟨stepsNat.length, hlengthNat, hbound, t, V, hV, ?_⟩
  rw [← hnatPull]
  exact hproduct.trans hsum

/-- One finite family of actual natural MPOs suffices for every supported
exterior Hamiltonian and every polynomial weight at the fixed degree and
crossing frequencies. The selected crossings remain unweighted. Supporting
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
theorem exists_common_physical_twoMarkerCoefficient_mpo_family
    {L q ell a b B : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell))
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ)
    (z : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℂ)
    (k i j : ℕ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let T := interval L 0 (a + p.val + 1)
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let hTE : Disjoint T E := disjoint_interval_interval (L := L) 0 _ _
  let g := threeSplit q T E hTE
  let e := exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)
  let Nnat := (b + s.val + 1) - (a + p.val + 1)
  let aNat := (a + 2 * ell + 1) - (a + p.val + 1)
  let Lnat := b - (a + 2 * ell + 1)
  let eE := intervalShiftOrderIso
    (show a + p.val + 1 ≤ b + s.val + 1 by have hp := p.isLt; omega)
    (show b + s.val + 1 ≤ L by have hs := s.isLt; omega)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega)
    (show b + 1 ≤ L by have hs := s.isLt; omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
    (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
  let RetDim := Fintype.card (MPOTensor.actualAffineRetainedConfig Nnat Lnat q aNat)
  ∃ (n : ℕ) (deg : Fin n → Fin (k + 1))
    (V : Fin n → Matrix (Fin Nnat → Fin q) (Fin Nnat → Fin q) ℂ),
    n ≤ Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
      (k + 1) * RetDim ^ 2 ∧
    (∀ r, IsOpenMPS Nnat (q * q) ((B ^ (deg r).val) ^ 2) (fun w ↦ V r
      (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
      (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2))) ∧
    ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
      Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
      let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
          Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
        Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
      let Dphys := ∑ t ∈ O, z t • F t
      ∀ cPoly : Fin (k + 1) → ℂ,
        ∃ B_out : Fin n →
            Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
              ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ,
          ((∑ r : Fin (k + 1),
              cPoly r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j).reindex
              (g.trans e) (g.trans e)).submatrix
                (fun x : ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ×
                    (Fin Nnat → Fin q) ↦ (x.1, x.2 ∘ eE.symm))
                (fun x : ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ×
                    (Fin Nnat → Fin q) ↦ (x.1, x.2 ∘ eE.symm)) =
            ∑ r, B_out r ⊗ₖ V r := by
  classical
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let T := interval L 0 (a + p.val + 1)
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let hTE : Disjoint T E := disjoint_interval_interval (L := L) 0 _ _
  let g := threeSplit q T E hTE
  let e := exteriorMiddleEquiv (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)
  let Nnat := (b + s.val + 1) - (a + p.val + 1)
  let aNat := (a + 2 * ell + 1) - (a + p.val + 1)
  let Lnat := b - (a + 2 * ell + 1)
  let eE := intervalShiftOrderIso
    (show a + p.val + 1 ≤ b + s.val + 1 by have hp := p.isLt; omega)
    (show b + s.val + 1 ≤ L by have hs := s.isLt; omega)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega)
    (show b + 1 ≤ L by have hs := s.isLt; omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun v ↦ Acore v (σ v) (τ v))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
    (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
  let RetDim := Fintype.card (MPOTensor.actualAffineRetainedConfig Nnat Lnat q aNat)
  let Nmid := fun (e₀ : E) (t : Fin (q * q)) ↦
    QuantumCircuit.embedOp (fun _ : Fin 1 ↦ e₀)
      (Matrix.single
        (fun _ : Fin 1 ↦ (finProdFinEquiv.symm t).1)
        (fun _ : Fin 1 ↦ (finProdFinEquiv.symm t).2) (1 : ℂ))
  obtain ⟨eL, eR, A, Kz, _heL, _heR, hA, hKz, hNL, hNR, hphysical⟩ :=
    exists_physical_twoMarkerCoefficient_prescribed_middle_decomposition
      WL WR hleft hright hab hb p s Mphys z k i j
  let Widx := TwoMarkerMiddleIndex k i j (q * q) (q * q)
  let d : Widx → ℕ := fun w ↦ (∑ h, (w.1.2 h).val) + i + j
  let nw : Widx → ℕ := fun w ↦ (d w + 1) * RetDim ^ 2
  let Psi : Widx → Matrix (E → Fin q) (E → Fin q) ℂ :=
    fun w ↦ twoMarkerMiddleFactor A (Nmid eL) (Nmid eR) w
  let natPsi : Widx → Matrix (Fin Nnat → Fin q) (Fin Nnat → Fin q) ℂ :=
    fun w ↦ (Psi w).submatrix
      (fun σ : Fin Nnat → Fin q ↦ σ ∘ eE.symm)
      (fun σ : Fin Nnat → Fin q ↦ σ ∘ eE.symm)
  have hd (w : Widx) : d w ≤ k := w.2.2.2
  have hword (w : Widx) :
      ∃ (t : Fin (nw w) → Fin (d w + 1))
        (Vw : Fin (nw w) → Matrix (Fin Nnat → Fin q) (Fin Nnat → Fin q) ℂ),
        (∀ r, IsOpenMPS Nnat (q * q) ((B ^ (t r).val) ^ 2) (fun v ↦ Vw r
          (fun x ↦ ((finProdFinEquiv (m := q) (n := q)).symm (v x)).1)
          (fun x ↦ ((finProdFinEquiv (m := q) (n := q)).symm (v x)).2))) ∧
        natPsi w = ∑ r, Vw r := by
    obtain ⟨dw, hdw, _hdk, t, Vw, hVw, hsum⟩ :=
      exists_actual_selected_middle_word_mpo_family
        (L := L) (a := a) (b := b) (ell := ell) (q := q) (B := B)
        (rU := q * q) (rV := q * q) hab hb p s Acore C0 (z (Sum.inr 1))
        Kz (Nmid eL) (Nmid eR) hKz hNL hNR k i j w
    have hdw' : dw = d w := hdw
    subst dw
    refine ⟨t, Vw, hVw, ?_⟩
    change (twoMarkerMiddleFactor A (Nmid eL) (Nmid eR) w).submatrix
      (fun σ : Fin Nnat → Fin q ↦ σ ∘ eE.symm)
      (fun σ : Fin Nnat → Fin q ↦ σ ∘ eE.symm) = ∑ r, Vw r
    rw [hA]
    exact hsum
  choose tWord VWord hVWord hPsiWord using hword
  let I := Σ w : Widx, Fin (nw w)
  let n := Fintype.card I
  let enum : I ≃ Fin n := Fintype.equivFin I
  let V : Fin n → Matrix (Fin Nnat → Fin q) (Fin Nnat → Fin q) ℂ :=
    fun r ↦ VWord (enum.symm r).1 (enum.symm r).2
  let deg : Fin n → Fin (k + 1) := fun r ↦
    ⟨(tWord (enum.symm r).1 (enum.symm r).2).val, by
      have ht := (tWord (enum.symm r).1 (enum.symm r).2).isLt
      have hlen := hd (enum.symm r).1
      omega⟩
  have hcount : n ≤ Fintype.card Widx * (k + 1) * RetDim ^ 2 := by
    calc
      n = ∑ w : Widx, (d w + 1) * RetDim ^ 2 := by
        simp only [n, I, Fintype.card_sigma, Fintype.card_fin, nw]
      _ ≤ ∑ _w : Widx, (k + 1) * RetDim ^ 2 := by
        apply Finset.sum_le_sum
        intro w _hw
        exact Nat.mul_le_mul_right (RetDim ^ 2) (Nat.add_le_add_right (hd w) 1)
      _ = Fintype.card Widx * (k + 1) * RetDim ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.cast_id, Nat.mul_assoc]
  have hV : ∀ r, IsOpenMPS Nnat (q * q) ((B ^ (deg r).val) ^ 2) (fun w ↦ V r
      (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).1)
      (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w v)).2)) := by
    intro r
    exact hVWord (enum.symm r).1 (enum.symm r).2
  let S : Submodule ℂ (Matrix (Fin Nnat → Fin q) (Fin Nnat → Fin q) ℂ) :=
    Submodule.span ℂ (Set.range V)
  have hgenerator (w : Widx) (r : Fin (nw w)) : VWord w r ∈ S := by
    apply Submodule.subset_span
    refine ⟨enum ⟨w, r⟩, ?_⟩
    exact congrArg (fun u : I ↦ VWord u.1 u.2)
      (enum.symm_apply_apply ⟨w, r⟩)
  have hPsiSpan (w : Widx) : natPsi w ∈ S := by
    rw [hPsiWord w]
    exact S.sum_mem (fun r _hr ↦ hgenerator w r)
  refine ⟨n, deg, V, hcount, hV, ?_⟩
  intro PL PR hPL hPR F Dphys cPoly
  obtain ⟨Bword, hBword⟩ := hphysical PL PR hPL hPR cPoly
  let Ext := (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)
  let readMiddle : Ext × (Fin Nnat → Fin q) → Ext × (E → Fin q) :=
    fun x ↦ (x.1, x.2 ∘ eE.symm)
  let Xnat : Matrix (Ext × (Fin Nnat → Fin q)) (Ext × (Fin Nnat → Fin q)) ℂ :=
    ((∑ r : Fin (k + 1),
      cPoly r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j).reindex
        (g.trans e) (g.trans e)).submatrix readMiddle readMiddle
  have hXnat : Xnat = ∑ w : Widx, Bword w ⊗ₖ natPsi w := by
    change ((∑ r : Fin (k + 1),
      cPoly r • twoMarkerCoefficient Dphys (WL p) (WR s) r.val i j).reindex
        (g.trans e) (g.trans e)).submatrix readMiddle readMiddle = _
    rw [hBword]
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
      readMiddle, natPsi, Psi, Nmid]
    rfl
  have hblocks (x y : Ext) : Matrix.operatorBlock Xnat x y ∈ S := by
    rw [hXnat, operatorBlock_sum]
    simp_rw [operatorBlock_kronecker_eq_smul]
    exact S.sum_mem (fun w _hw ↦ S.smul_mem (Bword w x y) (hPsiSpan w))
  exact Matrix.exists_left_factors_of_operatorBlock_mem_span Xnat V hblocks

/-- The common-family count has a single explicit polynomial base under the
positive local-dimension and degree assumptions. This is a coarse supporting
count for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333; it does
not assert the source's sharp bond or algorithmic estimate. -/
theorem actual_common_physical_mpo_card_le
    {L a b ell q k i j n : ℕ}
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (p s : Fin (2 * ell)) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hcount : n ≤ Fintype.card (TwoMarkerMiddleIndex k i j (q * q) (q * q)) *
      (k + 1) * Fintype.card (MPOTensor.actualAffineRetainedConfig
        ((b + s.val + 1) - (a + p.val + 1))
        (b - (a + 2 * ell + 1)) q
        ((a + 2 * ell + 1) - (a + p.val + 1))) ^ 2) :
    n ≤ (q * (k + 1)) ^ (8 * ell + 2 * (i + j) + 2) := by
  classical
  let E := interval L (a + p.val + 1) (b + s.val + 1)
  let Z := interval L (a + 2 * ell + 1) b
  let C : Finset E := Finset.univ.filter (fun x : E ↦ x.val ∉ Z)
  let Nnat := (b + s.val + 1) - (a + p.val + 1)
  let aNat := (a + 2 * ell + 1) - (a + p.val + 1)
  let Lnat := b - (a + 2 * ell + 1)
  let R := Fintype.card (MPOTensor.actualAffineRetainedConfig Nnat Lnat q aNat)
  let Widx := TwoMarkerMiddleIndex k i j (q * q) (q * q)
  let m := i + j
  let v := k + 1
  have hp := p.isLt
  have hs := s.isLt
  let eNat := intervalComplementEquiv (T := L)
    (c := a + p.val + 1) (d := b + s.val + 1)
    (u := a + 2 * ell + 1) (v := b) (by omega) (by omega) (by omega)
  let eC : C ≃ ↥(E \ Z) :=
    { toFun := fun x ↦ ⟨x.val.val, Finset.mem_sdiff.mpr
        ⟨x.val.property, (Finset.mem_filter.mp x.property).2⟩⟩
      invFun := fun x ↦ ⟨⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp x.property).2⟩⟩
      left_inv := fun _ ↦ by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun _ ↦ by apply Subtype.ext; rfl }
  have hsite : Fintype.card
      {r : Fin Nnat // ¬(aNat ≤ r.val ∧ r.val < aNat + Lnat)} = (E \ Z).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (eNat.trans eC)
  have hR : R = q ^ (E \ Z).card := by
    change Fintype.card
      ({r : Fin Nnat // ¬(aNat ≤ r.val ∧ r.val < aNat + Lnat)} → Fin q) = _
    rw [Fintype.card_fun, Fintype.card_fin, hsite]
  have hRle : R ≤ q ^ (4 * ell) := by
    rw [hR]
    exact pow_le_pow_right' hq (card_selected_middle_sdiff_strict_core_le hab p s)
  have hR2 : R ^ 2 ≤ q ^ (8 * ell) := by
    calc
      R ^ 2 ≤ (q ^ (4 * ell)) ^ 2 := Nat.pow_le_pow_left hRle 2
      _ = q ^ (8 * ell) := by
        rw [← pow_mul, show 4 * ell * 2 = 8 * ell by omega]
  have hwords : Fintype.card Widx ≤ 2 ^ m * q ^ (2 * m) * v ^ (m + 1) := by
    simpa only [pow_two] using card_twoMarkerMiddleIndex_square_le k i j q
  have htwo : 2 ^ m ≤ v ^ m := Nat.pow_le_pow_left (by dsimp only [v]; omega) m
  have hwords' : Fintype.card Widx ≤ q ^ (2 * m) * v ^ (2 * m + 1) := by
    calc
      Fintype.card Widx ≤ 2 ^ m * q ^ (2 * m) * v ^ (m + 1) := hwords
      _ ≤ v ^ m * q ^ (2 * m) * v ^ (m + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ htwo)
      _ = q ^ (2 * m) * (v ^ m * v ^ (m + 1)) := by ac_rfl
      _ = q ^ (2 * m) * v ^ (2 * m + 1) := by
        rw [← pow_add, show m + (m + 1) = 2 * m + 1 by omega]
  have hfactored : Fintype.card Widx * v * R ^ 2 ≤
      q ^ (8 * ell + 2 * m) * v ^ (2 * m + 2) := by
    calc
      Fintype.card Widx * v * R ^ 2 ≤
          (q ^ (2 * m) * v ^ (2 * m + 1)) * v * q ^ (8 * ell) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right v hwords') hR2
      _ = (q ^ (8 * ell) * q ^ (2 * m)) *
          (v ^ (2 * m + 1) * v ^ 1) := by rw [pow_one]; ac_rfl
      _ = q ^ (8 * ell + 2 * m) * v ^ ((2 * m + 1) + 1) := by
        rw [← pow_add, ← pow_add]
      _ = q ^ (8 * ell + 2 * m) * v ^ (2 * m + 2) := by
        rw [show (2 * m + 1) + 1 = 2 * m + 2 by omega]
  have hqexp : q ^ (8 * ell + 2 * m) ≤ q ^ (8 * ell + 2 * m + 2) :=
    pow_le_pow_right' hq (by omega)
  have hvexp : v ^ (2 * m + 2) ≤ v ^ (8 * ell + 2 * m + 2) :=
    pow_le_pow_right' (by dsimp only [v]; omega) (by omega)
  change n ≤ Fintype.card Widx * v * R ^ 2 at hcount
  calc
    n ≤ q ^ (8 * ell + 2 * m) * v ^ (2 * m + 2) := hcount.trans hfactored
    _ ≤ q ^ (8 * ell + 2 * m + 2) * v ^ (8 * ell + 2 * m + 2) :=
      Nat.mul_le_mul hqexp hvexp
    _ = (q * v) ^ (8 * ell + 2 * m + 2) := (Nat.mul_pow _ _ _).symm

/-- A coarse low-frequency consequence of the fixed-family cardinal estimate.
This supports ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333,
without asserting its sharp bond, algorithmic, or full-family conclusions. -/
theorem actual_common_physical_mpo_card_low_frequency_le
    {q k ell i j n : ℕ}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (hi : i ≤ k / (2 * ell)) (hj : j ≤ k / (2 * ell))
    (hcount : n ≤ (q * (k + 1)) ^ (8 * ell + 2 * (i + j) + 2)) :
    n ≤ (q * k) ^ (20 * ell + 4 * (k / ell)) := by
  have hsum : i + j ≤ 2 * (k / (2 * ell)) := by omega
  have hmul : (i + j) * ell ≤ k := by
    calc
      (i + j) * ell ≤ (2 * (k / (2 * ell))) * ell :=
        Nat.mul_le_mul_right ell hsum
      _ = (k / (2 * ell)) * (2 * ell) := by ac_rfl
      _ ≤ k := Nat.div_mul_le_self k (2 * ell)
  have hfreq : i + j ≤ k / ell :=
    (Nat.le_div_iff_mul_le (by omega : 0 < ell)).mpr hmul
  have hexp : 8 * ell + 2 * (i + j) + 2 ≤ 10 * ell + 2 * (k / ell) := by
    omega
  have hqk : 2 ≤ q * k := by
    have h := Nat.mul_le_mul hq hk
    simpa only [Nat.mul_one] using h
  have hbase : q * (k + 1) ≤ (q * k) ^ 2 := by
    calc
      q * (k + 1) ≤ q * (2 * k) := Nat.mul_le_mul_left q (by omega)
      _ = 2 * (q * k) := by ac_rfl
      _ ≤ (q * k) * (q * k) := Nat.mul_le_mul_right (q * k) hqk
      _ = (q * k) ^ 2 := (pow_two _).symm
  calc
    n ≤ (q * (k + 1)) ^ (8 * ell + 2 * (i + j) + 2) := hcount
    _ ≤ ((q * k) ^ 2) ^ (8 * ell + 2 * (i + j) + 2) :=
      Nat.pow_le_pow_left hbase _
    _ = (q * k) ^ (2 * (8 * ell + 2 * (i + j) + 2)) := (pow_mul _ _ _).symm
    _ ≤ (q * k) ^ (20 * ell + 4 * (k / ell)) :=
      pow_le_pow_right' (by omega) (by omega)

end TNLean.MPS.AreaLaw

end
