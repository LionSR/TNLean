/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.PID
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace

/-!
# Trace additivity over an invariant submodule

This file proves that the trace of an endomorphism of a finite-dimensional vector space splits,
over any submodule invariant under the endomorphism, as the sum of the trace of its restriction
to the submodule and the trace of the endomorphism induced on the quotient.

## Main results

* `LinearMap.trace_eq_trace_restrict_add_trace_quotient`: for `p` a submodule of a
  finite-dimensional `K`-vector space `V` and `f : V →ₗ[K] V` with `f x ∈ p` whenever
  `x ∈ p`,
  `trace K V f = trace K p (f.restrict hf) + trace K (V ⧸ p) (p.mapQ p f hf')`.
-/

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The trace of an endomorphism `f` of a finite-dimensional vector space splits, over any
`f`-invariant submodule `p`, as the trace of the restriction of `f` to `p` plus the trace of the
endomorphism of `V ⧸ p` induced by `f`. -/
theorem trace_eq_trace_restrict_add_trace_quotient (p : Submodule K V) (f : V →ₗ[K] V)
    (hf : ∀ x ∈ p, f x ∈ p) :
    trace K V f =
      trace K p (f.restrict hf) + trace K (V ⧸ p) (p.mapQ p f fun x hx => hf x hx) := by
  classical
  obtain ⟨q, hpq⟩ := p.exists_isCompl
  set P : V →ₗ[K] V := p.projection q hpq with hPdef
  have hPmem : ∀ x, P x ∈ p := fun x => Submodule.projection_apply_mem hpq x
  have hPfix : ∀ x ∈ p, P x = x := fun x hx => Submodule.projection_apply_of_mem_left hpq hx
  -- `f ∘ P` has range in `p`, and its restriction to `p` agrees with `f`'s restriction.
  have hcompmem : ∀ x, (f.comp P) x ∈ p := fun x => hf (P x) (hPmem x)
  have hrestr_eq : (f.comp P).restrict (fun x hx => hcompmem x) = f.restrict hf := by
    ext ⟨x, hx⟩
    simp [LinearMap.restrict_apply, hPfix x hx]
  have hstep1 : trace K V (f.comp P) = trace K p (f.restrict hf) := by
    rw [← LinearMap.trace_restrict_eq_of_forall_mem p (f.comp P) hcompmem, hrestr_eq]
  -- A section `σ : V ⧸ p → V` of the quotient map along the complement `q`.
  set σ : V ⧸ p →ₗ[K] V :=
    q.subtype.comp (p.quotientEquivOfIsCompl q hpq).toLinearMap with hσdef
  have hmkQσ : p.mkQ.comp σ = LinearMap.id := by
    ext x
    simp [σ, Submodule.Quotient.eq, sub_mem_comm_iff, Submodule.sub_projection_mem]
  have hσmkQ : σ.comp p.mkQ = LinearMap.id - P := by
    have h1 : (p.quotientEquivOfIsCompl q hpq).toLinearMap.comp p.mkQ
        = q.projectionOnto p hpq.symm := by
      rw [Submodule.toLinearMap_quotientEquivOfIsCompl, Submodule.liftQ_mkQ]
    calc σ.comp p.mkQ
        = q.subtype.comp ((p.quotientEquivOfIsCompl q hpq).toLinearMap.comp p.mkQ) := by
          rw [hσdef, LinearMap.comp_assoc]
      _ = q.subtype.comp (q.projectionOnto p hpq.symm) := by rw [h1]
      _ = q.projection p hpq.symm := rfl
      _ = LinearMap.id - P := Submodule.projection_eq_id_sub_projection hpq
  -- `f ∘ (1 - P)` and `mapQ f` are related by the cyclicity of the trace along `σ` and `mkQ`.
  have hstep2 : trace K V (f.comp (LinearMap.id - P)) =
      trace K (V ⧸ p) (p.mapQ p f fun x hx => hf x hx) := by
    have hcomp : f.comp (LinearMap.id - P) = f.comp σ ∘ₗ p.mkQ := by
      rw [← hσmkQ]
      exact (LinearMap.comp_assoc p.mkQ σ f).symm
    have hcyc : trace K V (f.comp σ ∘ₗ p.mkQ) =
        trace K (V ⧸ p) (p.mkQ ∘ₗ f.comp σ) := trace_comp_comm' p.mkQ (f.comp σ)
    have hmapq : p.mkQ.comp f = (p.mapQ p f fun x hx => hf x hx).comp p.mkQ := by
      ext x
      simp
    rw [hcomp, hcyc, ← LinearMap.comp_assoc, hmapq, LinearMap.comp_assoc, hmkQσ,
      LinearMap.comp_id]
  have hid : P + (LinearMap.id - P) = LinearMap.id := by abel
  calc trace K V f = trace K V (f.comp LinearMap.id) := by rw [LinearMap.comp_id]
    _ = trace K V (f.comp (P + (LinearMap.id - P))) := by rw [hid]
    _ = trace K V (f.comp P) + trace K V (f.comp (LinearMap.id - P)) := by
        rw [LinearMap.comp_add, map_add]
    _ = trace K p (f.restrict hf) + trace K (V ⧸ p) (p.mapQ p f fun x hx => hf x hx) := by
        rw [hstep1, hstep2]

end LinearMap
