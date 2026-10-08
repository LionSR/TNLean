from pathlib import Path
p=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-physical/TNLean/PEPS/Approximation/PartyPartitionAppend.lean');t=p.read_text()
a=t.index(' := by\n',t.index('private theorem appendPartitionIso_cons_left'));b=t.index('\nprivate theorem appendPartitionIso_cons_right',a)
t=t[:a]+''' := by
  let f := (isoL (appendPartitionIso (r :: a₁) a₂ b₁ b₂) ∘L
    (isoL (TensorProduct.assocIsometry ℂ r.space (Mem a₁) (Mem a₂)).symm ∘L
      appendLeft u).rTensor (Mem b₁ ⊗[ℂ] Mem b₂)).toLinearMap
  let g := (isoL
    (TensorProduct.assocIsometry ℂ r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))).symm ∘L
      appendLeft u ∘L isoL (appendPartitionIso a₁ a₂ b₁ b₂)).toLinearMap
  have h : f = g := TensorProduct.ext_fourfold' fun x₁ x₂ y₁ y₂ ↦ by
    change appendPartitionIso (r :: a₁) a₂ b₁ b₂
      (((TensorProduct.assocIsometry ℂ r.space (Mem a₁) (Mem a₂)).symm
        (u ⊗ₜ[ℂ] (x₁ ⊗ₜ[ℂ] x₂))) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)) = _
    simp only [TensorProduct.assocIsometry_symm_apply, TensorProduct.assoc_symm_tmul]
    rw [appendPartitionIso_tmul (r :: a₁) a₂ b₁ b₂ (u ⊗ₜ[ℂ] x₁) x₂ y₁ y₂]
    change _ = (TensorProduct.assocIsometry ℂ r.space
      (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))).symm
        (u ⊗ₜ[ℂ] appendPartitionIso a₁ a₂ b₁ b₂
          ((x₁ ⊗ₜ[ℂ] x₂) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)))
    rw [appendPartitionIso_tmul]
    rfl
  exact LinearMap.congr_fun h (x ⊗ₜ[ℂ] y)
''' +t[b:]
a=t.index(' := by\n',t.index('private theorem appendPartitionIso_cons_right'));b=t.index('\nprivate theorem appendPartitionIso_heq',a)
t=t[:a]+''' := by
  let f := (isoL (appendPartitionIso a₁ (r :: a₂) b₁ b₂) ∘L
    (isoL (leftCommIso r.space (Mem a₁) (Mem a₂)) ∘L
      appendLeft u).rTensor (Mem b₁ ⊗[ℂ] Mem b₂)).toLinearMap
  let g := (isoL (leftCommIso r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))) ∘L
    appendLeft u ∘L isoL (appendPartitionIso a₁ a₂ b₁ b₂)).toLinearMap
  have h : f = g := TensorProduct.ext_fourfold' fun x₁ x₂ y₁ y₂ ↦ by
    change appendPartitionIso a₁ (r :: a₂) b₁ b₂
      (leftCommIso r.space (Mem a₁) (Mem a₂)
        (u ⊗ₜ[ℂ] (x₁ ⊗ₜ[ℂ] x₂)) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)) = _
    simp only [leftCommIso_tmul]
    rw [appendPartitionIso_tmul a₁ (r :: a₂) b₁ b₂ x₁ (u ⊗ₜ[ℂ] x₂) y₁ y₂]
    change _ = leftCommIso r.space (Mem (a₁ ++ b₁)) (Mem (a₂ ++ b₂))
      (u ⊗ₜ[ℂ] appendPartitionIso a₁ a₂ b₁ b₂
        ((x₁ ⊗ₜ[ℂ] x₂) ⊗ₜ[ℂ] (y₁ ⊗ₜ[ℂ] y₂)))
    rw [appendPartitionIso_tmul]
    rfl
  exact LinearMap.congr_fun h (x ⊗ₜ[ℂ] y)
''' +t[b:]
Path('/tmp/PartyPartitionAppendRefactor.lean').write_text(t)
