def Nat.zero? : Nat → Bool
| .zero => true
| _ => false

theorem Nat.pred_succ_id : Nat.pred ∘ Nat.succ = id := by
  apply funext
  exact Nat.pred_succ

infix:100 " ⬝ " => Trans.trans

theorem congrArg2
  {α₀ : Sort u₀} {α₁ : Sort u₁} {β : Sort v} {a₀ a₀' : α₀} {a₁ a₁' : α₁}
  (f : α₀ → α₁ → β) (h₀ : Eq a₀ a₀') (h₁ : Eq a₁ a₁') : Eq (f a₀ a₁) (f a₀' a₁')
  := h₀ ▸ h₁ ▸ rfl

theorem congrArg3
  {α₀ : Sort u₀} {α₁ : Sort u₁} {α₂ : Sort u₂} {β : Sort v} {a₀ a₀' : α₀} {a₁ a₁' : α₁} {a₂ a₂' : α₂}
  (f : α₀ → α₁ → α₂ → β) (h₀ : Eq a₀ a₀') (h₁ : Eq a₁ a₁') (h₂ : Eq a₂ a₂') : Eq (f a₀ a₁ a₂) (f a₀' a₁' a₂')
  := h₀ ▸ h₁ ▸ h₂ ▸ rfl
