def Nat.zero? : Nat → Bool
| .zero => true
| _ => false

theorem Nat.pred_succ_id : Nat.pred ∘ Nat.succ = id := by
  apply funext
  exact Nat.pred_succ
