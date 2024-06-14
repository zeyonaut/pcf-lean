/-
This file contains some basic miscellanea used throughout the formalization.
-/

/-
We use the symbol `⬝` (\cdot) to concatenate two proofs of transitive relations.
-/

infix:100 " ⬝ " => Trans.trans

/-
`congrArg` (also known by `ap`, or 'action on paths') applies a function to an
identification of arguments to yield an identification of results. We define
equivalent operations for functions of two and three arguments for convenience.
-/

theorem congrArg2
  {α₀ : Sort u₀} {α₁ : Sort u₁} {β : Sort v} {a₀ a₀' : α₀} {a₁ a₁' : α₁}
  (f : α₀ → α₁ → β) (h₀ : Eq a₀ a₀') (h₁ : Eq a₁ a₁') : Eq (f a₀ a₁) (f a₀' a₁')
  := h₀ ▸ h₁ ▸ rfl

theorem congrArg3
  {α₀ : Sort u₀} {α₁ : Sort u₁} {α₂ : Sort u₂} {β : Sort v} {a₀ a₀' : α₀} {a₁ a₁' : α₁} {a₂ a₂' : α₂}
  (f : α₀ → α₁ → α₂ → β) (h₀ : Eq a₀ a₀') (h₁ : Eq a₁ a₁') (h₂ : Eq a₂ a₂') : Eq (f a₀ a₁ a₂) (f a₀' a₁' a₂')
  := h₀ ▸ h₁ ▸ h₂ ▸ rfl

/-
Lean favors classical mathematics, where if-and-only-if is represented by a proposition.
However, even though this formalization is classical, it's useful to have a type of pairs
of functions in both directions (since propositions can't be eliminated into types).
-/

structure LogicallyEquivalent (a : Sort i) (b : Sort j) : Sort max 1 i j where
  intro ::
  mp : a → b
  mpr : b → a

infix:20 "⇔" => LogicallyEquivalent

/-
We define a function which tests whether a natural number is zero.
-/

def Nat.zero? : Nat → Bool
| .zero => true
| _ => false

@[inline] def Function.id {α : Sort u} (a : α) : α := a
