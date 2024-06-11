import «oPCF».Domain

-- Definition 12 (Flat domain)
inductive Flat (α : Type) : Type where
  | none : Flat α
  | some : α → Flat α

def Flat.invert {x : Flat α} (p : x ≠ .none) : ∃ k, x = .some k :=
  match x with
  | .none => (p rfl).elim
  | .some x => ⟨x, rfl⟩

instance (a : Flat α) : Decidable (∃ k, a = .some k) :=
  match a with
  | .none => isFalse (fun p ↦ p.elim (fun _ y ↦ by injection y))
  | .some a => isTrue (.intro a rfl)

instance [DecidableEq α] : DecidableEq (Flat α) := fun a b ↦
  match a with
  | .none => match b with
    | .none => isTrue rfl
    | .some _ => isFalse Flat.noConfusion
  | .some a => match b with
    | .none => isFalse Flat.noConfusion
    | .some b => if p : a = b then isTrue (by rw [p]) else isFalse (fun q ↦ p (by injection q))

instance [DecidableEq α] : Order (Flat α) where
  R := fun x y ↦ (x ≠ .none) → x = y
  refl := fun _ ↦ rfl
  trans {x y z} p q :=
    if h : x = .none
    then fun a ↦ (a h).elim
    else fun a ↦ by rw [p h]; rw [p h] at h; rw [q h]
  anti {x y} p q :=
    if i : x = .none
    then if j : y = .none then by rw [i, j] else by rw [q j]
    else by rw [p i]

open Classical

noncomputable def flat_sup (c : Chain (Flat α)) : Flat α :=
  if p : ∃ a n, c.act n = .some a then .some p.choose else .none

theorem flat_chain_some {c : Chain (Flat _)} {a b : α}
  (p : ∃ k, c.act k = .some a) (q : ∃ k, c.act k = .some b) : a = b := by
  cases p
  case intro i si =>
  cases q
  case intro j sj =>
  have h : i ≤ j ∨ ¬ i ≤ j := Classical.em _
  cases h with
  | inl p =>
    have h₀ : c.act i ⊑ c.act j := c.act' p
    rw [si, sj] at h₀
    injection h₀ (by simp)
  | inr p =>
    apply Eq.symm
    have p : j ≤ i := Nat.le_of_lt (Nat.gt_of_not_le p)
    have h₀ : c.act j ⊑ c.act i := c.act' p
    rw [si, sj] at h₀
    injection h₀ (by simp)

theorem flat_sup_some {c : Chain _} {a : α} : (∃ k, c.act k = .some a) ↔ (flat_sup c = .some a) := by
  constructor
  case mp =>
    intro h;
    have p : ∃ a n, c.act n = .some a := ⟨a, h⟩
    rw [flat_chain_some h p.choose_spec]
    exact dif_pos p
  case mpr =>
    intro h;
    if p : ∃ a n, c.act n = .some a
    then
      have q : flat_sup c = .some _ := dif_pos p
      rw [←h, q]
      exact p.choose_spec
    else
      have q : flat_sup c = .none := dif_neg p
      rw [q] at h
      exact Flat.noConfusion h

noncomputable instance : Domain (Flat α) where
  bot := .none
  sup := flat_sup
  is_bot := by
    intro _ p;
    exfalso
    exact p rfl
  is_bound := by
    intro _ _ h
    obtain ⟨_, v⟩ := Flat.invert h
    rw [flat_sup_some.mp ⟨_, v⟩]
    exact v
  is_least := by
    intro c d h
    if p : flat_sup c = .none
    then rw [p]; intro q; exfalso; exact q rfl
    else
      obtain ⟨a, k⟩ := Flat.invert p
      rw [k]
      have u : ∃ k, c.act k = .some a := flat_sup_some.mpr k
      rw [←u.choose_spec]
      exact h

-- Proposition 7 (Flat domain lifting)
private def lift_flat (f : α → β) : Flat α → Flat β
| .none => .none
| .some x => .some (f x)

theorem flat_lift_converse {f : α → β} {a : Flat α} (p : lift_flat f a ≠ .none) : (a ≠ .none) := by
  intro q
  rw [q] at p
  exact p rfl

def Mono.flat (f : α → β) : (Mono (Flat α) (Flat β)) := ⟨
    lift_flat f,
    by {
      intro a b a_b
      cases a with
      | none => exact Domain.is_bot
      | some =>
        rw [a_b Flat.noConfusion]
        exact ⋆
    }
  ⟩

def Cont.flat (f : α → β) : (Cont (Flat α) (Flat β)) := ⟨
    Mono.flat f,
    by {
      intro c h
      have ⟨a, p₀⟩ := Flat.invert (flat_lift_converse h)
      rw [p₀]
      have ⟨n, p₁⟩ := flat_sup_some.mpr p₀
      have p₂ : ⨆ (Mono.flat f ∘ c) = .some (f a) := flat_sup_some.mp ⟨n, by
        calc lift_flat f (c n)
          _ = lift_flat f (Flat.some a) := congrArg _ p₁
          _ = Flat.some (f a)           := rfl
      ⟩
      exact p₂.symm
    }
  ⟩

theorem Cont.flat_comp (f : β → γ) (g : α → β) : Cont.flat (f ∘ g) = Cont.flat f ∘' Cont.flat g := by
  apply Cont.ext ∘ funext
  intro a
  cases a with
  | none | some => rfl

theorem Cont.flat_id : Cont.flat (id) = (Cont.id' : Cont (Flat α) (Flat α) ) := by
  apply Cont.ext ∘ funext
  intro a
  cases a with
  | none | some => rfl
