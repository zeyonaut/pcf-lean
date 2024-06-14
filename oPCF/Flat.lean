import «PCF».Domain

/-
Any set can be lifted into a 'flat' domain, which is essentially its discrete order but
freely completed with an initial element. Classically, this is just `Maybe`/`Option`.
-/

-- Definition 12 (Flat domain)
inductive Flat (α : Type) : Type where
  | none : Flat α
  | some : α → Flat α

theorem Flat.invert {x : Flat α} (p : x ≠ .none) : ∃ k, x = .some k :=
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

theorem Flat.chain_some {c : Chain (Flat _)} {a b : α}
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

theorem Flat.sup_some {c : Chain _} {a : α} : (∃ k, c.act k = .some a) ↔ (flat_sup c = .some a) := by
  constructor
  case mp =>
    intro h;
    have p : ∃ a n, c.act n = .some a := ⟨a, h⟩
    rw [Flat.chain_some h p.choose_spec]
    exact dif_pos p
  case mpr =>
    intro h;
    if p : ∃ a n, c.act n = .some a
    then
      have q : flat_sup c = .some _ := dif_pos p
      rw [← h, q]
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
    rw [Flat.sup_some.mp ⟨_, v⟩]
    exact v
  is_least := by
    intro c d h
    if p : flat_sup c = .none
    then rw [p]; intro q; exfalso; exact q rfl
    else
      obtain ⟨a, k⟩ := Flat.invert p
      rw [k]
      have u : ∃ k, c.act k = .some a := Flat.sup_some.mpr k
      rw [← u.choose_spec]
      exact h

/-
The following lemmas produce identifications from orderings on flat domains.
-/

theorem Flat.leq_none {a : Flat α} : a ⊑ .none → a = .none := by
  intro a_bf_n
  by_cases a = none
  case pos => assumption
  case neg h =>
    have ⟨n, a_eq_sn⟩ := Flat.invert h
    exact a_bf_n (by intro a_eq_n; injection a_eq_n.symm ⬝ a_eq_sn)

theorem Flat.some_leq {a : α} : (Flat.some a) ⊑ b → Flat.some a = b := by
  intro p
  have x := p (by {intro q; injection q})
  cases b with
  | none => injection x
  | some b => exact x

theorem Flat.under_eq {x : Flat α} : x ⊑ .some a → x ⊑ .some b → a ≠ b → x = .none := by
  intro under_a under_b a_neq_b
  by_cases x = none
  case pos => assumption
  case neg h => exfalso; exact a_neq_b (by injection (under_a h).symm ⬝ (under_b h))

/-
All chains in flat domains are eventually constant (and so monotone functions
between flat domains are continuous).
-/

noncomputable instance (α) [DecidableEq α] : TrivialDomain (Flat α) where
  eventually_const := fun c ↦ by {
    by_cases ⨆ c = .none
    case pos h => exact ⟨0,
      by {
        intro n _
        have cn_none := Domain.is_bound c n
        rw [h] at cn_none
        exact cn_none ⬝ Domain.is_bot
      }
    ⟩
    case neg h =>
      have ⟨a, supc_sa⟩ := Flat.invert h
      have ⟨N, cN_sa⟩ := Flat.sup_some.mpr supc_sa
      exact ⟨
        N,
        by {
          intro _ N_n _
          rw [(c • N_n) (by rw [cN_sa]; intro p; injection p)]
        }
      ⟩
  }

/-
Functions on underlying sets can be lifted into its flat domains, and these liftings
are automatically monotone (and hence continuous).
-/

-- Proposition 7 (Flat domain lifting)
def lift_flat (f : α → β) : Flat α → Flat β
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

def Cont.flat (f : α → β) : (Cont (Flat α) (Flat β)) := (Mono.flat f).promote_trivial

theorem Cont.flat_comp (f : β → γ) (g : α → β) : Cont.flat (f ∘ g) = Cont.flat f ∘' Cont.flat g := by
  apply Cont.ext ∘ funext
  intro a
  cases a with
  | none | some => rfl

theorem Cont.flat_id : Cont.flat (Function.id : α → α) = Cont.id := by
  apply Cont.ext ∘ funext
  intro a
  cases a with
  | none | some => rfl

/-
The flat-boolean conditional function is monotone and continuous.
-/

def cond' [Order α] [Domain α] : Mono (Flat Bool) (Cont (α × α) α) := ⟨
  fun b ↦ (
    match b with
    | .none => Cont.const ⊥
    | .some true => Cont.fst
    | .some false => Cont.snd
  ),
  by {
    intro a b a_b
    cases a with
    | none => exact Domain.is_bot
    | some a =>
      rw [a_b (by simp)]
      exact ⋆
  }
⟩

def Cont.cond [Order α] [Domain α] : Cont (Flat Bool) (Cont (α × α) α) := ⟨
  cond',
  by {
    intro c p
    by_cases ⨆ c = .none
    case pos h =>
      rw [h]
      exact Domain.is_bot
    case neg h =>
      obtain ⟨s, j₀⟩ := Flat.invert h
      obtain ⟨n, j₁⟩ := Flat.sup_some.mpr j₀
      calc ((cond' (⨆ c)).fn p)
        _ = ((cond' (c n)).fn p) := by rw [j₀, j₁]
        _ ⊑ ((⨆ (cond' ∘ c)).fn p) := (Domain.is_bound (cond' ∘ c) n) p
  }
⟩

/-
The partially-defined predecessor function on the flat naturals is monotone (and thus continuous).
-/

def Nat.partial_pred : Flat Nat → Flat Nat :=
  fun n ↦ match n with
  | .some (.succ n) => .some n
  | _ => .none

def Mono.pred : Mono (Flat Nat) (Flat Nat) := ⟨
    Nat.partial_pred,
    by {
      intro a b a_b
      cases a with
      | none => exact Domain.is_bot
      | some => rw [a_b Flat.noConfusion]; exact ⋆
    }
  ⟩

def Cont.pred : Cont (Flat Nat) (Flat Nat) := Mono.pred.promote_trivial

theorem Nat.partial_pred_converse {a : Flat Nat} (p : partial_pred a ≠ .none) : (a ≠ .none) := by
  intro q
  rw [q] at p
  exact p rfl

theorem Cont.pred_flat_succ_eq_id : Cont.pred ∘' Cont.flat (Nat.succ) = Cont.id := by
  apply Cont.ext; funext n; cases n with | _ => rfl
