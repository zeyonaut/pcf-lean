import «oPCF».Substitution
import «oPCF».Flat

structure DomainType : Type (i + 1) :=
  carrier : Type i
  order : Order carrier
  domain : Domain carrier

instance : Coe DomainType Type where
  coe D := D.carrier

instance (τ : DomainType) : Order (τ) := τ.order
instance (τ : DomainType) : Domain (τ) := τ.domain

-- Definition 22.
noncomputable def Sem : Ty → DomainType
  | .bool => ⟨Flat Bool, _, inferInstance⟩
  | .nat => ⟨Flat Nat, _, inferInstance⟩
  | .pow T₀ T₁ => by
    obtain ⟨T₀, O₀, D₀⟩ := Sem T₀
    obtain ⟨T₁, O₁, D₁⟩ := Sem T₁
    exact ⟨Cont T₀ T₁,  _ , inferInstance⟩

notation:max "⟦" τ " type⟧" => Sem τ

instance (τ υ : Ty): CoeFun (⟦τ ⇒ υ type⟧.carrier) (fun _ => ⟦τ type⟧.carrier → ⟦υ type⟧.carrier) where
  coe f := f.fn.act

-- Definition 23.
def Ev (Γ : Cx) : Type := ∀ τ, Var Γ τ → ↑⟦τ type⟧

notation:max "⟦" Γ " cx⟧" => Ev Γ

def Ev.nil : ⟦Cx.nil cx⟧ := by
  intro _ x
  cases x

def Ev.push {Γ : Cx} (ρ : ⟦Γ cx⟧) {τ : Ty} (d : ↑⟦τ type⟧) : ⟦Γ ∷ τ cx⟧ :=
  fun {τ} x ↦ match x with
  | .z => d
  | .s τ x => ρ τ x

noncomputable instance (Γ : Cx) : Order (⟦Γ cx⟧) where
  R := fun a b ↦ ∀ τ (x : Var Γ τ), a τ x ⊑ b τ x
  refl := fun _ _ ↦ ⋆
  trans := fun {_ _ _} p q {_} x ↦ p _ x ⬝ q _ x
  anti := fun p q ↦ funext fun _ ↦ (funext fun x ↦ p _ x ⇄! q _ x)

noncomputable instance (Γ : Cx) : Domain (⟦Γ cx⟧) where
  bot := fun _ _ ↦ ⊥
  sup := fun c _ x ↦ ⨆ ⟨fun n ↦ c.act n _ x, fun i_j ↦ c.act' i_j _ x⟩
  is_bot := fun _ _ ↦ Domain.is_bot
  is_bound := fun c {n} {_} x ↦ Domain.is_bound ⟨fun n ↦ c.act n _ x, fun i_j ↦ c.act' i_j _ x⟩ n
  is_least := fun c _ p {_} x ↦ Domain.is_least ⟨fun n ↦ c.act n _ x, fun i_j ↦ c.act' i_j _ x⟩ (fun {_} ↦ p _ x)

def Ev.from {Γ : Cx} {τ : Ty} : Cont (⟦Γ cx⟧ × ⟦τ type⟧) (⟦Γ ∷ τ cx⟧) := ⟨
  ⟨
    fun ⟨ρ, d⟩ υ x ↦ ρ.push d υ x,
    by {
      intro ⟨ρ₀, d₀⟩ ⟨ρ₁, d₁⟩ ⟨ρ', d'⟩ υ x
      cases x with
      | z => exact d'
      | s _ x => exact ρ' υ x
    }
  ⟩,
  by {
    intro c υ x
    cases x with
      | z => exact ⋆
      | s _ => exact ⋆
  }
⟩

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
      obtain ⟨n, j₁⟩ := flat_sup_some.mpr j₀
      calc ((cond' (⨆ c)).fn p)
        _ = ((cond' (c n)).fn p) := by rw [j₀, j₁]
        _ ⊑ ((⨆ (cond' ∘ c)).fn p) := (Domain.is_bound (cond' ∘ c) n) p
  }
⟩

def partial_pred : Flat Nat → Flat Nat :=
  fun n ↦ match n with
  | .some (.succ n) => .some n
  | _ => .none

theorem partial_pred_converse {a : Flat Nat} (p : partial_pred a ≠ .none) : (a ≠ .none) := by
  intro q
  rw [q] at p
  exact p rfl

def Mono.pred : Mono (Flat Nat) (Flat Nat) := ⟨
    partial_pred,
    by {
      intro a b a_b
      cases a with
      | none => exact Domain.is_bot
      | some =>
        rw [a_b Flat.noConfusion]
        exact ⋆
    }
  ⟩

def Cont.pred : Cont (Flat Nat) (Flat Nat) := ⟨
  Mono.pred,
  by {
      intro c h
      have ⟨a, p₀⟩ := Flat.invert (partial_pred_converse h)
      rw [p₀]
      have ⟨n, p₁⟩ := flat_sup_some.mpr p₀
      cases a with
      | zero =>
        show .none = ⨆ (Mono.pred ∘' c)
        exfalso
        apply h
        rw [p₀]
        rfl
      | succ a =>
        show .some a = ⨆ (Mono.pred ∘' c)
        have p₂ : ⨆ (Mono.pred ∘ c) = .some a := flat_sup_some.mp ⟨n, by
          calc partial_pred (c n)
            _ = partial_pred (Flat.some a.succ) := congrArg _ p₁
            _ = .some a                         := rfl
        ⟩
        exact p₂.symm
    }
  ⟩

noncomputable def denotation : (Γ ⊢ τ) → Cont (⟦Γ cx⟧) (⟦τ type⟧)
  | .var τ x => ⟨⟨fun ρ ↦ ρ τ x, fun ρ₀_ρ₁ ↦ ρ₀_ρ₁ τ x⟩, ⋆⟩
  | .true => Cont.const (.some true)
  | .false => Cont.const (.some false)
  | .zero => Cont.const (.some 0)
  | .succ e => Cont.flat (Nat.succ) ∘ denotation e
  | .pred e => Cont.pred ∘ denotation e
  | .zero? e => Cont.flat (Nat.zero?) ∘ denotation e
  | .cond s t f  => Cont.uncurry (Cont.cond) ∘ Cont.pair (denotation s) (Cont.pair (denotation t) (denotation f))
  | .fn e  => Cont.curry (denotation e ∘ Ev.from)
  | .app f e => Cont.eval ∘ (Cont.pair (denotation f) (denotation e))
  | .fix f => Cont.fix' ∘ denotation f

notation:100 "⟦" t "⟧" => denotation t

noncomputable def denotation_ren (r : Ren Γ Δ) : Cont (⟦Δ cx⟧) (⟦Γ cx⟧) :=
  ⟨⟨fun ρ _ x ↦ (⟦(x.ren r).tm⟧) ρ, fun ρ' _ x ↦ (⟦(x.ren r).tm⟧) • ρ'⟩, fun _ x ↦ (⟦(x.ren r).tm⟧).sub⟩

notation:100 "⟦" r "⟧" => denotation_ren r

noncomputable def denotation_subst (σ : Subst Γ Δ) : Cont (⟦Δ cx⟧) (⟦Γ cx⟧) :=
  ⟨⟨fun ρ _ x ↦ (⟦x.sub σ⟧) ρ, fun ρ' _ x ↦ (⟦x.sub σ⟧) • ρ'⟩, fun _ x ↦ (⟦x.sub σ⟧).sub⟩

notation:100 "⟦" σ "⟧" => denotation_subst σ

theorem deno_ground_bool : ∀ {n}, (⟦.from_bool n⟧) ρ = (.some n)
  | .false | .true => rfl

theorem deno_ground_nat : (⟦.from_nat n⟧) ρ = (.some n) := by
  induction n with
  | zero => rfl
  | succ n Φ =>
    calc (⟦.from_nat (n.succ)⟧) ρ
      _ = Cont.flat (.succ) ((⟦.from_nat n⟧) ρ) := rfl
      _ = Cont.flat (.succ) (.some n)           := by rw [Φ]
      _ = .some (n.succ)                        := rfl
