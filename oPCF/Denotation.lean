import «oPCF».Syntax
import «oPCF».Operation
import «oPCF».Domain
import «oPCF».Flat

structure DomainType : Type (i + 1) :=
  carrier : Type i
  order : Order carrier
  domain : Domain carrier

instance : Coe DomainType Type where
  coe D := D.carrier

-- Definition 22.
noncomputable def ty_deno (τ : Ty) : DomainType := by
  induction τ with
  | bool => exact ⟨Flat Bool, _, inferInstance⟩
  | nat => exact ⟨Flat Nat, _, inferInstance⟩
  | pow _ _ T₀ T₁ =>
    obtain ⟨T₀, O₀, D₀⟩ := T₀
    obtain ⟨T₁, O₁, D₁⟩ := T₁
    exact ⟨Cont T₀ T₁,  _ , inferInstance⟩

notation:100 "⟦" τ "⟧" => ty_deno τ

noncomputable instance (τ : Ty) : Order ↑(⟦τ⟧) := ⟦τ⟧.order
noncomputable instance (τ : Ty) : Domain ↑(⟦τ⟧) := ⟦τ⟧.domain

-- Definition 23.
def Ev (Γ : Cx) : Type := ∀ {τ}, Var Γ τ → ↑(⟦τ⟧)

notation:100 "⟦" Γ "⟧" => Ev Γ

def Ev.push {Γ : Cx} (ρ : ⟦Γ⟧) {τ : Ty} (d : ⟦τ⟧) : Ev (Γ ∷ τ) :=
  fun {τ} x ↦ match x with
  | .z => d
  | .s x => ρ x

noncomputable instance (Γ : Cx) : Order (⟦Γ⟧) where
  R := fun a b ↦ ∀ {τ} (x : Var Γ τ), a x ⊑ b x
  refl := fun _ ↦ ⋆
  trans := fun {_ _ _} p q {_} x ↦ p x ⬝ q x
  anti := fun p q ↦ funext fun _ ↦ (funext fun x ↦ p x ⇄! q x)

noncomputable instance (Γ : Cx) : Domain (⟦Γ⟧) where
  bot := fun _ ↦ ⊥
  sup := fun c _ x ↦ ⨆ ⟨fun n ↦ c.act n x, fun i_j ↦ c.act' i_j x⟩
  is_bot := fun _ ↦ Domain.is_bot
  is_bound := fun c {n} {_} x ↦ Domain.is_bound ⟨fun n ↦ c.act n x, fun i_j ↦ c.act' i_j x⟩ n
  is_least := fun c _ p {_} x ↦ Domain.is_least ⟨fun n ↦ c.act n x, fun i_j ↦ c.act' i_j x⟩ (fun {_} ↦ p x)

def Nat.zero? : Nat → Bool
| .zero => true
| _ => false

def Ev.from {Γ : Cx} {τ : Ty} : Cont (⟦Γ⟧ × ⟦τ⟧) (⟦Γ ∷ τ⟧) := ⟨
  ⟨
    fun ⟨ρ, d⟩ υ x ↦ ρ.push d x,
    by {
      intro ⟨ρ₀, d₀⟩ ⟨ρ₁, d₁⟩ ⟨ρ', d'⟩ υ x
      cases x with
      | z => exact d'
      | s x => exact ρ' x
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
      calc ((cond' $ ⨆ c).fn $ p)
        _ ⊑ ((cond' $ (c $ n)).fn $ p) := by rw [j₀, j₁]; exact ⋆
        _ ⊑ ((⨆ (cond' ∘ c)).fn $ p) := (Domain.is_bound (cond' ∘ c) n) p
  }
⟩

noncomputable def denotation : (Γ ⊢ τ) → Cont (⟦Γ⟧) (⟦τ⟧)
  | .var x => ⟨⟨fun ρ ↦ ρ x, fun ρ₀_ρ₁ ↦ ρ₀_ρ₁ x⟩, ⋆⟩
  | .true => Cont.const (.some true)
  | .false => Cont.const (.some false)
  | .zero => Cont.const (.some 0)
  | .succ e => Cont.flat (Nat.succ) ∘ denotation e
  | .pred e => Cont.flat (Nat.pred) ∘ denotation e
  | .zero? e => Cont.flat (Nat.zero?) ∘ denotation e
  | .cond s t f  => Cont.uncurry (Cont.cond) ∘ Cont.pair (denotation s) (Cont.pair (denotation t) (denotation f))
  | @Tm.fn Γ τ υ e  => by {
    show Cont (⟦Γ⟧) (Cont (⟦τ⟧) (⟦υ⟧))
    exact Cont.curry (denotation e ∘ Ev.from)
    }
  | @Tm.app Γ τ υ f e => by {
    have f' : Cont (⟦Γ⟧) (Cont (⟦τ⟧) (⟦υ⟧)) := denotation f
    exact Cont.eval ∘ (Cont.pair f' (denotation e))
  }
  | .fix f => Cont.fix ∘ denotation f
