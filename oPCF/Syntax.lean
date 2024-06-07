inductive Ty
  | bool
  | nat
  | pow : Ty → Ty → Ty

infixr:100 " ⇒ " => Ty.pow

inductive Cx
  | nil
  | cons : Cx -> Ty -> Cx

infixl:100 " ∷ " => Cx.cons

inductive Var : Cx → Ty → Type
  | z : Var (Γ ∷ τ) τ
  | s : Var Γ τ → Var (Γ ∷ υ) τ

inductive Tm : Cx → Ty → Type
  | var : Var Γ τ → Tm Γ τ
  | true : Tm Γ .bool
  | false : Tm Γ .bool
  | zero : Tm Γ .nat
  | succ : Tm Γ .nat → Tm Γ .nat
  | pred : Tm Γ .nat → Tm Γ .nat
  | zero? : Tm Γ .nat → Tm Γ .bool
  | cond : Tm Γ .bool → Tm Γ τ → Tm Γ τ → Tm Γ τ
  | fn : Tm (Γ ∷ τ) υ → Tm Γ (τ ⇒ υ)
  | app : Tm Γ (τ ⇒ υ) → Tm Γ τ → Tm Γ υ
  | fix : Tm Γ (τ ⇒ τ) → Tm Γ τ

notation:10 Γ "⊢" τ => Tm Γ τ
