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

notation:10 Γ " ⊢ " τ => Tm Γ τ

def Tm.from_bool : Bool → (Γ ⊢ .bool)
  | .true => .true
  | .false => .false

def Tm.from_nat : Nat → (Γ ⊢ .nat)
  | .zero => .zero
  | .succ n => .succ (Tm.from_nat n)

inductive Tm.is_value : (Γ ⊢ τ) → Type
  | true : true.is_value
  | false : false.is_value
  | zero : zero.is_value
  | succ {v : Tm ..} : v.is_value → v.succ.is_value
  | fn {e : Tm ..} : e.fn.is_value


def Ren Γ Δ := ∀ {τ}, Var Γ τ → Var Δ τ
def Reb Γ Δ := {τ : Ty} → Tm Γ τ → Tm Δ τ

def extend_ren (r : Ren Γ Δ) {τ  : Ty} : Ren (Γ ∷ τ) (Δ ∷ τ) :=
  fun v => match v with
  | .z => .z
  | .s x => .s (r x)

def rename (r : Ren Γ Δ) : Reb Γ Δ :=
  fun dv => match dv with
  | .var x => .var (r x)
  | .true => .true
  | .false => .false
  | .zero => .zero
  | .succ e => (rename r e).succ
  | .pred e => (rename r e).pred
  | .zero? e => (rename r e).zero?
  | .cond s et ef => (rename r s).cond (rename r et) (rename r ef)
  | .fn e => (rename (extend_ren r) e).fn
  | .app f a => (rename r f).app (rename r a)
  | .fix f => (rename r f).fix

def Tm.ren (t : Γ ⊢ τ) (r : Ren Γ Δ) : Δ ⊢ τ := rename r t

def Subst Γ Δ := ∀ τ, Var Γ τ → Tm Δ τ

def extend_subst (σ : Subst Γ Δ) {τ : Ty} : Subst (Γ ∷ τ) (Δ ∷ τ) :=
  fun τ x => match x with
  | .z => .var .z
  | .s x => (σ τ x).ren .s

def subst (σ : Subst Γ Δ) : Reb Γ Δ :=
  fun {τ} e => match e with
  | .var x => σ τ x
  | .true => .true
  | .false => .false
  | .zero => .zero
  | .succ e => (subst σ e).succ
  | .pred e => (subst σ e).pred
  | .zero? e => (subst σ e).zero?
  | .cond s et ef => (subst σ s).cond (subst σ et) (subst σ ef)
  | .fn e => (subst (extend_subst σ) e).fn
  | .app f a => (subst σ f).app (subst σ a)
  | .fix f => (subst σ f).fix

def Tm.sub (t : Γ ⊢ τ) (σ : Subst Γ Δ) : Δ ⊢ τ := subst σ t

def sb1 (a : Tm Γ υ) : Subst (Γ ∷ υ) Γ := fun τ v => match v with
  | .z => a
  | .s x => .var x
