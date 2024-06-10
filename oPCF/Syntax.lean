import «oPCF».Utility

inductive Ty
  | bool
  | nat
  | pow : Ty → Ty → Ty

infixr:100 " ⇒ " => Ty.pow

inductive Ty.is_ground : Ty → Type
  | bool : bool.is_ground
  | nat : nat.is_ground

inductive Cx
  | nil
  | cons : Cx -> Ty -> Cx

infixl:100 " ∷ " => Cx.cons

inductive Var : Cx → Ty → Type
  | z : Var (Γ ∷ τ) τ
  | s : ∀ τ, Var Γ τ → Var (Γ ∷ υ) τ

def Var.succ (x : Var Γ τ) : Var (Γ ∷ υ) τ := s τ x

def Var.tr_cx (t : Var Γ τ) : (Γ = Δ) → (Var Δ τ)
  | p => by rw [p] at t; exact t

inductive Tm : Cx → Ty → Type
  | var : ∀ τ, Var Γ τ → Tm Γ τ
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

def Var.tm (x : Var Γ τ) : Γ ⊢ τ := Tm.var τ x

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

def Tm.is_value.ground_bool : {v : nil ⊢ .bool} → v.is_value → (n : Bool) ×' v = from_bool n
  | .true, .true => ⟨.true, rfl⟩
  | .false, .false => ⟨.false, rfl⟩

def Tm.is_value.ground_nat : {v : nil ⊢ .nat} → v.is_value → (n : Nat) ×' v = from_nat n
  | .zero, .zero => ⟨.zero, rfl⟩
  | .succ _, .succ v' => let Φ := ground_nat v'; ⟨Φ.fst.succ, congrArg Tm.succ Φ.snd⟩

def Cx.append (Γ : Cx) : Cx → Cx
  | .nil => Γ
  | .cons Δ τ => Γ.append Δ ∷ τ

def Cx.append_append_eq (Γ Δ₀ Δ₁ : Cx) : (Γ.append Δ₀).append Δ₁ = Γ.append (Δ₀.append Δ₁) := by
  induction Δ₁ with
  | nil => rfl
  | cons Δ₁ τ Φ => calc ((Γ.append Δ₀).append Δ₁) ∷ τ = Γ.append (Δ₀.append Δ₁) ∷ τ := by rw [Φ]
