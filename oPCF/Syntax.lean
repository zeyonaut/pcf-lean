import «oPCF».Utility

/-
The syntax of PCF consists of objects of four sorts: types, contexts, variables, and terms.
-/

inductive Ty
  | bool
  | nat
  | pow : Ty → Ty → Ty

infixr:100 " ⇒ " => Ty.pow

inductive Cx
  | nil
  | cons : Cx -> Ty -> Cx

infixl:70 " ∷ "  => Cx.cons

inductive Var : Cx → Ty → Type
  | z : ∀ {Γ : Cx}, Var (Γ ∷ τ) τ
  | s : ∀ {Γ : Cx} {υ : Ty} τ, Var Γ τ → Var (Γ ∷ υ) τ

infix:70 " ∋ " => Var

inductive Tm : Cx → Ty → Type
  | var : ∀ τ, Γ ∋ τ → Tm Γ τ
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

infix:70 " ⊢ " => Tm

/-
Certain terms are designated as 'values'.
-/

inductive Tm.IsValue : Γ ⊢ τ → Type
  | true : true.IsValue
  | false : false.IsValue
  | zero : zero.IsValue
  | succ {v : Tm ..} : v.IsValue → v.succ.IsValue
  | fn {e : Tm ..} : e.fn.IsValue

/-
The types of booleans and naturals are designated as 'ground types'.
-/

inductive Ty.IsGround : Ty → Type
  | bool : bool.IsGround
  | nat : nat.IsGround

def Ty.IsGround.repr : Ty.IsGround τ → Type
  | .bool => Bool
  | .nat => Nat

/-
We define functions for converting between mathematical objects and ground values.
-/

def Tm.from_bool : Bool → Γ ⊢ .bool
  | .true => .true
  | .false => .false

def Tm.from_nat : Nat → Γ ⊢ .nat
  | .zero => .zero
  | .succ n => .succ (Tm.from_nat n)

def Tm.IsValue.extract_bool : {v : nil ⊢ .bool} → v.IsValue → (n : Bool) ×' v = from_bool n
  | .true, .true => ⟨.true, rfl⟩
  | .false, .false => ⟨.false, rfl⟩

def Tm.IsValue.extract_nat : {v : nil ⊢ .nat} → v.IsValue → (n : Nat) ×' v = from_nat n
  | .zero, .zero => ⟨.zero, rfl⟩
  | .succ _, .succ v' => let Φ := Tm.IsValue.extract_nat v'; ⟨Φ.fst.succ, congrArg Tm.succ Φ.snd⟩

def Tm.from_nat_is_value : ∀ n, (Tm.from_nat n : Γ ⊢ .nat).IsValue
  | .zero   => .zero
  | .succ n => .succ (from_nat_is_value n)

/-
We define a notion of appending one context to another.
-/

def Cx.append (Γ : Cx) : Cx → Cx
  | .nil => Γ
  | .cons Δ τ => (Γ.append Δ) ∷ τ

instance : Append Cx where
  append := Cx.append

/-
We also define helper functions for converting terms to variables and weakening variables.
-/

def Var.tm (x : Γ ∋ τ) : Γ ⊢ τ := Tm.var τ x

def Var.succ (x : Γ ∋ τ) {υ : Ty} : (Γ ∷ υ) ∋ τ := s τ x
