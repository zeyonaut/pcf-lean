import «oPCF».Syntax

def Ren Γ Δ := {τ : Ty} → Var Γ τ → Var Δ τ
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

def Subst Γ Δ := {τ : Ty} → Var Γ τ → Tm Δ τ

def extend_subst (σ : Subst Γ Δ) {τ : Ty} : Subst (Γ ∷ τ) (Δ ∷ τ) :=
  fun dv => match dv with
  | .z => .var .z
  | .s x => rename .s (σ x)

def subst (σ : Subst Γ Δ) : Reb Γ Δ :=
  fun {τ} e => match e with
  | .var x => σ x
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

def sb1 (a : Tm Γ υ) : Subst (Γ ∷ υ) Γ := fun v => match v with
  | .z => a
  | .s x => .var x

def subst_1 (e : Tm (Γ ∷ τ) υ) (a : Tm Γ τ) : Tm Γ υ
  :=subst (sb1 a) e

inductive Eval : Tm .nil τ → Tm .nil τ → Type
  | true : Eval .true .true
  | false : Eval .false .false
  | zero : Eval .zero .zero
  | succ : Eval t v → Eval (t.succ) (v.succ)
  | fn : Eval (.fn e) (e.fn)
  | pred : Eval t (.succ v) → Eval (.pred t) (v)
  | zero?_zero : Eval t (.zero) → Eval (t.zero?) .true
  | zero?_succ : Eval t (.succ v) → Eval (t.zero?) .false
  | cond_true {t ct cf vt} : Eval t (.true) → Eval ct vt → Eval (t.cond ct cf) vt
  | cond_false {t ct cf vf} : Eval t (.false) → Eval cf vf → Eval (t.cond ct cf) vf
  | app : Eval f (e.fn) → Eval (subst_1 e u) v → Eval (f.app u) v

infixl:75 " ⇓ " => Eval

theorem determinism : t ⇓ v₀ → t ⇓ v₁ → v₀ = v₁ := by
  intro h₀ h₁
  induction h₀ with
  | true =>
    cases h₁
    rfl
  | false =>
    cases h₁
    rfl
  | zero =>
    cases h₁
    rfl
  | succ _ Φ =>
    cases h₁
    case _ _ x =>
    congr
    exact Φ x
  | fn =>
    cases h₁
    rfl
  | pred _ Φ =>
    cases h₁
    case _ _ x =>
    injection Φ x
  | zero?_zero _ Φ =>
    cases h₁ with
    | zero?_zero => rfl
    | zero?_succ x => injection Φ x
  | zero?_succ _ Φ =>
    cases h₁ with
    | zero?_zero x => injection Φ x
    | zero?_succ x => rfl
  | cond_true _ _ Φ₀ Φ₁ =>
    cases h₁ with
    | cond_true _ x₁ => exact Φ₁ x₁
    | cond_false x₀ => injection Φ₀ x₀
  | cond_false _ _ Φ₀ Φ₁ =>
    cases h₁ with
    | cond_true x₀ => injection Φ₀ x₀
    | cond_false _ x₁ => exact Φ₁ x₁
  | app _ _ Φ₀ Φ₁ =>
    cases h₁
    case _ x₀ x₁ =>
    injection Φ₀ x₀ with _ _ _ p
    rw [←p] at x₁
    exact Φ₁ x₁
