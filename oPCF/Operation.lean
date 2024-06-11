import «oPCF».Substitution

/-
The 'big-step' operational semantics of PCF characterizes the results of terms.
-/

inductive Eval : (.nil ⊢ τ) → (.nil ⊢ τ) → Type
  | true : Eval .true .true
  | false : Eval .false .false
  | zero : Eval .zero .zero
  | succ : Eval t v → Eval (t.succ) (v.succ)
  | fn : Eval (.fn e) (e.fn)
  | pred : Tm.is_value v → Eval t (v.succ) → Eval (t.pred) (v)
  | zero?_zero : Eval t (.zero) → Eval (t.zero?) .true
  | zero?_succ : Tm.is_value v → Eval t (v.succ) → Eval (t.zero?) .false
  | cond_true {t ct cf vt} : Eval t (.true) → Eval ct vt → Eval (t.cond ct cf) vt
  | cond_false {t ct cf vf} : Eval t (.false) → Eval cf vf → Eval (t.cond ct cf) vf
  | app {e : Tm ..} : Eval f (e.fn) → Eval (e.sub (Subst.inst u)) v → Eval (f.app u) v
  | fix {f : Tm ..} : Eval (f.app f.fix) v → Eval (f.fix) v

infixl:75 " ⇓ " => Eval

/-
Evaluation is deterministic: evaluation results are unique.
-/

theorem Eval.determinism : t ⇓ v₀ → t ⇓ v₁ → v₀ = v₁ := by
  intro h₀ h₁
  induction h₀ with
  | true | false | zero | fn => cases h₁; rfl
  | succ _ Φ =>
    cases h₁ with
    | succ x => congr; exact Φ x
  | pred _ _ Φ =>
    cases h₁ with
    | pred _ x => injection Φ x
  | zero?_zero _ Φ =>
    cases h₁ with
    | zero?_zero => rfl
    | zero?_succ _ x => injection Φ x
  | zero?_succ _ _ Φ =>
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
    cases h₁ with
    | app  x₀ x₁ =>
      injection Φ₀ x₀ with _ _ _ p
      rw [← p] at x₁
      exact Φ₁ x₁
  | fix _ Φ =>
    cases h₁ with
    | fix x₀ => exact Φ x₀

/-
Evaluation results are values.
-/

def Eval.value : (t ⇓ v) → v.is_value
  | .true | .false | .zero | .fn | .zero?_zero .. | .zero?_succ .. => by constructor
  | succ e   => e.value.succ
  | pred v _ => v
  | .cond_true _ e | .cond_false _ e | .app _ e | .fix e => e.value

/-
Any value evaluates to itself.
-/

def Tm.is_value.self_evaluates : v.is_value → (v ⇓ v)
  | .true | .false | .zero | .fn => by constructor
  | .succ n => .succ n.self_evaluates
