import «oPCF».Substitution

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

-- Proposition 23 (Determinism)
theorem determinism : t ⇓ v₀ → t ⇓ v₁ → v₀ = v₁ := by
  intro h₀ h₁
  induction h₀ with
  | true | false | zero | fn =>
    cases h₁
    rfl
  | succ _ Φ =>
    cases h₁
    case _ _ x =>
    congr
    exact Φ x
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
    cases h₁
    case _ x₀ x₁ =>
    injection Φ₀ x₀ with _ _ _ p
    rw [←p] at x₁
    exact Φ₁ x₁
  | fix _ Φ =>
    cases h₁
    case fix x₀ =>
    exact Φ x₀
