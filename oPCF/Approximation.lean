import «oPCF».Denotation
import «oPCF».Evaluation
import «oPCF».Context

/-
We define formal approximation for three sorts: terms, substitutions, and contexts.
-/

-- Definition 27
-- NOTE: We state the type parameters of approximation in reverse so Lean can infer the type.
def Tm.Approx : ∀ {τ}, (.nil ⊢ τ) → ↑⟦τ type⟧ → Type
  | .bool   => fun t d ↦ ∀ n,   d = .some n → t ⇓ Tm.from_bool n
  | .nat    => fun t d ↦ ∀ n,   d = .some n → t ⇓ Tm.from_nat n
  | .pow .. => fun t d ↦ ∀ e s, Tm.Approx e s → Tm.Approx (t.app e) (d s)

notation:75 d " ◃ " t => Tm.Approx t d

infix:75 " ◃ " => Tm.Approx

-- Definition 29
def Subst.Approx {Γ : Cx} (ρ : ⟦Γ cx⟧) (σ : Subst Γ .nil) : Type :=
  ∀ τ x, ρ τ x ◃ x.sub σ

infixl:75 " ◃ " => Subst.Approx

def Con.Approx (D: (Cont (Cont ⟦Δ cx⟧ ⟦υ type⟧) (⟦τ type⟧))) (C : Con Δ υ .nil τ) : Type :=
    ∀ (d : Cont ⟦Δ cx⟧ ⟦υ type⟧) (t : Δ ⊢ υ),
      (∀ {ρ : ⟦Δ cx⟧} {σ}, (ρ ◃ σ) → (d ρ ◃ t.sub σ)) → D d ◃ C t

infix:75 " ◃ " => Con.Approx

/-
The approximations of a term form a {0, ω}-coclosed subset.
-/

-- Lemma 31
def bottom_approximates : ∀ {τ} {t : .nil ⊢ τ}, ⊥ ◃ t
  | .bool | .nat => fun _ p   ↦ Flat.noConfusion p
  | .pow ..      => fun _ _ _ ↦ bottom_approximates

-- Lemma 32
noncomputable def supremum_approximates {τ} {t : .nil ⊢ τ} : ∀ {c}, (∀ n, c n ◃ t) → ⨆ c ◃ t := by
  induction τ with
  | bool | nat =>
    intro c c_t d sc_d
    have a := flat_sup_some.mpr sc_d
    exact c_t a.choose d a.choose_spec
  | pow τ₀ τ₁ _ Φ₁ =>
    intro c c_t d u u_d
    show ⨆ (c.apply u) ◃ t.app d
    apply Φ₁
    intro n
    exact c_t n d u u_d

/-
It is also extremely helpful to notice that if one term's evaluations are a subset of another's,
then its approximations are also a subset of the other term's approximations.
-/

-- Lemma 34
noncomputable def same_eval_same_approx
  : ∀ {t₀ t₁ : .nil ⊢ τ}, (∀ {v}, t₀ ⇓ v → t₁ ⇓ v) → ∀ {d}, (d ◃ t₀) → (d ◃ t₁) := by
  intro t₀ t₁ same_eval d d_t₀
  induction τ with
  | bool | nat =>
    intro n d_n
    exact same_eval (d_t₀ n d_n)
  | pow τ₀ τ₁ _ Φ₁ =>
    intro u e e_u
    have d_e_t₀_u : d e ◃ t₀.app u := d_t₀ u e e_u
    show d e ◃ t₁.app u
    suffices same_eval_app : ∀ {v}, t₀.app u ⇓ v → t₁.app u ⇓ v from Φ₁ same_eval_app d_e_t₀_u
    intro v t₀_u_v
    cases t₀_u_v with
    | app f_fn_e e_u_v => exact .app (same_eval f_fn_e) e_u_v

noncomputable def fn_same_eval {e : _ ⊢ _} : (e.sub (σ.push t) ⇓ v) → (e.fn.sub σ).app t ⇓ v := by
  intro eσu_v
  apply Eval.app Eval.fn
  calc (e.sub (σ ∷ₛ _)).sub (Subst.inst t)
    _ = e.sub ((σ ∷ₛ _) ⬝ Subst.inst t) := by rw [Tm.sub_comp_eq]
    _ = e.sub (σ.push t)                := by rw [Subst.push_eq]
    _ ⇓ v                               := eσu_v

/-
We now define methods that lift operations on objects to operations on approximation relations.
-/

def Tm.Approx.succ {t : Tm ..} {d} : (d ◃ t) → (Cont.flat Nat.succ d ◃ t.succ) := by
    intro d_t n succ_d_n
    show t.succ ⇓ Tm.from_nat n
    cases d with
    | none => exact Flat.noConfusion succ_d_n
    | some d =>
      cases n with
      | zero => injection succ_d_n with succ_d_0; exact Nat.noConfusion succ_d_0
      | succ n =>
        injection succ_d_n with h
        injection h with d_n
        rw [d_n] at d_t
        exact .succ (d_t _ rfl)

def Tm.Approx.pred {t : Tm ..} {d} : (d ◃ t) → (Cont.pred d ◃ t.pred) := by
    intro d_t n pred_d_n
    show t.pred ⇓ Tm.from_nat n
    cases d with
    | none => exact Flat.noConfusion pred_d_n
    | some d =>
      cases d with
      | zero => injection pred_d_n
      | succ d =>
        injection pred_d_n with pred_d_n
        change d = n at pred_d_n
        rw [pred_d_n] at d_t
        exact .pred (from_nat_is_value n) (d_t n.succ rfl)

def Tm.Approx.zero? {t : Tm ..} {d} : (d ◃ t) → (Cont.flat Nat.zero? d ◃ t.zero?) := by
  intro d_t n zero?_d_n
  cases d with
  | none => exact Flat.noConfusion zero?_d_n
  | some d =>
    injection zero?_d_n with zero?_d_n
    cases d with
    | zero =>
      rw [← zero?_d_n]
      exact .zero?_zero (d_t .zero rfl)
    | succ d =>
      rw [← zero?_d_n]
      exact .zero?_succ (from_nat_is_value d) (d_t (d.succ) rfl)

noncomputable def Tm.Approx.fix {t : _ ⊢ τ ⇒ τ} {d} : (d ◃ t) → (Cont.fix d ◃ t.fix) := by
  intro d_t
  suffices closed : ∀ {e}, (e ◃ t.fix) → (d e ◃ t.fix)
    from scott bottom_approximates supremum_approximates closed
  intro e e_tfix
  apply same_eval_same_approx Eval.fix
  exact d_t t.fix e e_tfix

noncomputable def Tm.Approx.cond {s : .nil ⊢ .bool} {s'} {t f : .nil ⊢ τ} {t' f'}
  : (s' ◃ s) → (t' ◃ t) → (f' ◃ f) → Cont.cond.uncurry (s', (t', f')) ◃ s.cond t f := by
  intro s'_s t'_t f'_f
  cases s' with
  | none =>
    have h : Cont.cond.uncurry (Flat.none, t', f') = ⊥ := rfl
    rw [h]
    exact bottom_approximates
  | some s' =>
    cases s' with
    | true =>
      suffices same_eval : ∀ {v}, (t ⇓ v) → s.cond t f ⇓ v from same_eval_same_approx same_eval t'_t
      exact .cond_true (s'_s .true rfl)
    | false =>
      suffices same_eval : ∀ {v}, (f ⇓ v) → s.cond t f ⇓ v from same_eval_same_approx same_eval f'_f
      exact .cond_false (s'_s .false rfl)

def Subst.Approx.id' : Ev.nil ◃ Subst.id' := by intro τ x; cases x

def Subst.Approx.push {σ : Subst Γ .nil} {ρ : ⟦Γ cx⟧} (ρ_σ : ρ ◃ σ) {u : .nil ⊢ τ} {d : ↑⟦τ type⟧} (d_u : d ◃ u) : ρ.push d ◃ σ.push u := by
    intro τ x
    cases x with
    | z => exact d_u
    | s τ x => exact ρ_σ τ x

/-
Finally, we can prove the fundamental property of formal approximation, which effectively
states that any object is formally approximated by its denotation.
-/

-- Theorem 29 (Fundamental property of formal approximation)
noncomputable def Tm.approx (t : Γ ⊢ τ) {ρ : ⟦Γ cx⟧} {σ : Subst Γ .nil}
  : (ρ ◃ σ) → (⟦t⟧) ρ ◃ t.sub σ := by
  intro ρ_σ
  induction t with
  | var τ x =>
    exact ρ_σ τ x
  | true | false | zero =>
    intro _ h
    injection h with h
    rw [← h]
    constructor
  | app _ _ Φf Φa       => exact (Φf ρ_σ) _ _ (Φa ρ_σ)
  | succ _ Φ            => exact (Φ ρ_σ).succ
  | pred _ Φ            => exact (Φ ρ_σ).pred
  | zero? _ Φ           => exact (Φ ρ_σ).zero?
  | fix _ Φ             => exact (Φ ρ_σ).fix
  | cond _ _ _ Φs Φt Φf => exact (Φs ρ_σ).cond (Φt ρ_σ) (Φf ρ_σ)
  | @fn Δ τ υ e Φ =>
    intro t d d_t
    exact same_eval_same_approx fn_same_eval (Φ (ρ_σ.push d_t))

noncomputable def Subst.approx (σ' : Subst Γ' Γ) {ρ : ⟦Γ cx⟧} {σ : Subst Γ Cx.nil}
  : (ρ ◃ σ) → ((⟦σ'⟧) ρ ◃ σ' ⬝ σ) := by
  intro ρ_σ _ x
  exact (x.sub σ').approx ρ_σ

noncomputable def Con.approx (C : Con Δ υ Γ τ) {ρ : ⟦Γ cx⟧} {σ : Subst Γ .nil}
  : (ρ ◃ σ) → ⟦C con⟧.curry ρ ◃ C.sub σ := by
  intro ρ_σ d t d_t
  induction C with
  | id' =>
    exact d_t ρ_σ
  | comp C₀ C₁ Φ₀ Φ₁ =>
    let d' := (((⟦C₀ con⟧) ∘' Cont.swap).curry d)
    let t' := C₀ t
    show ⟦C₁ con⟧.curry ρ d' ◃ C₁.sub σ t'
    apply Φ₁ ρ_σ d' t'
    intro ρ' σ' ρ'_σ'
    show ⟦C₀ con⟧.curry ρ' d ◃ C₀.sub σ' t
    apply Φ₀ ρ'_σ' d t
    intro ρ'' σ'' ρ''_σ''
    exact d_t ρ''_σ''
  | sub C σ' Φ =>
    show (⟦C con⟧).curry ((⟦σ'⟧) ρ) d ◃ ((C t).sub σ').sub σ
    rw [← Tm.sub_comp_eq]
    exact Φ (σ'.approx ρ_σ) d t d_t
  | app_f _ a Φ    => exact (Φ ρ_σ _ _ d_t) _ _ (a.approx ρ_σ)
  | app_a f _ Φ    => exact (f.approx ρ_σ) _ _ (Φ ρ_σ _ _ d_t)
  | succ _ Φ       => exact (Φ ρ_σ _ _ d_t).succ
  | pred _ Φ       => exact (Φ ρ_σ _ _ d_t).pred
  | zero? _ Φ      => exact (Φ ρ_σ _ _ d_t).zero?
  | fix _ Φ        => exact (Φ ρ_σ _ _ d_t).fix
  | cond_s _ e f Φ => exact (Φ ρ_σ _ _ d_t).cond (e.approx ρ_σ) (f.approx ρ_σ)
  | cond_t s _ f Φ => exact (s.approx ρ_σ).cond (Φ ρ_σ _ _ d_t) (f.approx ρ_σ)
  | cond_f s e _ Φ => exact (s.approx ρ_σ).cond (e.approx ρ_σ) (Φ ρ_σ _ _ d_t)
  | @fn Δ ν Γ υ τ C Φ =>
    intro e u u_e
    exact same_eval_same_approx fn_same_eval (Φ (ρ_σ.push u_e) _ _ d_t)
