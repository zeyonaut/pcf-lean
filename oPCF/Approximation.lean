import «oPCF».Denotation
import «oPCF».Operation

-- NOTE: We define the type arguments of approximation in this order so τ can be inferred.
-- Definition 27 (Formal approximation)
def Approx : ∀ {τ}, (.nil ⊢ τ) → ↑⟦τ type⟧ → Type
| .bool   => fun t d ↦ ∀ n,   d = .some n → t ⇓ Tm.from_bool n
| .nat    => fun t d ↦ ∀ n,   d = .some n → t ⇓ Tm.from_nat n
| .pow .. => fun t d ↦ ∀ u e, Approx u e → Approx (t.app u) (d e)

infixl:75 " ▹ " => Approx
notation:75 d " ◃ " t => Approx t d

def Tm.approximations (t : .nil ⊢ τ) (d : ↑⟦τ type⟧) : Type := d ◃ t

-- Definition 29 (Formal approximation for substitution)
def Approx_Subst {Γ : Cx} (ρ : ⟦Γ cx⟧) (σ : Subst Γ .nil) : Type :=
  ∀ τ x, ρ τ x ◃ σ τ x

infixl:75 " ◃ " => Approx_Subst

def from_nat_is_value : ∀ n, (Tm.from_nat n : Γ ⊢ .nat).is_value
  | .zero => .zero
  | .succ n => .succ (from_nat_is_value n)

-- Lemma 31
def bottom_approximates : ∀ {τ} {t : .nil ⊢ τ}, ⊥ ◃ t
  | .bool   => fun _ p   ↦ Flat.noConfusion p
  | .nat    => fun _ p   ↦ Flat.noConfusion p
  | .pow .. => fun _ _ _ ↦ bottom_approximates

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


-- Theorem 29 (Fundamental property of formal approximation)
noncomputable def approximation_fundamental {Γ : Cx} {ρ : ⟦Γ cx⟧} {σ : Subst Γ .nil} (t : Γ ⊢ τ)
  : (ρ ◃ σ) → (⟦t⟧) ρ ◃ t.sub σ := by
  induction t with
  | var τ x =>
    intro ρ_σ
    exact ρ_σ τ x
  | true | false | zero =>
    intro _ _ h
    injection h with h
    rw [← h]
    constructor
  | app _ a Φf Φa =>
    intro ρ_σ
    exact Φf ρ_σ (a.sub σ) ((⟦a⟧) ρ) (Φa ρ_σ)
  | succ t Φ =>
    intro ρ_σ
    suffices lem : ∀ {t : Tm ..} {d}, (d ◃ t) → (Cont.flat Nat.succ d ◃ t.succ) from lem (Φ ρ_σ)
    intro t d d_t n succ_d_n
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
  | pred t Φ =>
    intro ρ_σ
    suffices lem : ∀ {t : Tm ..} {d}, (d ◃ t) → (Cont.flat Nat.pred d ◃ t.pred) from lem (Φ ρ_σ)
    intro t d d_t n pred_d_n
    show t.pred ⇓ Tm.from_nat n
    cases d with
    | none => exact Flat.noConfusion pred_d_n
    | some d =>
      injection pred_d_n with pred_d_n
      cases d with
      | zero =>
        cases n with
        | zero => exact .pred_zero (d_t 0 rfl)
        | succ => injection pred_d_n
      | succ d =>
        change d = n at pred_d_n
        rw [pred_d_n] at d_t
        exact .pred_succ (from_nat_is_value n) (d_t n.succ rfl)
  | zero? t Φ =>
    intro ρ_σ
    suffices lem : ∀ {t : Tm ..} {d}, (d ◃ t) → (Cont.flat Nat.zero? d ◃ t.zero?) from lem (Φ ρ_σ)
    intro t d d_t n zero?_d_n
    cases d with
    | none => exact Flat.noConfusion zero?_d_n
    | some d =>
      injection zero?_d_n with zero?_d_n
      cases d with
      | zero =>
        change true = n at zero?_d_n
        rw [← zero?_d_n]
        exact .zero?_zero (d_t .zero rfl)
      | succ d =>
        change false = n at zero?_d_n
        rw [← zero?_d_n]
        exact .zero?_succ (from_nat_is_value d) (d_t (d.succ) rfl)
  | cond s t f Φs Φt Φf =>
    intro ρ_σ
    suffices lem : ∀ {s : Tm ..} {s'} {t f : Tm ..} {t' f'}, (s' ◃ s) → (t' ◃ t) → (f' ◃ f)
      → Cont.cond.uncurry (s', (t', f')) ◃ s.cond t f
      from lem (Φs ρ_σ) (Φt ρ_σ) (Φf ρ_σ)
    intro s s' t f t' f' s'_s t'_t f'_f
    cases s' with
    | none =>
      have h : Cont.cond.uncurry (Flat.none, t', f') = ⊥ := rfl
      rw [h]
      exact bottom_approximates
    | some s' =>
      cases s' with
      | true =>
        have same_eval : ∀ {v}, (t ⇓ v) → s.cond t f ⇓ v := fun t_v ↦ Eval.cond_true (s'_s true rfl) t_v
        exact same_eval_same_approx same_eval t'_t
      | false =>
        have same_eval : ∀ {v}, (f ⇓ v) → s.cond t f ⇓ v := fun f_v ↦ Eval.cond_false (s'_s false rfl) f_v
        exact same_eval_same_approx same_eval f'_f
  | fix t Φ =>
    intro ρ_σ
    suffices lem : ∀ {t : Tm ..} {d}, (d ◃ t) → (Cont.fix d ◃ t.fix) from lem (Φ ρ_σ)
    intro t d d_t
    suffices closed : ∀ {e}, (e ◃ t.fix) → (d e ◃ t.fix)
      from scott bottom_approximates supremum_approximates closed
    intro e e_tfix
    apply same_eval_same_approx Eval.fix
    exact d_t t.fix e e_tfix
  | @fn Δ τ υ e Φ =>
    intro ρ_σ u d d_u
    have tρd_tσu : (⟦e⟧) (ρ.push d) ◃ e.sub (σ.push u) := by {
      apply Φ
      show ρ.push d ◃ σ.push u
      intro τ x
      cases x with
      | z => exact d_u
      | s τ x => exact ρ_σ τ x
    }
    have same_eval : ∀ {v}, (e.sub (σ.push u) ⇓ v) → (e.fn.sub σ).app u ⇓ v := by {
      intro v eσu_v
      apply Eval.app Eval.fn
      calc (e.sub (σ.keep _)).sub (Subst.inst u)
        _ = e.sub (σ.keep _ ⬝ Subst.inst u) := by rw [sub_trans_eq]
        _ = e.sub (σ.push u) := by rw [sub_push_eq_keep_inst]
        _ ⇓ v := eσu_v
    }
    exact same_eval_same_approx same_eval tρd_tσu

-- Theorem 30 (Adequacy)
noncomputable def adequacy {t v : Cx.nil ⊢ τ} : τ.is_ground → v.is_value → ⟦t⟧ = ⟦v⟧ → t ⇓ v := by
  intro τ_is_ground v_is_value deno_t_v
  cases τ_is_ground with
  | bool =>
    have ⟨n, v_n⟩ := v_is_value.ground_bool
    have nil_approx_id : Ev.nil ◃ Subst.id' := by intro τ x; cases x
    have lem : (⟦t⟧) Ev.nil ◃ t.sub (Subst.id') := approximation_fundamental t nil_approx_id
    rw [deno_t_v, v_n, deno_ground_bool, sub_id_eq] at lem
    rw [v_n]
    exact lem n rfl
  | nat =>
    have ⟨n, v_n⟩ := v_is_value.ground_nat
    have nil_approx_id : Ev.nil ◃ Subst.id' := by intro τ x; cases x
    have lem : (⟦t⟧) Ev.nil ◃ t.sub (Subst.id') := approximation_fundamental t nil_approx_id
    rw [deno_t_v, v_n, deno_ground_nat, sub_id_eq] at lem
    rw [v_n]
    exact lem n rfl
