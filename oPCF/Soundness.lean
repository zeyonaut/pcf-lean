import «oPCF».Context
import «oPCF».Approximation

/-
Soundness states that the evaluand and result of any evaluation have the same denotation.
-/

theorem soundness {t v : Cx.nil ⊢ τ} : t ⇓ v → ⟦t⟧ = ⟦v⟧ := by
  intro e
  induction e with
  | true | false | zero | fn => rfl
  | succ _ t_v | @zero?_zero _ _ t_v =>
    exact congrArg (fun p ↦ Cont.flat _ ∘' p) t_v
  | @pred v t _ _ t_v_succ =>
    apply Cont.ext; funext ρ
    calc  (⟦t.pred⟧) ρ
      _ = Cont.pred ((⟦t⟧) ρ)      := rfl
      _ = Cont.pred ((⟦v.succ⟧) ρ) := by rw [t_v_succ]
      _ = ((Cont.pred ∘' Cont.flat (Nat.succ)) ∘' (⟦v⟧)) ρ := rfl
      _ = (Cont.id' ∘' (⟦v⟧)) ρ    := by rw [pred_flat_succ_eq_id]
      _ = (⟦v⟧) ρ                  := rfl
  | @zero?_succ v t v' _ t_v_succ =>
    apply Cont.ext; funext ρ
    have ⟨n, vn⟩ := v'.extract_nat
    calc  (⟦t.zero?⟧) ρ
      _ = Cont.flat (Nat.zero?) ((⟦t⟧) ρ)      := rfl
      _ = Cont.flat (Nat.zero?) ((⟦v.succ⟧) ρ) := by rw [t_v_succ]
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ ((⟦v⟧) ρ)) := rfl
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ ((⟦.from_nat n⟧) ρ)) := by rw [vn]
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ (.some n)) := by rw [deno_ground_nat]
      _ = (⟦.false⟧) ρ := rfl
  | @cond_true _ s t f tv _ _ se te =>
    apply Cont.ext; funext ρ
    calc  (⟦s.cond t f⟧) ρ
      _ = (Cont.cond ((⟦s⟧) ρ) ((⟦t⟧) ρ, (⟦f⟧) ρ))      := rfl
      _ = (Cont.cond ((⟦.true⟧) ρ) ((⟦tv⟧) ρ, (⟦f⟧) ρ)) := by rw [se, te]
      _ = (⟦tv⟧) ρ                                      := rfl
  | @cond_false _ s t f fv _ _ se fe =>
    apply Cont.ext; funext ρ
    calc  (⟦s.cond t f⟧) ρ
      _ = (Cont.cond ((⟦s⟧) ρ) ((⟦t⟧) ρ, (⟦f⟧) ρ))       := rfl
      _ = (Cont.cond ((⟦.false⟧) ρ) ((⟦t⟧) ρ, (⟦fv⟧) ρ)) := by rw [se, fe]
      _ = (⟦fv⟧) ρ                                       := rfl
  | @app _ _ f a v e _ _ sf sv =>
    apply Cont.ext; funext ρ
    calc  (⟦f.app a⟧) ρ
      _ = ((⟦f⟧) ρ) ((⟦a⟧) ρ)           := rfl
      _ = ((⟦e.fn⟧) ρ) ((⟦a⟧) ρ)        := by rw [sf]
      _ = (⟦e⟧) (Ev.from (ρ, (⟦a⟧) ρ))  := rfl
      _ = (⟦e⟧) ((⟦Subst.inst a⟧) ρ)    := by rw [deno_inst_eq]
      _ = ((⟦e⟧) ∘' (⟦Subst.inst a⟧)) ρ := rfl
      _ = (⟦e.sub (Subst.inst a)⟧) ρ    := by rw [deno_subst_eq]
      _ = (⟦v⟧) ρ                       := by rw [sv]
  | @fix _ v f _ f_v =>
    apply Cont.ext; funext ρ
    calc  (⟦f.fix⟧) ρ
      _ = ((⟦f⟧) ρ).fix           := rfl
      _ = ((⟦f⟧) ρ) ((⟦f⟧) ρ).fix := by rw [Cont.fix_is_fixed]
      _ = (⟦f.app f.fix⟧) ρ       := rfl
      _ = (⟦v⟧) ρ                 := by rw [f_v]

/-
Compositionality states that contextual application preserves denotational equality.
-/

def compositionality {t₀ t₁ : Δ ⊢ ν} (p : ⟦t₀⟧ = ⟦t₁⟧) : ∀ (C : Con Δ ν Γ τ), ⟦C t₀⟧ = ⟦C t₁⟧ := by
  intro C
  induction C with
  | id'            => exact p
  | comp _ _ Φ Φ'  => exact Φ' (Φ p)
  | succ _ Φ       => exact congrArg (fun t ↦ Cont.flat (Nat.succ) ∘' t) (Φ p)
  | pred _ Φ       => exact congrArg (fun t ↦ Cont.pred ∘' t) (Φ p)
  | zero? _ Φ      => exact congrArg (fun t ↦ Cont.flat (Nat.zero?) ∘' t) (Φ p)
  | fn _ Φ         => exact congrArg (fun t ↦ Cont.curry (t ∘ Ev.from)) (Φ p)
  | fix _ Φ        => exact congrArg (fun t ↦ Cont.fix' ∘' t) (Φ p)
  | app_f _ a Φ    => exact congrArg (fun f ↦ _ ∘' (Cont.pair f (⟦a⟧))) (Φ p)
  | app_a f _ Φ    => exact congrArg (fun a ↦ _ ∘' (Cont.pair (⟦f⟧) a)) (Φ p)
  | cond_s _ t f Φ => exact congrArg (fun s ↦ _ ∘' Cont.pair s (Cont.pair (⟦t⟧) (⟦f⟧))) (Φ p)
  | cond_t s _ f Φ => exact congrArg (fun t ↦ _ ∘' Cont.pair (⟦s⟧) (Cont.pair t (⟦f⟧))) (Φ p)
  | cond_f s t _ Φ => exact congrArg (fun f ↦ _ ∘' Cont.pair (⟦s⟧) (Cont.pair (⟦t⟧) f)) (Φ p)
  | sub C σ Φ      =>
    show ⟦(C.fill t₀).sub σ⟧ = ⟦(C.fill t₁).sub σ⟧
    rw [deno_subst_eq, deno_subst_eq, Φ p]

/-
Adequacy states that if a term and value of ground type have the same denotation, then said term
evaluates to said value.
-/

noncomputable def adequacy {t v : Cx.nil ⊢ τ} : τ.IsGround → v.IsValue → ⟦t⟧ = ⟦v⟧ → t ⇓ v := by
  intro τ_is_ground v_is_value deno_t_v
  cases τ_is_ground with
  | bool =>
    have ⟨n, v_n⟩ := v_is_value.extract_bool
    have lem : (⟦t⟧) Ev.nil ◃ t.sub (Subst.id') := t.approx Subst.Approx.id'
    rw [deno_t_v, v_n, deno_ground_bool, Tm.sub_id_eq] at lem
    rw [v_n]
    exact lem n rfl
  | nat =>
    have ⟨n, v_n⟩ := v_is_value.extract_nat
    have lem : (⟦t⟧) Ev.nil ◃ t.sub (Subst.id') := t.approx Subst.Approx.id'
    rw [deno_t_v, v_n, deno_ground_nat, Tm.sub_id_eq] at lem
    rw [v_n]
    exact lem n rfl

/-
Together, soundness, compositionality, and adequacy can be used to show that denotational equality
implies contextual equivalence.
-/

noncomputable def den_eq_implies_con_equiv {t₀ t₁ : Γ ⊢ τ} (eq : ⟦t₀⟧ = ⟦t₁⟧) : t₀ ≅ᶜ t₁
  := by
  intro τ τ_is_ground C v
  constructor
  case mp =>
    show C t₀ ⇓ v → C t₁ ⇓ v
    intro C_t₀_v
    exact adequacy τ_is_ground C_t₀_v.result_is_value ((compositionality eq C).symm ⬝ soundness C_t₀_v)
  case mpr =>
    show C t₁ ⇓ v → C t₀ ⇓ v
    intro C_t₁_v
    exact adequacy τ_is_ground C_t₁_v.result_is_value (compositionality eq C ⬝ soundness C_t₁_v)
