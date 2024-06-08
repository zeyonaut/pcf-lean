import «oPCF».Denotation
import «oPCF».Operation

theorem eval_ground_bool : ∀ {n}, (⟦.from_bool n⟧) ρ = (.some n)
  | .false => rfl
  | .true => rfl

theorem eval_ground_nat : (⟦.from_nat n⟧) ρ = (.some n) := by
  induction n with
  | zero => rfl
  | succ n Φ =>
    calc (⟦.from_nat (n.succ)⟧) ρ
      _ = Cont.flat (.succ) ((⟦.from_nat n⟧) ρ) := rfl
      _ = Cont.flat (.succ) (.some n)           := by rw [Φ]
      _ = .some (n.succ)                        := rfl

theorem deno_ren_eq (e : Γ ⊢ τ) : ∀ Δ, (r : Ren Γ Δ) → ⟦e.ren r⟧ = (⟦e⟧) ∘' (⟦r⟧) := by
  induction e with
  | var => intro Γ r; rfl
  | true => intro _ _; rfl
  | false => intro _ _ ; rfl
  | zero => intro _ _; rfl
  | succ t Φ =>
    intro _ r
    calc ⟦t.succ.ren r⟧
      _ = Cont.flat Nat.succ ∘' ⟦t.ren r⟧ := rfl
      _ = Cont.flat Nat.succ ∘' (⟦t⟧) ∘' ⟦r⟧ := by rw [Φ _ r]
      _ = (⟦t.succ⟧) ∘' ⟦r⟧ := rfl
  | pred t Φ =>
    intro _ r
    calc ⟦t.pred.ren r⟧
      _ = Cont.flat Nat.pred ∘' ⟦t.ren r⟧ := rfl
      _ = Cont.flat Nat.pred ∘' (⟦t⟧) ∘' ⟦r⟧ := by rw [Φ _ r]
      _ = (⟦t.pred⟧) ∘' ⟦r⟧ := rfl
  | zero? t Φ =>
    intro _ r
    calc ⟦t.zero?.ren r⟧
      _ = Cont.flat Nat.zero? ∘' ⟦t.ren r⟧ := rfl
      _ = Cont.flat Nat.zero? ∘' (⟦t⟧) ∘' ⟦r⟧ := by rw [Φ _ r]
      _ = (⟦t.zero?⟧) ∘' ⟦r⟧ := rfl
  | cond s t f Φs Φt Φf =>
    intro _ r
    calc ⟦(s.cond t f).ren r⟧
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s.ren r⟧) (Cont.pair (⟦t.ren r⟧) (⟦f.ren r⟧)) := rfl
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair ((⟦s⟧) ∘' ⟦r⟧) (Cont.pair ((⟦t⟧) ∘' ⟦r⟧) ((⟦f⟧) ∘' ⟦r⟧))
        := by rw [Φs, Φt, Φf]
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s⟧) ((Cont.pair (⟦t⟧) (⟦f⟧))) ∘' ⟦r⟧
        := by rw [Cont.pair_after (⟦t⟧) (⟦f⟧) (⟦r⟧), Cont.pair_after (⟦s⟧) _ (⟦r⟧)]
      _ = (⟦s.cond t f⟧) ∘' ⟦r⟧ := rfl
  | fn e Φ =>
    intro _ r
    calc ⟦e.fn.ren r⟧
      _ = Cont.curry ((⟦e.ren (extend_ren r)⟧) ∘ Ev.from) := rfl
      _ = Cont.curry (((⟦e⟧) ∘' ⟦extend_ren r⟧) ∘ Ev.from) := by rw [Φ _ (extend_ren r)]
      _ = (⟦e.fn⟧) ∘' ⟦r⟧ := by {
        apply Cont.ext ∘ funext
        intro ρ
        apply Cont.ext ∘ funext
        intro d
        have p : (⟦extend_ren r⟧) (Ev.from (ρ, d)) = Ev.from ((⟦r⟧) ρ, d) := by {
          apply funext
          intro τ
          apply funext
          intro x
          cases x with
          | z => rfl
          | s x => rfl
        }
        calc ((((⟦e⟧) ∘' ⟦extend_ren r⟧) ∘' Ev.from).curry ρ) d
          _ = (⟦e⟧) ((⟦extend_ren r⟧) (Ev.from (ρ, d))) := rfl
          _ = (⟦e⟧) (Ev.from ((⟦r⟧) ρ, d)) := by rw [p]
          _ = ((⟦e.fn⟧) ((⟦r⟧) ρ)) d := rfl
      }
  | app f a Φf Φa =>
    intro _ r
    calc ⟦(f.app a).ren r⟧
      _ = Cont.eval ∘' Cont.pair (⟦f.ren r⟧) (⟦a.ren r⟧) := rfl
      _ = Cont.eval ∘' Cont.pair ((⟦f⟧) ∘' ⟦r⟧) ((⟦a⟧) ∘' ⟦r⟧) := by rw [Φf _ r, Φa _  r]
      _ = (⟦f.app a⟧) ∘' ⟦r⟧ := rfl
  | fix f Φ =>
    intro _ r
    calc ⟦f.fix.ren r⟧
      _ = Cont.fix' ∘' ⟦f.ren r⟧ := rfl
      _ = Cont.fix' ∘' (⟦f⟧) ∘' ⟦r⟧ := by rw [Φ _ r]
      _ = (⟦f.fix⟧) ∘' ⟦r⟧ := rfl

theorem ren_s_eq : (⟦.s⟧) (Ev.from (ρ, d)) = ρ := by
  apply funext
  intro τ
  apply funext
  intro x
  rfl

theorem deno_subst_eq (e : Γ ⊢ τ) : ∀ Δ, (σ : Subst Γ Δ) → ⟦e.sub σ⟧ = (⟦e⟧) ∘' (⟦σ⟧) := by
  induction e with
  | var => intro _ _; rfl
  | true => intro _ _; rfl
  | false => intro _ _ ; rfl
  | zero => intro _ _; rfl
  | succ t Φ =>
    intro _ σ
    calc ⟦t.succ.sub σ⟧
      _ = Cont.flat Nat.succ ∘' ⟦t.sub σ⟧ := rfl
      _ = Cont.flat Nat.succ ∘' (⟦t⟧) ∘' ⟦σ⟧ := by rw [Φ _ σ]
      _ = (⟦t.succ⟧) ∘' ⟦σ⟧ := rfl
  | pred t Φ =>
    intro _ σ
    calc ⟦t.pred.sub σ⟧
      _ = Cont.flat Nat.pred ∘' ⟦t.sub σ⟧ := rfl
      _ = Cont.flat Nat.pred ∘' (⟦t⟧) ∘' ⟦σ⟧ := by rw [Φ _ σ]
      _ = (⟦t.pred⟧) ∘' ⟦σ⟧ := rfl
  | zero? t Φ =>
    intro _ σ
    calc ⟦t.zero?.sub σ⟧
      _ = Cont.flat Nat.zero? ∘' ⟦t.sub σ⟧ := rfl
      _ = Cont.flat Nat.zero? ∘' (⟦t⟧) ∘' ⟦σ⟧ := by rw [Φ _ σ]
      _ = (⟦t.zero?⟧) ∘' ⟦σ⟧ := rfl
  | cond s t f Φs Φt Φf =>
    intro _ σ
    calc ⟦(s.cond t f).sub σ⟧
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s.sub σ⟧) (Cont.pair (⟦t.sub σ⟧) (⟦f.sub σ⟧)) := rfl
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair ((⟦s⟧) ∘' ⟦σ⟧) (Cont.pair ((⟦t⟧) ∘' ⟦σ⟧) ((⟦f⟧) ∘' ⟦σ⟧))
        := by rw [Φs, Φt, Φf]
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s⟧) ((Cont.pair (⟦t⟧) (⟦f⟧))) ∘' ⟦σ⟧
        := by rw [Cont.pair_after (⟦t⟧) (⟦f⟧) (⟦σ⟧), Cont.pair_after (⟦s⟧) _ (⟦σ⟧)]
      _ = (⟦s.cond t f⟧) ∘' ⟦σ⟧ := rfl
  | fn e Φ =>
    intro _ σ
    calc ⟦e.fn.sub σ⟧
      _ = Cont.curry ((⟦e.sub (extend_subst σ)⟧) ∘ Ev.from) := rfl
      _ = Cont.curry (((⟦e⟧) ∘' ⟦extend_subst σ⟧) ∘ Ev.from) := by rw [Φ _ (extend_subst σ)]
      _ = (⟦e.fn⟧) ∘' ⟦σ⟧ := by {
        apply Cont.ext ∘ funext
        intro ρ
        apply Cont.ext ∘ funext
        intro d
        have p : (⟦extend_subst σ⟧) (Ev.from (ρ, d)) = Ev.from ((⟦σ⟧) ρ, d) := by {
          apply funext
          intro τ
          apply funext
          intro x
          cases x with
          | z => rfl
          | s x =>
            calc (⟦extend_subst σ⟧) (Ev.from (ρ, d)) τ x.s
              _ = (⟦(σ τ x).ren .s⟧) (Ev.from (ρ, d)) := rfl
              _ = ((⟦σ τ x⟧) ∘' ⟦.s⟧) (Ev.from (ρ, d)) := by rw [deno_ren_eq]
              _ = (⟦σ τ x⟧) ((⟦.s⟧) (Ev.from (ρ, d))) := rfl
              _ = (⟦σ τ x⟧) (ρ) := by rw [ren_s_eq]
              _ = Ev.from ((⟦σ⟧) ρ, d) τ x.s := rfl
        }
        calc ((((⟦e⟧) ∘' ⟦extend_subst σ⟧) ∘' Ev.from).curry ρ) d
          _ = (⟦e⟧) ((⟦extend_subst σ⟧) (Ev.from (ρ, d))) := rfl
          _ = (⟦e⟧) (Ev.from ((⟦σ⟧) ρ, d)) := by rw [p]
          _ = ((⟦e.fn⟧) ((⟦σ⟧) ρ)) d := rfl
      }
  | app f a Φf Φa =>
    intro _ σ
    calc ⟦(f.app a).sub σ⟧
      _ = Cont.eval ∘' Cont.pair (⟦f.sub σ⟧) (⟦a.sub σ⟧) := rfl
      _ = Cont.eval ∘' Cont.pair ((⟦f⟧) ∘' ⟦σ⟧) ((⟦a⟧) ∘' ⟦σ⟧) := by rw [Φf _ σ, Φa _  σ]
      _ = (⟦f.app a⟧) ∘' ⟦σ⟧ := rfl
  | fix f Φ =>
    intro _ σ
    calc ⟦f.fix.sub σ⟧
      _ = Cont.fix' ∘' ⟦f.sub σ⟧ := rfl
      _ = Cont.fix' ∘' (⟦f⟧) ∘' ⟦σ⟧ := by rw [Φ _ σ]
      _ = (⟦f.fix⟧) ∘' ⟦σ⟧ := rfl

theorem deno_sb1_eq : ⟦sb1 a⟧ = Ev.from ∘' (Cont.pair Cont.id' (⟦a⟧)) := by
  apply Cont.ext ∘ funext
  intro d
  apply funext
  intro τ
  apply funext
  intro x
  cases x with
  | z => rfl
  | s => rfl

theorem soundness {t v : Cx.nil ⊢ τ} : t ⇓ v → ⟦t⟧ = ⟦v⟧ := by
  intro e
  induction e with
  | true => rfl
  | false => rfl
  | zero => rfl
  | succ _ t' => exact ap (λ p ↦ Cont.flat _ ∘' p) t'
  | fn => rfl
  | @pred v t _ _ t_v_succ =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦t.pred⟧) ρ
      _ = Cont.flat (Nat.pred) ((⟦t⟧) ρ) := rfl
      _ = Cont.flat (Nat.pred) ((⟦v.succ⟧) ρ) := by rw [t_v_succ]
      _ = ((Cont.flat (Nat.pred) ∘' Cont.flat (Nat.succ)) ∘' (⟦v⟧)) ρ := rfl
      _ = (Cont.flat (Nat.pred ∘ Nat.succ) ∘' (⟦v⟧)) ρ := by rw [Cont.flat_comp Nat.pred Nat.succ]
      _ = (Cont.flat (id) ∘' (⟦v⟧)) ρ := by rw [Nat.pred_succ_id]
      _ = (Cont.id' ∘' (⟦v⟧)) ρ := by rw [Cont.flat_id]
      _ = (⟦v⟧) ρ := rfl
  | @zero?_zero t _ t_zero =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦t.zero?⟧) ρ
      _ = Cont.flat (Nat.zero?) ((⟦t⟧) ρ) := rfl
      _ = Cont.flat (Nat.zero?) ((⟦Tm.zero⟧) ρ) := by rw [t_zero]
      _ = (⟦Tm.true⟧) ρ := rfl
  | @zero?_succ v t v' _ t_v_succ =>
    apply Cont.ext ∘ funext
    intro ρ
    have ⟨n, vn⟩ := v'.ground_nat
    calc (⟦t.zero?⟧) ρ
      _ = Cont.flat (Nat.zero?) ((⟦t⟧) ρ) := rfl
      _ = Cont.flat (Nat.zero?) ((⟦v.succ⟧) ρ) := by rw [t_v_succ]
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ ((⟦v⟧) ρ)) := rfl
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ ((⟦.from_nat n⟧) ρ)) := by rw [vn]
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ (.some n)) := by rw [eval_ground_nat]
      _ = (⟦Tm.false⟧) ρ := rfl
  | @cond_true _ s t f tv _ _ se te =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦s.cond t f⟧) ρ
      _ = (Cont.cond ((⟦s⟧) ρ) ((⟦t⟧) ρ, (⟦f⟧) ρ)) := rfl
      _ = (Cont.cond ((⟦Tm.true⟧) ρ) ((⟦tv⟧) ρ, (⟦f⟧) ρ)) := by rw [se, te]
      _ = (⟦tv⟧) ρ := rfl
  | @cond_false _ s t f fv _ _ se fe =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦s.cond t f⟧) ρ
      _ = (Cont.cond ((⟦s⟧) ρ) ((⟦t⟧) ρ, (⟦f⟧) ρ)) := rfl
      _ = (Cont.cond ((⟦Tm.false⟧) ρ) ((⟦t⟧) ρ, (⟦fv⟧) ρ)) := by rw [se, fe]
      _ = (⟦fv⟧) ρ := rfl
  | @app _ _ f a v e _ _ sf sv =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦f.app a⟧) ρ
      _ = ((⟦f⟧) ρ) ((⟦a⟧) ρ) := rfl
      _ = ((⟦e.fn⟧) ρ) ((⟦a⟧) ρ) := by rw [sf]
      _ = ((⟦e⟧) ∘' Ev.from ∘' (Cont.pair Cont.id' (⟦a⟧))) ρ := rfl
      _ = ((⟦e⟧) ∘' ⟦sb1 a⟧) ρ := by rw [deno_sb1_eq]
      _ = (⟦e.sub (sb1 a)⟧) ρ := by rw [deno_subst_eq]
      _ = (⟦v⟧) ρ := by rw [sv]
  | @fix _ v f _ f_v =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦f.fix⟧) ρ
      _ = ((⟦f⟧) ρ).fix := rfl
      _ = ((⟦f⟧) ρ) ((⟦f⟧) ρ).fix := by rw [Cont.fix_is_fixed]
      _ = (⟦f.app f.fix⟧) ρ := rfl
      _ = (⟦v⟧) ρ := by rw [f_v]
