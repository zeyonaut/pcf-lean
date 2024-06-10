import «oPCF».Denotation
import «oPCF».Operation

theorem deno_ren_eq (e : Γ ⊢ τ) : ∀ {Δ}, (r : Ren Γ Δ) → ⟦e.ren r⟧ = (⟦e⟧) ∘' (⟦r⟧) := by
  induction e with
  | fn e Φ =>
    intro _ r
    calc ⟦e.fn.ren r⟧
      _ = Cont.curry ((⟦e.ren r.keep⟧) ∘ Ev.from) := rfl
      _ = Cont.curry (((⟦e⟧) ∘' ⟦r.keep⟧) ∘ Ev.from) := by rw [Φ r.keep]
      _ = (⟦e.fn⟧) ∘' ⟦r⟧ := by {
        apply Cont.ext ∘ funext
        intro ρ
        apply Cont.ext ∘ funext
        intro d
        have p : (⟦r.keep⟧) (Ev.from (ρ, d)) = Ev.from ((⟦r⟧) ρ, d) := by {
          apply funext
          intro τ
          apply funext
          intro x
          cases x with
          | z => rfl
          | s x => rfl
        }
        calc ((((⟦e⟧) ∘' ⟦r.keep⟧) ∘' Ev.from).curry ρ) d
          _ = (⟦e⟧) ((⟦r.keep⟧) (Ev.from (ρ, d))) := rfl
          _ = (⟦e⟧) (Ev.from ((⟦r⟧) ρ, d)) := by rw [p]
          _ = ((⟦e.fn⟧) ((⟦r⟧) ρ)) d := rfl
      }
  | var | true | false | zero => intros; rfl
  | succ _ Φ | pred _ Φ | zero? _ Φ | fix _ Φ => intro _ r; exact congrArg _ (Φ r)
  | app f a Φf Φa =>
    intro _ r; exact congrArg2 (fun f a ↦ Cont.eval ∘' Cont.pair f a) (Φf r) (Φa r)
  | cond s t f Φs Φt Φf =>
    intro _ r
    calc ⟦(s.cond t f).ren r⟧
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s.ren r⟧) (Cont.pair (⟦t.ren r⟧) (⟦f.ren r⟧)) := rfl
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair ((⟦s⟧) ∘' ⟦r⟧) (Cont.pair ((⟦t⟧) ∘' ⟦r⟧) ((⟦f⟧) ∘' ⟦r⟧))
        := by rw [Φs, Φt, Φf]
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s⟧) ((Cont.pair (⟦t⟧) (⟦f⟧))) ∘' ⟦r⟧
        := by rw [Cont.pair_after (⟦t⟧) (⟦f⟧) (⟦r⟧), Cont.pair_after (⟦s⟧) _ (⟦r⟧)]
      _ = (⟦s.cond t f⟧) ∘' ⟦r⟧ := rfl

theorem ren_s_eq : (⟦.s⟧) (Ev.from (ρ, d)) = ρ := by
  apply funext
  intro τ
  apply funext
  intro x
  rfl

theorem deno_subst_eq (e : Γ ⊢ τ) : ∀ {Δ}, (σ : Subst Γ Δ) → ⟦e.sub σ⟧ = (⟦e⟧) ∘' (⟦σ⟧) := by
  induction e with
  | fn e Φ =>
    intro _ σ
    calc ⟦e.fn.sub σ⟧
      _ = Cont.curry ((⟦e.sub (σ.keep _)⟧) ∘ Ev.from) := rfl
      _ = Cont.curry (((⟦e⟧) ∘' ⟦σ.keep _⟧) ∘ Ev.from) := by rw [Φ (σ.keep _)]
      _ = (⟦e.fn⟧) ∘' ⟦σ⟧ := by {
        apply Cont.ext ∘ funext
        intro ρ
        apply Cont.ext ∘ funext
        intro d
        have p : (⟦σ.keep _⟧) (Ev.from (ρ, d)) = Ev.from ((⟦σ⟧) ρ, d) := by {
          apply funext
          intro τ
          apply funext
          intro x
          cases x with
          | z => rfl
          | s τ x =>
            calc (⟦σ.keep _⟧) (Ev.from (ρ, d)) τ x.succ
              _ = (⟦(σ τ x).ren .s⟧) (Ev.from (ρ, d)) := rfl
              _ = ((⟦σ τ x⟧) ∘' ⟦.s⟧) (Ev.from (ρ, d)) := by rw [deno_ren_eq]
              _ = (⟦σ τ x⟧) ((⟦.s⟧) (Ev.from (ρ, d))) := rfl
              _ = (⟦σ τ x⟧) (ρ) := by rw [ren_s_eq]
              _ = Ev.from ((⟦σ⟧) ρ, d) τ x.s := rfl
        }
        calc ((((⟦e⟧) ∘' ⟦σ.keep _⟧) ∘' Ev.from).curry ρ) d
          _ = (⟦e⟧) ((⟦σ.keep _⟧) (Ev.from (ρ, d))) := rfl
          _ = (⟦e⟧) (Ev.from ((⟦σ⟧) ρ, d)) := by rw [p]
          _ = ((⟦e.fn⟧) ((⟦σ⟧) ρ)) d := rfl
      }
  | var | true | false | zero => intros; rfl
  | succ _ Φ | pred _ Φ | zero? _ Φ | fix _ Φ => intro _ σ; exact congrArg _ (Φ σ)
  | app _ _ Φf Φa =>
    intro _ σ; exact congrArg2 (fun f a ↦ Cont.eval ∘' Cont.pair f a) (Φf σ) (Φa σ)
  | cond s t f Φs Φt Φf =>
    intro _ σ
    calc ⟦(s.cond t f).sub σ⟧
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s.sub σ⟧) (Cont.pair (⟦t.sub σ⟧) (⟦f.sub σ⟧)) := rfl
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair ((⟦s⟧) ∘' ⟦σ⟧) (Cont.pair ((⟦t⟧) ∘' ⟦σ⟧) ((⟦f⟧) ∘' ⟦σ⟧))
        := by rw [Φs, Φt, Φf]
      _ = Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s⟧) ((Cont.pair (⟦t⟧) (⟦f⟧))) ∘' ⟦σ⟧
        := by rw [Cont.pair_after (⟦t⟧) (⟦f⟧) (⟦σ⟧), Cont.pair_after (⟦s⟧) _ (⟦σ⟧)]
      _ = (⟦s.cond t f⟧) ∘' ⟦σ⟧ := rfl

-- Proposition 27 (Substitution property of the semantic function)
theorem deno_inst_eq : ⟦Subst.inst a⟧ = Ev.from ∘' (Cont.pair Cont.id' (⟦a⟧)) := by
  apply Cont.ext ∘ funext
  intro d
  apply funext
  intro τ
  apply funext
  intro x
  cases x with
  | z | s => rfl

-- Theorem 28 (Soundness)
theorem soundness {t v : Cx.nil ⊢ τ} : t ⇓ v → ⟦t⟧ = ⟦v⟧ := by
  intro e
  induction e with
  | true | false | zero | fn => rfl
  | succ _ t_v => exact congrArg (fun p ↦ Cont.flat _ ∘' p) t_v
  | @pred_zero t _ t_zero =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦t.pred⟧) ρ
      _ = Cont.flat (Nat.pred) ((⟦t⟧) ρ) := rfl
      _ = Cont.flat (Nat.pred) ((⟦.zero⟧) ρ) := by rw [t_zero]
      _ = (⟦.zero⟧) ρ := rfl
  | @pred_succ v t _ _ t_v_succ =>
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
      _ = (⟦.true⟧) ρ := rfl
  | @zero?_succ v t v' _ t_v_succ =>
    apply Cont.ext ∘ funext
    intro ρ
    have ⟨n, vn⟩ := v'.ground_nat
    calc (⟦t.zero?⟧) ρ
      _ = Cont.flat (Nat.zero?) ((⟦t⟧) ρ) := rfl
      _ = Cont.flat (Nat.zero?) ((⟦v.succ⟧) ρ) := by rw [t_v_succ]
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ ((⟦v⟧) ρ)) := rfl
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ ((⟦.from_nat n⟧) ρ)) := by rw [vn]
      _ = Cont.flat (Nat.zero?) (Cont.flat .succ (.some n)) := by rw [deno_ground_nat]
      _ = (⟦.false⟧) ρ := rfl
  | @cond_true _ s t f tv _ _ se te =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦s.cond t f⟧) ρ
      _ = (Cont.cond ((⟦s⟧) ρ) ((⟦t⟧) ρ, (⟦f⟧) ρ)) := rfl
      _ = (Cont.cond ((⟦.true⟧) ρ) ((⟦tv⟧) ρ, (⟦f⟧) ρ)) := by rw [se, te]
      _ = (⟦tv⟧) ρ := rfl
  | @cond_false _ s t f fv _ _ se fe =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦s.cond t f⟧) ρ
      _ = (Cont.cond ((⟦s⟧) ρ) ((⟦t⟧) ρ, (⟦f⟧) ρ)) := rfl
      _ = (Cont.cond ((⟦.false⟧) ρ) ((⟦t⟧) ρ, (⟦fv⟧) ρ)) := by rw [se, fe]
      _ = (⟦fv⟧) ρ := rfl
  | @app _ _ f a v e _ _ sf sv =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦f.app a⟧) ρ
      _ = ((⟦f⟧) ρ) ((⟦a⟧) ρ) := rfl
      _ = ((⟦e.fn⟧) ρ) ((⟦a⟧) ρ) := by rw [sf]
      _ = ((⟦e⟧) ∘' Ev.from ∘' (Cont.pair Cont.id' (⟦a⟧))) ρ := rfl
      _ = ((⟦e⟧) ∘' ⟦Subst.inst a⟧) ρ := by rw [deno_inst_eq]
      _ = (⟦e.sub (Subst.inst a)⟧) ρ := by rw [deno_subst_eq]
      _ = (⟦v⟧) ρ := by rw [sv]
  | @fix _ v f _ f_v =>
    apply Cont.ext ∘ funext
    intro ρ
    calc (⟦f.fix⟧) ρ
      _ = ((⟦f⟧) ρ).fix := rfl
      _ = ((⟦f⟧) ρ) ((⟦f⟧) ρ).fix := by rw [Cont.fix_is_fixed]
      _ = (⟦f.app f.fix⟧) ρ := rfl
      _ = (⟦v⟧) ρ := by rw [f_v]
