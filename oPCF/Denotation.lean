import «oPCF».Substitution
import «oPCF».Flat
import «oPCF».Context

structure DomainType : Type (i + 1) :=
  carrier : Type i
  order : Order carrier
  domain : Domain carrier

instance : Coe DomainType Type where
  coe D := D.carrier

instance (τ : DomainType) : Order (τ) := τ.order
instance (τ : DomainType) : Domain (τ) := τ.domain

-- Definition 22.
noncomputable def Sem : Ty → DomainType
  | .bool => ⟨Flat Bool, _, inferInstance⟩
  | .nat => ⟨Flat Nat, _, inferInstance⟩
  | .pow T₀ T₁ => by
    obtain ⟨T₀, O₀, D₀⟩ := Sem T₀
    obtain ⟨T₁, O₁, D₁⟩ := Sem T₁
    exact ⟨Cont T₀ T₁,  _ , inferInstance⟩

notation:max "⟦" τ " type⟧" => Sem τ

instance (τ υ : Ty): CoeFun (⟦τ ⇒ υ type⟧.carrier) (fun _ => ⟦τ type⟧.carrier → ⟦υ type⟧.carrier) where
  coe f := f.fn.act

-- Definition 23.
def Ev (Γ : Cx) : Type := ∀ τ, Var Γ τ → ↑⟦τ type⟧

notation:max "⟦" Γ " cx⟧" => Ev Γ

def Ev.nil : ⟦Cx.nil cx⟧ := by
  intro _ x
  cases x

def Ev.push {Γ : Cx} (ρ : ⟦Γ cx⟧) {τ : Ty} (d : ↑⟦τ type⟧) : ⟦Γ ∷ τ cx⟧ :=
  fun {τ} x ↦ match x with
  | .z => d
  | .s τ x => ρ τ x

noncomputable instance (Γ : Cx) : Order (⟦Γ cx⟧) where
  R := fun a b ↦ ∀ τ (x : Var Γ τ), a τ x ⊑ b τ x
  refl := fun _ _ ↦ ⋆
  trans := fun {_ _ _} p q {_} x ↦ p _ x ⬝ q _ x
  anti := fun p q ↦ funext fun _ ↦ (funext fun x ↦ p _ x ⇄! q _ x)

noncomputable instance (Γ : Cx) : Domain (⟦Γ cx⟧) where
  bot := fun _ _ ↦ ⊥
  sup := fun c _ x ↦ ⨆ ⟨fun n ↦ c.act n _ x, fun i_j ↦ c.act' i_j _ x⟩
  is_bot := fun _ _ ↦ Domain.is_bot
  is_bound := fun c {n} {_} x ↦ Domain.is_bound ⟨fun n ↦ c.act n _ x, fun i_j ↦ c.act' i_j _ x⟩ n
  is_least := fun c _ p {_} x ↦ Domain.is_least ⟨fun n ↦ c.act n _ x, fun i_j ↦ c.act' i_j _ x⟩ (fun {_} ↦ p _ x)

def Ev.from {Γ : Cx} {τ : Ty} : Cont (⟦Γ cx⟧ × ⟦τ type⟧) (⟦Γ ∷ τ cx⟧) := ⟨
  ⟨
    fun ⟨ρ, d⟩ υ x ↦ ρ.push d υ x,
    by {
      intro ⟨ρ₀, d₀⟩ ⟨ρ₁, d₁⟩ ⟨ρ', d'⟩ υ x
      cases x with
      | z => exact d'
      | s _ x => exact ρ' υ x
    }
  ⟩,
  by {
    intro c υ x
    cases x with
      | z => exact ⋆
      | s _ => exact ⋆
  }
⟩

noncomputable def denotation : (Γ ⊢ τ) → Cont (⟦Γ cx⟧) (⟦τ type⟧)
  | .var τ x => ⟨⟨fun ρ ↦ ρ τ x, fun ρ₀_ρ₁ ↦ ρ₀_ρ₁ τ x⟩, ⋆⟩
  | .true => Cont.const (.some true)
  | .false => Cont.const (.some false)
  | .zero => Cont.const (.some 0)
  | .succ e => Cont.flat (Nat.succ) ∘ denotation e
  | .pred e => Cont.pred ∘ denotation e
  | .zero? e => Cont.flat (Nat.zero?) ∘ denotation e
  | .cond s t f  => Cont.uncurry (Cont.cond) ∘ Cont.pair (denotation s) (Cont.pair (denotation t) (denotation f))
  | .fn e  => Cont.curry (denotation e ∘ Ev.from)
  | .app f e => Cont.eval ∘ (Cont.pair (denotation f) (denotation e))
  | .fix f => Cont.fix' ∘ denotation f

notation:100 "⟦" t "⟧" => denotation t

noncomputable def denotation_ren (r : Ren Γ Δ) : Cont (⟦Δ cx⟧) (⟦Γ cx⟧) :=
  ⟨⟨fun ρ _ x ↦ (⟦(x.ren r).tm⟧) ρ, fun ρ' _ x ↦ (⟦(x.ren r).tm⟧) • ρ'⟩, fun _ x ↦ (⟦(x.ren r).tm⟧).sub⟩

notation:100 "⟦" r "⟧" => denotation_ren r

noncomputable def denotation_subst (σ : Subst Γ Δ) : Cont (⟦Δ cx⟧) (⟦Γ cx⟧) :=
  ⟨⟨fun ρ _ x ↦ (⟦x.sub σ⟧) ρ, fun ρ' _ x ↦ (⟦x.sub σ⟧) • ρ'⟩, fun _ x ↦ (⟦x.sub σ⟧).sub⟩

notation:100 "⟦" σ "⟧" => denotation_subst σ

noncomputable def Con.den : Con Δ υ Γ τ → Cont (⟦Γ cx⟧ × Cont (⟦Δ cx⟧) (⟦υ type⟧)) ⟦τ type⟧
  | id'        => Cont.uncurry Cont.id' ∘' Cont.swap
  | comp C₀ C₁ => Cont.uncurry (Cont.curry (C₁.den ∘' Cont.swap)
                             ∘' Cont.curry (C₀.den ∘' Cont.swap)) ∘' Cont.swap
  | sub C σ => Cont.uncurry ((Cont.curry C.den) ∘' (⟦σ⟧))
  | succ C => Cont.flat (Nat.succ) ∘' C.den
  | pred C => Cont.pred ∘' C.den
  | zero? C => Cont.flat (Nat.zero?) ∘' C.den
  | fn C   => Cont.curry ((Cont.uncurry (Cont.curry C.den ∘' Ev.from)) ∘' Cont.assoc_swap_assoc)
  | cond_s C t f => Cont.uncurry (Cont.cond)
    ∘' Cont.pair C.den (Cont.pair ((⟦t⟧) ∘' Cont.fst) ((⟦f⟧) ∘' Cont.fst))
  | cond_t s C f => Cont.uncurry (Cont.cond)
    ∘' Cont.pair ((⟦s⟧) ∘' Cont.fst) (Cont.pair C.den ((⟦f⟧) ∘' Cont.fst))
  | cond_f s t C => Cont.uncurry (Cont.cond)
    ∘' Cont.pair ((⟦s⟧) ∘' Cont.fst) (Cont.pair ((⟦t⟧) ∘' Cont.fst) C.den)
  | app_f C a => Cont.eval ∘' (Cont.pair C.den ((⟦a⟧) ∘' Cont.fst))
  | app_a f C => Cont.eval ∘' (Cont.pair ((⟦f⟧) ∘' Cont.fst) C.den)
  | fix C => Cont.fix' ∘' C.den

notation:100 "⟦" C " con⟧" => Con.den C

theorem deno_ground_bool : ∀ {n}, (⟦.from_bool n⟧) ρ = (.some n)
  | .false | .true => rfl

theorem deno_ground_nat : (⟦.from_nat n⟧) ρ = (.some n) := by
  induction n with
  | zero => rfl
  | succ n Φ =>
    calc (⟦.from_nat (n.succ)⟧) ρ
      _ = Cont.flat (.succ) ((⟦.from_nat n⟧) ρ) := rfl
      _ = Cont.flat (.succ) (.some n)           := by rw [Φ]
      _ = .some (n.succ)                        := rfl

theorem deno_ren_eq (e : Γ ⊢ τ) : ∀ {Δ}, (r : Ren Γ Δ) → ⟦e.ren r⟧ = (⟦e⟧) ∘' (⟦r⟧) := by
  induction e with
  | fn e Φ =>
    intro _ r
    calc ⟦e.fn.ren r⟧
      _ = Cont.curry ((⟦e.ren (r.keep _)⟧) ∘ Ev.from) := rfl
      _ = Cont.curry (((⟦e⟧) ∘' ⟦r.keep _⟧) ∘ Ev.from) := by rw [Φ (r.keep _)]
      _ = (⟦e.fn⟧) ∘' ⟦r⟧ := by {
        apply Cont.ext ∘ funext
        intro ρ
        apply Cont.ext ∘ funext
        intro d
        have p : (⟦r.keep _⟧) (Ev.from (ρ, d)) = Ev.from ((⟦r⟧) ρ, d) := by {
          funext τ x
          cases x with
          | z => rfl
          | s x => rfl
        }
        calc ((((⟦e⟧) ∘' ⟦r.keep _⟧) ∘' Ev.from).curry ρ) d
          _ = (⟦e⟧) ((⟦r.keep _⟧) (Ev.from (ρ, d))) := rfl
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

theorem ren_s_eq : (⟦Ren.weak⟧) (Ev.from (ρ, d)) = ρ := by
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
          funext τ x
          cases x with
          | z => rfl
          | s τ x =>
            calc (⟦σ.keep _⟧) (Ev.from (ρ, d)) τ x.succ
              _ = (⟦(x.sub σ).ren Ren.weak⟧) (Ev.from (ρ, d)) := rfl
              _ = ((⟦x.sub σ⟧) ∘' ⟦Ren.weak⟧) (Ev.from (ρ, d)) := by rw [deno_ren_eq]
              _ = (⟦x.sub σ⟧) ((⟦Ren.weak⟧) (Ev.from (ρ, d))) := rfl
              _ = (⟦x.sub σ⟧) (ρ) := by rw [ren_s_eq]
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
theorem deno_inst_eq : (⟦Subst.inst a⟧) ρ = (Ev.from (ρ, (⟦a⟧) ρ)) := by
  funext _ x; cases x with | _ => rfl

def Con.fill_den_eq (C : Con Δ υ Γ τ) : ⟦C t⟧ = ((⟦C con⟧) ∘' Cont.swap).curry (⟦t⟧) := by
  induction C with
  | id' => rfl
  | comp C₀ C₁ Φ₀ Φ₁ => show ⟦C₁ (C₀ t)⟧ = _; rw [Φ₁, Φ₀]; rfl
  | sub C σ Φ => show ⟦(C t).sub σ⟧ = _; rw [deno_subst_eq, Φ]; rfl
  | fn C Φ => show Cont.curry ((⟦C t⟧) ∘ Ev.from) = _; rw [Φ]; rfl
  | succ _ Φ | pred _ Φ | zero? _ Φ | fix _ Φ => exact congrArg _ Φ
  | app_f C a Φ => show Cont.eval ∘' (Cont.pair (⟦C t⟧) (⟦a⟧)) = _; rw [Φ]; rfl
  | app_a f C Φ => show Cont.eval ∘' (Cont.pair (⟦f⟧) (⟦C t⟧)) = _; rw [Φ]; rfl
  | cond_s C e f Φ =>
    show Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦C t⟧) (Cont.pair (⟦e⟧) (⟦f⟧)) = _
    rw [Φ]; rfl
  | cond_t s C f Φ =>
    show Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s⟧) (Cont.pair (⟦C t⟧) (⟦f⟧)) = _
    rw [Φ]; rfl
  | cond_f s e C Φ =>
    show Cont.uncurry (Cont.cond) ∘' Cont.pair (⟦s⟧) (Cont.pair (⟦e⟧) (⟦C t⟧)) = _
    rw [Φ]; rfl
