import «PCF».Flat
import «PCF».Context

/-
To construct a denotational semantics for PCF, we associate each syntactic object
with a semantic counterpart, called its denotation.
-/

/-
The denotation of a type is a domain whose elements are semantic values.
-/

-- Definition 22.
noncomputable def Ty.den : Ty → DomainType
  | .bool => ⟨Flat Bool, _, inferInstance⟩
  | .nat => ⟨Flat Nat, _, inferInstance⟩
  | .pow T₀ T₁ => by
    obtain ⟨T₀, O₀, D₀⟩ := T₀.den
    obtain ⟨T₁, O₁, D₁⟩ := T₁.den
    exact ⟨Cont T₀ T₁,  _ , inferInstance⟩

notation:max "⟦" τ " ty⟧" => Ty.den τ

instance (τ υ : Ty): CoeFun (⟦τ ⇒ υ ty⟧.carrier) (fun _ => ⟦τ ty⟧.carrier → ⟦υ ty⟧.carrier) where
  coe f := f.fn.act

noncomputable instance : TrivialDomain (⟦.bool ty⟧) := inferInstanceAs (TrivialDomain (Flat Bool))
noncomputable instance : TrivialDomain (⟦.nat ty⟧) := inferInstanceAs (TrivialDomain (Flat Nat))

/-
The denotation of a context is an environment, which assigns semantic values to each variable in scope.
-/

-- Definition 23.
def Ev (Γ : Cx) : Type := ∀ τ, Var Γ τ → ↑⟦τ ty⟧

notation:max "⟦" Γ " cx⟧" => Ev Γ

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
  is_least := fun c _ p {_} x ↦ Domain.is_least ⟨fun n ↦ c.act n _ x, fun i_j ↦ c.act' i_j _ x⟩
    (fun {_} ↦ p _ x)

-- Empty environment
def Ev.nil : ⟦Cx.nil cx⟧ := by
  intro _ x
  cases x

-- Extended environment
def Ev.push {Γ : Cx} (ρ : ⟦Γ cx⟧) {τ : Ty} (d : ↑⟦τ ty⟧) : ⟦Γ ∷ τ cx⟧ :=
  fun {τ} x ↦ match x with
  | .z => d
  | .s τ x => ρ τ x

-- Conversion between pairs and environments.
def Ev.from {Γ : Cx} {τ : Ty} : Cont (⟦Γ cx⟧ × ⟦τ ty⟧) (⟦Γ ∷ τ cx⟧) := ⟨
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
    intro _ _ x
    cases x with
    | _ => exact ⋆
  }
⟩

/-
The denotation of a term is a function that produces a semantic value when given an environment.
-/

noncomputable def Tm.den : (Γ ⊢ τ) → Cont (⟦Γ cx⟧) (⟦τ ty⟧)
  | .var τ x => ⟨⟨fun ρ ↦ ρ τ x, fun ρ₀_ρ₁ ↦ ρ₀_ρ₁ τ x⟩, ⋆⟩
  | .true => Cont.const (.some .true)
  | .false => Cont.const (.some .false)
  | .zero => Cont.const (.some 0)
  | .succ e => Cont.flat (Nat.succ) ∘ e.den
  | .pred e => Cont.pred ∘ e.den
  | .zero? e => Cont.flat (Nat.zero?) ∘ e.den
  | .cond s t f  => Cont.uncurry (Cont.cond) ∘ Cont.pair s.den (Cont.pair t.den f.den)
  | .fn e  => Cont.curry (e.den ∘ Ev.from)
  | .app f e => Cont.eval ∘ (Cont.pair f.den e.den)
  | .fix f => Cont.fix' ∘ f.den

notation:100 "⟦" t "⟧" => Tm.den t

/-
The denotations of renamings and substitutions are functions that transform one environment into another.
-/

noncomputable def Ren.den (r : Ren Γ Δ) : Cont (⟦Δ cx⟧) (⟦Γ cx⟧) :=
  ⟨⟨fun ρ _ x ↦ (⟦(x.ren r).tm⟧) ρ, fun ρ' _ x ↦ (⟦(x.ren r).tm⟧) • ρ'⟩, fun _ x ↦ (⟦(x.ren r).tm⟧).sub⟩

notation:100 "⟦" r "⟧" => Ren.den r

noncomputable def Sb.den (σ : Sb Γ Δ) : Cont (⟦Δ cx⟧) (⟦Γ cx⟧) :=
  ⟨⟨fun ρ _ x ↦ (⟦x.sub σ⟧) ρ, fun ρ' _ x ↦ (⟦x.sub σ⟧) • ρ'⟩, fun _ x ↦ (⟦x.sub σ⟧).sub⟩

notation:100 "⟦" σ "⟧" => Sb.den σ

/-
The denotations of evaluation contexts are functions that transform one term denotation into another.

We represent these higher order functions in an uncurried form for convenience.
-/

noncomputable def Con.den : Con Δ υ Γ τ → Cont (⟦Γ cx⟧ × Cont (⟦Δ cx⟧) (⟦υ ty⟧)) ⟦τ ty⟧
  | id         => Cont.uncurry Cont.id ∘' Cont.swap
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

/-
The denotation of ground values yields semantic values independently of the environment given.
-/

theorem Tm.from_bool_den_eq : ∀ {n}, (⟦.from_bool n⟧) ρ = (.some n)
  | .false | .true => rfl

theorem Tm.from_nat_den_eq : (⟦.from_nat n⟧) ρ = (.some n) := by
  induction n with
  | zero => rfl
  | succ n Φ =>
    calc (⟦.from_nat (n.succ)⟧) ρ
      _ = Cont.flat (.succ) ((⟦.from_nat n⟧) ρ) := rfl
      _ = Cont.flat (.succ) (.some n)           := by rw [Φ]
      _ = .some (n.succ)                        := rfl

/-
The denotation of a term renaming is compositional.
-/

theorem Tm.ren_den_eq (e : Γ ⊢ τ) : ∀ {Δ}, (r : Ren Γ Δ) → ⟦e.ren r⟧ = (⟦e⟧) ∘' (⟦r⟧) := by
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

theorem Ren.weak_den_eq : (⟦Ren.weak⟧) (Ev.from (ρ, d)) = ρ := by
  rfl

/-
The denotation of a term substitution is compositional.
-/

theorem Tm.sub_den_eq (e : Γ ⊢ τ) : ∀ {Δ}, (σ : Sb Γ Δ) → ⟦e.sub σ⟧ = (⟦e⟧) ∘' (⟦σ⟧) := by
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
              _ = ((⟦x.sub σ⟧) ∘' ⟦Ren.weak⟧) (Ev.from (ρ, d)) := by rw [(x.sub σ).ren_den_eq]
              _ = (⟦x.sub σ⟧) ((⟦Ren.weak⟧) (Ev.from (ρ, d))) := rfl
              _ = (⟦x.sub σ⟧) (ρ) := by rw [Ren.weak_den_eq]
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
      _ = _ ∘' Cont.pair (⟦s.sub σ⟧) (Cont.pair (⟦t.sub σ⟧) (⟦f.sub σ⟧))          := rfl
      _ = _ ∘' Cont.pair ((⟦s⟧) ∘' ⟦σ⟧) (Cont.pair ((⟦t⟧) ∘' ⟦σ⟧) ((⟦f⟧) ∘' ⟦σ⟧)) := by rw [Φs, Φt, Φf]
      _ = _ ∘' Cont.pair (⟦s⟧) ((Cont.pair (⟦t⟧) (⟦f⟧))) ∘' ⟦σ⟧
        := by rw [Cont.pair_after (⟦t⟧) (⟦f⟧) (⟦σ⟧), Cont.pair_after (⟦s⟧) _ (⟦σ⟧)]
      _ = (⟦s.cond t f⟧) ∘' ⟦σ⟧ := rfl

-- Proposition 27 (Substitution property of the semantic function)
theorem Sb.inst_den_eq : (⟦Sb.inst a⟧) ρ = (Ev.from (ρ, (⟦a⟧) ρ)) := by
  funext _ x; cases x with | _ => rfl

/-
The denotation of a evaluation context filling is compositional.
-/

def Con.fill_den_eq (C : Con Δ υ Γ τ) : ⟦C t⟧ = ((⟦C con⟧) ∘' Cont.swap).curry (⟦t⟧) := by
  induction C with
  | id               => rfl
  | comp C₀ C₁ Φ₀ Φ₁ => show ⟦C₁ (C₀ t)⟧ = _; rw [Φ₁, Φ₀]; rfl
  | sub C σ Φ        => show ⟦(C t).sub σ⟧ = _; rw [(C t).sub_den_eq, Φ]; rfl
  | succ _ Φ | pred _ Φ | zero? _ Φ | fix _ Φ => exact congrArg _ Φ
  | fn C Φ      => show Cont.curry ((⟦C t⟧) ∘ Ev.from) = _; rw [Φ]; rfl
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
