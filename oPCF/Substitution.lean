import «PCF».Syntax

/-
We define the action of substitutions on the syntax of PCF in terms of renamings, which take
variables in one context to variables in another.
-/

def Ren Γ Δ := ∀ τ, Γ ∋ τ → Δ ∋ τ

def Var.ren (v : Γ ∋ τ) (r : Ren Γ Δ) := r τ v

/-
Renaming is reflexive and transitive.
-/

def Ren.id : Ren Γ Γ := fun _ ↦ Function.id

def Ren.comp (r₀₁ : Ren Γ₀ Γ₁) (r₁₂ : Ren Γ₁ Γ₂) : Ren Γ₀ Γ₂ :=
  fun _ x => (x.ren r₀₁).ren r₁₂

instance : Trans Ren Ren Ren where
  trans := Ren.comp

/-
Context extension acts functorially on renamings.
-/

def Ren.keep (r : Ren Γ Δ) (τ  : Ty) : Ren (Γ ∷ τ) (Δ ∷ τ) :=
  fun υ v => match v with
  | .z     => .z
  | .s _ x => (x.ren r).succ

infixl:70 " ∷ᵣ "  => Ren.keep

-- Context extension preserves the identity renaming.
theorem Ren.keep_id {Γ : Cx} (τ : Ty) : (@ Ren.id Γ) ∷ᵣ τ = Ren.id := by
  funext υ x; cases x with | _ => rfl

-- Context extension preserves the composition of renamings.
theorem Ren.keep_comp {r₀₁ : Ren Γ₀ Γ₁} {r₁₂ : Ren Γ₁ Γ₂}
  : (r₀₁ ⬝ r₁₂) ∷ᵣ τ = (r₀₁ ∷ᵣ τ) ⬝ (r₁₂ ∷ᵣ τ) := by
  funext τ x; cases x with | _ => rfl

def Ren.keeps (r : Ren Γ₀ Γ₁) : (Δ : Cx) → Ren (Γ₀ ++ Δ) (Γ₁ ++ Δ)
  | .nil      => r
  | .cons Δ τ => (r.keeps Δ).keep τ

infixl:70 " ++ᵣ "  => Ren.keeps

/-
Renaming extends to transforming terms in one context to terms in another.
-/

def Tm.ren (t : Γ ⊢ τ) (r : Ren Γ Δ) : Δ ⊢ τ :=
  match t with
  | .var τ x    => (x.ren r).tm
  | .true       => .true
  | .false      => .false
  | .zero       => .zero
  | .succ e     => (e.ren r).succ
  | .pred e     => (e.ren r).pred
  | .zero? e    => (e.ren r).zero?
  | .cond s t f => (s.ren r).cond (t.ren r) (f.ren r)
  | .fn e       => (e.ren (r ∷ᵣ _)).fn
  | .app f a    => (f.ren r).app (a.ren r)
  | .fix f      => (f.ren r).fix

/-
The functoriality of context extension on renamings allows us to prove that applying the
identity renaming and composite renamings to a term does exactly what we would expect.
-/

def Tm.ren_id_eq {t : Γ ⊢ τ} : t.ren Ren.id = t := by
  induction t with
  | fn e Φ =>
    calc (e.ren (Ren.id ∷ᵣ _)).fn
      _ = (e.ren Ren.id).fn := by rw [Ren.keep_id]
      _ = e.fn               := by rw [Φ]
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa       => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

theorem Ren.ren_comp_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}, t.ren (σ₀₁ ⬝ σ₁₂) = (t.ren σ₀₁).ren σ₁₂ := by
  induction t with
  | @fn _ τ υ e Φ =>
    intro _ _ r₀₁ r₁₂
    calc (e.ren ((r₀₁ ⬝ r₁₂) ∷ᵣ τ)).fn
      _ = (e.ren ((r₀₁ ∷ᵣ τ) ⬝ (r₁₂ ∷ᵣ τ))).fn   := by rw [Ren.keep_comp]
      _ = ((e.ren (r₀₁ ∷ᵣ τ)).ren (r₁₂ ∷ᵣ τ)).fn := by rw [Φ]
  | var | true | false | zero => intros; rfl
  | succ _ Φ | pred _ Φ | zero? _ Φ | fix _ Φ => exact congrArg _ Φ
  | app _ _ Φf Φa       => exact congrArg2 _ Φf Φa
  | cond _ _ _ Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

/-
Renaming can also be used to weaken variables in a context and rebase variables in identical contexts.
-/

def Ren.weak {τ  : Ty} : Ren Γ (Γ ∷ τ) := Var.s

theorem Ren.ren_weak_exch {r : Ren Γ₀ Γ₁} : r ⬝ Ren.weak = Ren.weak ⬝ (r ∷ᵣ υ) := by
  funext τ x
  rfl

def Ren.weaks : (Δ : Cx) → Ren Γ (Γ ++ Δ)
  | .nil      => id
  | .cons Δ _ => fun υ x ↦ weak υ (weaks Δ υ x)

def Ren.cast : (Γ = Δ) → Ren Γ Δ := by
  intro p; induction p; exact Ren.id

/-
We define substitutions on the syntax of PCF, which takes variables in one context to terms
in another.
-/

def Sb Γ Δ := ∀ τ, Γ ∋ τ → Δ ⊢ τ

def Var.sub (v : Γ ∋ τ) (σ : Sb Γ Δ) := σ τ v

/-
Context extension acts on substitutions. (We leave functoriality until later.)
-/

def Sb.keep (σ : Sb Γ Δ) (τ : Ty) : Sb (Γ ∷ τ) (Δ ∷ τ) :=
  fun _ x => match x with
  | .z     => .var τ .z
  | .s _ x => (x.sub σ).ren .s

infixl:70 " ∷ₛ "  => Sb.keep

def Sb.keeps (σ : Sb Γ₀ Γ₁) : (Δ : Cx) → Sb (Γ₀ ++ Δ) (Γ₁ ++ Δ)
  | .nil      => σ
  | .cons Δ τ => (σ.keeps Δ).keep τ

infixl:70 " ++ₛ "  => Sb.keeps

theorem Sb.keeps_keep_assoc (σ : Sb Γ₀ Γ₁) {Δ : Cx} (τ : Ty) : (σ ++ₛ Δ) ∷ₛ τ = σ ++ₛ (Δ ∷ τ) := by
  funext υ x; rfl

/-
Substitution extends to transforming terms in one context to terms in another.
-/

def Tm.sub (t : Γ ⊢ τ) (σ : Sb Γ Δ) : Δ ⊢ τ :=
  match t with
  | .var _ x    => x.sub σ
  | .true       => .true
  | .false      => .false
  | .zero       => .zero
  | .succ t     => (t.sub σ).succ
  | .pred t     => (t.sub σ).pred
  | .zero? t    => (t.sub σ).zero?
  | .cond s t f => (s.sub σ).cond (t.sub σ) (f.sub σ)
  | .fn e       => (e.sub (σ ∷ₛ _)).fn
  | .app f a    => (f.sub σ).app (a.sub σ)
  | .fix f      => (f.sub σ).fix

/-
Substitution is reflexive and transitive.
-/

def Sb.id : Sb Γ Γ := fun τ x => .var τ x

def Sb.comp (σ₀₁ : Sb Γ₀ Γ₁) (σ₁₂ : Sb Γ₁ Γ₂) : Sb Γ₀ Γ₂ :=
  fun _ x => (x.sub σ₀₁).sub σ₁₂

instance : Trans Sb Sb Sb where
  trans := Sb.comp

/-
Substitution and weakening commute. This takes a decent amount of preparation to prove.
-/

-- The following lemmas allow manipulating variables and renamings in the presence of type casts.
private theorem cx_eq_cons {Γ Δ : Cx} (p : Γ = Δ) (υ : Ty) : Γ ∷ υ = Δ ∷ υ := by
  rw [p]

private theorem cx_comp_eq_cx {Γ Δ : Cx} (h : Γ ∷ τ = Δ ∷ υ) : Γ = Δ := by
  cases h with | refl => rfl

private theorem cx_comp_eq_ty {Γ Δ : Cx} (h : Γ ∷ τ = Δ ∷ υ) : τ = υ := by
  cases h with | refl => rfl

private theorem Tm.ren_cast_rfl (t : Γ ⊢ τ) : t.ren (Ren.cast rfl) = t := Tm.ren_id_eq

private theorem Var.ren_cast_z (h : Γ ∷ υ = Δ ∷ υ) : (Var.z).ren (Ren.cast h) = Var.z := by
  cases h with | refl => rfl

private theorem Var.ren_cast_s (h : Γ = Δ)
  : (Var.s τ x).ren (Ren.cast (cx_eq_cons h υ)) = Var.s τ (x.ren (Ren.cast h)) := by
  cases h with | refl => rfl

private theorem Ren.cast_keep_eq
  : (Ren.cast h ∷ᵣ υ : Ren (Γ ∷ υ) (Δ ∷ υ)) = Ren.cast (cx_eq_cons h υ) := by
  funext τ x; induction h with | refl => cases x with | _ => rfl

-- Shorthand for weakening with an arbitrary context appension.
private def weak' {Γ} {τ} {Δ} : Ren (Γ ++ Δ) (Γ ∷ τ ++ Δ) := Ren.weak ++ᵣ Δ

-- The application of substitution and generalized weakening commutes on variables.
private theorem sub_weak'_exchange_var {Δ} : ∀ {Γ} {Γ₀ Γ₁ : Cx} {σ : Sb Γ₀ Γ₁} {τ'}
  {h : Γ = Γ₀ ++ Δ} {ν} {x : Γ ∋ ν},
    (((x.ren (Ren.cast h)).ren (Ren.id ++ᵣ Δ)).sub (σ ++ₛ Δ)).ren weak'
  = (((x.ren (Ren.cast h)).ren (Ren.id ++ᵣ Δ)).ren weak').sub ((σ ∷ₛ τ') ++ₛ Δ)
  := by
  induction Δ with
  | nil => intros; rfl
  | cons Δ τ Φ =>
    intro Γ Γ₀ Γ₁ σ τ' h ν x
    cases x with
    | z => induction cx_comp_eq_ty h with | refl => rw [Var.ren_cast_z]; rfl
    | @s Γ υ _ x =>
      induction cx_comp_eq_ty h with
      | refl =>
        rw [Var.ren_cast_s (cx_comp_eq_cx h)]
        let y := ((x.ren (Ren.cast (cx_comp_eq_cx h)))).ren (Ren.id ++ᵣ Δ)
        calc  (y.succ.sub (σ ++ₛ (Δ ∷ υ))).ren weak'
          _ = ((y.sub (σ ++ₛ Δ)).ren Ren.weak).ren (weak' ∷ᵣ υ)     := rfl
          _ = (y.sub (σ ++ₛ Δ)).ren (Ren.weak ⬝ (weak' ∷ᵣ υ))       := by rw [Ren.ren_comp_eq]
          _ = (y.sub (σ ++ₛ Δ)).ren (weak' ⬝ Ren.weak)              := by rw [Ren.ren_weak_exch]
          _ = ((y.sub (σ ++ₛ Δ)).ren weak').ren Ren.weak            := by rw [Ren.ren_comp_eq]
          _ = ((y.ren weak').sub ((σ ∷ₛ τ') ++ₛ Δ)).ren Ren.weak    := by rw [Φ]
          _ = (y.succ.ren (weak' ∷ᵣ υ)).sub (σ ∷ₛ τ' ++ₛ (Δ ∷ υ))   := rfl

-- The application of substitution and generalized weakening commutes on terms.
private theorem sub_weak'_exchange_tm {t : Γ ⊢ τ} : ∀ Δ {Γ₀ Γ₁ : Cx}
  {h : Γ = Γ₀ ++ Δ} {σ : Sb Γ₀ Γ₁} {τ'},
    (((t.ren (Ren.cast h)).ren (Ren.id ++ᵣ Δ)).sub (σ ++ₛ Δ)).ren weak'
  = (((t.ren (Ren.cast h)).ren (Ren.id ++ᵣ Δ)).ren weak').sub ((σ ∷ₛ τ') ++ₛ Δ)
  := by
  induction t with
  | @fn Γ' υ τ e Φ =>
    intro Δ Γ₀ Γ₁ h σ τ'
    let y₀ := ((e.ren (Ren.cast h ∷ᵣ υ)).ren (Ren.id ++ᵣ (Δ ∷ υ)))
    let y₁ := ((e.ren (Ren.cast (cx_eq_cons h υ))).ren (Ren.id ++ᵣ (Δ ∷ υ)))
    show ((y₀.sub _).ren _).fn = ((y₀.ren _).sub _).fn
    dsimp [y₀]; rw [Ren.cast_keep_eq]
    show ((y₁.sub _).ren _).fn = ((y₁.ren _).sub _).fn
    congr
    exact Φ (Δ ∷ υ)
  | var υ x => intros; exact sub_weak'_exchange_var
  | true | false | zero => intros; rfl
  | succ _ Φ | pred _ Φ | zero? _ Φ | fix _ Φ => intros; exact congrArg _ (Φ _)
  | app _ _ Φf Φa       => intros; exact congrArg2 _ (Φf _) (Φa _)
  | cond _ _ _ Φs Φt Φf => intros; exact congrArg3 _ (Φs _) (Φt _) (Φf _)

-- The application of substitution and weakening commutes on terms.
private def sub_weak_exchange {t : Γ₀ ⊢ τ} {σ : Sb Γ₀ Γ₁}
  : (t.sub σ).ren Ren.weak = (t.ren Ren.weak).sub (σ ∷ₛ υ) := by
  have p := @sub_weak'_exchange_tm Γ₀ τ t Cx.nil Γ₀ Γ₁ rfl σ υ
  rw [Tm.ren_cast_rfl] at p
  change ((t.ren Ren.id).sub _).ren _ = ((t.ren Ren.id).ren _).sub _ at p
  rw [Tm.ren_id_eq] at p
  exact p

/-
Context extension acts functorially on substitutions.
-/

-- Context extension preserves the identity substitution.
def Sb.keep_id : (@ Sb.id Γ) ∷ₛ τ = Sb.id := by
  funext _ x; cases x with | _ => rfl

-- Context extension preserves the composition of substitutions.
def Sb.keep_comp {σ₀₁ : Sb Γ₀ Γ₁} {σ₁₂ : Sb Γ₁ Γ₂}
  : (σ₀₁ ⬝ σ₁₂) ∷ₛ τ = (σ₀₁ ∷ₛ τ) ⬝ (σ₁₂ ∷ₛ τ) := by
  funext υ x
  cases x with
  | z => rfl
  | s => exact sub_weak_exchange

/-
The functoriality of context extension on substitutions allows us to prove that applying the
identity substitution and composite substitutions to a term does exactly what we would expect.
-/

def Tm.sub_id_eq {t : Γ ⊢ τ} : t.sub (Sb.id) = t := by
  induction t with
  | fn e Φ =>
    calc  e.fn.sub Sb.id
      _ = (e.sub (Sb.id ∷ₛ _)).fn := rfl
      _ = (e.sub Sb.id).fn        := by rw [Sb.keep_id]
      _ = e.fn                        := by rw [Φ]
  | var | true | false | zero                 => rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa                             => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf                       => apply congrArg3 _ Φs Φt Φf

def Tm.sub_comp_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {σ₀₁ : Sb Γ₀ Γ₁} {σ₁₂ : Sb Γ₁ Γ₂}, t.sub (σ₀₁ ⬝ σ₁₂) = (t.sub σ₀₁).sub σ₁₂ := by
  induction t with
  | @fn _ τ _ e Φ =>
    intro _ _ σ₀₁ σ₁₂
    calc   e.fn.sub (σ₀₁ ⬝ σ₁₂)
      _ = (e.sub ((σ₀₁ ⬝ σ₁₂) ∷ₛ τ)).fn          := rfl
      _ = (e.sub ((σ₀₁ ∷ₛ τ) ⬝ (σ₁₂ ∷ₛ τ))).fn   := by rw [Sb.keep_comp]
      _ = ((e.sub (σ₀₁ ∷ₛ τ)).sub (σ₁₂ ∷ₛ τ)).fn := by rw [Φ]
      _ = (e.fn.sub σ₀₁).sub σ₁₂                 := rfl
  | var | true | false | zero                 => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg  _ Φ
  | app f a Φf Φa                             => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf                       => exact congrArg3 _ Φs Φt Φf

/-
It's also useful to have a notion of heterogeneously composing a renaming with a substitution.
-/

def Ren.then (r : Ren Γ₀ Γ₁) (σ : Sb Γ₁ Γ₂) : Sb Γ₀ Γ₂ :=
  fun _ x => (x.ren r).sub σ

instance : Trans Ren Sb Sb where
  trans := Ren.then

def Sb.keep_then_eq {r : Ren Γ₀ Γ₁} {σ : Sb Γ₁ Γ₂} : (r ⬝ σ) ∷ₛ τ = ((r ∷ᵣ τ) ⬝ (σ ∷ₛ τ)) := by
  funext τ x; cases x with | _ => rfl

def Tm.sub_then_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {r : Ren Γ₀ Γ₁} {σ : Sb Γ₁ Γ₂}, t.sub (r ⬝ σ) = (t.ren r).sub σ := by
  induction t with
  | fn e Φ =>
    intro _ _ r σ
    calc  e.fn.sub (r ⬝ σ)
      _ = ((e.sub ((r ⬝ σ) ∷ₛ _)).fn)          := rfl
      _ = ((e.sub ((r ∷ᵣ _) ⬝ (σ ∷ₛ _))).fn)   := by rw [Sb.keep_then_eq]
      _ = (((e.ren (r ∷ᵣ _)).sub (σ ∷ₛ _)).fn) := by rw [Φ]
      _ = (e.fn.ren r).sub σ                   := rfl
  | var | true | false | zero                 => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg  _ Φ
  | app f a Φf Φa                             => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf                       => exact congrArg3 _ Φs Φt Φf

/-
While weakening adds a new variable to the context, instantiation removes a variable
(the outermost), replacing it with a specified term.
-/

def Sb.inst : (t : Γ ⊢ τ) → Sb (Γ ∷ τ) Γ :=
  fun a _ x => match x with
  | .z     => a
  | .s _ x => x.tm

def Sb.weak_inst_eq : Ren.weak ⬝ (Sb.inst a) = Sb.id := by
  funext _ x; cases x with | _ => rfl

def Tm.weak_inst_eq {t : Γ ⊢ τ} : (t.ren Ren.weak).sub (Sb.inst a) = t := by
  calc (t.ren Ren.weak).sub (Sb.inst a)
    _ = t.sub (Ren.weak ⬝ (Sb.inst a)) := by rw [Tm.sub_then_eq]
    _ = t.sub (Sb.id)                 := by rw [Sb.weak_inst_eq]
    _ = t                                 := by rw [Tm.sub_id_eq]

/-
Lastly, we directly characterize `keep` composed with `inst` as 'pushing' a term onto a substitution.
-/

def Sb.push (σ : Sb Γ Δ) {υ : Ty} (a : Δ ⊢ υ) : Sb (Γ ∷ υ) Δ :=
  fun _ x => match x with
  | .z     => a
  | .s _ x => x.sub σ

def Sb.push_eq {σ : Sb  Γ Δ} {υ : Ty} {a : Δ ⊢ υ} : σ.push a = (σ ∷ₛ υ) ⬝ Sb.inst a := by
  funext _ x
  cases x with
  | z     => rfl
  | s _ x =>
    calc  x.succ.sub (σ.push a)
      _ = x.sub σ                                     := rfl
      _ = ((x.sub σ).ren Ren.weak).sub (Sb.inst a) := by rw [Tm.weak_inst_eq]
      _ = x.succ.sub ((σ ∷ₛ υ) ⬝ Sb.inst a)        := rfl
