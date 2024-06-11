import «oPCF».Syntax

/-
We define the action of substitutions on the syntax of PCF in terms of renamings, which take
variables in one context to variables in another.
-/

def Ren Γ Δ := ∀ τ, Γ ∋ τ → Δ ∋ τ

def Var.ren (v : Γ ∋ τ) (r : Ren Γ Δ) := r τ v

/-
Renaming is reflexive and transitive.
-/

def Ren.id' : Ren Γ Γ := fun _ ↦ id

def Ren.comp (r₀₁ : Ren Γ₀ Γ₁) (r₁₂ : Ren Γ₁ Γ₂) : Ren Γ₀ Γ₂ :=
  fun τ x => r₁₂ τ (r₀₁ τ x)

instance : Trans Ren Ren Ren where
  trans := Ren.comp

/-
Context extension, and hence appension, acts functorially on renamings.
-/

def Ren.keep (r : Ren Γ Δ) (τ  : Ty) : Ren (Γ ∷ τ) (Δ ∷ τ) :=
  fun υ v => match v with
  | .z => .z
  | .s τ x => .s τ (r τ x)

infixl:70 " ∷ᵣ "  => Ren.keep

-- Context extension preserves the identity renaming.
theorem Ren.keep_id {Γ : Cx} (τ : Ty) : (@ Ren.id' Γ) ∷ᵣ τ = Ren.id' := by
  funext υ x; cases x with | _ => rfl

-- Context extension preserves the composition of renamings.
theorem Ren.keep_comp {r₀₁ : Ren Γ₀ Γ₁} {r₁₂ : Ren Γ₁ Γ₂}
  : (r₀₁ ⬝ r₁₂) ∷ᵣ τ = (r₀₁ ∷ᵣ τ) ⬝ (r₁₂ ∷ᵣ τ) := by
  funext τ x; cases x with | z | s => rfl

def Ren.keeps (r : Ren Γ₀ Γ₁) : (Δ : Cx) → Ren (Γ₀ ++ Δ) (Γ₁ ++ Δ)
  | .nil => r
  | .cons Δ τ => (r.keeps Δ).keep τ

infixl:70 " ++ᵣ "  => Ren.keeps

/-
Renaming extends to transforming terms in one context to terms in another.
-/

def Tm.ren (t : Γ ⊢ τ) (r : Ren Γ Δ) : Δ ⊢ τ :=
  match t with
  | .var τ x => .var τ (x.ren r)
  | .true => .true
  | .false => .false
  | .zero => .zero
  | .succ e => (e.ren r).succ
  | .pred e => (e.ren r).pred
  | .zero? e => (e.ren r).zero?
  | .cond s t f => (s.ren r).cond (t.ren r) (f.ren r)
  | .fn e => (e.ren (r ∷ᵣ _)).fn
  | .app f a => (f.ren r).app (a.ren r)
  | .fix f => (f.ren r).fix

/-
The functoriality of context extension on renamings allows us to prove that applying the
identity renaming and composite renamings to a term does exactly what we would expect.
-/

def Tm.ren_id_eq {t : Γ ⊢ τ} : t.ren Ren.id' = t := by
  induction t with
  | fn e Φ =>
    calc (e.ren (Ren.id' ∷ᵣ _)).fn
      _ = (e.ren Ren.id').fn := by rw [Ren.keep_id]
      _ = e.fn := by rw [Φ]
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

theorem Ren.ren_comp_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}, t.ren (σ₀₁ ⬝ σ₁₂) = (t.ren σ₀₁).ren σ₁₂ := by
  induction t with
  | @fn _ τ υ e Φ =>
    intro _ _ r₀₁ r₁₂
    calc (e.ren ((r₀₁ ⬝ r₁₂) ∷ᵣ τ)).fn
      _ = (e.ren ((r₀₁ ∷ᵣ τ) ⬝ (r₁₂ ∷ᵣ τ))).fn := by rw [Ren.keep_comp]
      _ = ((e.ren (r₀₁ ∷ᵣ τ)).ren (r₁₂ ∷ᵣ τ)).fn := by rw [Φ]
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

/-
Renaming can also be used to weaken variables in a context.
-/

def Ren.weak {τ  : Ty} : Ren Γ (Γ ∷ τ) := Var.s

theorem Ren.ren_weak_exch {r : Ren Γ₀ Γ₁} : r ⬝ Ren.weak = Ren.weak ⬝ (r ∷ᵣ υ) := by
  funext τ x
  rfl

def Ren.weaks : (Δ : Cx) → Ren Γ (Γ ++ Δ)
  | .nil => id'
  | .cons Δ _ => fun υ x ↦ weak υ (weaks Δ υ x)

def Tm.tr_cx (t : Γ ⊢ τ) (p : Γ = Δ) : (Δ ⊢ τ) :=
  t.ren (fun _ x ↦ x.tr_cx p)

def Tm.tr_cx_rfl (t : Γ ⊢ τ) : t.tr_cx rfl = t := by
  exact Tm.ren_id_eq

/-
We define substitutions on the syntax of PCF, which takes variables in one context to terms
in another.
-/

def Subst Γ Δ := ∀ τ, Γ ∋ τ → Δ ⊢ τ

def Var.sub (v : Γ ∋ τ) (σ : Subst Γ Δ) := σ τ v

/-
Context extension, and hence appension, acts on substitutions.
-/

def Subst.keep (σ : Subst Γ Δ) (τ : Ty) : Subst (Γ ∷ τ) (Δ ∷ τ) :=
  fun _ x => match x with
  | .z => .var τ .z
  | .s τ x => (σ τ x).ren .s

infixl:70 " ∷ₛ "  => Subst.keep

def Subst.keeps (σ : Subst Γ₀ Γ₁) : (Δ : Cx) → Subst (Γ₀ ++ Δ) (Γ₁ ++ Δ)
  | .nil => σ
  | .cons Δ τ => (σ.keeps Δ).keep τ

infixl:70 " ++ₛ "  => Subst.keeps

theorem Subst.keeps_keep_assoc (σ : Subst Γ₀ Γ₁) {Δ : Cx} (τ : Ty)
  : (σ ++ₛ Δ) ∷ₛ τ = σ ++ₛ (Δ ∷ τ) := by
  funext υ x
  rfl

/-
Substitution extends to transforming terms in one context to terms in another.
-/

def Tm.sub (t : Γ ⊢ τ) (σ : Subst Γ Δ) : Δ ⊢ τ :=
  match t with
  | .var _ x => x.sub σ
  | .true => .true
  | .false => .false
  | .zero => .zero
  | .succ t => (t.sub σ).succ
  | .pred t => (t.sub σ).pred
  | .zero? t => (t.sub σ).zero?
  | .cond s t f => (s.sub σ).cond (t.sub σ) (f.sub σ)
  | .fn e => (e.sub (σ ∷ₛ _)).fn
  | .app f a => (f.sub σ).app (a.sub σ)
  | .fix f => (f.sub σ).fix

/-
Substitution is reflexive and transitive.
-/

def Subst.id' : Subst Γ Γ := fun τ x => .var τ x

def Subst.comp (σ₀₁ : Subst Γ₀ Γ₁) (σ₁₂ : Subst Γ₁ Γ₂) : Subst Γ₀ Γ₂ :=
  fun τ x => (σ₀₁ τ x).sub σ₁₂

instance : Trans Subst Subst Subst where
  trans := Subst.comp

def Subst.weak {υ : Ty} : Subst Γ (Γ ∷ υ):=
  fun _ x => x.succ.tm

/-
Our next goal is to show that context extension acts functorially on substitutions (that is,
preserves identity and composition). This is surprisingly involved, as you're about to see.
-/

-- Context extension preserves the identity substitution.
def Subst.keep_id : (@ Subst.id' Γ) ∷ₛ τ = Subst.id' := by
  funext τ x
  cases x with | z | s => rfl

-- The following lemmas allow manipulating variables and renamings in the presence of type casts.
def cx_eq_cons {Γ Δ : Cx} (p : Γ = Δ) (υ : Ty) : Γ ∷ υ = Δ ∷ υ := by
  rw [p]

def cx_comp_eq_cx {Γ Δ : Cx} (h : Γ ∷ τ = Δ ∷ υ) : Γ = Δ := by
  cases h with | refl => rfl

def cx_comp_eq_ty {Γ Δ : Cx} (h : Γ ∷ τ = Δ ∷ υ) : τ = υ := by
  cases h with | refl => rfl

def Var.tr_cx_z
  (h : Γ ∷ υ = Δ ∷ υ) : (Var.z).tr_cx h = Var.z := by
  cases h with | refl => rfl

def Var.tr_cx_s
  (h : Γ = Δ) : (Var.s τ x).tr_cx (cx_eq_cons h υ) = Var.s τ (x.tr_cx h) := by
  cases h with | refl => rfl

def keep_tr_cx
  : ((fun _ x ↦ x.tr_cx h) ∷ᵣ υ : Ren (Γ ∷ υ) (Δ ∷ υ)) = fun _ x ↦ x.tr_cx (cx_eq_cons h υ) := by
  funext τ x
  induction h with | refl => cases x with | z | s => rfl

-- Shorthand for weakening with an arbitrary context appension.
def weak' {Γ} {τ} {Δ} : Ren (Γ ++ Δ) (Γ ∷ τ ++ Δ) := Ren.weak ++ᵣ Δ

-- The application of substitution and generalized weakening commutes on variables.
def sub_weak'_exchange_var {Δ} : ∀ {Γ} {Γ₀ Γ₁ : Cx} {σ : Subst Γ₀ Γ₁} {τ'} {h : Γ = Γ₀ ++ Δ} {ν} {x : Γ ∋ ν},
    (((x.tr_cx h).ren (Ren.id' ++ᵣ Δ)).sub (σ ++ₛ Δ)).ren weak'
  = (((x.tr_cx h).ren (Ren.id' ++ᵣ Δ)).ren weak').sub ((σ ∷ₛ τ') ++ₛ Δ)
    := by
    induction Δ with
    | nil => intros; rfl
    | cons Δ τ Φ =>
      intro Γ Γ₀ Γ₁ σ τ' h ν x
      cases x with
      | @z ν Γ => induction cx_comp_eq_ty h with | refl => rw [Var.tr_cx_z]; rfl
      | @s Γ υ ν x =>
        induction cx_comp_eq_ty h with
        | refl =>
          rw [Var.tr_cx_s (cx_comp_eq_cx h)]
          let y := ((x.tr_cx (cx_comp_eq_cx h))).ren (Ren.id' ++ᵣ Δ)
          calc  (y.succ.sub (σ ++ₛ (Δ ∷ υ))).ren weak'
            _ = ((y.sub (σ ++ₛ Δ)).ren Ren.weak).ren (weak' ∷ᵣ υ)     := rfl
            _ = (y.sub (σ ++ₛ Δ)).ren (Ren.weak ⬝ (weak' ∷ᵣ υ))       := by rw [Ren.ren_comp_eq]
            _ = (y.sub (σ ++ₛ Δ)).ren (weak' ⬝ Ren.weak)              := by rw [Ren.ren_weak_exch]
            _ = ((y.sub (σ ++ₛ Δ)).ren weak').ren Ren.weak            := by rw [Ren.ren_comp_eq]
            _ = ((y.ren weak').sub ((σ ∷ₛ τ') ++ₛ Δ)).ren Ren.weak    := by rw [Φ]
            _ = (y.succ.ren (weak' ∷ᵣ υ)).sub (σ ∷ₛ τ' ++ₛ (Δ ∷ υ)) := rfl

-- The application of substitution and generalized weakening commutes on terms.
def sub_weak'_exchange_tm {t : Γ ⊢ τ} : ∀ Δ {Γ₀ Γ₁ : Cx} {h : Γ = Γ₀ ++ Δ} {σ : Subst Γ₀ Γ₁} {τ'},
    (((t.tr_cx h).ren (Ren.id' ++ᵣ Δ)).sub (σ ++ₛ Δ)).ren weak'
  = (((t.tr_cx h).ren (Ren.id' ++ᵣ Δ)).ren weak').sub ((σ ∷ₛ τ') ++ₛ Δ)
  := by
  induction t with
  -- If `t` is a variable, this is exactly our variable exchange assumption.
  | var υ x =>
    intro Δ Γ₀ Γ₁ h σ τ'
    show ((((x.tr_cx h).ren (Ren.id' ++ᵣ Δ))).sub (σ ++ₛ Δ)).ren weak'
       = ((((x.tr_cx h).ren (Ren.id' ++ᵣ Δ))).ren weak').sub ((σ ∷ₛ τ') ++ₛ (Δ))
    rw [sub_weak'_exchange_var]
  -- If `t` is a function `e.fn`, we must prove our variable exchange assumption for a weakened context,
  -- allowing the induction hypothesis to be applied for the function body `e`.
  | @fn Γ' υ τ e Φ =>
    intro Δ Γ₀ Γ₁ h σ τ'
    calc (((e.fn.tr_cx h).ren (Ren.id' ++ᵣ Δ)).sub (σ ++ₛ Δ)).ren weak'
      _ = ((((e.ren ((fun _ x ↦ x.tr_cx h) ∷ᵣ υ)).ren (Ren.id' ++ᵣ (Δ ∷ υ))).sub
        (σ ++ₛ (Δ ∷ υ))).ren (weak'.keep _)).fn := rfl
      _ = ((((e.ren (fun _ x ↦ x.tr_cx (cx_eq_cons h υ))).ren (Ren.id' ++ᵣ (Δ ∷ υ))).sub
        ((σ ++ₛ (Δ ∷ υ)))).ren (weak'.keep _)).fn := by rw [keep_tr_cx]
      _ = ((((e.tr_cx (cx_eq_cons h υ)).ren (Ren.id' ++ᵣ (Δ ∷ υ))).sub (σ ++ₛ (Δ ∷ υ))).ren
        (weak'.keep _)).fn := rfl
      _ = ((((e.tr_cx (cx_eq_cons h υ)).ren (Ren.id' ++ᵣ (Δ ∷ υ))).ren (weak'.keep _)).sub
        ((σ.keep τ') ++ₛ (Δ ∷ υ))).fn := by congr; apply Φ (Δ ∷ υ)
      _ = ((((e.ren (fun _ x ↦ x.tr_cx (cx_eq_cons h υ))).ren ((Ren.id' ++ᵣ Δ).keep _)).ren
        (weak'.keep _)).sub (((σ.keep τ') ++ₛ Δ).keep υ)).fn := rfl
      _ = ((((e.ren (Ren.keep (fun _ x ↦ x.tr_cx h) _)).ren ((Ren.id' ++ᵣ Δ).keep _)).ren
        (weak'.keep _)).sub (((σ.keep τ') ++ₛ Δ).keep υ)).fn := by rw [keep_tr_cx]
      _ =  (((e.fn.tr_cx h).ren (Ren.id' ++ᵣ Δ)).ren weak').sub (σ ∷ₛ τ' ++ₛ Δ) := rfl
  | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ =>
    intro _ _ _ _ _ _
    exact congrArg _ (Φ _)
  | app f a Φf Φa =>
    intro _ _ _ _ _ _
    exact congrArg2 _ (Φf _) (Φa _)
  | cond s t f Φs Φt Φf =>
    intro _ _ _ _ _ _
    exact congrArg3 _ (Φs _) (Φt _) (Φf _)

-- The application of substitution and weakening commutes on terms.
def sub_weak_exchange {t : Γ₀ ⊢ τ} {σ : Subst Γ₀ Γ₁}  : (t.sub σ).ren .s = (t.ren .s).sub (σ ∷ₛ υ) := by
    have p
      : ((((t.tr_cx rfl).ren ((Ren.weaks Cx.nil) ++ᵣ Cx.nil)).sub (σ ++ₛ (Cx.nil ++ Cx.nil))).ren .s)
      = (((t.tr_cx rfl).ren ((Ren.weaks Cx.nil) ++ᵣ Cx.nil)).ren .s).sub ((σ ∷ₛ υ) ++ₛ (Cx.nil ++ Cx.nil))
      := @sub_weak'_exchange_tm Γ₀ τ t Cx.nil Γ₀ Γ₁ rfl σ υ
    rw [Tm.tr_cx_rfl] at p
    change ((t.ren Ren.id').sub σ).ren .s = ((t.ren Ren.id').ren .s).sub (σ ∷ₛ υ) at p
    rw [Tm.ren_id_eq] at p
    exact p

-- Context extension preserves the composition of substitutions.
def Subst.keep_comp {σ₀₁ : Subst Γ₀ Γ₁} {σ₁₂ : Subst Γ₁ Γ₂}
  : (σ₀₁ ⬝ σ₁₂) ∷ₛ τ = (σ₀₁ ∷ₛ τ) ⬝ (σ₁₂ ∷ₛ τ) := by
  funext υ x
  cases x with
  | z => calc Var.z.tm = Var.z.tm := rfl
  | s υ x =>
    show ((σ₀₁ υ x).sub σ₁₂).ren .s = ((σ₀₁ υ x).ren .s).sub (σ₁₂ ∷ₛ τ)
    exact sub_weak_exchange

/-
The functoriality of context extension on substitutions allows us to prove that applying the
identity substitution and composite substitutions to a term does exactly what we would expect.
-/

def Tm.sub_id_eq {t : Γ ⊢ τ} : t.sub (Subst.id') = t := by
  induction t with
  | fn e Φ =>
    calc e.fn.sub Subst.id'
      _ = (e.sub (Subst.id' ∷ₛ _)).fn := rfl
      _ = (e.sub Subst.id').fn        := by rw [Subst.keep_id]
      _ = e.fn                        := by rw [Φ]
  | var | true | false | zero => rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => apply congrArg3 _ Φs Φt Φf

def Tm.sub_comp_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {σ₀₁ : Subst Γ₀ Γ₁} {σ₁₂ : Subst Γ₁ Γ₂}, t.sub (σ₀₁ ⬝ σ₁₂) = (t.sub σ₀₁).sub σ₁₂ := by
  induction t with
  | @fn _ τ υ e Φ =>
    intro _ _ σ₀₁ σ₁₂
    calc e.fn.sub (σ₀₁ ⬝ σ₁₂)
      _ = (e.sub ((σ₀₁ ⬝ σ₁₂) ∷ₛ τ)).fn          := rfl
      _ = (e.sub ((σ₀₁ ∷ₛ τ) ⬝ (σ₁₂ ∷ₛ τ))).fn   := by rw [Subst.keep_comp]
      _ = ((e.sub (σ₀₁ ∷ₛ τ)).sub (σ₁₂ ∷ₛ τ)).fn := by rw [Φ]
      _ = (e.fn.sub σ₀₁).sub σ₁₂                 := rfl
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

/-
Instantiation is dual to weakening, and
-/

def Subst.inst : (t : Γ ⊢ τ) → Subst (Γ ∷ τ) Γ :=
  fun a τ x => match x with
  | .z => a
  | .s τ x => .var τ x

def Subst.amend (σ : Subst Γ₁ Γ₂) (r : Ren Γ₀ Γ₁) : Subst Γ₀ Γ₂ :=
  fun τ x => σ τ (r τ x)

def Subst.push (σ : Subst Γ Δ) {υ : Ty} (a : Δ ⊢ υ) : Subst (Γ ∷ υ) Δ :=
  fun τ x => match x with
  | .z => a
  | .s τ x => σ τ x

def sub_amend_keep_eq {r : Ren Γ₀ Γ₁} {σ : Subst Γ₁ Γ₂}
  : (σ.amend r) ∷ₛ τ = ((σ ∷ₛ τ).amend (r ∷ᵣ τ)) := by
  funext τ x
  cases x with
  | z | s => rfl

def sub_amend_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {r : Ren Γ₀ Γ₁} {σ : Subst Γ₁ Γ₂}, (t.ren r).sub σ = t.sub (σ.amend r) := by
  induction t with
  | fn e Φ =>
    intro _ _ r σ
    calc (e.fn.ren r).sub σ
      _ = (((e.ren (r ∷ᵣ _)).sub (σ ∷ₛ _)).fn) := rfl
      _ = ((e.sub ((σ ∷ₛ _).amend (r ∷ᵣ _))).fn) := by rw [Φ]
      _ = ((e.sub ((σ.amend r) ∷ₛ _)).fn) := by rw [sub_amend_keep_eq]
      _ = e.fn.sub (σ.amend r) := rfl
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

def inst_amend_weak_eq_id : (Subst.inst a).amend .s = Subst.id' := by
  funext τ x
  cases x with | z | s => rfl

def ren_weak_sub_inst_eq {t : Γ ⊢ τ} : (t.ren .s).sub (Subst.inst a) = t := by
  calc (t.ren .s).sub (Subst.inst a)
    _ = t.sub ((Subst.inst a).amend .s) := by rw [sub_amend_eq]
    _ = t.sub (Subst.id')               := by rw [inst_amend_weak_eq_id]
    _ = t                               := by rw [Tm.sub_id_eq]

def sub_push_eq_keep_inst {σ : Subst  Γ Δ} {υ : Ty} {a : Δ ⊢ υ} : σ.push a = (σ ∷ₛ υ) ⬝ Subst.inst a := by
  funext τ x
  cases x with
  | z => rfl
  | s τ x =>
    calc σ.push a τ x.s
      _ = σ τ x := rfl
      _ = ((σ τ x).ren .s).sub (Subst.inst a) := by rw [ren_weak_sub_inst_eq]
      _ = ((σ ∷ₛ υ) ⬝ Subst.inst a) τ x.s     := rfl
