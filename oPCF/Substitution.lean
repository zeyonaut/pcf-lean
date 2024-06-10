import «oPCF».Syntax

def Ren Γ Δ := ∀ τ, Var Γ τ → Var Δ τ
def Reb Γ Δ := {τ : Ty} → Tm Γ τ → Tm Δ τ

def Ren.trans (r₀₁ : Ren Γ₀ Γ₁) (r₁₂ : Ren Γ₁ Γ₂) : Ren Γ₀ Γ₂ :=
  fun τ x => r₁₂ τ (r₀₁ τ x)

instance : Trans Ren Ren Ren where
  trans := Ren.trans

def Ren.id' : Ren Γ Γ := fun _ ↦ id

def Ren.weak {τ  : Ty} : Ren Γ (Γ ∷ τ) := Var.s

def Ren.weaks : (Δ : Cx) → Ren Γ (Γ.append Δ)
  | .nil => id'
  | .cons Δ _ => fun υ x ↦ weak υ (weaks Δ υ x)

def Ren.keep (r : Ren Γ Δ) {τ  : Ty} : Ren (Γ ∷ τ) (Δ ∷ τ) :=
  fun υ v => match v with
  | .z => .z
  | .s τ x => .s τ (r τ x)

def Ren.keeps (r : Ren Γ₀ Γ₁) : (Δ : Cx) → Ren (Γ₀.append Δ) (Γ₁.append Δ)
  | .nil => r
  | .cons Δ _ => (r.keeps Δ).keep

theorem Ren.id_keep_eq_keep {Γ : Cx} (τ : Ty)
  : Ren.id'.keep = (Ren.id' : Ren (Γ ∷ τ) (Γ ∷ τ)) := by
  funext υ x
  cases x with
  | z | s => rfl

theorem Ren.keeps_keep_eq_keep (r : Ren Γ₀ Γ₁) {Δ : Cx} (τ : Ty)
  : (r.keeps Δ).keep = r.keeps (Δ ∷ τ) := by
  funext υ x
  rfl

def Ren.swap {α β : Ty} : Ren (Γ ∷ β ∷ α) (Γ ∷ α ∷ β) := fun _ x ↦ match x with
  | .z => .s α .z
  | .s α .z => .z
  | .s _ (.s _ x) => x.succ.succ

def rename (r : Ren Γ Δ) : Reb Γ Δ :=
  fun dv => match dv with
  | .var τ x => .var τ (r τ x)
  | .true => .true
  | .false => .false
  | .zero => .zero
  | .succ e => (rename r e).succ
  | .pred e => (rename r e).pred
  | .zero? e => (rename r e).zero?
  | .cond s et ef => (rename r s).cond (rename r et) (rename r ef)
  | .fn e => (rename (r.keep) e).fn
  | .app f a => (rename r f).app (rename r a)
  | .fix f => (rename r f).fix

def Tm.ren (t : Γ ⊢ τ) (r : Ren Γ Δ) : Δ ⊢ τ := rename r t

def Tm.tr_cx (t : Γ ⊢ τ) (p : Γ = Δ) : (Δ ⊢ τ) :=
  t.ren (fun _ x ↦ x.tr_cx p)

def Tm.ren_id {t : Γ ⊢ τ} : t.ren Ren.id' = t := by
  induction t with
  | fn e Φ =>
    calc (e.ren Ren.id'.keep).fn
      _ = (e.ren Ren.id').fn := by rw [Ren.id_keep_eq_keep]
      _ = e.fn := by rw [Φ]
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

def Tm.tr_cx_rfl (t : Γ ⊢ τ) : t.tr_cx rfl = t := by
  exact Tm.ren_id

theorem Ren.keep_composite_eq {r₀₁ : Ren Γ₀ Γ₁} {r₁₂ : Ren Γ₁ Γ₂}
  : (r₀₁ ⬝ r₁₂).keep = (r₀₁.keep ⬝ r₁₂.keep : Ren (Γ₀ ∷ τ) (Γ₂ ∷ τ)) := by
  funext τ x
  cases x with | z | s => rfl

theorem Ren.weak_after_eq {r : Ren Γ₀ Γ₁} : r ⬝ Ren.weak = (Ren.weak ⬝ r.keep : Ren Γ₀ (Γ₁ ∷ υ)) := by
  funext τ x
  rfl

theorem ren_trans_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}, t.ren (σ₀₁ ⬝ σ₁₂) = (t.ren σ₀₁).ren σ₁₂ := by
  induction t with
  | @fn _ τ υ e Φ =>
    intro _ _ r₀₁ r₁₂
    calc (e.ren (r₀₁ ⬝ r₁₂).keep).fn
      _ = (e.ren (r₀₁.keep ⬝ r₁₂.keep)).fn := by rw [Ren.keep_composite_eq]
      _ = ((e.ren r₀₁.keep).ren r₁₂.keep).fn := by rw [Φ]
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

-- Definition 28 (Parallel closed substitution)
def Subst Γ Δ := ∀ τ, Var Γ τ → Tm Δ τ

-- TODO: Remove unused variants
def Subst.keep (σ : Subst Γ Δ) (τ : Ty) : Subst (Γ ∷ τ) (Δ ∷ τ) :=
  fun _ x => match x with
  | .z => .var τ .z
  | .s τ x => (σ τ x).ren .s

def Subst.keeps' (σ : Subst Γ₀ Γ₁) : (Δ : Cx) → Subst (Γ₀.append Δ) (Γ₁.append Δ)
  | .nil => σ
  | .cons Δ τ => (σ.keeps' Δ).keep τ

theorem Subst.keeps_keep_eq_keep (σ : Subst Γ₀ Γ₁) {Δ : Cx} (τ : Ty)
  : (σ.keeps' Δ).keep τ = σ.keeps' (Δ ∷ τ) := by
  funext υ x
  rfl

def subst (σ : Subst Γ Δ) : Reb Γ Δ :=
  fun {τ} e => match e with
  | .var _ x => σ τ x
  | .true => .true
  | .false => .false
  | .zero => .zero
  | .succ e => (subst σ e).succ
  | .pred e => (subst σ e).pred
  | .zero? e => (subst σ e).zero?
  | .cond s et ef => (subst σ s).cond (subst σ et) (subst σ ef)
  | .fn e => (subst (σ.keep _) e).fn
  | .app f a => (subst σ f).app (subst σ a)
  | .fix f => (subst σ f).fix

def Tm.sub (t : Γ ⊢ τ) (σ : Subst Γ Δ) : Δ ⊢ τ := subst σ t

def Subst.id' : Subst Γ Γ := fun τ x => .var τ x

def Subst.trans (σ₀₁ : Subst Γ₀ Γ₁) (σ₁₂ : Subst Γ₁ Γ₂) : Subst Γ₀ Γ₂ :=
  fun τ x => (σ₀₁ τ x).sub σ₁₂

instance : Trans Subst Subst Subst where
  trans := Subst.trans

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

def Subst.weak {υ : Ty} : Subst Γ (Γ ∷ υ):=
  fun _ x => x.succ.tm

set_option pp.proofs true

def id_keep_eq_id : (Subst.id' : Subst Γ Γ).keep τ = Subst.id' := by
  funext τ x
  cases x with | z | s => rfl

def sub_id_eq {t : Γ ⊢ τ} : t.sub (Subst.id') = t := by
  induction t with
  | fn e Φ =>
    calc e.fn.sub Subst.id'
      _ = (e.sub (Subst.id'.keep _)).fn := rfl
      _ = (e.sub Subst.id').fn := by rw [id_keep_eq_id]
      _ = e.fn := by rw [Φ]
  | var | true | false | zero => rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => apply congrArg3 _ Φs Φt Φf

def cx_eq_cons {Γ Δ : Cx} (p : Γ = Δ) (υ : Ty) : Γ ∷ υ = Δ ∷ υ := by
  rw [p]

def Var.tr_cx_z
  (h : Γ ∷ υ = Δ ∷ υ) : (Var.z).tr_cx h = Var.z := by
  cases h with | refl => rfl

def Var.tr_cx_s
  (h : Γ = Δ) : (Var.s τ x).tr_cx (cx_eq_cons h υ) = Var.s τ (x.tr_cx h) := by
  cases h with | refl => rfl

def keep_tr_cx
  : (Ren.keep fun _ x ↦ x.tr_cx h : Ren (Γ ∷ υ) (Δ ∷ υ)) = fun _ x ↦ x.tr_cx (cx_eq_cons h υ) := by
  funext τ x
  induction h with | refl => cases x with | z | s => rfl

-- NOTE: The signature of this lemma betrays the horror within.
def sub_ren_exchange {t : Γ ⊢ τ} : ∀ {Δ} Δ' {Γ₀ Γ₁ : Cx} (h : Γ = Γ₀.append Δ') {σ : Subst Γ₀ Γ₁} {τ'}
    (r : ∀ {Γ}, Ren (Γ.append (Δ.append Δ')) ((Γ ∷ τ').append (Δ.append Δ'))),
    (∀ ν (x : Var Γ ν),
      (σ.keeps'          (Δ.append Δ') ν      (((Ren.weaks Δ).keeps Δ' ν (x.tr_cx h)).tr_cx (Cx.append_append_eq Γ₀ Δ Δ'))).ren r
    = (σ.keep τ').keeps' (Δ.append Δ') ν (r ν (((Ren.weaks Δ).keeps Δ' ν (x.tr_cx h)).tr_cx (Cx.append_append_eq Γ₀ Δ Δ'))))
  → ((((t.tr_cx h).ren ((Ren.weaks Δ).keeps Δ')).tr_cx (Cx.append_append_eq Γ₀ Δ Δ')).sub (σ.keeps' (Δ.append Δ'))).ren r
    = ((((t.tr_cx h).ren ((Ren.weaks Δ).keeps Δ')).tr_cx (Cx.append_append_eq Γ₀ Δ Δ')).ren r).sub ((σ.keep τ').keeps' (Δ.append Δ'))
  := by
  induction t with
  | var υ x =>
    intro Δ Δ' Γ₀ Γ₁ h σ τ' r lem
    calc (σ.keeps' (Δ.append Δ') υ (((Ren.weaks Δ).keeps Δ' υ (x.tr_cx h)).tr_cx (Cx.append_append_eq Γ₀ Δ Δ'))).ren r
      _ = (σ.keep τ').keeps' (Δ.append Δ') υ (r υ (((Ren.weaks Δ).keeps Δ' υ (x.tr_cx h)).tr_cx (Cx.append_append_eq Γ₀ Δ Δ')))
      := by rw [lem]
  | @fn Γ' υ τ e Φ =>
    -- WARNING: Only suffering awaits.
    intro Δ Δ' Γ₀ Γ₁ h σ τ' r lem
    have lemₑ : ∀ (ν : Ty) (x : Var (Γ' ∷ υ) ν),
      (σ.keeps'          (Δ.append (Δ' ∷ υ)) ν           (((Ren.weaks Δ).keeps (Δ' ∷ υ) ν (x.tr_cx (cx_eq_cons h υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ)))).ren r.keep =
      (σ.keep τ').keeps' (Δ.append (Δ' ∷ υ)) ν (r.keep ν (((Ren.weaks Δ).keeps (Δ' ∷ υ) ν (x.tr_cx (cx_eq_cons h υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ)))) := by {
        intro ν x
        cases x with
        | z =>
          rw [Var.tr_cx_z]
          show (σ.keeps' (Δ.append (Δ' ∷ υ)) υ (Var.z.tr_cx _)).ren r.keep
            = (σ.keep τ').keeps' (Δ.append (Δ' ∷ υ)) υ (r.keep υ (Var.z.tr_cx _))
          rw [Var.tr_cx_z]
          rfl
        | s ν x =>
          -- First, we hide the casts under the constructor, allowing computations to proceed.
          show (σ.keeps'          (Δ.append (Δ' ∷ υ)) ν           (((Ren.weaks Δ).keeps (Δ' ∷ υ) ν ((Var.s ν x).tr_cx (cx_eq_cons h υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ)))).ren r.keep
             = (σ.keep τ').keeps' (Δ.append (Δ' ∷ υ)) ν (r.keep ν (((Ren.weaks Δ).keeps (Δ' ∷ υ) ν ((Var.s ν x).tr_cx (cx_eq_cons h υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ))))
          rw [Var.tr_cx_s h]
          show (σ.keeps'          (Δ.append (Δ' ∷ υ)) ν           ((Var.s ν ((Ren.weaks Δ).keeps Δ' ν (x.tr_cx h))).tr_cx (cx_eq_cons (Cx.append_append_eq Γ₀ Δ Δ') υ))).ren r.keep
             = (σ.keep τ').keeps' (Δ.append (Δ' ∷ υ)) ν (r.keep ν ((Var.s ν ((Ren.weaks Δ).keeps Δ' ν (x.tr_cx h))).tr_cx (cx_eq_cons (Cx.append_append_eq Γ₀ Δ Δ') υ)))
          rw [Var.tr_cx_s (Cx.append_append_eq Γ₀ Δ Δ')]
          let y := (((Ren.weaks Δ).keeps Δ' ν (x.tr_cx h)).tr_cx (Cx.append_append_eq Γ₀ Δ Δ'))
          let lem_x :
            (σ.keeps' (Δ.append Δ') ν y).ren r = (σ.keep τ').keeps' (Δ.append Δ') ν (r ν y)
            := lem ν x
          -- To understand what's going on below, it's helpful to draw the components of the equation as a
          -- diagram of context morphisms. The proof then follows by dissecting the diagram and proving its -- component equalities.
          calc   (σ.keeps' (Δ.append (Δ' ∷ υ)) ν (Var.s ν y)).ren r.keep
             _ = ((σ.keeps' (Δ.append Δ') ν y).ren Ren.weak).ren r.keep
              := rfl
             _ = (σ.keeps' (Δ.append Δ') ν y).ren (Ren.weak ⬝ r.keep)
              := by rw [ren_trans_eq]
             _ = (σ.keeps' (Δ.append Δ') ν y).ren (r ⬝ Ren.weak)
              := by rw [Ren.weak_after_eq]
             _ = ((σ.keeps' (Δ.append Δ') ν y).ren r).ren Ren.weak
              := by rw [ren_trans_eq]
             _ = ((σ.keep τ').keeps' (Δ.append Δ') ν (r ν y)).ren Ren.weak
              := by rw [lem_x]
             _ = (σ.keep τ').keeps' (Δ.append (Δ' ∷ υ)) ν (r.keep ν (Var.s ν y))
              := rfl
      }
    -- TODO: Clean this up.
    calc (((((e.fn).tr_cx h).ren ((Ren.weaks Δ).keeps Δ')).tr_cx (Cx.append_append_eq Γ₀ Δ Δ')).sub (σ.keeps' (Δ.append Δ'))).ren r
    _ = (((((e.ren (Ren.keep fun _ x ↦ x.tr_cx h)).ren ((Ren.weaks Δ).keeps Δ').keep).ren (Ren.keep fun _ x ↦ x.tr_cx (Cx.append_append_eq Γ₀ Δ Δ'))).sub ((σ.keeps' (Δ.append Δ')).keep υ)).ren r.keep).fn
      := rfl
    _ = (((((e.ren (fun _ x ↦ x.tr_cx (cx_eq_cons h υ))).ren ((Ren.weaks Δ).keeps Δ').keep).ren (fun _ x ↦ x.tr_cx (cx_eq_cons (Cx.append_append_eq Γ₀ Δ Δ') υ))).sub ((σ.keeps' (Δ.append Δ')).keep υ)).ren r.keep).fn
      := by rw [keep_tr_cx, keep_tr_cx]
    _ = (((((e.tr_cx (cx_eq_cons h υ)).ren ((Ren.weaks Δ).keeps (Δ' ∷ υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ))).sub ((σ.keeps' (Δ.append Δ')).keep υ)).ren r.keep).fn
      := rfl
    _ = (((((e.tr_cx (cx_eq_cons h υ)).ren ((Ren.weaks Δ).keeps (Δ' ∷ υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ))).sub (σ.keeps' (Δ.append Δ' ∷ υ))).ren r.keep).fn
      := by rw [Subst.keeps_keep_eq_keep]
    _ = (((((e.tr_cx (cx_eq_cons h υ)).ren ((Ren.weaks Δ).keeps (Δ' ∷ υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ))).sub (σ.keeps' (Δ.append (Δ' ∷ υ)))).ren r.keep).fn
      := rfl
    _ = (((((e.tr_cx (cx_eq_cons h υ)).ren ((Ren.weaks Δ).keeps (Δ' ∷ υ))).tr_cx (Cx.append_append_eq Γ₀ Δ (Δ' ∷ υ))).ren r.keep).sub ((σ.keep τ').keeps' (Δ.append (Δ' ∷ υ)))).fn
      := by {
        congr
        apply Φ (Δ' ∷ υ) (cx_eq_cons h υ) r.keep lemₑ
      }
    _ = (((((e.ren (fun _ x ↦ x.tr_cx (cx_eq_cons h υ))).ren (((Ren.weaks Δ).keeps Δ').keep)).ren (fun _ x ↦ x.tr_cx (cx_eq_cons (Cx.append_append_eq Γ₀ Δ Δ') υ))).ren r.keep).sub (((σ.keep τ').keeps' (Δ.append Δ')).keep υ)).fn
      := rfl
    _ = (((((e.ren (Ren.keep fun _ x ↦ x.tr_cx h)).ren (((Ren.weaks Δ).keeps Δ').keep)).ren (Ren.keep fun _ x ↦ x.tr_cx (Cx.append_append_eq Γ₀ Δ Δ'))).ren r.keep).sub (((σ.keep τ').keeps' (Δ.append Δ')).keep υ)).fn
      := by rw [keep_tr_cx, keep_tr_cx]
    _ = (((((e.fn).tr_cx h).ren ((Ren.weaks Δ).keeps Δ')).tr_cx (Cx.append_append_eq Γ₀ Δ Δ')).ren r).sub ((σ.keep τ').keeps' (Δ.append Δ'))
      := rfl
  | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ =>
    intro _ _ _ _ _ _ _ r lem
    exact congrArg _ (Φ _ _ r lem)
  | app f a Φf Φa =>
    intro _ _ _ _ _ _ _ r lem
    exact congrArg2 _ (Φf _ _ r lem) (Φa _ _ r lem)
  | cond s t f Φs Φt Φf =>
    intro _ _ _ _ _ _ _ r lem
    exact congrArg3 _ (Φs _ _ r lem) (Φt _ _ r lem) (Φf _ _ r lem)

def sub_weak_exchange {t : Γ₀ ⊢ τ} {σ : Subst Γ₀ Γ₁}  : (t.sub σ).ren .s = (t.ren .s).sub (σ.keep υ) := by
    have p
      : (((((t.tr_cx rfl).ren ((Ren.weaks Cx.nil).keeps Cx.nil)).tr_cx rfl).sub (σ.keeps' (Cx.nil.append Cx.nil))).ren .s)
      = ((((t.tr_cx rfl).ren ((Ren.weaks Cx.nil).keeps Cx.nil)).tr_cx rfl).ren .s).sub ((σ.keep υ).keeps' (Cx.nil.append Cx.nil))
      := @sub_ren_exchange Γ₀ τ t Cx.nil Cx.nil Γ₀ Γ₁ rfl σ υ .s (fun ν x ↦ rfl)
    rw [Tm.tr_cx_rfl, Tm.tr_cx_rfl] at p
    change ((t.ren Ren.id').sub σ).ren .s = ((t.ren Ren.id').ren .s).sub (σ.keep υ) at p
    rw [Tm.ren_id] at p
    exact p

def trans_keep_eq_id {σ₀₁ : Subst Γ₀ Γ₁} {σ₁₂ : Subst Γ₁ Γ₂} : (σ₀₁ ⬝ σ₁₂).keep τ = (σ₀₁.keep τ) ⬝ (σ₁₂.keep τ) := by
  funext υ x
  cases x with
  | z => calc Var.z.tm = Var.z.tm := rfl
  | s υ x =>
    show ((σ₀₁ υ x).sub σ₁₂).ren .s = ((σ₀₁ υ x).ren .s).sub (σ₁₂.keep τ)
    exact sub_weak_exchange

def sub_trans_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {σ₀₁ : Subst Γ₀ Γ₁} {σ₁₂ : Subst Γ₁ Γ₂}, t.sub (σ₀₁ ⬝ σ₁₂) = (t.sub σ₀₁).sub σ₁₂ := by
  induction t with
  | @fn _ τ υ e Φ =>
    intro _ _ σ₀₁ σ₁₂
    calc e.fn.sub (σ₀₁ ⬝ σ₁₂)
      _ = (e.sub ((σ₀₁ ⬝ σ₁₂).keep τ)).fn := rfl
      _ = (e.sub (σ₀₁.keep τ ⬝ σ₁₂.keep τ)).fn := by rw [trans_keep_eq_id]
      _ = ((e.sub (σ₀₁.keep τ)).sub (σ₁₂.keep τ)).fn := by rw [Φ]
      _ = (e.fn.sub σ₀₁).sub σ₁₂ := rfl
  | var | true | false | zero => intros; rfl
  | succ e Φ | pred e Φ | zero? e Φ | fix e Φ => exact congrArg _ Φ
  | app f a Φf Φa => exact congrArg2 _ Φf Φa
  | cond s t f Φs Φt Φf => exact congrArg3 _ Φs Φt Φf

def sub_amend_keep_eq {r : Ren Γ₀ Γ₁} {σ : Subst Γ₁ Γ₂}
  : (σ.amend r).keep τ = ((σ.keep τ).amend r.keep) := by
  funext τ x
  cases x with
  | z | s => rfl

def sub_amend_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {r : Ren Γ₀ Γ₁} {σ : Subst Γ₁ Γ₂}, (t.ren r).sub σ = t.sub (σ.amend r) := by
  induction t with
  | fn e Φ =>
    intro _ _ r σ
    calc (e.fn.ren r).sub σ
      _ = (((e.ren r.keep).sub (σ.keep _)).fn) := rfl
      _ = ((e.sub ((σ.keep _).amend r.keep)).fn) := by rw [Φ]
      _ = ((e.sub ((σ.amend r).keep _)).fn) := by rw [sub_amend_keep_eq]
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
    _ = t                               := by rw [sub_id_eq]

def sub_push_eq_keep_inst {σ : Subst  Γ Δ} {υ : Ty} {a : Δ ⊢ υ} : σ.push a = σ.keep υ ⬝ Subst.inst a := by
  funext τ x
  cases x with
  | z => rfl
  | s τ x =>
    calc σ.push a τ x.s
      _ = σ τ x := rfl
      _ = ((σ τ x).ren .s).sub (Subst.inst a) := by rw [ren_weak_sub_inst_eq]
      _ = (σ.keep υ ⬝ Subst.inst a) τ x.s     := rfl
