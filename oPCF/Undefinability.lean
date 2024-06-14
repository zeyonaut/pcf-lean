import «oPCF».Extensionality

/-
While the denotational semantics defined here are 'sound' (in the sense that equality of denotation
implies contextual equivalence), they are not 'fully abstract', which is the converse.
-/

def FullAbstraction := ∀ {Γ τ} {t₀ t₁ : Γ ⊢ τ}, t₀ ≅ᶜ t₁ → ⟦t₀⟧ = ⟦t₁⟧

/-
To show this, we first define the parallel OR function, a pathological semantic value.
-/

def por_fn : (Flat Bool × Flat Bool) → (Flat Bool)
  | (.some true, _)            => .some true
  | (_, .some true)            => .some true
  | (.some false, .some false) => .some false
  | _                          => .none

def Mono.por : Mono (Flat Bool × Flat Bool) (Flat Bool) := ⟨
  por_fn,
  by {
    intro a b a_b
    obtain ⟨a₀, a₁⟩ := a
    obtain ⟨b₀, b₁⟩ := b
    obtain ⟨ab₀, ab₁⟩ := a_b
    cases a₀ with
    | none =>
      cases a₁ with
      | none => exact Domain.is_bot
      | some a₁ => cases a₁ with
        | true =>
          rw [← Flat.some_leq ab₁]
          cases b₀ with | none => exact ⋆ | some b₀ => cases b₀ with | _ => exact ⋆
        | false => exact Domain.is_bot
    | some a₀ =>
      cases a₀ with
      | true =>
        rw [← Flat.some_leq ab₀]
        cases a₁ with
        | some a₁ =>
          cases a₁ with
          | _ =>
            rw [← Flat.some_leq ab₁]
            exact ⋆
        | none =>
          cases b₁ with | none => exact ⋆ | some b₁ => cases b₁ with | _ => exact ⋆
      | false =>
        rw [← Flat.some_leq ab₀]
        cases a₁ with
        | none => exact Domain.is_bot
        | some a₁ =>
          rw [← Flat.some_leq ab₁]
          cases a₁ with
          | true =>
            cases b₀ with | none => exact ⋆ | some b₀ => cases b₀ with | _ => exact ⋆
          | false => exact ⋆
  }
⟩

def Cont.por : Cont (Flat Bool × Flat Bool) (Flat Bool) := Mono.por.promote_trivial

/-
In PCF, we can define the parallel OR test functions, which produce some
semantic boolean when their denotations are applied to a binary boolean operation.
-/

-- Diverging terms.
def loop {τ : Ty} : Γ ⊢ τ := Var.z.tm.fn.fix

def loop_den_eq : (⟦(loop : _ ⊢ τ)⟧) ρ = ⊥ := by
  let φ := fun (x : ↑⟦τ ty⟧) ↦ x ⊑ ⊥
  suffices lem : φ ((⟦Var.z.tm.fn⟧) ρ).fix from lem ⇄! Domain.is_bot
  apply scott

  -- 0-coclosed
  show ⊥ ⊑ ⊥
  exact ⋆

  -- ω-coclosed
  intro c φc
  show ⨆ c ⊑ ⊥
  apply Domain.is_least
  intro n
  show c n ⊑ ⊥
  exact φc n

  -- (.. ⊑ ⊥)-closed
  intro d φd
  show (⟦Var.z.tm⟧) (Ev.from (ρ, d)) ⊑ ⊥
  exact φd

theorem loop_diverges_at_bool {v : .nil ⊢ .bool} : loop ⇓ v → False := by
  intro eval
  have den_eq : (⟦loop⟧) Ev.nil = (⟦v⟧) Ev.nil := by rw [soundness eval]
  cases eval.result_is_value with
  | _ => rw [loop_den_eq] at den_eq; injection den_eq

-- Parallel OR test functions.
def por_test (b : Bool) : .nil ⊢ (.bool ⇒ .bool ⇒ .bool) ⇒ .bool :=
  (((Var.z.tm.app .true).app loop).cond
    (((Var.z.tm.app loop).app .true).cond
      (((Var.z.tm.app .false).app .false).cond
        loop
        (Tm.from_bool b))
      loop)
    loop).fn

/-
The two parallel OR test functions have unequal denotations, as witnessed by parallel OR.
-/

def por_curry : ↑⟦.bool ⇒ .bool ⇒ .bool ty⟧ := Cont.por.curry

def por_test_left_true : (⟦(Var.z.tm.app .true).app loop⟧) (Ev.nil.push por_curry) = Flat.some true := by
  show por_curry (Flat.some true) ((⟦loop⟧) (Ev.nil.push por_curry)) = Flat.some true
  rw [loop_den_eq]
  rfl

def por_test_right_true : (⟦(Var.z.tm.app loop).app .true⟧) (Ev.nil.push por_curry) = Flat.some true := by
  show por_curry ((⟦loop⟧) (Ev.nil.push por_curry)) (Flat.some true) = Flat.some true
  rw [loop_den_eq]
  rfl

def por_test_b_den_por_eq_b : ∀ {b}, (⟦por_test b⟧) Ev.nil por_curry = Flat.some b :=
   by {
    intro b

    -- We split up the term to help Lean's elaborator out a little.
    let ρ_por  := Ev.nil.push por_curry
    let inner  := cond' ((⟦(Var.z.tm.app .false).app .false⟧) ρ_por)
      ((⟦loop⟧) ρ_por, (⟦(Tm.from_bool b)⟧) ρ_por)
    let middle := cond' ((⟦(Var.z.tm.app loop).app .true⟧) ρ_por) (inner, (⟦loop⟧) ρ_por)
    let outer  := cond' ((⟦(Var.z.tm.app .true).app loop⟧) ρ_por) (middle,(⟦loop⟧) ρ_por)

    show outer = Flat.some b
    dsimp [inner, middle, outer]
    rw [loop_den_eq, por_test_left_true, por_test_right_true]

    show (⟦(Tm.from_bool b)⟧) ρ_por = Flat.some b
    rw [deno_ground_bool]
  }

theorem por_test_den_unequal : ⟦por_test false⟧ ≠ ⟦por_test true⟧ := by
  intro equal
  replace equal : (⟦por_test false⟧) Ev.nil por_curry = (⟦por_test true⟧) Ev.nil por_curry
    := by rw [equal]
  rw [por_test_b_den_por_eq_b, por_test_b_den_por_eq_b] at equal
  injection equal with equal
  injection equal

/-
However, the parallel OR test functions are contextually equivalent. To show this, we first find
a logical relation between semantic values that is preserved by the constructs of the language
but not by parallel OR. The following is one such logical relation, as described by Kurt Sieber
in "Reasoning about sequential functions via logical relations".
-/

def Ty.Magic : (τ : Ty) → ↑⟦τ ty⟧ → ↑⟦τ ty⟧ → ↑⟦τ ty⟧ → Prop
  | .bool | .nat => fun t₀ t₁ t₂ ↦ (t₀ = ⊥ ∨ t₁ = ⊥) ∨ (t₀ = t₂ ∧ t₁ = t₂)
  | .pow τ₀ τ₁   => fun t₀ t₁ t₂ ↦ ∀ a₀ a₁ a₂, τ₀.Magic a₀ a₁ a₂ → τ₁.Magic (t₀ a₀) (t₁ a₁) (t₂ a₂)

def Cx.Magic (Γ : Cx) (ρ₀ ρ₁ ρ₂ : ⟦Γ cx⟧) : Sort :=
  ∀ (τ : Ty) (x : Γ ∋ τ), τ.Magic (ρ₀ τ x) (ρ₁ τ x) (ρ₂ τ x)

def por_is_not_magical : ¬(.bool ⇒ .bool ⇒ .bool).Magic por_curry por_curry por_curry := by
  intro h
  replace h := h ⊥ (.some true) (.some false) (by left; left; rfl)
  replace h := h (.some true) ⊥ (.some false) (by left; right; rfl)
  cases h with
  | inl h => cases h with
    | _ => injection (by assumption)
  | inr h =>
    injection h.left with h
    injection h

/-
Now, we prove that this relation is preserved by the language. This should look extremely
similar to the proof of the fundamental property of formal approximation, because it is.
-/

def Ty.bottom_magic_left : (τ : Ty) → ∀ {a b}, τ.Magic ⊥ a b
  | .bool | .nat => by intros; left; left; exact rfl
  | .pow τ₀ τ₁   => by unfold Magic; intros; exact τ₁.bottom_magic_left

def Ty.bottom_magic_right : (τ : Ty) → ∀ {a b}, τ.Magic a ⊥ b
  | .bool | .nat => by intros; left; right; exact rfl
  | .pow τ₀ τ₁   => by unfold Magic; intros; exact τ₁.bottom_magic_right

noncomputable def Ty.supremum_magic : (τ : Ty) →  ∀ {c₀ c₁ c₂},
  (∀ n, τ.Magic (c₀ n) (c₁ n) (c₂ n)) → τ.Magic (⨆ c₀) (⨆ c₁) (⨆ c₂) := by
  intro τ c₀ c₁ c₂
  induction τ with
  | bool | nat =>
    intro mc
    by_cases ⨆ c₀ = .none
    case pos h₀ => left; left; exact h₀
    case neg h₀ =>
    by_cases ⨆ c₁ = .none
    case pos h₁ => left; right; exact h₁
    case neg h₁ =>
    have ⟨N₀, ec₀⟩ := TrivialDomain.eventually_const c₀
    have ⟨N₁, ec₁⟩ := TrivialDomain.eventually_const c₁
    have ⟨N₂, ec₂⟩ := TrivialDomain.eventually_const c₂
    have le_max_l   := Nat.le_max_left N₀ N₁ ⬝ Nat.le_max_left _ N₂
    have le_max_r   := Nat.le_max_right N₀ N₁⬝ Nat.le_max_left _ N₂
    have ins := mc (max (max N₀ N₁) N₂)
    have k₀ := Domain.eventually_const_sup ec₀ ⇄! Domain.is_bound c₀ N₀
    have k₁ := Domain.eventually_const_sup ec₁ ⇄! Domain.is_bound c₁ N₁
    have f₀ := ec₀ le_max_l ⇄! (c₀ • le_max_l)
    have f₁ := ec₁ le_max_r ⇄! (c₁ • le_max_r)
    cases ins with
    | inl ins =>
      cases ins with
      | inl ins => rw [f₀, ← k₀] at ins; exfalso; exact h₀ ins
      | inr ins => rw [f₁, ← k₁] at ins; exfalso; exact h₁ ins
    | inr ins =>
      have h₂ :=
        calc c₂.act (max (max N₀ N₁) N₂)
        _ = c₂.act N₂ := ec₂ (Nat.le_max_right _ _) ⇄! (c₂ • Nat.le_max_right _ _)
        _ = ⨆ c₂      := Domain.is_bound c₂ _       ⇄! Domain.eventually_const_sup ec₂
      rw [f₀, ← k₀, f₁, ← k₁, h₂] at ins
      right; exact ins
  | pow _ _ _ Φ₁ =>
    intro mc _ _ _ ma
    apply Φ₁
    intro n
    exact mc n _ _ _ ma

def Ty.Magic.succ : Ty.nat.Magic t₀ t₁ t₂
  → Ty.nat.Magic (Cont.flat (Nat.succ) t₀) (Cont.flat (Nat.succ) t₁) (Cont.flat (Nat.succ) t₂) := by
  intro m; cases m with
  | inl m => cases m with | _ m => rw [m]; left; try {left; rfl}; try {right; rfl}
  | inr m => right; rw [m.left, m.right]; exact ⟨rfl, rfl⟩

def Ty.Magic.pred : Ty.nat.Magic t₀ t₁ t₂ → Ty.nat.Magic (Cont.pred t₀) (Cont.pred t₁) (Cont.pred t₂) := by
  intro m; cases m with
  | inl m => cases m with | _ m => rw [m]; left; try {left; rfl}; try {right; rfl}
  | inr m => right; rw [m.left, m.right]; exact ⟨rfl, rfl⟩

def Ty.Magic.zero? : Ty.nat.Magic t₀ t₁ t₂
  → Ty.bool.Magic (Cont.flat (Nat.zero?) t₀) (Cont.flat (Nat.zero?) t₁) (Cont.flat (Nat.zero?) t₂) := by
  intro m; cases m with
  | inl m => cases m with | _ m => rw [m]; left; try {left; rfl}; try {right; rfl}
  | inr m => right; rw [m.left, m.right]; exact ⟨rfl, rfl⟩

def Ty.Magic.cond {τ : Ty} {t₀ t₁ t₂ f₀ f₁ f₂ : ↑⟦τ ty⟧}
  : Ty.bool.Magic s₀ s₁ s₂ → τ.Magic t₀ t₁ t₂ → τ.Magic f₀ f₁ f₂
  → τ.Magic (Cont.cond.uncurry (s₀, (t₀, f₀)))
    (Cont.cond.uncurry (s₁, (t₁, f₁))) (Cont.cond.uncurry (s₂, (t₂, f₂))) := by
  intro ms mt mf
  cases ms
  case inl ms => cases ms with
    | inl ms => rw [ms]; exact bottom_magic_left τ
    | inr ms => rw [ms]; exact bottom_magic_right τ
  case inr ms =>
    rw [ms.left, ms.right]
    cases s₂ with
    | none => exact bottom_magic_left τ
    | some s₂ => cases s₂ with
      | true => exact mt
      | false => exact mf

def Ty.Magic.fix  : (τ ⇒ τ).Magic t₀ t₁ t₂ → τ.Magic (Cont.fix' t₀) (Cont.fix' t₁) (Cont.fix' t₂) := by
  intro mt
  apply scott3 τ.bottom_magic_left τ.supremum_magic
  intro d₀ d₁ d₂ md
  exact mt _ _ _ md

def Cx.Magic.nil : Cx.nil.Magic Ev.nil Ev.nil Ev.nil := by
  intro _ x; cases x

def Cx.Magic.push {Γ : Cx} {ρ₀ ρ₁ ρ₂} : Γ.Magic ρ₀ ρ₁ ρ₂ → τ.Magic d₀ d₁ d₂
  → (Γ ∷ τ).Magic (ρ₀.push d₀) (ρ₁.push d₁) (ρ₂.push d₂) := by
  intro mρ md
  intro τ x
  cases x with
  | z => exact md
  | s τ x => exact mρ τ x

-- The 'fundamental lemma' for the relation.
def Tm.magic (t : Γ ⊢ τ) : ∀ {ρ₀ ρ₁ ρ₂}, Γ.Magic ρ₀ ρ₁ ρ₂  → τ.Magic ((⟦t⟧) ρ₀) ((⟦t⟧) ρ₁) ((⟦t⟧) ρ₂) := by
  intro ρ₀ ρ₁ ρ₂ mρ
  induction t with
  | var τ x => exact mρ τ x
  | true | false | zero => right; exact ⟨rfl, rfl⟩
  | succ t Φ => exact (Φ mρ).succ
  | pred t Φ => exact (Φ  mρ).pred
  | zero? t Φ => exact (Φ mρ).zero?
  | app f a Φf Φa => exact (Φf mρ) _ _ _ (Φa mρ)
  | cond s t f Φs Φt Φf => exact (Φs mρ).cond (Φt mρ) (Φf mρ)
  | fix t Φ => exact (Φ mρ).fix
  | @fn Γ υ τ t Φ => intro _ _ _ ma; exact Φ (mρ.push ma)

/-
With the fundamental lemma, we can prove that parallel OR is undefinable.
-/

def por_is_undefinable {f : .nil ⊢ .bool ⇒ .bool ⇒  .bool} : ¬(⟦f⟧) Ev.nil = por_curry := by
  intro definable
  have f_magical := f.magic Cx.Magic.nil
  rw [definable] at f_magical
  exfalso
  exact por_is_not_magical f_magical


/-
Additionally, any function on which the parallel OR test functions evaluate must be denotationally
equal to parallel OR.
-/

-- We disable this option temporarily to mitigate a bug in the Lean linter.
set_option linter.unusedVariables false

def por_test_some_den : (por_test k).app f ⇓ Tm.from_bool n → (⟦f⟧) Ev.nil = por_curry := by
  let k' := k; cases k with
  | _ =>
  intro eval
  cases eval
  case app a b =>
  injection a.determinism Tm.IsValue.fn.self_evaluates with _ _ _ h
  rw [h] at b
  change
    ((f.app .true).app loop).cond
      (((f.app loop).app .true).cond
        (((f.app .false).app .false).cond
          loop
          (Tm.from_bool k'))
        loop)
      loop ⇓ Tm.from_bool n
    at b
  cases b
  case cond_false _ b => exfalso; exact loop_diverges_at_bool b
  case cond_true f_true_loop_eval_true b =>
  cases b
  case cond_false _ b => exfalso; exact loop_diverges_at_bool b
  case cond_true f_loop_true_eval_true b =>
  cases b
  case cond_true _ b => exfalso; exact loop_diverges_at_bool b
  case cond_false f_false_false_eval_false _ =>

  replace f_true_loop_eval_true : (⟦f⟧) Ev.nil (.some true) ((⟦loop⟧) Ev.nil) = .some true
    := congrFun (congrArg CoeFun.coe (soundness f_true_loop_eval_true)) Ev.nil
  replace f_loop_true_eval_true : (⟦f⟧) Ev.nil ((⟦loop⟧) Ev.nil) (.some true) = .some true
    := congrFun (congrArg CoeFun.coe (soundness f_loop_true_eval_true)) Ev.nil
  replace f_false_false_eval_false : (⟦f⟧) Ev.nil (.some false) (.some false) = .some false
    := congrFun (congrArg CoeFun.coe (soundness f_false_false_eval_false)) Ev.nil
  rw [loop_den_eq] at f_true_loop_eval_true f_loop_true_eval_true

  change ((⟦f⟧) Ev.nil).uncurry (_, _) = _ at f_true_loop_eval_true
  change ((⟦f⟧) Ev.nil).uncurry (_, _) = _ at f_loop_true_eval_true
  change ((⟦f⟧) Ev.nil).uncurry (_, _) = _ at f_false_false_eval_false

  have f_true_any_eq : ∀ n, ((⟦f⟧) Ev.nil).uncurry (.some true, n) = .some true := by
    intro n
    suffices lem : .some true ⊑ ((⟦f⟧) Ev.nil).uncurry (.some true, n)
      from (Flat.some_leq lem).symm
    cases n with
    | none =>
      calc .some true
        _ ⊑ .some true                                     := ⋆
        _ = ((⟦f⟧) Ev.nil).uncurry (.some true, ⊥)         := by rw [f_true_loop_eval_true]
        _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some true, ⊥)     := ((⟦f⟧) Ev.nil).uncurry • ⟨⋆, Domain.is_bot⟩
    | some n₁ => let n₁' := n₁; cases n₁ with | _ =>
      calc .some true
        _ ⊑ .some true                                     := ⋆
        _ = ((⟦f⟧) Ev.nil).uncurry (.some true, ⊥)         := by rw [f_true_loop_eval_true]
        _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some true, .some n₁') := ((⟦f⟧) Ev.nil).uncurry • ⟨⋆, Domain.is_bot⟩

  have f_any_true_eq : ∀ n, ((⟦f⟧) Ev.nil).uncurry (n, .some true) = .some true := by
    intro n
    suffices lem : .some true ⊑ ((⟦f⟧) Ev.nil).uncurry (n, .some true)
      from (Flat.some_leq lem).symm
    cases n with
    | none =>
      calc .some true
        _ ⊑ .some true                                     := ⋆
        _ = ((⟦f⟧) Ev.nil).uncurry (⊥, .some true)         := by rw [f_loop_true_eval_true]
        _ ⊑ ((⟦f⟧) Ev.nil).uncurry (⊥, .some true)     := ((⟦f⟧) Ev.nil).uncurry • ⟨Domain.is_bot, ⋆⟩
    | some n₁ => let n₁' := n₁; cases n₁ with | _ =>
      calc .some true
        _ ⊑ .some true                                     := ⋆
        _ = ((⟦f⟧) Ev.nil).uncurry (⊥, .some true)         := by rw [f_loop_true_eval_true]
        _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some n₁', .some true) := ((⟦f⟧) Ev.nil).uncurry • ⟨Domain.is_bot, ⋆⟩

  apply Cont.ext
  ext n₀ n₁
  cases n₀ with
  | some n₀ =>
    cases n₀ with
    | true =>
      cases n₁ with
      | some n₁ => cases n₁ with | _ => exact f_true_any_eq _
      | none => exact f_true_any_eq _
    | false =>
      show (⟦f⟧) Ev.nil (.some false) n₁ = por_curry (.some false) n₁
      cases n₁ with
      | some n₁ =>
        cases n₁ with
        | true => exact f_any_true_eq _
        | false =>
          show ((⟦f⟧) Ev.nil).uncurry (.some false, .some false) = Flat.some false
          rw [f_false_false_eval_false]
      | none =>
        show ((⟦f⟧) Ev.nil).uncurry (.some false, ⊥) = ⊥
        have hf := calc ((⟦f⟧) Ev.nil).uncurry (.some false, ⊥)
          _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some false, .some false)
            := ((⟦f⟧) Ev.nil).uncurry • ⟨⋆, Domain.is_bot⟩
          _ = .some false                                   := by rw [f_false_false_eval_false]
        have ht := calc ((⟦f⟧) Ev.nil).uncurry (.some false, ⊥)
          _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some false, .some true) := ((⟦f⟧) Ev.nil).uncurry • ⟨⋆, Domain.is_bot⟩
          _ = .some true                                   := by rw [f_any_true_eq _]
        exact Flat.under_eq ht hf (Bool.noConfusion)
  | none =>
    show (⟦f⟧) Ev.nil ⊥ n₁ = por_curry ⊥ n₁
    cases n₁ with
    | some n₁ =>
      cases n₁ with
      | true => exact f_any_true_eq _
      | false =>
        show ((⟦f⟧) Ev.nil).uncurry (⊥, .some false) = ⊥
        have hf := calc ((⟦f⟧) Ev.nil).uncurry (⊥, .some false)
          _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some false, .some _) := ((⟦f⟧) Ev.nil).uncurry • ⟨Domain.is_bot, ⋆⟩
          _ = .some false                                   := by rw [f_false_false_eval_false]
        have ht := calc ((⟦f⟧) Ev.nil).uncurry (⊥, .some false)
          _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some true, .some _) := ((⟦f⟧) Ev.nil).uncurry • ⟨Domain.is_bot, ⋆⟩
          _ = .some true                                   := by rw [f_true_any_eq _]
        exact Flat.under_eq ht hf (Bool.noConfusion)
    | none =>
      show ((⟦f⟧) Ev.nil).uncurry (⊥, ⊥) = ⊥
      have hf := calc ((⟦f⟧) Ev.nil).uncurry (⊥, ⊥)
        _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some false, .some false)
          := ((⟦f⟧) Ev.nil).uncurry • ⟨Domain.is_bot, Domain.is_bot⟩
        _ = .some false                                   := by rw [f_false_false_eval_false]
      have ht := calc ((⟦f⟧) Ev.nil).uncurry (⊥, ⊥)
        _ ⊑ ((⟦f⟧) Ev.nil).uncurry (.some true, ⊥) := ((⟦f⟧) Ev.nil).uncurry • ⟨Domain.is_bot, ⋆⟩
        _ = .some true                                   := by rw [f_true_any_eq _]
      exact Flat.under_eq ht hf (Bool.noConfusion)

-- Re-enable temporarily disabled linter option.
set_option linter.unusedVariables true

/-
As such, the parallel OR test functions must be contextually equivalent.
-/

noncomputable def por_test_con_equiv : por_test false ≅ᶜ por_test true := by
  intro not_con_equiv

  apply ConEquiv.from_preord

  show por_test false ≤ᶜ por_test true
  apply approx_implies_con_preord
  intro f f' f_f' n a_n
  have h := (por_test false).approx Subst.Approx.id'
  rw [Tm.sub_id_eq] at h
  have test_f_approx := h _ _ f_f'
  rw [a_n] at test_f_approx
  have k := test_f_approx _ rfl
  exfalso
  exact por_is_undefinable (por_test_some_den k)

  -- The other direction is identical.
  show por_test true ≤ᶜ por_test false
  apply approx_implies_con_preord
  intro f f' f_f' n a_n
  have h := (por_test true).approx Subst.Approx.id'
  rw [Tm.sub_id_eq] at h
  have test_f_approx := h _ _ f_f'
  rw [a_n] at test_f_approx
  have k := test_f_approx _ rfl
  exfalso
  exact por_is_undefinable (por_test_some_den k)

/-
Therefore, our denotational semantics is not fully abstract.
-/

theorem full_abstraction_fails : ¬FullAbstraction := by
  intro fully_abstract
  exact por_test_den_unequal (fully_abstract por_test_con_equiv)
