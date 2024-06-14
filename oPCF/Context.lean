import «oPCF».Evaluation

/-
To capture the observable characteristics of terms in PCF, we define a sort of evaluation contexts,
which take a term of a type in some context and produce a term of another type in another context.
-/

inductive Con : Cx → Ty → Cx → Ty → Type
  | id     : Con Γ τ Γ τ
  | comp   : Con Γ₀ τ₀ Γ₁ τ₁   → Con Γ₁ τ₁ Γ₂ τ₂   → Con Γ₀ τ₀ Γ₂ τ₂
  | sub    : Con Δ ν Γ τ       → Sb Γ Γ'           → Con Δ ν Γ' τ
  | succ   : Con Δ ν Γ .nat    → Con Δ ν Γ .nat
  | pred   : Con Δ ν Γ .nat    → Con Δ ν Γ .nat
  | zero?  : Con Δ ν Γ .nat    → Con Δ ν Γ .bool
  | cond_s : Con Δ ν Γ .bool   → Γ ⊢ τ             → Γ ⊢ τ       → Con Δ ν Γ τ
  | cond_t : Γ ⊢ .bool         → Con Δ ν Γ τ       → Γ ⊢ τ       → Con Δ ν Γ τ
  | cond_f : Γ ⊢ .bool         → Γ ⊢ τ             → Con Δ ν Γ τ → Con Δ ν Γ τ
  | fn     : Con Δ ν (Γ ∷ υ) τ → Con Δ ν Γ (υ ⇒ τ)
  | app_f  : Con Δ ν Γ (υ ⇒ τ) → Γ ⊢ υ             → Con Δ ν Γ τ
  | app_a  : Γ ⊢ υ ⇒ τ         → Con Δ ν Γ υ       → Con Δ ν Γ τ
  | fix    : Con Δ ν Γ (τ ⇒ τ) → Con Δ ν Γ τ

-- Filling the hole of an evaluation context with a term produces another term.
def Con.fill : Con Δ υ Γ τ → Δ ⊢ υ → Γ ⊢ τ
  | id          , t => t
  | comp C C'   , f => C'.fill (C.fill f)
  | sub C σ     , f => (C.fill f).sub σ
  | succ C      , t => (C.fill t).succ
  | pred C      , t => (C.fill t).pred
  | zero? C     , t => (C.fill t).zero?
  | cond_s C t f, s => (C.fill s).cond t f
  | cond_t s C f, t => s.cond (C.fill t) f
  | cond_f s t C, f => s.cond t (C.fill f)
  | fn C        , t => (C.fill t).fn
  | app_f C a   , f => (C.fill f).app a
  | app_a f C   , a => f.app (C.fill a)
  | fix C       , f => (C.fill f).fix

-- We enable juxtaposition notation for filling evaluation contexts.
instance : CoeFun (Con Δ υ Γ τ) (fun _ => Δ ⊢ υ → Γ ⊢ τ) where
  coe C := C.fill

/-
Evaluation contexts enable the notion of contextual equivalence, which holds for two terms
whenever they evaluate to identical values when 'observed' by any closed evaluation context.
-/

def ConEquiv (t₀ t₁ : Δ ⊢ τ) : Type :=
  ∀ γ, γ.IsGround → ∀ (C : Con Δ τ .nil γ) v, (C t₀ ⇓ v) ⇔ (C t₁ ⇓ v)

infix:75 " ≅ᶜ " => ConEquiv

/-
We also define a contextual preorder as a one-way variant of contextual equivalence.
-/

def ConPreord (t₀ t₁ : Δ ⊢ τ) : Type :=
  ∀ γ, γ.IsGround → ∀ (C : Con Δ τ .nil γ) v, (C t₀ ⇓ v) → C t₁ ⇓ v

infix:75 " ≤ᶜ " => ConPreord

def ConEquiv.from_preord : t₀ ≤ᶜ t₁ → t₁ ≤ᶜ t₀ → t₀ ≅ᶜ t₁ := by
  intro l r _ γ_is_ground C v
  exact ⟨l _ γ_is_ground C v, r _ γ_is_ground C v⟩
