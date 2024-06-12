import «oPCF».Evaluation

inductive Con : Cx → Ty → Cx → Ty → Type
  | ι : Con Γ τ Γ τ
  | succ : Con Δ ν Γ .nat → Con Δ ν Γ .nat
  | pred : Con Δ ν Γ .nat → Con Δ ν Γ .nat
  | zero? : Con Δ ν Γ .nat → Con Δ ν Γ .bool
  | cond_s : Con Δ ν Γ .bool → Γ ⊢ τ → Γ ⊢ τ → Con Δ ν Γ τ
  | cond_t : Γ ⊢ .bool → Con Δ ν Γ τ → Γ ⊢ τ → Con Δ ν Γ τ
  | cond_f : Γ ⊢ .bool → Γ ⊢ τ → Con Δ ν Γ τ → Con Δ ν Γ τ
  | fn : Con Δ ν (Γ ∷ υ) τ → Con Δ ν Γ (υ ⇒ τ)
  | app_f : Con Δ ν Γ (υ ⇒ τ) → Γ ⊢ υ → Con Δ ν Γ τ
  | app_a : Γ ⊢ υ ⇒ τ → Con Δ ν Γ υ → Con Δ ν Γ τ
  | fix : Con Δ ν Γ (τ ⇒ τ) → Con Δ ν Γ τ

def Con.fill : Con Δ υ Γ τ → Δ ⊢ υ → Γ ⊢ τ
| ι           , t => t
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

instance : CoeFun (Con Δ υ Γ τ) (fun _ => Δ ⊢ υ → Γ ⊢ τ) where
  coe C := C.fill

def is_contextually_equivalent (t₀ t₁ : Δ ⊢ ν) : Type :=
  ∀ {τ}, τ.is_ground → ∀ (C : Con Δ ν .nil τ) (v : .nil ⊢ τ), (C t₀ ⇓ v) ⇔ (C t₁ ⇓ v)

infix:20 " ≅ᶜ " => is_contextually_equivalent
