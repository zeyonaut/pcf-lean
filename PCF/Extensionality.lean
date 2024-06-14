import «PCF».Soundness

/-
The contextual preorder is stated in terms of all contexts, but proving it can be done with
much less generality. To show this, we first define a test context for each ground value
which evaluates to true exactly when filled with a term which evaluates to that value.
-/

def Ty.IsGround.test_con {v : Γ ⊢ γ} : (γ.IsGround) → (v.IsValue) → Con Δ γ Δ .bool
  | .bool, .true   => .id
  | .bool, .false  => Con.id.cond_s .false .true
  | .nat,  .zero   => Con.id.zero?
  | .nat,  .succ n => Con.id.pred.comp (IsGround.nat.test_con n)

noncomputable def Ty.IsGround.test_con_true_iff {v : _ ⊢ γ}
  (γ_is_ground : γ.IsGround) (v_is_value : v.IsValue) (t) :
  (γ_is_ground.test_con v_is_value).fill t ⇓ .true ⇔ t ⇓ v := by
  constructor
  case mp =>
    intro test_t_true
    induction v_is_value with
    | true =>
      cases γ_is_ground with
      | bool => exact test_t_true
    | false =>
      cases γ_is_ground with
      | bool =>
        cases test_t_true with
        | cond_true _ false_true => injection false_true.determinism Tm.IsValue.false.evaluates
        | cond_false t_false => exact t_false
    | zero =>
      cases γ_is_ground with
      | nat => cases test_t_true with
        | zero?_zero t_zero => exact t_zero
    | succ n Φ =>
      cases γ_is_ground with
      | nat =>
        cases (Φ .nat _ test_t_true) with
        | pred _ t_v_succ => exact t_v_succ
    | fn => cases γ_is_ground
  case mpr =>
    intro t_v
    induction v_is_value with
    | true =>
      cases γ_is_ground with
      | bool => exact t_v
    | false =>
      cases γ_is_ground with
      | bool => exact .cond_false t_v Tm.IsValue.true.evaluates
    | zero =>
      cases γ_is_ground with
      | nat => exact Eval.zero?_zero t_v
    | succ n Φ =>
      cases γ_is_ground with
      | nat =>
        cases t_v.result_is_value with
        | succ v_is_value =>
          have pred_t_v := t_v.pred v_is_value
          have test_n_succ_t_pred_true := Φ .nat _ pred_t_v
          cases pred_t_v with
          | pred v_is_value t_v_succ =>
            show nat.test_con n t.pred ⇓ Tm.true
            exact test_n_succ_t_pred_true
    | fn => cases γ_is_ground

/-
To prove a contextual preordering of two terms, it suffices to prove that all bool-valued
contexts return true for the left term only if they return true for the right.
-/

noncomputable def ConPreord.from_fill
  : (∀ (C : Con ..), C t₀ ⇓ .true → C t₁ ⇓ .true) → t₀ ≤ᶜ t₁ := by
  intro con_fill γ γ_is_ground C v C_t₀_v
  let v_is_value := C_t₀_v.result_is_value
  let test : Con .nil γ .nil .bool := γ_is_ground.test_con (v_is_value)
  let test_true_iff_v := γ_is_ground.test_con_true_iff v_is_value
  have lem₀ := (test_true_iff_v (C t₀)).mpr
  have lem₁ := (test_true_iff_v (C t₁)).mp
  exact lem₁ (con_fill (C.comp test) (lem₀ C_t₀_v))

/-
If one terms' denotation approximates another, then the two are related by
the contextual preorder.
-/

noncomputable def approx_implies_con_preord (t₀ t₁ : .nil ⊢ τ) : (((⟦t₀⟧) Ev.nil) ◃ t₁) → t₀ ≤ᶜ t₁ := by
  intro t₀_t₁
  apply ConPreord.from_fill

  show ∀ (C : Con ..), C t₀ ⇓ .true → C t₁ ⇓ .true
  intro C C_t₀_true
  have den_C_t₀_true := soundness C_t₀_true
  have C_C := C.approx Sb.Approx.id
  have C_t₀_C_t₁ : (⟦C con⟧) (Ev.nil, ⟦t₀⟧) ◃ (C t₁).sub (Sb.id) := C_C (⟦t₀⟧) t₁ (by
    intro ρ σ _
    have eq_ρ : ρ = Ev.nil := by funext _ x; cases x
    have eq_σ : σ = Sb.id := by funext _ x; cases x
    rw [eq_ρ, eq_σ, Tm.sub_id_eq]
    exact t₀_t₁
  )
  have eq : (⟦C con⟧) (Ev.nil, ⟦t₀⟧) = (⟦C.fill t₀⟧) Ev.nil := by
    rw [Con.fill_den_eq]; rfl
  rw [den_C_t₀_true] at eq
  change ⟦C con⟧.fn.act (Ev.nil, ⟦t₀⟧) = Flat.some true at eq
  have C_t₁_true := C_t₀_C_t₁ true eq
  rw [Tm.sub_id_eq] at C_t₁_true
  exact C_t₁_true
