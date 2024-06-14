import «oPCF».Order

-- Definition 8 (Domain)
class Domain (α) [Order α] where
  bot : α
  sup : (c : Chain α) → α
  is_bot {x} : bot ⊑ x
  is_bound (c) (n): c.act n ⊑ sup c
  is_least (c) {d} : ({n : _} → c.act n ⊑ d) → sup c ⊑ d

notation:max "⊥" => Domain.bot
notation:max "⨆" => Domain.sup

structure DomainType : Type (i + 1) :=
  carrier : Type i
  order : Order carrier
  domain : Domain carrier

instance : Coe DomainType Type where
  coe D := D.carrier

instance (τ : DomainType) : Order (τ) := τ.order
instance (τ : DomainType) : Domain (τ) := τ.domain

def Domain.sup_of_const [Order α] [Domain α] (a : α) : ⨆ (Mono.const a) = a :=
  (by exact Domain.is_least (Mono.const a) ⋆) ⇄! (Domain.is_bound (Mono.const a) 0)

def sup_is_mono [Order α] [Domain α] {c d : Chain α} (p : c ⊑ d) : ⨆ c ⊑ ⨆ d := by
  apply Domain.is_least c
  intro n
  exact p n ⬝ Domain.is_bound d n

def Mono.sup [Order α] [Domain α] : Mono (Chain α) α :=
  ⟨⨆, sup_is_mono⟩

def sup_succ [Order α] [Domain α] {c : Chain α} : ⨆ (c ∘ Mono.succ) ⊑ ⨆ c := by
  apply Domain.is_least
  intro n
  exact Domain.is_bound c (n.succ)

def continuous [Order α] [Order β] [Domain α] [Domain β] (f : Mono α β) :=
  ∀ {c : Chain α}, f.act (⨆ c) ⊑ ⨆ (f ∘ c)

-- Definition 9 (Continuity)
structure Cont (α) (β) [Order α] [Order β] [Domain α] [Domain β] where
  fn : Mono α β
  sub : ∀ {c : Chain α}, fn.act (⨆ c) ⊑ ⨆ (fn ∘ c)

instance [Order α] [Order β] [Domain α] [Domain β] : CoeFun (Cont α β) (fun _ => α → β) where
  coe f := f.fn.act

notation:101 f " • " x:100 => Mono.act' (Cont.fn f) x

@[ext] theorem Cont.ext [Order α] [Order β] [Domain α] [Domain β] {f g : Cont α β} (p : f.fn.act = g.fn.act) : f = g := by
  obtain ⟨f, _⟩ := f
  obtain ⟨g, _⟩ := g
  have p : f = g := Mono.ext p
  simp [p]

-- Proposition 8 (Products preserve lubs and least element)
instance [Order α] [Order β] [Domain α] [Domain β] : Domain (α × β) where
  bot := ⟨⊥, ⊥⟩
  sup := fun c ↦ ⟨⨆ c.fst, ⨆ c.snd⟩
  is_bot := ⟨Domain.is_bot, Domain.is_bot⟩
  is_bound := fun c n ↦ ⟨Domain.is_bound c.fst n, Domain.is_bound c.snd n⟩
  is_least := fun c _ p ↦ ⟨Domain.is_least c.fst p.left, Domain.is_least c.snd p.right⟩

-- Proposition 9 (Projections and pairing)
def Cont.fst [Order α] [Order β] [Domain α] [Domain β] : Cont (α × β) α :=
  ⟨⟨Prod.fst, And.left⟩, sup_is_mono (fun _ ↦ ⋆)⟩

def Cont.snd [Order α] [Order β] [Domain α] [Domain β] : Cont (α × β) β :=
  ⟨⟨Prod.snd, And.right⟩, sup_is_mono (fun _ ↦ ⋆)⟩

def Cont.pair [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ]
  (f : Cont γ α) (g : Cont γ β) : Cont γ (α × β) := ⟨
    ⟨fun c ↦ ⟨f c, g c⟩, fun p ↦ ⟨f • p, g • p⟩⟩,
    ⟨f.sub ⬝ sup_is_mono (fun _ ↦ ⋆), g.sub ⬝ sup_is_mono (fun _ ↦ ⋆)⟩
  ⟩

-- Proposition 5 for eval
def diagonalize_eval [Order α] [Order β] [Domain β] (c : Chain (Mono α β)) (d : Chain α)
  : ⨆ (Mono.sup ∘ Mono.comp ∘ (Mono.pair c (Mono.const d)))
  ⊑ ⨆ (Mono.eval ∘ Mono.pair c d)
  := by
    apply Domain.is_least
    intro i
    apply Domain.is_least
    intro j
    calc (c i).act (d j)
      _ ⊑ (c i).act (d (max i j))         := (c i).act' (d.act' (Nat.le_max_right ..))
      _ ⊑ (c (max i j)).act (d (max i j)) := (c.act' (Nat.le_max_left ..)) _
      _ ⊑ ⨆ (Mono.eval ∘ Mono.pair c d)   := Domain.is_bound (Mono.eval ∘ Mono.pair c d) ..

-- Exponentials

instance [Order α] [Order β] [Domain α] [Domain β] : Order (Cont α β) where
  R := fun x y ↦ x.fn.act ⊑ y.fn.act
  refl := fun _ ↦ ⋆
  trans := fun p q ↦ p ⬝ q
  anti := fun p q ↦ Cont.ext (p ⇄! q)

def Cont.const [Order α] [Order β] [Domain α] [Domain β] (b : β) : Cont α β := ⟨Mono.const b, fun {c} ↦ by
  have p : (Mono.const b) ∘' c = Mono.const b := Mono.ext (funext fun _ ↦ rfl)
  rw [p, Domain.sup_of_const b]
  exact Order.refl
⟩

def Chain.apply [Order α] [Order β] [Domain α] [Domain β] (c : Chain (Cont α β)) (a : α) : Chain β where
  act := fun n ↦ (c n) a
  act' := fun a_b ↦ (c • a_b) _

def chain_apply_monotone_in_a [Order α] [Order β] [Domain α] [Domain β] {x y : α} (c : Chain (Cont α β))
  (x_y : x ⊑ y) : c.apply x ⊑ c.apply y := by
  intro n
  exact (c n) • x_y

-- Proposition 2 (Monotonicity of lubs)
def cont_sup_mono [Order α] [Order β] [Domain α] [Domain β] (c : Chain (Cont α β)) : Mono α β
  := ⟨fun a ↦ ⨆ (c.apply a), by
      intro p q p_q
      apply Domain.is_least
      intro n
      exact chain_apply_monotone_in_a c p_q n ⬝ Domain.is_bound (c.apply q) n
    ⟩

-- Continuous functions form a domain.
instance [Order α] [Order β] [Domain α] [Domain β] : Domain (Cont α β) where
  bot := ⟨⟨fun _ ↦ ⊥, fun _ ↦ Domain.is_bot⟩, Domain.is_bot⟩
  sup := fun c ↦ ⟨cont_sup_mono c, by {
    intro as
    apply Domain.is_least
    intro n
    exact (c.act n).sub ⬝ (by
      apply Domain.is_least
      intro m
      exact Domain.is_bound (c.apply (as.act m)) n ⬝ Domain.is_bound ((cont_sup_mono c) ∘ as) m
    )
  }⟩
  is_bot := fun _ ↦ Domain.is_bot
  is_bound := by
    intro c n a
    exact Domain.is_bound (c.apply a) n
  is_least := by
    intro c d p a
    apply Domain.is_least
    intro n
    exact p a

def Mono.from_cont [Order α] [Order β] [Domain α] [Domain β] : Mono (Cont α β) (Mono α β) :=
  ⟨Cont.fn, fun p a ↦ p a⟩

def Cont.id' [Order α] [Domain α] : Cont α α
  := ⟨⟨fun x ↦ x, fun x_y ↦ x_y⟩, ⋆⟩

-- Proposition 15 (Continuity of composition)
def Cont.comp {α : Type i} {β : Type j} {γ : Type k}
  [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] : Cont (Cont β γ × Cont α β) (Cont α γ)
  := ⟨⟨
      fun h ↦ ⟨⟨fun x ↦ h.fst (h.snd x), fun x_y ↦ h.fst • h.snd • x_y⟩, by {
        intro c
        calc h.fst (h.snd (⨆ c))
        _ ⊑ h.fst (⨆ (h.snd.fn ∘' c)) := (h.fst • h.snd.sub)
        _ ⊑ (⨆ (h.fst.fn ∘' (h.snd.fn ∘' c))) := h.fst.sub
      }⟩,
      fun {h₀ h₁} h a ↦ (h₀.fst • h.right a) ⬝ (h.left (h₁.snd a))
    ⟩,
    fun {c} a ↦ by
    calc ⨆ (c.fst.apply (⨆ (c.snd.apply a)))
      _ ⊑ ⨆ (Mono.sup ∘ Mono.comp ∘ (Mono.pair (Mono.from_cont ∘ c.fst) (Mono.const (c.snd.apply a))))
        := sup_is_mono (fun n ↦ (c.fst n).sub)
      _ ⊑ ⨆ (Mono.eval ∘ Mono.pair (Mono.from_cont ∘ c.fst) (c.snd.apply a))
        := diagonalize_eval _ _
  ⟩

def Cont.comp' [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] (f : Cont β γ) (g : Cont α β)
  : Cont α γ
  := Cont.comp.fn.act (f, g)

infix:100 " ∘ " => Cont.comp'
infixr:100 " ∘' " => Cont.comp'

theorem Cont.pair_after [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] [Order δ] [Domain δ]
  (f : Cont γ α) (g : Cont γ β) (h : Cont δ γ) : (f ∘' h).pair (g ∘' h) = (f.pair g) ∘' h := by
  apply Cont.ext ∘ funext
  intro x
  rfl

def eval_cont_mono {α : Type i} {β : Type j} [Order α] [Order β] [Domain α] [Domain β] : Mono (Cont α β × α) β :=
   ⟨fun x ↦ x.fst x.snd, fun {x y} p ↦ (x.fst • p.right) ⬝ (p.left y.snd)⟩

-- Proposition 13 (Evaluation)
def Cont.eval {α : Type i} {β : Type j} [Order α] [Order β] [Domain α] [Domain β] : Cont (Cont α β × α) β := ⟨
  eval_cont_mono,
  by {
    intro c
    calc (eval_cont_mono (⨆ c))
      _ = ⨆ (c.fst.apply (⨆ c.snd)) := rfl
      _ ⊑ ⨆ (Mono.sup ∘ Mono.comp ∘ (Mono.pair (Mono.from_cont ∘ c.fst) (Mono.const c.snd)))
                                    := sup_is_mono (fun n ↦ (c.fst n).sub)
      _ ⊑ ⨆ (Mono.eval ∘ Mono.pair (Mono.from_cont ∘ c.fst) c.snd)
                                    := diagonalize_eval _ _
      _ = ⨆ (eval_cont_mono ∘ c)    := rfl
  }
⟩

-- Proposition 14 (Currying)
def Cont.curry {α : Type i} {β : Type j} [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] (f : Cont (α × β) γ) : Cont α (Cont β γ) := ⟨
  ⟨
    fun a ↦ ⟨
      ⟨
        fun b ↦ f (a, b),
        fun b' ↦ f • ⟨⋆, b'⟩
      ⟩,
      by {
        intro c
        calc f (a, ⨆ c)
          _ ⊑ f (⨆ (Mono.const a), ⨆ c) := by rw [Domain.sup_of_const a]; exact ⋆
          _ = f (⨆ (Mono.pair (Mono.const a) c)) := rfl
          _ ⊑ ⨆ (f.fn ∘ Mono.pair (Mono.const a) c) := f.sub
      }
    ⟩,
    fun a' b ↦ f • ⟨a', ⋆⟩
  ⟩,
  by {
    intro c b
    calc f (⨆ c, b)
      _ ⊑ f (⨆ c, ⨆ (Mono.const b)) := by rw [Domain.sup_of_const b]; exact ⋆
      _ = f (⨆ (Mono.pair c (Mono.const b))) := rfl
      _ ⊑ ⨆ (f.fn ∘ Mono.pair c (Mono.const b)) := f.sub
  }
⟩

def uncurry' {α : Type i} {β : Type j} [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] (f : Cont α (Cont β γ)) : Mono (α × β) γ := ⟨
  fun ⟨a, b⟩ ↦ (f a) b,
  by {
    intro ⟨a₀, b₀⟩ ⟨a₁, b₁⟩ ⟨a', b'⟩
    calc ((f a₀) b₀)
      _ ⊑ ((f a₀) b₁) := (f a₀) • b'
      _ ⊑ ((f a₁) b₁) := (f • a') b₁
  }
⟩

def Cont.uncurry {α : Type i} {β : Type j} [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] (f : Cont α (Cont β γ)) : Cont (α × β) γ  := ⟨
  uncurry' f,
  by {
    intro c
    calc uncurry' f (⨆ c)
      _ = (f (⨆ c.fst)) (⨆ c.snd)           := rfl
      _ ⊑ (⨆ (f.fn ∘ c.fst)) (⨆ c.snd)    := (f.sub) (⨆ c.snd)
      _ ⊑ ⨆ ((⨆ (f.fn ∘ c.fst)).fn ∘ c.snd) := (⨆ (f.fn ∘ c.fst)).sub
      _ ⊑ ⨆ (uncurry' f ∘ c) := by {
        -- TODO: Can this be nicely refactored into diagonalization?
        apply Domain.is_least
        intro i
        apply Domain.is_least
        intro j
        calc Chain.apply (f.fn ∘ c.fst) (c.snd i) j
          _ = ((f (c.fst j)) (c.snd i))
              := rfl
          _ ⊑ ((f (c.fst j)) (c.snd (max i j)))
              := (f (c.fst j)).fn.act' (c.snd.act' (Nat.le_max_left ..))
          _ ⊑ ((f (c.fst (max i j))) (c.snd (max i j)))
              := ((f • (c.fst • (Nat.le_max_right ..)))) (c.snd (max i j))
          _ ⊑ ⨆ (uncurry' f ∘ c) := Domain.is_bound (uncurry' f ∘ c) ..
      }
  }
⟩

def Cont.iter [Order α] [Domain α] : Nat → Cont α α → Cont α α
| 0 => fun _ ↦ Cont.id'
| .succ n => fun f ↦ f ∘ iter n f

def Cont.iterations [Order α] [Domain α] (f : Cont α α) : Chain α :=
  ⟨
    fun n ↦ Cont.iter n f ⊥,
    increasing_implies_monotone (fun n ↦ iter n f ⊥) (by
      intro n
      induction n with
      | zero => exact Domain.is_bot
      | succ x Φ => exact (f.fn.act' Φ)
    )
  ⟩

def is_prefixed [Order α] [Domain α] (f : Cont α α) (a : α) := f a ⊑ a

-- Proposition 16 (Continuity of the fixed point operator)
def Cont.fix [Order α] [Domain α] (f : Cont α α) := ⨆ f.iterations

def fix_is_prefixed [Order α] [Domain α] (f : Cont α α) : is_prefixed f (⨆ f.iterations) := by
  calc (f (f.fix))
    _ ⊑ ⨆ (f.fn ∘ f.iterations)      := f.sub
    _ = ⨆ (f.iterations ∘ Mono.succ) := rfl
    _ ⊑ f.fix                        := sup_succ

def fix_is_least_prefixed [Order α] [Domain α] (f : Cont α α) (a : α) (h : is_prefixed f a)
  : f.fix ⊑ a
  := by
  apply Domain.is_least
  intro n
  induction n with
  | zero => exact Domain.is_bot
  | succ n Φ =>
    calc (f.iterations.act (n + 1))
      _ ⊑ f a := f • Φ
      _ ⊑ a     := h

-- Theorem 6 (Kleene’s fixed point theorem)
def Cont.fix_is_fixed [Order α] [Domain α] (f : Cont α α) : f (f.fix) = f.fix := by
  apply Order.anti
  apply fix_is_prefixed
  apply fix_is_least_prefixed
  apply f.fn.act'
  apply fix_is_prefixed

def Cont.fix_mono [Order α] [Domain α] : Mono (Cont α α) α := ⟨
    Cont.fix,
    by
      intro f g f_g
      apply fix_is_least_prefixed
      calc f (fix g)
        _ ⊑ g (fix g) := f_g _
        _ ⊑ fix g       := fix_is_prefixed _
  ⟩

-- Proposition 16
def Cont.fix' [Order α] [Domain α] : Cont (Cont α α) α := ⟨
    fix_mono,
    by
      intro f
      apply fix_is_least_prefixed
      calc ⨆ f (⨆ (fix_mono ∘ f))
        _ = ⨆ (f.apply (⨆ (fix_mono ∘ f))) := rfl
        _ ⊑ ⨆ (Mono.sup ∘ Mono.comp ∘ Mono.pair (Mono.from_cont ∘ f) (Mono.const (fix_mono ∘ f))) := by {
          apply sup_is_mono
          intro n
          exact (f n).sub
        }
        _ ⊑ ⨆ (Mono.eval ∘ Mono.pair (Mono.from_cont ∘ f) (fix_mono ∘ f)) := diagonalize_eval _ _
        _ ⊑ ⨆ (fix_mono ∘ f) := by {
          apply sup_is_mono
          intro n
          exact fix_is_prefixed (f n)
        }
  ⟩

-- Theorem 17 (Scott induction)
def scott [Order D] [Domain D] {φ : D → Sort u} {f : Cont D D}
  : φ ⊥ → (∀ {c}, (∀ n, φ (c n)) → φ (⨆ c)) → (∀ {d}, φ d → φ (f d)) → φ (f.fix) := by
  intro closed_0 closed_chain closed_f
  apply closed_chain
  intro n
  induction n with
  | zero => exact closed_0
  | succ n Φ => exact closed_f Φ

def scott3 [Order D] [Domain D] {φ : D → D → D → Sort u} {f₀ : Cont D D} {f₁ : Cont D D} {f₂ : Cont D D}
  : φ ⊥ ⊥ ⊥
  → (∀ {c₀ c₁ c₂}, (∀ n, φ (c₀ n) (c₁ n) (c₂ n)) → φ (⨆ c₀) (⨆ c₁) (⨆ c₂))
  → (∀ {d₀ d₁ d₂}, φ d₀ d₁ d₂ → φ (f₀ d₀) (f₁ d₁) (f₂ d₂)) → φ (f₀.fix) (f₁.fix) (f₂.fix) := by
  intro closed_0 closed_chain closed_φ
  apply closed_chain
  intro n
  induction n with
  | zero => exact closed_0
  | succ n Φ => exact closed_φ Φ

def Mono.swap [Order α] [Domain α] [Order β] [Domain β] : Mono (α × β) (β × α) := ⟨
  fun p ↦ ⟨p.snd, p.fst⟩,
  fun ⟨a', b'⟩ ↦ ⟨b', a'⟩
⟩

def Cont.swap [Order α] [Domain α] [Order β] [Domain β] : Cont (α × β) (β × α) := ⟨
  Mono.swap,
  by {
    intro c
    calc Mono.swap (⨆ c)
      _ ⊑ ⨆ (c.snd.pair c.fst) := ⋆
      _ ⊑ ⨆ (Mono.swap ∘' c) := sup_is_mono ⋆
  }
⟩

def assoc_swap_assoc' {α : Type i} {β : Type j} [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] : Mono ((α × β) × γ) ((α × γ) × β) := ⟨
  fun p ↦ ⟨⟨p.fst.fst, p.snd⟩, p.fst.snd⟩,
  fun ⟨⟨a', b'⟩, c'⟩ ↦ ⟨⟨a', c'⟩, b'⟩
⟩

def Cont.assoc_swap_assoc {α : Type i} {β : Type j} [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ] : Cont ((α × β) × γ) ((α × γ) × β) := ⟨
  assoc_swap_assoc',
  by {
    intro c
    calc assoc_swap_assoc' (⨆ c)
      _ ⊑ ⨆ ((c.fst.fst.pair c.snd).pair c.fst.snd) := ⋆
      _ ⊑ ⨆ (assoc_swap_assoc' ∘' c) := sup_is_mono ⋆
  }
⟩

class TrivialDomain (α) [Order α] [Domain α] where
  eventually_const : (c : Chain α) → ∃ N, ∀ {n}, N ≤ n → c n ⊑ c N

def Domain.eventually_const_sup [Order α] [Domain α]
  {c : Chain α} : (∀ {n}, N ≤ n → c n ⊑ c N) → ⨆ c ⊑ c N := by
  intro eventually_const
  -- suffices lem : ⨆ c ⊑ c N from lem ⇄! Domain.is_bound c N
  apply Domain.is_least
  intro n
  suffices lem : c (max n N) ⊑ c N from (c • Nat.le_max_left n N) ⬝ lem
  exact eventually_const (Nat.le_max_right n N)

def Mono.promote_trivial [Order α] [Domain α] [TrivialDomain α] [Order β] [Domain β] [TrivialDomain β] (f : Mono α β) : Cont α β := ⟨
  f,
  by {
    intro c
    have ⟨N₀, ec₀⟩ := TrivialDomain.eventually_const c
    have ⟨N₁, ec₁⟩ := TrivialDomain.eventually_const (f ∘' c)
    calc f (⨆ c)
      _ ⊑ f (c N₀)             := f • Domain.eventually_const_sup ec₀
      _ ⊑ f (c (max N₀ N₁))    := f • (c • (Nat.le_max_left N₀ N₁))
      _ = (f ∘' c) (max N₀ N₁) := rfl
      _ ⊑ (f ∘' c) N₁          := (ec₁ (Nat.le_max_right N₀ N₁))
      _ ⊑ ⨆ (f ∘' c)           := Domain.is_bound (f ∘' c) N₁
  }
⟩

instance (α β)  [Order α] [Domain α] [TrivialDomain α] [Order β] [Domain β] [TrivialDomain β] : TrivialDomain (α × β) where
  eventually_const := by {
    intro c
    have ⟨N₀, ec₀⟩ := TrivialDomain.eventually_const c.fst
    have ⟨N₁, ec₁⟩ := TrivialDomain.eventually_const c.snd
    exact ⟨
      max N₀ N₁,
      by {
        intro n Nm_le_n
        have m₀ := Nat.le_max_left N₀ N₁
        have m₁ := Nat.le_max_right N₀ N₁
        constructor
        exact ec₀ (m₀ ⬝ Nm_le_n) ⬝ (c.fst • m₀)
        exact ec₁ (m₁ ⬝ Nm_le_n) ⬝ (c.snd • m₁)
      }
    ⟩
  }
