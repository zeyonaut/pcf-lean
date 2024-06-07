class Order (α) where
  R : α → α → Prop
  refl {x} : R x x
  trans {x y z} : R x y → R y z → R x z
  anti {x y} : R x y → R y x → x = y

instance [o : Order α] : Trans o.R o.R o.R where
  trans := o.trans

infix:100 " ⊑ " => Order.R
notation:max "⋆" => Order.refl
infix:100 " ⬝ " => Order.trans
infix:100 " ⇄! " => Order.anti

instance : Order Nat where
  R := Nat.le
  refl := Nat.le_refl _
  trans := Nat.le_trans
  anti := Nat.le_antisymm

instance [Order α] [Order β] : Order (α → β) where
  R := fun f g ↦ ∀ x, f x ⊑ g x
  refl := by intro f x; exact ⋆
  trans := by intro f g h p q x; exact p x ⬝ q x
  anti := by
    intro f g p q
    exact funext fun x ↦ p x ⇄! q x

def is_monotone [Order α] [Order β] (f : α → β) := ∀ {x y : α}, x ⊑ y → f x ⊑ f y

def increasing_implies_monotone [Order α] (f : Nat → α) : (∀ n, f n ⊑ f n.succ) → is_monotone f := by
  intro f_step n x n_x
  induction n_x with
  | refl => exact ⋆
  | step _ fn_fx => exact fn_fx ⬝ f_step _

structure Mono (α) (β) [Order α] [Order β] where
  act : α → β
  act' : is_monotone act

infixl:100 " $ " => Mono.act
infixl:100 " $ " => Mono.act'

@[ext] theorem Mono.ext [Order α] [Order β] {f g : Mono α β} (p : f.act = g.act) : f = g := by
  obtain ⟨f, _⟩ := f
  obtain ⟨g, _⟩ := g
  have p : f = g := p
  simp [p]

def Mono.const [Order α] [Order β] (b : β) : Mono α β := ⟨fun _ ↦ b, fun _ ↦ ⋆⟩

instance [Order α] [Order β] : Order (Mono α β) where
  R := fun x y ↦ x.act ⊑ y.act
  refl := by intro f x; exact ⋆
  trans := by intro f g h p q; exact p ⬝ q
  anti := by
    intro f g p q
    obtain ⟨f , _⟩ := f
    obtain ⟨g , _⟩ := g
    have x : f = g := p ⇄! q
    simp [x]

def Chain (α : Type i) [Order α] := Mono Nat α

instance [Order α] : Order (Chain α) := inferInstanceAs (Order (Mono ..))

class Domain (α) [Order α] where
  bot : α
  sup : (c : Chain α) → α
  is_bot {x} : bot ⊑ x
  is_bound (c) (n): c.act n ⊑ sup c
  is_least (c) {d} : ({n : _} → c.act n ⊑ d) → sup c ⊑ d

notation:max "⊥" => Domain.bot
notation:max "⨆" => Domain.sup

def Domain.sup_of_const [Order α] [Domain α] (a : α) : ⨆ (Mono.const a) = a :=
  (by exact Domain.is_least (Mono.const a) ⋆) ⇄! (Domain.is_bound (Mono.const a) 0)

def sup_is_mono [Order α] [Domain α] {c d : Chain α} (p : c ⊑ d) : ⨆ c ⊑ ⨆ d := by
  apply Domain.is_least c
  intro n
  exact p n ⬝ Domain.is_bound d n

def Mono.sup [Order α] [Domain α] : Mono (Chain α) α :=
  ⟨⨆, sup_is_mono⟩

def Mono.id [Order α] : Mono α α
  := ⟨fun x ↦ x, fun x_y ↦ x_y⟩

def Mono.comp' [Order α] [Order β]  [Order γ] (f : Mono β γ) (g : Mono α β) : Mono α γ where
  act := f.act ∘ g.act
  act' := fun x_y ↦ f $ (g $ x_y)

infixr:100 " ∘ " => Mono.comp'

def Mono.succ : Mono Nat Nat := ⟨Nat.succ, Nat.succ_le_succ⟩

-- Definition 13
instance [Order α] [Order β] : Order (α × β) where
  R := fun ⟨a₀, b₀⟩ ⟨a₁, b₁⟩ ↦ a₀ ⊑ a₁ ∧ b₀ ⊑ b₁
  refl := ⟨⋆, ⋆⟩
  trans := fun ⟨p₀, p₁⟩ ⟨q₀, q₁⟩ ↦ ⟨p₀ ⬝ q₀, p₁ ⬝ q₁⟩
  anti := fun ⟨p₀, p₁⟩ ⟨q₀, q₁⟩ ↦ Prod.ext (p₀ ⇄! q₀) (p₁ ⇄! q₁)

def Chain.fst [Order α] [Order β] (c : Chain (α × β)) : Chain α :=
  ⟨fun n ↦ (c $ n).fst, fun p ↦ by exact (c $ p).left⟩

def Chain.snd [Order α] [Order β] (c : Chain (α × β)) : Chain β :=
  ⟨fun n ↦ (c $ n).snd, fun p ↦ by exact (c $ p).right⟩

def Mono.pair [Order α] [Order β] [Order γ]
  (f : Mono γ α) (g : Mono γ β) : Mono γ (α × β) :=
    ⟨fun c ↦ ⟨f $ c, g $ c⟩, fun p ↦ ⟨f $ p, g $ p⟩⟩

def Mono.comp {α : Type i} {β : Type j} {γ : Type k} [Order α] [Order β] [Order γ] : Mono (Mono β γ × Mono α β) (Mono α γ) := ⟨
      fun h ↦ ⟨fun x ↦ h.fst $ (h.snd $ x), fun x_y ↦ h.fst $ (h.snd $ x_y)⟩,
      fun {h₀ h₁} h a ↦ (h₀.fst $ h.right a) ⬝ (h.left (h₁.snd $ a))
    ⟩

def Mono.eval {α : Type i} {β : Type j} [Order α] [Order β] : Mono (Mono α β × α) β :=
  ⟨fun x ↦ x.fst $ x.snd, fun {x y} p ↦ (x.fst $ p.right) ⬝ (p.left $ y.snd)⟩
