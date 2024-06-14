import «oPCF».Utility

/-
A partial order is a relation which is reflexive, transitive, and antisymmetric.
In our semantics, we'll use them to represent a notion of 'relative definition',
where `a ⊑ b` means that `b` is at least as 'defined' as `a`.
-/

class Order (α) where
  R : α → α → Prop
  refl {x} : R x x
  trans {x y z} : R x y → R y z → R x z
  anti {x y} : R x y → R y x → x = y

instance [o : Order α] : Trans o.R o.R o.R where
  trans := o.trans

infix:100 " ⊑ " => Order.R
notation:max "⋆" => Order.refl
infix:100 " ⇄! " => Order.anti

-- The naturals form a partial order.
instance : Order Nat where
  R := Nat.le
  refl := Nat.le_refl _
  trans := Nat.le_trans
  anti := Nat.le_antisymm

-- Functions between partial orders form a partial order.
instance [Order α] [Order β] : Order (α → β) where
  R := fun f g ↦ ∀ x, f x ⊑ g x
  refl := by intro f x; exact ⋆
  trans := by intro f g h p q x; exact p x ⬝ q x
  anti := by
    intro f g p q
    exact funext fun x ↦ p x ⇄! q x

/-
Monotone functions are functions between orders that preserve the ordering. With respect
to relative definition, if a monotone function is given a better-defined argument, it does
not produce a worse-defined result.
-/

def is_monotone [Order α] [Order β] (f : α → β) := ∀ {x y : α}, x ⊑ y → f x ⊑ f y

def increasing_implies_monotone [Order α] (f : Nat → α) : (∀ n, f n ⊑ f n.succ) → is_monotone f := by
  intro f_step n x n_x
  induction n_x with
  | refl => exact ⋆
  | step _ fn_fx => exact fn_fx ⬝ f_step _

structure Mono (α) (β) [Order α] [Order β] where
  act : α → β
  act' : is_monotone act

instance [Order α] [Order β] : CoeFun (Mono α β) (fun _ => α → β) where
  coe f := f.act

infixl:100 " • " => Mono.act'

@[ext] theorem Mono.ext [Order α] [Order β] {f g : Mono α β} (p : f.act = g.act) : f = g := by
  obtain ⟨f, _⟩ := f
  obtain ⟨g, _⟩ := g
  have p : f = g := p
  simp [p]

-- Monotone functions form a partial order.
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

-- Constant functions are monotone.
def Mono.const [Order α] [Order β] (b : β) : Mono α β := ⟨fun _ ↦ b, fun _ ↦ ⋆⟩

-- The identity is monotone.
def Mono.id [Order α] : Mono α α
  := ⟨Function.id, Function.id⟩

-- A composition of monotone functions is monotone.
def Mono.comp' [Order α] [Order β]  [Order γ] (f : Mono β γ) (g : Mono α β) : Mono α γ where
  act := f.act ∘ g.act
  act' := fun x_y ↦ f • (g • x_y)

infixr:100 " ∘ " => Mono.comp'
infixr:100 " ∘' " => Mono.comp'

-- The successor function is monotone.
def Mono.succ : Mono Nat Nat := ⟨Nat.succ, Nat.succ_le_succ⟩

/-
We set aside a special class of monotone functions, 'chains', which are infinite monotone
sequences indexed by the natural numbers. We'll use these to represent approximating
sequences of definitions, which can be used to understand recursive functions.
-/

def Chain (α : Type i) [Order α] := Mono Nat α

instance [Order α] : Order (Chain α) := inferInstanceAs (Order (Mono ..))

instance [Order α] : CoeFun (Chain α) (fun _ => Nat → α) where
  coe f := f.act

/-
A Cartesian product of partial orders is also a partial order.
-/

-- Definition 13 (Binary product of two orders)
instance [Order α] [Order β] : Order (α × β) where
  R := fun ⟨a₀, b₀⟩ ⟨a₁, b₁⟩ ↦ a₀ ⊑ a₁ ∧ b₀ ⊑ b₁
  refl := ⟨⋆, ⋆⟩
  trans := fun ⟨p₀, p₁⟩ ⟨q₀, q₁⟩ ↦ ⟨p₀ ⬝ q₀, p₁ ⬝ q₁⟩
  anti := fun ⟨p₀, p₁⟩ ⟨q₀, q₁⟩ ↦ Prod.ext (p₀ ⇄! q₀) (p₁ ⇄! q₁)

-- The left and right projections of a chain are both chains.
def Chain.fst [Order α] [Order β] (c : Chain (α × β)) : Chain α :=
  ⟨fun n ↦ (c n).fst, fun p ↦ by exact (c • p).left⟩

def Chain.snd [Order α] [Order β] (c : Chain (α × β)) : Chain β :=
  ⟨fun n ↦ (c n).snd, fun p ↦ by exact (c • p).right⟩

-- Two monotone functions from the same source can be paired into another.
def Mono.pair [Order α] [Order β] [Order γ]
  (f : Mono γ α) (g : Mono γ β) : Mono γ (α × β) :=
    ⟨fun c ↦ ⟨f c, g c⟩, fun p ↦ ⟨f • p, g • p⟩⟩

/-
Swapping the order of a pair is a continuous operation.
-/

def Mono.swap [Order α] [Order β] : Mono (α × β) (β × α) := ⟨
    fun p ↦ ⟨p.snd, p.fst⟩,
    fun ⟨a', b'⟩ ↦ ⟨b', a'⟩
  ⟩

-- We also define a means of swapping the last two fields of a triple, for convenience
def Mono.assoc_swap_assoc {α : Type i} {β : Type j}
  [Order α] [Order β] [Order γ] : Mono ((α × β) × γ) ((α × γ) × β) := ⟨
    fun p ↦ ⟨⟨p.fst.fst, p.snd⟩, p.fst.snd⟩,
    fun ⟨⟨a', b'⟩, c'⟩ ↦ ⟨⟨a', c'⟩, b'⟩
  ⟩

/-
Composition and evaluation of monotone functions are also monotone themselves.
-/

def Mono.comp {α : Type i} {β : Type j} {γ : Type k} [Order α] [Order β] [Order γ]
  : Mono (Mono β γ × Mono α β) (Mono α γ) := ⟨
    fun h ↦ ⟨fun x ↦ h.fst (h.snd x), fun x_y ↦ h.fst • (h.snd • x_y)⟩,
    fun {h₀ h₁} h a ↦ (h₀.fst • h.right a) ⬝ (h.left (h₁.snd a))
  ⟩

def Mono.eval {α : Type i} {β : Type j} [Order α] [Order β] : Mono (Mono α β × α) β :=
  ⟨fun x ↦ x.fst x.snd, fun {x y} p ↦ (x.fst • p.right) ⬝ (p.left y.snd)⟩
