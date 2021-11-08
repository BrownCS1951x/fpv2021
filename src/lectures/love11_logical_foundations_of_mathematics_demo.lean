import .love05_inductive_predicates_demo
import data.real.cardinality


/-! # LoVe Demo 11: Logical Foundations of Mathematics

We dive deeper into the logical foundations of Lean. Most of the features
described here are especially relevant for defining mathematical objects and
proving theorems about them. -/


set_option pp.beta true
set_option pp.generalized_field_notation false
open_locale cardinal 

namespace LoVe


/-! ## Universes

Not only terms have a type, but also types have a type. For example, by the PAT
principle:

    `@and.intro : ∀(a b : Prop), a → b → a ∧ b`

Moreover:

    `∀(a b : Prop), a → b → a ∧ b : Prop`

Now, what is the type of `Prop`? `Prop` has the same type as virtually all other
types we have constructed so far:

    `Prop : Type`

What is the type of `Type`? The typing `Type : Type` would lead to a
contradiction, called **Girard's paradox**, resembling Russell's paradox.
Instead:

    `Type   : Type 1`
    `Type 1 : Type 2`
    `Type 2 : Type 3`
    ⋮

Aliases:

    `Type`   := `Type 0`
    `Prop`   := `Sort 0`
    `Type u` := `Sort (u + 1)`

The types of types (`Sort u`, `Type u`, and `Prop`) are called __universes__.
The `u` in `Sort u` is a __universe level__.

The hierarchy is captured by the following typing judgment:

    ————————————————————————— Sort
    C ⊢ Sort u : Sort (u + 1) -/

#check @and.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2

universe variables u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type*

#check ulift 

/- 
### Girard's Paradox 

References: 
Hurkens, *A simplification of Girard's Paradox* (https://www.cs.cmu.edu/~kw/scans/hurkens95tlca.pdf)
Watkins, implemented in LF (http://www.cs.cmu.edu/~kw/research/hurkens95tlca.elf)
Carneiro, implemented in Lean (https://github.com/leanprover-community/mathlib/blob/master/counterexamples/girard.lean)


What happens if we have `Type u : Type u` for some `u`?

We can't axiomatize this directly. But we can still explore. 

First, consider the normal Π operator.
-/

#check Π T : Type, T × T 
#check λ T : Type, T × T 

/-
Given a function like `f := λ T : Type, T × T : Type → Type`,
`Π f` has type `Type 1`.
In a sense, the "type" of `Π` is `(Type → Type) → Type 1`, or more generally,
`(Type u → Type v) → Type (1 + max u v)`.

If we collapsed the universe hierarchy, though, it would have type 
`(Type → Type) → Type`. 
-/

namespace girard
section  

parameter pi   : (Type → Type) → Type
parameter lam  : Π {A : Type → Type}, (Π x, A x) → pi A 
parameter app  : Π {A : Type → Type}, pi A → Π x, A x
parameter beta : Π {A : Type → Type} (f : Π x, A x) (x : Type), app (lam f) x = f x

/-
As long as we have such a `pi` operator and a smaller universe `Prop < Type`, 
we can derive false. 
-/

/-- 
F X is a particular function type. 
We have `F : Type → Type`.
-/
def F (X : Type) : Type := 
(set (set X) → X) → set (set X)  

/-- 
U is the type of functions that take in a type `X` and produce a function of type `F X`. 
This will be our "paradoxical type."
-/
def U : Type := 
pi F

#check Π X, F X
#check U

def G (T : set (set U)) (X : Type) : F X := 
λ f : set (set X) → X, 
  { s : set X | 
      {x : U | f (app x X f) ∈ s} ∈ T 
  }

/--
τ is a function of type `𝒫𝒫U → U`.
-/
def τ (T : set (set U)) : U := 
lam (G T)

#check τ

/--
σ is a function of type `U → 𝒫𝒫U`.
-/
def σ (S : U) : set (set U) := 
app S U τ

lemma σ_τ_spec : ∀ {s : set U} {S : set (set U)}, 
  s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := 
λ s S, iff_of_eq (congr_arg (λ f : F U, s ∈ f τ) (beta (G S) U) : _)

/- a set `p` is in `ω` if for every `x : U` such that `p ∈ σ x`, `x ∈ p`. -/
def ω : set (set U) := 
{p : set U | ∀ x : U, p ∈ σ x → x ∈ p}

/-
`δ S` is true iff every `p ∈ S` contains `τ S`. 
-/
def δ (S : set (set U)) : Prop := 
∀ p : set U, p ∈ S → τ S ∈ p 

lemma δ_ω_spec : δ ω :=
λ p d, d (τ ω) (σ_τ_spec.2 (λ x h, d (τ (σ x)) (σ_τ_spec.2 h)))

def bad_set : set U :=
{y : U | ¬ δ (σ y)}

theorem girard : false := 
have h1 : ∀ p : set U, p ∈ ω → τ ω ∈ p := δ_ω_spec,
have h2 : bad_set ∈ ω → τ ω ∈ bad_set := h1 bad_set,
have h3 : bad_set ∈ ω := λ x e f, f _ e (λ p h, f _ (σ_τ_spec.1 h)),
have h4 : τ ω ∈ bad_set := h2 h3,
have h5 : ¬ δ (σ (τ ω)) := h4,
have h6 : δ (σ (τ ω)) := λ p h, δ_ω_spec _ (σ_τ_spec.1 h),
show false, from h5 h6

end 
end girard



/-! ## The Peculiarities of Prop

`Prop` is different from the other universes in many respects.


### Impredicativity

The function type `σ → τ` is put into the larger one of the universes that
`σ` and `τ` live in:

    C ⊢ σ : Type u    C ⊢ τ : Type v
    ————————————————————————————————— Arrow-Type
    C ⊢ σ → τ : Type (max u v)

For dependent types, this generalizes to

    C ⊢ σ : Type u    C, x : σ ⊢ τ[x] : Type v
    ——————————————————————————————————————————— Forall-Type
    C ⊢ (∀x : σ, τ[x]) : Type (max u v)

This behavior of the universes `Type v` is called __predicativity__.

To force expressions such as `∀a : Prop, a → a` to be of type `Prop` anyway, we
need a special typing rule for `Prop`:

    C ⊢ σ : Sort u    x : σ ⊢ τ[x] : Prop
    —————————————————————————————————————— Forall-Prop
    C ⊢ (∀x : σ, τ[x]) : Prop

This behavior of `Prop` is called __impredicativity__.

The rules `Forall-Type` and `Forall-Prop` can be generalized into a single rule:

    C ⊢ σ : Sort u    C, x : σ ⊢ τ[x] : Sort v
    ——————————————————————————————————————————— Forall
    C ⊢ (∀x : σ, τ[x]) : Sort (imax u v)

where

    `imax u 0       = 0`
    `imax u (v + 1) = max u (v + 1)` -/

#check λ(α : Type u) (β : Type v), α → β
#check ∀a : Prop, a → a


/-! ### Proof Irrelevance

A second difference between `Prop` and `Type u` is __proof irrelevance__:

    `∀(a : Prop) (h₁ h₂ : a), h₁ = h₂`

This makes reasoning about dependent types easier.

When viewing a proposition as a type and a proof as an element of that type,
proof irrelevance means that a proposition is either an empty type or has
exactly one inhabitant.

Proof irrelevance can be proved `by refl`. -/

#check proof_irrel

lemma proof_irrel {a : Prop} (h₁ h₂ : a) :
  h₁ = h₂ :=
by refl


/-! ### No Large Elimination

A further difference between `Prop` and `Type u` is that `Prop` does not allow
__large elimination__, meaning that it impossible to extract data from a proof
of a proposition.

This is necessary to allow proof irrelevance. -/

#check 0

-- fails
def unsquare (i : ℤ) (hsq : ∃j, i = j * j) : ℤ :=
match hsq with
| Exists.intro j _ := j
end

/-! If the above were accepted, we could derive `false` as follows.

Let

    `hsq₁` := `Exists.intro 3 (by linarith)`
    `hsq₂` := `Exists.intro (-3) (by linarith)`

be two proofs of `∃j, (9 : ℤ) = j * j`. Then

    `unsquare 9 hsq₁ = 3`
    `unsquare 9 hsq₂ = -3`

However, by proof irrelevance, `hsq₁ = hsq₂`. Hence

    `unsquare 9 hsq₂ = 3`

Thus

    `3 = -3`

a contradiction.

As a compromise, Lean allows __small elimination__. It is called small
elimination because it eliminate only into `Prop`, whereas large elimination can
eliminate into an arbitrary large universe `Sort u`. This means we can use
`match` to analyze the structure of a proof, extract existential witnesses, and
so on, as long as the `match` expression is itself a proof. We have seen several
examples of this in lecture 5.

As a further compromise, Lean allows large elimination for
__syntactic subsingletons__: types in `Prop` for which it can be established
syntactically that they have cardinality 0 or 1. These are propositions such as
`false` and `a ∧ b` that can be proved in at most one way.
-/


/-
### Impredicative, proof-irrelevant Prop

Coquand has recently shown that impredicative Prop + proof-irrelevant = 
leads to a failure of strong normalization. 
<https://arxiv.org/pdf/1911.08174.pdf>

Lean code adapted from Mario Carneiro.
-/

namespace no_sn 

def false' : Prop := 
∀ p : Prop, p

def true' : Prop := 
false' → false'

theorem omega : (∀ (A B : Prop), A = B) → false' :=
λ h A, @cast true' _ (h true' A) (λ z: false', z true' z)

theorem Omega : (∀ (A B : Prop), A = B) → false' :=
λ h, omega h true' (omega h)

-- #reduce Omega -- timeout

example (h : ∀ A B : Prop, A = B) : Omega h = Omega h :=
calc Omega h = omega h true' (omega h) : rfl
         ... = @cast true' true' (h true' true') (λ z: false', z true' z) (omega h) : rfl
         ... = (λ z: false', z true' z) (omega h) : rfl
         ... = (omega h) true' (omega h) : rfl
         ... = Omega h : rfl

end no_sn 

/-
## The Axiom of Choice

Lean's logic includes the axiom of choice, which makes it possible to obtain an
arbitrary element from any nonempty type.

Consider Lean's `nonempty` inductive predicate: -/

#print nonempty

/-! The predicate states that `α` has at least one element.

To prove `nonempty α`, we must provide an `α` value to `nonempty.intro`: -/

lemma nat.nonempty :
  nonempty ℕ :=
nonempty.intro 0

/-! Since `nonempty` lives in `Prop`, large elimination is not available, and
thus we cannot extract the element that was used from a proof of `nonempty α`.

The axiom of choice allows us to obtain some element of type `α` if we can show
`nonempty α`: -/

#print classical.choice

/-! It will just give us an arbitrary element of `α`; we have no way of knowing
whether this is the element that was used to prove `nonempty α`.

The constant `classical.choice` is noncomputable, one of the reasons why some
logicians prefer to work without this axiom. -/

#eval classical.choice nat.nonempty     -- fails
#reduce classical.choice nat.nonempty   -- result: classical.choice _

/-! The axiom of choice is only an axiom in Lean's core library, giving users
the freedom to work with or without it.

Definitions using it must be marked as `noncomputable`: -/

noncomputable def arbitrary_nat : ℕ :=
classical.choice nat.nonempty

/-! The following tools rely on choice.


### Law of Excluded Middle -/

#check classical.em
#check classical.by_contradiction

/-! ### Hilbert Choice -/

#print classical.some
#print classical.some_spec

#check λ(p : ℕ → Prop) (h : ∃n : ℕ, p n), classical.some h
#check λ(p : ℕ → Prop) (h : ∃n : ℕ, p n), classical.some_spec h


/-! ### Set-Theoretic Axiom of Choice -/

#print classical.axiom_of_choice


/-! ## Consistency

If we can construct a closed term `p : false` (or `p : empty`), we can prove
any proposition. Hopefully this is not the case.

*Theorem* (consistency): there is no closed term `p : false`. 

This can be interpreted in two ways:
* Theoretical: abstractly, the inference rules are consistent
* Applied: the actual implementation is consistent

We'll focus on the theoretical side.

Where would we even begin to prove something like theoretical consistency?


We used semantic arguments to prove meta-properties about PL. 
*Model* the abstract syntax of the language in some other system,
and show that this interpretation preserves all of the axioms, properties,
etc. of the original system. 

If the semantic domain is consistent, then the original system is too. 

Carneiro, 2019:
<https://github.com/digama0/lean-type-theory/releases/download/v1.0/main.pdf>

"... [we] construct the expected set-theoretic model, from which we derive 
consistency of Lean relative to ZFC + {there are n inaccessible cardinals | n < ω}"

Types -> sets, propositions -> true/false.

There's more we can do with this notion of modeling. 
What propositions are provable in Lean? 
Those that are true in *every* model.
-/

section 
local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow

example : ℕ ≠ ℤ :=
begin 
  sorry
end

example : ℕ ≠ ℝ :=
begin 
  have nat_card : #ℕ = cardinal.omega := cardinal.mk_nat,
  have real_card : #ℝ = 2 ^ cardinal.omega := cardinal.mk_real,
  intro h,
  cases' h,
  rw nat_card at real_card,
  have card_lt : cardinal.omega < 2 ^ cardinal.omega := cardinal.cantor cardinal.omega,
  exact ne_of_lt card_lt real_card
end

end 

/-!

### Consistency of implementation 

Modeling the abstract logical rules doesn't tell us anything about the actual implementation. 
There could still be bugs: in elaboration, tactics, type checking, ... 

This is now an engineering issue!
The trusted code base only needs to answer one question:
"Given two fully elaborated terms `t` and `T`, does `t` have type `T`?"

Engineering task: minimize and simplify the code needed to answer this question. 
All the work done by tactics, etc will be checked by this small (~8k loc) kernel.

Even better, you can write a totally independent type checker to check the kernel's work.


-/




/-! ## Subtypes

Subtyping is a mechanism to create new types from existing ones.

Given a predicate on the elements of the base type, the __subtype__ contains
only those elements of the base type that fulfill this property. More precisely,
the subtype contains element–proof pairs that combine an element of the base
type and a proof that it fulfills the property.

Subtyping is useful for those types that cannot be defined as an inductive
type. For example, any attempt at defining the type of finite sets along the
following lines is doomed to fail: -/

inductive finset (α : Type) : Type
| empty  : finset
| insert : α → finset → finset

/-! Given a base type and a property, the subtype has the syntax

    `{` _variable_ `:` _base-type_ `//` _property-applied-to-variable_ `}`

Example:

    `{i : ℕ // i ≤ n}`

Alias:

    `{x : τ // P[x]}` := `@subtype τ (λx, P[x])`


### First Example: Full Binary Trees -/

#check subtype

#check btree
#check is_full
#check mirror
#check is_full_mirror
#check mirror_mirror

def full_btree (α : Type) : Type :=
{t : btree α // is_full t}

#print subtype
#check subtype.mk

/-! To define elements of `full_btree`, we must provide a `btree` and a proof
that it is full: -/

def empty_full_btree : full_btree ℕ :=
subtype.mk btree.empty is_full.empty

def full_btree_6 : full_btree ℕ :=
subtype.mk (btree.node 6 btree.empty btree.empty)
  begin
    apply is_full.node,
    apply is_full.empty,
    apply is_full.empty,
    refl
  end

#reduce subtype.val full_btree_6
#check subtype.property full_btree_6

/-! We can lift existing operations on `btree` to `full_btree`: -/

def full_btree.mirror {α : Type} (t : full_btree α) :
  full_btree α :=
subtype.mk (mirror (subtype.val t))
  begin
    apply is_full_mirror,
    apply subtype.property t
  end

#reduce subtype.val (full_btree.mirror full_btree_6)

/-! And of course we can prove lemmas about the lifted operations: -/

lemma full_btree.mirror_mirror {α : Type} (t : full_btree α) :
  (full_btree.mirror (full_btree.mirror t)) = t :=
begin
  apply subtype.eq,
  simp [full_btree.mirror],
  apply mirror_mirror
end

#check subtype.eq


/-! ### Second Example: Vectors -/

#check vector

def vector (α : Type) (n : ℕ) : Type :=
{xs : list α // list.length xs = n}

def vector_123 : vector ℤ 3 :=
subtype.mk [1, 2, 3] (by refl)

def vector.neg {n : ℕ} (v : vector ℤ n) : vector ℤ n :=
subtype.mk (list.map int.neg (subtype.val v))
  begin
    rw list.length_map,
    exact subtype.property v
  end

lemma vector.neg_neg (n : ℕ) (v : vector ℤ n) :
  vector.neg (vector.neg v) = v :=
begin
  apply subtype.eq,
  simp [vector.neg]
end

#check finset


/-! ## Quotient Types

Quotients are a powerful construction in mathematics used to construct `ℤ`, `ℚ`,
`ℝ`, and many other types.

Like subtyping, quotienting constructs a new type from an existing type. Unlike
a subtype, a quotient type contains all of the elements of the base type, but
some elements that were different in the base type are considered equal in the
quotient type. In mathematical terms, the quotient type is isomorphic to a
partition of the base type.

To define a quotient type, we need to provide a type that it is derived from and
a equivalence relation on it that determines which elements are considered
equal. -/

#check quotient
#print setoid

#check quotient.mk
#check quotient.sound
#check quotient.exact

#check quotient.lift
#check quotient.lift₂
#check quotient.induction_on


/-! ## First Example: Integers

Let us build the integers `ℤ` as a quotient over pairs of natural numbers
`ℕ × ℕ`.

A pair `(p, n)` of natural numbers represents the integer `p - n`. Nonnegative
integers `p` can be represented by `(p, 0)`. Negative integers `-n` can be
represented by `(0, n)`. However, many representations of the same integer are
possible; e.g., `(7, 0)`, `(8, 1)`, `(9, 2)`, and `(10, 3)` all represent the
integer `7`.

Which equivalence relation can we use?

We want two pairs `(p₁, n₁)` and `(p₂, n₂)` to be equal if `p₁ - n₁ = p₂ - n₂`.
However, this does not work because subtraction on `ℕ` is ill-behaved (e.g.,
`0 - 1 = 0`). Instead, we use `p₁ + n₂ = p₂ + n₁`. -/

@[instance] def int.rel : setoid (ℕ × ℕ) :=
{ r     :=
    λpn₁ pn₂ : ℕ × ℕ,
      prod.fst pn₁ + prod.snd pn₂ = prod.fst pn₂ + prod.snd pn₁,
  iseqv :=
    begin
      repeat { apply and.intro },
      { intro pn,
        refl },
      { intros pn₁ pn₂ h,
        rw h },
      { intros pn₁ pn₂ pn₃ h₁₂ h₂₃,
        apply @add_right_cancel _ _ _ (prod.snd pn₂),
        cc }
    end }

#print equivalence

lemma int.rel_iff (pn₁ pn₂ : ℕ × ℕ) :
  pn₁ ≈ pn₂ ↔
  prod.fst pn₁ + prod.snd pn₂ = prod.fst pn₂ + prod.snd pn₁ :=
by refl

def int : Type :=
quotient int.rel

def int.zero : int :=
⟦(0, 0)⟧

lemma int.zero_eq (m : ℕ) :
  int.zero = ⟦(m, m)⟧ :=
begin
  rw int.zero,
  apply quotient.sound,
  rw int.rel_iff,
  simp
end

def int.add : int → int → int :=
quotient.lift₂
  (λpn₁ pn₂ : ℕ × ℕ,
     ⟦(prod.fst pn₁ + prod.fst pn₂,
       prod.snd pn₁ + prod.snd pn₂)⟧)
  begin
    intros pn₁ pn₂ pn₁' pn₂' h₁ h₂,
    apply quotient.sound,
    rw int.rel_iff at *,
    linarith
  end

lemma int.add_eq (p₁ n₁ p₂ n₂ : ℕ) :
  int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ = ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
by refl

lemma int.add_zero (i : int) :
  int.add int.zero i = i :=
begin
  apply quotient.induction_on i,
  intro pn,
  rw int.zero,
  cases' pn with p n,
  rw int.add_eq,
  apply quotient.sound,
  simp
end

/-! This definitional syntax would be nice: -/

-- fails
def int.add : int → int → int
| ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ := ⟦(p₁ + p₂, n₁ + n₂)⟧

/-! But it would be dangerous: -/

-- fails
def int.fst : int → ℕ
| ⟦(p, n)⟧ := p

/-! Using `int.fst`, we could derive `false`. First, we have

    `int.fst ⟦(0, 0)⟧ = 0`
    `int.fst ⟦(1, 1)⟧ = 1`

But since `⟦(0, 0)⟧ = ⟦(1, 1)⟧`, we get

    `0 = 1` -/


/-! ### Second Example: Unordered Pairs

__Unordered pairs__ are pairs for which no distinction is made between the first
and second components. They are usually written `{a, b}`.

We will introduce the type `upair` of unordered pairs as the quotient of pairs
`(a, b)` with respect to the relation "contains the same elements as". -/

@[instance] def upair.rel (α : Type) : setoid (α × α) :=
{ r     := λab₁ ab₂ : α × α,
    ({prod.fst ab₁, prod.snd ab₁} : set α) =
    ({prod.fst ab₂, prod.snd ab₂} : set α),
  iseqv := by repeat { apply and.intro }; finish }

-- needed for technical reasons, to deprioritize `upair.rel` w.r.t. `int.rel`
attribute [instance, priority 999] upair.rel

lemma upair.rel_iff {α : Type} (ab₁ ab₂ : α × α) :
  ab₁ ≈ ab₂ ↔
  ({prod.fst ab₁, prod.snd ab₁} : set α) =
  ({prod.fst ab₂, prod.snd ab₂} : set α) :=
by refl

def upair (α : Type) : Type :=
quotient (upair.rel α)

def upair.mk {α : Type} (a b : α) : upair α :=
⟦(a, b)⟧

/-! It is easy to prove that the `upair.mk` constructor is symmetric: -/

lemma upair.mk_symm {α : Type} (a b : α) :
  upair.mk a b = upair.mk b a :=
begin
  unfold upair.mk,
  apply quotient.sound,
  rw upair.rel_iff,
  apply set.union_comm
end

/-! Another representation of unordered pairs is as sets of cardinality 1 or 2.
The following operation converts `upair` to that representation: -/

def set_of_upair {α : Type} : upair α → set α :=
quotient.lift (λab : α × α, {prod.fst ab, prod.snd ab})
  begin
    intros ab₁ ab₂ h,
    rw upair.rel_iff at *,
    exact h
  end


/-! ### Alternative Definitions via Normalization and Subtyping

Each element of a quotient type correspond to an `≈`-equivalence class.
If there exists a systematic way to obtain a **canonical representative** for
each class, we can use a subtype instead of a quotient, keeping only the
canonical representatives.

Consider the quotient type `int` above. We could say that a pair `(p, n)` is
__canonical__ if `p` or `n` is `0`. -/

namespace alternative

inductive int.is_canonical : ℕ × ℕ → Prop
| nonpos {n : ℕ} : int.is_canonical (0, n)
| nonneg {p : ℕ} : int.is_canonical (p, 0)

def int : Type :=
{pn : ℕ × ℕ // int.is_canonical pn}

/-! **Normalizing** pairs of natural numbers is easy: -/

def int.normalize : ℕ × ℕ → ℕ × ℕ
| (p, n) := if p ≥ n then (p - n, 0) else (0, n - p)

lemma int.is_canonical_normalize (pn : ℕ × ℕ) :
  int.is_canonical (int.normalize pn) :=
begin
  cases' pn with p n,
  simp [int.normalize],
  split_ifs,
  { exact int.is_canonical.nonneg },
  { exact int.is_canonical.nonpos }
end

/-! For unordered pairs, there is no obvious normal form, except to always put
the smaller element first (or last). This requires a linear order `≤` on `α`. -/

def upair.is_canonical {α : Type} [linear_order α] :
  α × α → Prop
| (a, b) := a ≤ b

def upair (α : Type) [linear_order α] : Type :=
{ab : α × α // upair.is_canonical ab}

end alternative

end LoVe
