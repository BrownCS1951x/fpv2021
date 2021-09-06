import ..lovelib


/-!

# LoVe Demo 1: Definitions and Statements

We introduce the basics of Lean and proof assistants, without trying to carry
out actual proofs yet. We focus on specifying objects and statements of their
intended properties. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## A View of Lean

In a first approximation:

    Lean = functional programming + logic

In today's lecture, we cover inductive types, recursive functions, and lemma
statements.

If you are not familiar with typed functional programming (e.g., Haskell, ML,
OCaml, Scala), we recommend that you study a tutorial, such as the first
chapters of the online tutorial __Learn You a Haskell for Great Good!__:

    http://learnyouahaskell.com/chapters

Make sure to at least reach the section titled "Lambdas".


## Types and Terms

Similar to simply typed λ-calculus or typed functional programming languages
(ML, OCaml, Haskell).

Types `σ`, `τ`, `υ`:

* type variables `α`;
* basic types `T`;
* complex types `T σ1 … σN`.

Some type constructors `T` are written infix, e.g., `→` (function type).

The function arrow is right-associative:
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`.

Polymorphic types are also possible. In Lean, the type variables must be bound
using `∀`, e.g., `∀α, α → α`.

Terms `t`, `u`:

* constants `c`;
* variables `x`;
* applications `t u`;
* λ-expressions `λx, t`.

__Currying__: functions can be

* fully applied (e.g., `f x y z` if `f` is ternary);
* partially applied (e.g., `f x y`, `f x`);
* left unapplied (e.g., `f`).

Application is left-associative: `f x y z` = `((f x) y) z`. -/

#check ℕ
#check ℤ

#check empty
#check unit
#check bool

#check ℕ → ℤ
#check ℤ → ℕ
#check bool → ℕ → ℤ
#check (bool → ℕ) → ℤ
#check ℕ → (bool → ℕ) → ℤ

#check λx : ℕ, x
#check λf : ℕ → ℕ, λg : ℕ → ℕ, λh : ℕ → ℕ, λx : ℕ, h (g (f x))
#check λ(f g h : ℕ → ℕ) (x : ℕ), h (g (f x))

constants a b : ℤ
constant f : ℤ → ℤ
constant g : ℤ → ℤ → ℤ

#check λx : ℤ, g (f (g a x)) (g x b)
#check λx, g (f (g a x)) (g x b)

#check λx, x

constant trool : Type
constants trool.true trool.false trool.maybe : trool


/-! ### Type Checking and Type Inference

Type checking and type inference are decidable problems, but this property is
quickly lost if features such as overloading or subtyping are added.

Type judgment: `C ⊢ t : σ`, meaning `t` has type `σ` in local context `C`.

Typing rules:

    —————————— Cst   if c is declared with type σ
    C ⊢ c : σ

    —————————— Var   if x : σ occurs in C
    C ⊢ x : σ

    C ⊢ t : σ → τ    C ⊢ u : σ
    ——————————————————————————— App
    C ⊢ t u : τ

    C, x : σ ⊢ t : τ
    ———————————————————————— Lam
    C ⊢ (λx : σ, t) : σ → τ


### Type Inhabitation

Given a type `σ`, the __type inhabitation__ problem consists of finding a term
of that type.

Recursive procedure:

1. If `σ` is of the form `τ → υ`, a candidate inhabitant is an anonymous
   function of the form `λx, _`.

2. Alternatively, you can use any constant or variable `x : τ₁ → ⋯ → τN → σ` to
   build the term `x _ … _`. -/

constants α β γ : Type

def some_fun_of_type : (α → β → γ) → ((β → α) → β) → α → γ :=
λf g a, f a (g (λb, a))


/-! ## Type Definitions

An __inductive type__ (also called __inductive datatype__,
__algebraic datatype__, or just __datatype__) is a type that consists all the
values that can be built using a finite number of applications of its
__constructors__, and only those.


### Natural Numbers -/

namespace my_nat

/-! Definition of type `nat` (= `ℕ`) of natural numbers, using Peano-style unary
notation: -/

inductive nat : Type
| zero : nat
| succ : nat → nat

#check nat
#check nat.zero
#check nat.succ

end my_nat

#print nat
#print ℕ


/-! ### Arithmetic Expressions -/

inductive aexp : Type
| num : ℤ → aexp
| var : string → aexp
| add : aexp → aexp → aexp
| sub : aexp → aexp → aexp
| mul : aexp → aexp → aexp
| div : aexp → aexp → aexp


/-! ### Lists -/

namespace my_list

inductive list (α : Type) : Type
| nil  : list
| cons : α → list → list

#check list.nil
#check list.cons

end my_list

#print list


/-! ## Function Definitions

The syntax for defining a function operating on an inductive type is very
compact: We define a single function and use __pattern matching__ to extract the
arguments to the constructors. -/

def add : ℕ → ℕ → ℕ
| m nat.zero     := m
| m (nat.succ n) := nat.succ (add m n)

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
| _ nat.zero     := nat.zero
| m (nat.succ n) := add m (mul m n)

#eval mul 2 7

#print mul
#print mul._main

def power : ℕ → ℕ → ℕ
| _ nat.zero     := 1
| m (nat.succ n) := m * power m n

#eval power 2 5

def power₂ (m : ℕ) : ℕ → ℕ
| nat.zero     := 1
| (nat.succ n) := m * power₂ n

#eval power₂ 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
| nat.zero     := z
| (nat.succ n) := f (iter n)

#check iter

def power₃ (m n : ℕ) : ℕ :=
iter ℕ 1 (λl, m * l) n

#eval power₃ 2 5

def append (α : Type) : list α → list α → list α
| list.nil         ys := ys
| (list.cons x xs) ys := list.cons x (append xs ys)

#check append
#eval append _ [3, 1] [4, 1, 5]

/-! Aliases:

    `[]`          := `nil`
    `x :: xs`     := `cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []` -/

def append₂ {α : Type} : list α → list α → list α
| list.nil         ys := ys
| (list.cons x xs) ys := list.cons x (append₂ xs ys)

#check append₂
#eval append₂ [3, 1] [4, 1, 5]

#check @append₂
#eval @append₂ _ [3, 1] [4, 1, 5]

def append₃ {α : Type} : list α → list α → list α
| []        ys := ys
| (x :: xs) ys := x :: append₃ xs ys

def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

def eval (env : string → ℤ) : aexp → ℤ
| (aexp.num i)     := i
| (aexp.var x)     := env x
| (aexp.add e₁ e₂) := eval e₁ + eval e₂
| (aexp.sub e₁ e₂) := eval e₁ - eval e₂
| (aexp.mul e₁ e₂) := eval e₁ * eval e₂
| (aexp.div e₁ e₂) := eval e₁ / eval e₂

#eval eval (λs, 7) (aexp.div (aexp.var "x") (aexp.num 0))

/-! Lean only accepts the function definitions for which it can prove
termination. In particular, it accepts __structurally recursive__ functions,
which peel off exactly one constructor at a time.


## Lemma Statements

Notice the similarity with `def` commands. -/

namespace sorry_lemmas

lemma add_comm (m n : ℕ) :
  add m n = add n m :=
sorry

lemma add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
sorry

lemma mul_comm (m n : ℕ) :
  mul m n = mul n m :=
sorry

lemma mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
sorry

lemma mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
sorry

lemma reverse_reverse {α : Type} (xs : list α) :
  reverse (reverse xs) = xs :=
sorry

/-! Axioms are like lemmas but without proofs (`:= …`). Constant declarations
are like definitions but without bodies (`:= …`). -/

constants a b : ℤ

axiom a_less_b :
  a < b

end sorry_lemmas

end LoVe
