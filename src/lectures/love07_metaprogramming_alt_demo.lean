import ..lovelib

/-! # LoVe Demo 7: Metaprogramming

Users can extend Lean with custom tactics and tools. This kind of
programming—programming the prover—is called metaprogramming.

Lean's metaprogramming framework uses mostly the same notions and syntax as
Lean's input language itself. Abstract syntax trees __reflect__ internal data
structures, e.g., for expressions (terms). The prover's C++ internals are
exposed through Lean interfaces, which we can use for

* accessing the current context and goal;
* unifying expressions;
* querying and modifying the environment;
* setting attributes.

Most of Lean's predefined tactics are implemented in Lean (and not in C++).

Example applications:

* proof goal transformations;
* heuristic proof search;
* decision procedures;
* definition generators;
* advisor tools;
* exporters;
* ad hoc automation.

Advantages of Lean's metaprogramming framework:

* Users do not need to learn another programming language to write
  metaprograms; they can work with the same constructs and notation used to
  define ordinary objects in the prover's library.

* Everything in that library is available for metaprogramming purposes.

* Metaprograms can be written and debugged in the same interactive environment,
  encouraging a style where formal libraries and supporting automation are
  developed at the same time. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

/-! 

## Well-founded and non-well-founded recursion 

The recursive functions we've written are structurally recursive.
But sometimes this feels like too strong of a restriction.
-/

def list.map {α β : Type} (f : α → β) : list α → list β
| [] := [] 
| (h::t) := f h :: list.map t

lemma list.map_length {α β : Type} (f : α → β): ∀ l : 
  list α, list.length (list.map f l) = list.length l 
| [] := rfl 
| (h::t) := by simp [list.map, list.map_length]

def list.multimap' {α : Type} (f : α → α) : list α → list α
| [] := []
| (h::t) := f h :: list.multimap' (list.map f t)

def list.multimap {α : Type} (f : α → α) : list α → list α
| [] := []
| (h::t) := 
  have hl : list.sizeof (list.map f t) < 1 + list.sizeof t := sorry,
  f h :: list.multimap (list.map f t)

#eval list.multimap (λ x, x + 1) [0, 0, 0, 0]

def list.multimap' {α : Type} (f : α → α) : list α → list α
| [] := []
| (h::t) := 
  have hl : list.length (list.map f t) < list.length t + 1 :=
    by simp [list.map_length, nat.lt_succ_self],
  f h :: list.multimap' (list.map f t)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

/-!
Proving well-foundedness can be arbitrarily hard.
-/

def f : ℕ → ℕ
| n := if n = 1 then 1 
       else if n%2 = 0 then f (n/2)
       else f (3*n + 1)

/-!
All functions in "standard" Lean must terminate, otherwise we could prove false.

But maybe all we want to do is *compute* with the function, and not worry about
proving anything about it.

The keyword *meta* lets us do exactly this. 
Like *noncomputable*, *meta* is sticky: anything that references a meta declaration 
must be meta itself. 
All it does is disable the well-foundedness checker.
-/

meta def g : ℕ → ℕ
| n := if n = 1 then 1 
       else if n%2 = 0 then g (n/2)
       else g (3*n + 1)

#eval (list.iota 100).map g

meta def oops : false := oops

/-!

Note that this use of the word "meta" is somewhat misleading. 
Nothing is "about Lean" yet, we've just defined a language extension. 
Morally speaking, meta definitions are ones that we intend for "computation 
purposes only."


## What are tactics, really?

Recall that when we write a tactic proof, it's generating a proof term under the hood.

Between each tactic we can inspect a *proof state*, which has a context and goal. 

A tactic behaves like a function from proof state to proof state. 
-/

lemma test_lemma : ∀ x, x = 3 → x + 10 = 13 := 
begin 
  intros x hx,
  cases hx,
  refl
end

#print test_lemma 

/-
But tactics can fail. So they're not total functions. 
And tactics can also fail to terminate.
-/


-- example (x y z : ℕ) : x + y + z = z + y + x :=
-- by simp [add_comm x y, add_comm y x]


/-!


So it feels like we have something like

    meta def simp : simp_args → tactic_state → option tactic_state 

Which is actually not so far from the truth!



We've mentioned the difference between `#reduce` and `#eval`. 
`#eval` is for data only. It doesn't care about proof terms, instead interpreting
expressions in the Lean virtual machine. 

It replaces certain data types and operations with more efficient implementations,
e.g. arithmetic on `nat`. 

It also replaces certain *constants* with actual data.

-/


#print tactic_state
#print tactic_state.get_options 


/-

So a tactic in Lean is like a function `tactic_state → tactic_state`. 
It can use these uninterpreted constants like `get_options`. 
In a `begin...end` block, Lean generates the initial tactic state. 
Then it sequentially calls the tactics in the block, producing a new tactic state. 
When a tactic leaves a state that has no goals, the proof is done.


There are some hiccups here.
* "State"? Sounds imperative!
* Stringing together `option`-valued functions sounds annoying. 
* How do we write these? Can we read and write to the state at the same time?


These questions aren't unique to Lean -- these are common functional programming issues. 
They have a solution: *monads*.


## Monads

Monads are an abstraction of "programming with side effects."
The side effects we'll be interested in are state and failure. 


In general, a __monad__ is a type constructor `m` that depends on some type
parameter `α` (i.e., `m α`) equipped with two distinguished operations:

    `pure {α : Type} : α → m α`
    `bind {α β : Type} : m α → (α → m β) → m β`

Consider the following programming task:

    Implement a function `sum_2_5_7 ns` that sums up the second, fifth, and
    seventh items of a list `ns` of natural numbers. Use `option ℕ` for the
    result so that if the list has fewer than seven elements, you can return
    `option.none`.

A straightforward solution follows: -/

def sum_2_5_7 (ns : list ℕ) : option ℕ :=
match list.nth ns 1 with
| option.none    := option.none
| option.some n2 :=
  match list.nth ns 4 with
  | option.none    := option.none
  | option.some n5 :=
    match list.nth ns 6 with
    | option.none    := option.none
    | option.some n7 := option.some (n2 + n5 + n7)
    end
  end
end

/-!
`option` is a monad with failure. `some v` is the success case, 
`none` is the failure case.

If `v : ℕ`, then `pure v = some v`. `bind` is `connect`:
-/

def connect {α : Type} {β : Type} :
  option α → (α → option β) → option β
| option.none     f := option.none
| (option.some a) f := f a

def sum_2_5_7₂ (ns : list ℕ) : option ℕ :=
connect (list.nth ns 1)
  (λn2, connect (list.nth ns 4)
     (λn5, connect (list.nth ns 6)
        (λn7, option.some (n2 + n5 + n7))))


def sum_2_5_7₆ (ns : list ℕ) : option ℕ :=
do
  n2 ← list.nth ns 1,
  n5 ← list.nth ns 4,
  n7 ← list.nth ns 6,
  pure (n2 + n5 + n7)


/-!

Programming with state is also monadic. 

`action σ α` is the type of functions that take in a state of type `σ`
and produce a value of type `α`, along with a possibly updated state.
-/

def action (σ α : Type) : Type :=
σ → α × σ

def action.read {σ : Type} : action σ σ :=
λ s, (s, s)

def action.write {σ : Type} (s : σ) : action σ unit :=
λ _, ((), s)

def action.pure {σ α : Type} (a : α) : action σ α := 
λ s, (a, s)

def action.bind {σ : Type} {α β : Type} (ma : action σ α)
    (f : α → action σ β) :
  action σ β := 
λ s, match ma s with
| (a, s') := f a s'
end 


@[instance] def action.monad {σ : Type} :
  monad (action σ) :=
{ pure       := @action.pure σ,
  bind       := @action.bind σ }

def nat_action : action ℕ string :=
do 
  first_val ← action.read,
  action.write (first_val * 2),
  new_val ← action.read,
  pure (to_string first_val ++ " ---> " ++ to_string new_val)

#eval nat_action 3



/-!

## The tactic monad

tactic α := tactic_state → result tactic_state α

A tactic can read and/or modify the tactic state, and either succeeds
(producing a value of type α) or fails with an exception message.

-/

#print tactic 
#print result

#check tactic.local_context

open tactic 

meta def my_first_tactic : tactic unit :=
do 
  l ← local_context,
  trace l 

meta def show_true : tactic unit :=
do applyc `trivial

example (a b c : ℕ) (h : a + b + c = 0) : true :=
begin 
  my_first_tactic,
  show_true
end

run_cmd my_first_tactic

meta def apply_and : tactic unit :=
do 
  trace "applying and.intro",
  applyc `and.intro 

example : true ∧ true :=
begin
  apply_and,
  show_true, show_true
end

meta def apply_and_or_intro : tactic unit :=
do applyc `and.intro <|> 
do intro `nv, skip

example : false → true ∧ true :=
begin 
  apply_and_or_intro,
  apply_and_or_intro,
  show_true, show_true
end 

meta def my_repeat : tactic unit → tactic unit :=
λ t, (do t, my_repeat t) <|> skip

example : false → true ∧ true :=
begin 
  my_repeat apply_and_or_intro,
  my_repeat show_true
end 


/-!

## Built-in data types 

-/

#check name 
#print name 

#check expr 
#print expr 

end LoVe 