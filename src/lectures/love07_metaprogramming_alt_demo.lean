import .lovelib

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

def list.multimap₁ {α : Type} (f : α → α) : list α → list α
| [] := []
| (h::t) := f h :: list.multimap₁ (list.map f t)

def list.multimap₂ {α : Type} (f : α → α) : list α → list α
| [] := []
| (h::t) := 
  have hl : list.sizeof (list.map f t) < 1 + list.sizeof t := sorry,
  f h :: list.multimap₂ (list.map f t)

#eval list.multimap₂ (λ x, x + 1) [0, 0, 0, 0]

def list.multimap₃ {α : Type} (f : α → α) : list α → list α
| [] := []
| (h::t) := 
  have hl : list.length (list.map f t) < list.length t + 1 :=
    by simp [list.map_length, nat.lt_succ_self],
  f h :: list.multimap₃ (list.map f t)
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

Extra reference: https://leanprover.github.io/programming_in_lean/#07_Monads.html

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

To be properly "meta," our tactics should be able to express 
and manipulate Lean programs (= terms).
We see these in Lean as traditional data types. But, like `tactic_state` 
and others, the runtime representation of these is different.

-/

#check declaration 
#check tactic.get_decl

#check name 
#print name 

#check `nat 
#check `nat.succ 

#print prefix name

#check expr 
#print expr 

#check expr.to_raw_fmt

open tactic 

run_cmd do 
  d ← get_decl `nat.succ,
  trace d.type.to_raw_fmt

/-!

A closed expression (e.g. the type or body of a declaration in the environment)
should have no occurrences of `local_const` or `mvar`. 
`elet` and `macro` can always be expanded. 

Bound variables (`var`) are indexed by natural numbers, not names!
The names and types are stored in the binders (`lam` or `pi`). 
`var 0` refers to "the variable bound by the closest binder."
`var 1` refers to "the variable bound by the second-closest binder."
And so on.

But often we aren't dealing with closed expressions. 
If we get the type of the goal in the middle of a proof, it will probably refer 
to things in the local context. 
These are represented as local constants, `local_const`. 
They have a unique name, pretty-printing name, binder info, and type. 

-/

meta def expr.local_unique_name : expr → name 
| (expr.local_const nm ppnm bi tp) := nm
| _ := default _

example (a a a : ℕ) : true := by do 
  lc ← local_context, 
  trace lc,
  trace (lc.map expr.local_unique_name),
  triv

/-!

Things that are already defined in our environment can be accessed as `const`s. 
A `const` has a name and list of universe parameters.

Often we won't build these by hand, but use `tactic.mk_const`.
-/

#check expr.const `nat []
run_cmd do 
  e ← mk_const `nat,
  trace e.to_raw_fmt 

/-!
Building expressions by hand is rather cumbersome. There are ways around this. 
`tactic.mk_app` will fill in implicit arguments for you.
-/

#check tactic.mk_app

run_cmd do 
  z ← mk_const `nat.zero,
  a ← mk_app `nat.add [z, z],
  trace a,
  if a = z then trace "eq" else trace "neq"

/-!
We can also write *quoted* expressions, like quoted names.
-/

#check `(0 + 0)

/-!
We can insert expressions into quoted expressions using antiquotes:
-/

meta def trace_add_expr (e : expr) : tactic unit := 
trace `(0 + %%e)

run_cmd trace_add_expr `(44)

run_cmd trace_add_expr `(nat)

/-! 
Sometimes expr quoting fails. In these cases, we might have to use `pexpr`s.
A pre-expression corresponds to unelaborated, input-level syntax:
implicit arguments have not been filled in yet.

`tactic.to_expr` performs *elaboration*: it turns a `pexpr` into an `expr`.
-/

meta def trace_add_expr' (e : expr) : tactic unit := 
trace `(%%e + %%e)

meta def trace_add_expr' (e : expr) : tactic unit := do 
  e ← to_expr ``(%%e + %%e),
  trace e

run_cmd trace_add_expr' `(44)

run_cmd trace_add_expr' `(nat)

/-!
We can walk through expressions, normally and monadically:
-/

#check @expr.fold

#eval expr.fold `(1 + 0) "" (λ e _ s, s ++ ", " ++ to_string e)

#check @expr.mfold 

run_cmd expr.mfold `(1 + 0) () (λ e _ _, tactic.trace e)


/-!
One of the most important operations on `expr` is type inference.
-/

run_cmd do 
  t ← infer_type `(λ x : ℕ, x + 1),
  trace t

/-!

*Declarations* are stored in the *environment*. 
A declaration is an axiom, constant, theorem, or definition. 

-/

#check tactic.get_env
#check environment.fold 
#check environment.mfold

run_cmd do 
  e ← get_env,
  environment.mfold e () (λ d _, tactic.trace (declaration.to_name d))

/-!
## Working with goals and hypotheses 

We already saw the tactic `local_context` for getting hypotheses. 
`target` returns the type of the goal.
`get_local` retrieves a single hypothesis by name.
-/

example (a b c : ℕ) (h : a + b = c) : a + c + 0 = a + c + 1 - 1 :=
by do 
  lc ← local_context,
  trace lc,
  lc_types ← list.mmap infer_type lc, 
  trace lc_types,
  tgt ← target,
  trace tgt,
  admit

/-!
`tactic.assert` adds a new hypothesis, creating a new goal for its proof. 

There are lots of variants. 
-/

example (a b c : ℕ) : true :=
by do 
  ac ← get_local `a,
  bc ← get_local `b,  
  tactic.assert `new_hyp `(%%ac + %%bc = 0),
  trace_state,
  admit, 
  admit 

#check tactic.assert 
#check tactic.assertv 
#check @tactic.note 
#check @tactic.note_anon

/-!

To modify the goal, we have our familiar `apply` tactic, 
in a few variants:

-/

#check tactic.apply 
#check tactic.applyc
#check tactic.exact

/-!
There are lots of ways to call the simplifier...
-/

#check tactic.simplify
#check tactic.simp_target
#check tactic.simp_hyp 

/-!
If you want the familiar begin..end block syntax, there's 
yet another form of quotation: e.g.

    `[simp [lemma1, lemma2] at h] 

is of type `tactic unit`. 
-/

example (a b c : ℕ) (h : a + b = c) : a + c + 0 = a + c + 1 - 1 :=
by do 
  lc ← local_context,
  trace lc,
  lc_types ← list.mmap infer_type lc, 
  trace lc_types,
  tgt ← target,
  trace tgt,
  `[simp]




/-! ## Example: A Conjuction-Destructing Tactic

We define a `destruct_and` tactic that automates the elimination of `∧` in
premises, automating proofs such as these: -/

lemma abcd_a (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  a :=
and.elim_left h

lemma abcd_b (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b :=
and.elim_left (and.elim_left (and.elim_right h))

lemma abcd_bc (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ c :=
and.elim_left (and.elim_right h)

/-! Our tactic relies on a helper metafunction, which takes as argument the
hypothesis `h` to use as an expression rather than as a name: -/

meta def destruct_and_helper : expr → tactic unit
| h :=
  do
    t ← tactic.infer_type h,
    match t with
    | `(%%a ∧ %%b) :=
      tactic.exact h
      <|>
      do {
        ha ← tactic.to_expr ``(and.elim_left %%h),
        destruct_and_helper ha }
      <|>
      do {
        hb ← tactic.to_expr ``(and.elim_right %%h),
        destruct_and_helper hb }
    | _            := tactic.exact h
    end

meta def tactic.destruct_and (nam : name) : tactic unit :=
do
  h ← tactic.get_local nam,
  destruct_and_helper h

/-! Let us check that our tactic works: -/

lemma abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
  a :=
by tactic.destruct_and `h

lemma abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
  b :=
by tactic.destruct_and `h

lemma abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c :=
by tactic.destruct_and `h

lemma abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
  a ∧ c :=
by destruct_and `h   -- fails


/-!
## Interactive parsing

Writing 
    destruct_and `h
with the quoted name `h` is ugly. We don't want to do this in our tactic proofs. 
And indeed, most of the time, we don't have to:
there's no quoting in `apply h`, `simp [h]`, etc.


There's some trickery going on here at the parser level. 
`begin...end` and `by` blocks are parsed in "interactive tactic mode."
When we wrote `by destruct_and` above, Lean first looked for a declaration 
called `tactic.interactive.destruct_and`. When it failed to find such a tactic,
it fell back on resolving `destruct_and` in the normal way. 
-/

#check @tactic.apply
#check @tactic.interactive.apply

/-!
Instead of taking arguments of type `expr`, `name`, etc., interactive mode tactics
take parser commands. 

`setup_tactic_parser` is equivalent to 
```
open _root_.lean
open _root_.lean.parser
open _root_.interactive _root_.interactive.types
local postfix `?`:9001 := optional
local postfix *:9001 := many .
```
-/
 
section interactive_mode

setup_tactic_parser 

meta def _root_.tactic.interactive.destruct_and (h : parse ident) : tactic unit :=
tactic.destruct_and h


/-!
`parse ident` is definitionally equal to `name`, but in interactive mode,
we can write it unquoted.
We put this in the `_root_` namespace to escape the `LoVe` namespace. 
-/


lemma abc_bc' (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c :=
by destruct_and h



#check parse parser.pexpr 
#check parse pexpr_list
#check parse ident*
#check parse ident?

end interactive_mode


meta def tactic.destruct_and_anon : tactic unit :=
do 
  lc ← local_context,
  lc.mfirst (λ h, destruct_and_helper h)


section interactive_mode

setup_tactic_parser

meta def _root_.tactic.interactive.destruct_and' (h : parse ident?) : tactic unit :=
match h with 
| some h' := tactic.destruct_and h'
| none    := tactic.destruct_and_anon
end 


lemma abc_bc'' (a b c : Prop) (h : a ∧ b ∧ c) :
  b ∧ c :=
by destruct_and'



end interactive_mode 

/-!

## Goal management

We know that tactics ultimately need to build a proof term. 
How does this actually happen?

At the beginning of a begin...end block where the goal is to prove `T`, 
Lean creates a *metavariable* `?m1 : T`. 
Tactics that update the goal, like `applyc`, 
(partially) assign values to the goal metavariable.
These values can contain new metavariables. 

-/

example : true ∧ false :=
by do 
  gs ← get_goals,
  trace gs,
  trace (gs.map expr.to_raw_fmt),
  gs' ← gs.mmap infer_type,
  trace gs',
  let orig_goal := gs.head,
  trace "------",

  applyc `and.intro,

  gs ← get_goals,
  trace gs,
  trace (gs.map expr.to_raw_fmt),
  gs' ← gs.mmap infer_type,
  trace gs',
  trace "------",

  orig_goal ← instantiate_mvars orig_goal, 
  trace orig_goal.to_raw_fmt

/-!
`get_goals` returns a list of metavariables (of type `epxr`),
representing the remaining proof obligations. 
*Unifying* these metavariables with other terms will create partial assignments.

(This is a very low-level technique, we don't usually do this in practice!)
-/

example : true :=
by do 
  [g] ← get_goals,
  trace g,
  unify g `(trivial),
  gs ← get_goals,
  trace gs,
  set_goals [],
  gs ← get_goals,
  trace gs



/-!
Note that this can also get us in "trouble": we can tell the system we've 
finished a proof when we really haven't.
-/


meta def _root_.tactic.interactive.oops : tactic unit :=
do 
  mv ← mk_meta_var `(true),
  set_goals [mv]

example : false :=
begin 
  oops,
  trivial,
end 


/-!

Metavariable assignments are stored in the tactic state. 
So the ultimate goal of a begin...end block is:
"write a function tactic_state → tactic_state that assigns the initial goal 
metavariable to a term that does not contain any metavariables."

-/


/-! 

## Proof by reflection

YOu may have noticed that we can't prove anything about the tactics we write. 
But there's a middle ground: sometimes with a bit of meta "wrapper code,"
we can turn proofs about syntax-like operations into actual proof terms. 

The general strategy looks like this:
* represent the syntax of some class of formulas in (non-meta) Lean 
* define an interpretation function from these formulas to Prop
* define some operation on this syntax, and prove it correct with respect to the interpretation 
* write a small bit of meta code that turns a goal into a statement about your reflected syntax 

The idea is that the goal left after applying your correctness theorem can be proved by computation.

This is commonly used for evaluation or normalization functions. 
`ring`, for example, can be implemented by defining the syntax of ring expressions 
and verifying a normalization algorithm: 
if 
`ring_syntax : Type`,
`interp {α : Type} [ring α] : ring_syntax → α`,
`normalize : ring_syntax → ring_syntax`, then 
`∀ r1 r2 : ring_syntax, interp r1 = interp r2 ↔ normalize r1 = normalize r2`. 

The meta code looks at a goal `c + a*b = b*a + c`,
constructs `ring_syntax` objects `r1` and `r2` representing both sides,
and changes the goal to showing that `normalize r1 = normalize r2`. 
This can be proved by `refl`.

You could imagine doing the same with, say, a SAT solver.
-/

inductive bexpr 
| atom : bool → bexpr 
| and : bexpr → bexpr → bexpr 
| or : bexpr → bexpr → bexpr 
| imp : bexpr → bexpr → bexpr 
| not : bexpr → bexpr 

open bexpr

def interp : bexpr → Prop 
| (atom tt) := true 
| (atom ff) := false
| (and a b) := interp a ∧ interp b
| (or a b) := interp a ∨ interp b
| (imp a b) := interp a → interp b
| (not b) := ¬ interp b

@[simp]
def normalize : bexpr → bool 
| (atom b) := b
| (and a b) := normalize a && normalize b
| (or a b) := normalize a || normalize b
| (imp a b) := (bnot (normalize a)) || normalize b
| (not b) := bnot (normalize b)

theorem normalize_correct (b : bexpr) : normalize b = tt ↔ interp b :=
begin 
  induction' b; try {simp [interp] at *},
  case and : { finish },
  case or : { finish },
  case not : { simpa using not_iff_not.mpr ih },
  case atom:
  { cases b,
    { simp [normalize], intro h, cases h },
    { simp [interp] } },
  case imp : 
  { have h_not : normalize b = ff ↔ ¬ interp b := by simpa using not_iff_not.mpr ih_b,
    simp [imp_iff_not_or, *] },
end 

meta def bexpr_of_expr : expr → option expr 
| `(true) := some `(bexpr.atom tt)
| `(false) := some `(bexpr.atom ff)
| `(%%a ∧ %%b) := do a ← bexpr_of_expr a, b ← bexpr_of_expr b, some `(bexpr.and %%(a) %%(b))
| `(%%a ∨ %%b) := do a ← bexpr_of_expr a, b ← bexpr_of_expr b, some `(bexpr.or %%(a) %%(b))
| `(%%a → %%b) := do a ← bexpr_of_expr a, b ← bexpr_of_expr b, some `(bexpr.imp %%(a) %%(b))
| `(¬ %%a) := do a ← bexpr_of_expr a, some `(bexpr.not %%(a))
| _ := none

meta def _root_.tactic.interactive.change_goal : tactic unit :=
do 
  t ← target, 
  match bexpr_of_expr t with 
  | some t' := do apply `(iff.mp (normalize_correct %%(t'))), skip
  | none := fail "goal is not a bexpr pattern"
  end


example : (true → true) ∨ false :=
begin 
  change_goal,
  refl
end

end LoVe 