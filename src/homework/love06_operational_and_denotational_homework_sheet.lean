import ..lectures.love01_definitions_and_statements_demo
import ..lectures.love10_denotational_semantics_demo

/-!
# FPV Homework 6: Operational and denotational semantics

This homework corresponds to chapters 8 and 10 of the HHG.
-/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (4 points): Operational Semantics of Regular Expressions

Regular expression are a very popular tool for software development. Often,
when textual input needs to be analyzed it is matched against a regular
expression. In this question, we define the syntax of regular expressions and
what it means for a regular expression to match a string.

We define `regex` to represent the following grammar:

    R ::= ∅       — `nothing`: matches nothing
        | ε       — `empty`: matches the empty string
        | a       — `atom`: matches the atom `a`
        | R ⬝ R    — `concat`: matches the concatenation of two regexes
        | R + R   — `alt`: matches either of two regexes
        | R*      — `star`: matches arbitrary many repetitions of a regex

Notice the rough correspondence with a WHILE language:

    `empty`  ~ `skip`
    `atom`   ~ assignment
    `concat` ~ sequential composition
    `alt`    ~ conditional statement
    `star`   ~ while loop -/

inductive regex (α : Type) : Type
| nothing {} : regex
| empty   {} : regex
| atom       : α → regex
| concat     : regex → regex → regex
| alt        : regex → regex → regex
| star       : regex → regex

/-! The `matches r s` predicate indicates that the regular expression `r` matches
the string `s`. -/

inductive matches {α : Type } : regex α → list α → Prop
| empty :
  matches regex.empty []
| atom (a : α) :
  matches (regex.atom a) [a]
| concat {r₁ r₂ : regex α} (s₁ s₂ : list α) (h₁ : matches r₁ s₁)
    (h₂ : matches r₂ s₂) :
  matches (regex.concat r₁ r₂) (s₁ ++ s₂)
| alt_left {r₁ r₂ : regex α} (s : list α) (h : matches r₁ s) :
  matches (regex.alt r₁ r₂) s
| alt_right {r₁ r₂ : regex α} (s : list α) (h : matches r₂ s) :
  matches (regex.alt r₁ r₂) s
| star_base {r : regex α} :
  matches (regex.star r) []
| star_step {r : regex α} (s s' : list α) (h₁ : matches r s)
    (h₂ : matches (regex.star r) s') :
  matches (regex.star r) (s ++ s')

/-! The introduction rules correspond to the following cases:

* match the empty string
* match one atom (e.g., character)
* match two concatenated regexes
* match the left option
* match the right option
* match the empty string (the base case of `R*`)
* match `R` followed again by `R*` (the induction step of `R*`)

1.1 (1 point). Explain why there is no rule for `nothing`. -/

-- enter your answer here

/-! 1.2 (3 points). Prove the following inversion rules. -/

@[simp] lemma matches_atom {α : Type} {s : list α} {a : α} :
  matches (regex.atom a) s ↔ s = [a] :=
sorry

@[simp] lemma matches_nothing {α : Type} {s : list α} :
  ¬ matches regex.nothing s :=
sorry

@[simp] lemma matches_empty {α : Type} {s : list α} :
  matches regex.empty s ↔ s = [] :=
sorry

@[simp] lemma matches_concat {α : Type} {s : list α} {r₁ r₂ : regex α} :
  matches (regex.concat r₁ r₂) s
  ↔ (∃s₁ s₂, matches r₁ s₁ ∧ matches r₂ s₂ ∧ s = s₁ ++ s₂) :=
sorry

@[simp] lemma matches_alt {α : Type} {s : list α} {r₁ r₂ : regex α} :
  matches (regex.alt r₁ r₂) s ↔ (matches r₁ s ∨ matches r₂ s) :=
sorry



/-! ## Question 2: Monotonicity (4 points)

2.1 (2 points). Prove the following lemma from the Ch. 10 lecture. -/

lemma monotone_comp {α β : Type} [partial_order α] (f g : α → set (β × β))
    (hf : monotone f) (hg : monotone g) :
  monotone (λa, f a ◯ g a) :=
sorry

/-! 2.2 (2 points). Prove its cousin. -/

lemma monotone_restrict {α β : Type} [partial_order α] (f : α → set (β × β))
    (p : β → Prop) (hf : monotone f) :
  monotone (λa, f a ⇃ p) :=
sorry


/-! ## Question 3: Denotational Semantics of Regular Expressions (4 points)

In this exercise, we explore an alternative semantics of regular
expressions. Namely, we can imagine that the atoms represent binary relations,
instead of letters or symbols. Concatenation corresponds to composition of
relations, and alternation is union. Mathematically, regexes and binary
relations are both instances of Kleene algebras.

3.1 (2 points). Complete the following translation of regular expressions to relations.

Hint: Exploit the correspondence with the WHILE language. -/

def rel_of_regex {α : Type} : regex (set (α × α)) → set (α × α)
| regex.nothing        := ∅
| regex.empty          := Id
| (regex.atom s)       := s
-- enter the missing cases here

/-! 3.2 (2 points). Prove the following recursive equation about your definition. -/

lemma rel_of_regex_star {α : Type} (r : regex (set (α × α))) :
  rel_of_regex (regex.star r) =
  rel_of_regex (regex.alt (regex.concat r (regex.star r)) regex.empty) :=
sorry


end LoVe
