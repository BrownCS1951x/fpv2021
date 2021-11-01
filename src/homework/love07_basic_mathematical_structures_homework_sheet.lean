import ..lectures.love12_basic_mathematical_structures_demo
import data.int.gcd

/-! # LoVe Homework 7: Basic Mathematical Structures 

This homework covers Ch 12 of the HHG.

-/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Numbers and embeddings (5 points)

We start with some questions to get you used to the "numeral tactics".

Remember that:
* `norm_num` will simplify numeral expressions without variables. 
* `norm_cast` will simplify expressions with coercions.
* If you have an assumption `hx`, you can also `norm_cast at hx`.
* `exact_mod_cast h` is like `exact h`, except it will call `norm_cast` on `h` and the goal.


1.1 (1 point).
Use these tactics to solve the following problems.
-/

lemma num1 : 12345 < 67890 := 
sorry

lemma num2 {α : Type} [linear_ordered_field α] : 123 + 45 < 67890/3 := 
sorry 

lemma num3 (x : ℤ) (hx : (x : ℝ) < 25*100) : x < 25*100 := 
sorry

/-!
1.2 (1 point). For each of these statements, either prove it, or prove its negation. 
Think about why the statement (or its negation) is true!
-/

lemma num4 : 7/3 > 2 := 
sorry 

lemma num5 : 40 - (2*30) + 20 = 0 := 
sorry 

lemma num6 : 5 / (2 - 1 - 1) + 8 = 2 * 4 := 
sorry


/-!
1.3 (3 points). 


This seems like a very natural way to write the theorem
"If `a` and `b` are coprime, then there are coefficients `u` and `v` such that `u*a + v*b = 1`."
But I've made a mistake! What did I do wrong? Correct the statement of the theorem and prove it.

You'll probably find the lemmas `nat.gcd_eq_gcd_ab` and `nat.coprime.gcd_eq_one` helpful.
-/
#check nat.gcd_eq_gcd_ab
#check nat.coprime.gcd_eq_one 

lemma sum_eq_one_of_coprime (a b : ℕ) (h : nat.coprime a b) : ∃ u v, u*a+v*b = 1 :=
sorry 

/-! ## Question 2: algebraic lemmas and classes (7 points)

2.1. (2 points) State and prove a lemma that says: 
for any element `x` of an additive monoid, if `x` has a left inverse `y` 
and a right inverse `z`, then `y = z`. 
-/

-- your answer here


/-!
2.2 (2 points). A `rng` (not a random number generator)
is an algebraic structure like a ring, but that does not require 
a multiplicative identity element.
<https://en.wikipedia.org/wiki/Rng_(algebra)>

Define a type class `rng` that represents the structure, in the style of 
the "monolithic group" from the Ch 12 demo. 
That is, your structure should not extend existing structures:
bundle all of the necessary axioms into your definition. 
-/

#check monolithic_group.group

@[class] structure rng (α : Type) : Type :=
sorry 

/-! 2.3 (2 points). Define an instance that shows that any `rng` is an `add_monoid`. -/

instance {α : Type} [rng α] : add_monoid α :=
sorry 

/-! 2.4 (1 point). Show that for any `α : Type`, the type of functions `α → α` is 
a monoid under the composition operator: `f * g = λ x, f (g x))` 
-/

instance (α : Type) : monoid (α → α) := 
sorry

end LoVe