import ..lectures.love13_rational_and_real_numbers_demo
import data.nat.parity

/-! # LoVe Homework 9: Rationals, Reals, Quotients -/

namespace LoVe

/-! 

## Question 1 (4 points): Cauchy sequences 

1,1 (4 points). In the demo, we sorry'ed the proof that the sum of two Cauchy sequences is Cauchy.
Prove this!


Hint: depending on how you approach this, you might want to do a long calc-mode proof.  
It can be nice to structure this as

```
    begin
      <other tactics here>
      calc 
        t1 = t2 : _ 
       ... ≤ t3 : _ 
       ... < t4 : _ 
    end 
```
leaving the placeholders _ in the calc block. 
At the end of the calc block, you will be left with one goal for each step of the calculation. 

example:
-/

lemma quarter_pos {x : ℚ} (hx : 0 < x) : 0 < x / 4 := 
begin 
  have hx2 : 0 < x / 2 := half_pos hx,
  calc 0 < (x / 2) / 2 : _ 
     ... = x / 4 : _,
  { apply half_pos,
    exact hx2 },
  { ring }
end 

lemma sum_is_cauchy (f g : ℕ → ℚ) (hf : is_cau_seq f) (hg : is_cau_seq g) : 
  is_cau_seq (λ n, f n + g n) :=
sorry

/-! 
## Question 2 (4 points): Operations on the reals 

2.1 (3 points). In the demo, we proved `add_comm` on the reals by first proving it for 
Cauchy sequences and then lifting this proof. Follow this same procedure 
to prove `zero_add : ∀ x : real, 0 + x = x`. 
-/

open LoVe.cau_seq 


/-! 
2.2 (1 point). Every rational number corresponds to a real number. 
Define this coercion.
-/


instance rat_real_coe : has_coe ℚ real :=
{ coe := sorry }

/-! 

## Question 3 (6 points): Quotients in general 

In this problem we'll take a weird quotient of ℕ.

The following lemmas may be useful:
-/

#check nat.even_zero
#check nat.not_even_one

/-!  

3.1 (2 points). Define a setoid structure on ℕ using the equivalence relation 
where `x ≈ y` if and only if `x` and `y` are both even or both odd.
E.g. 0 ≈ 2, 1 ≈ 5, but ¬ 4 ≈ 5. 
-/
instance eqv : setoid ℕ :=
{ r := sorry,
  iseqv := sorry
}


/-! 
Now we'll define the quotient of ℕ by this relation. 
There are two elements of the quotient:
-/
def eonat := quotient LoVe.eqv  

def e : eonat := ⟦0⟧
def o : eonat := ⟦1⟧

/-!
3.2 (2 points). Prove that these are the only two elements of `eonat`.
-/
lemma e_or_o (x : eonat) : x = e ∨ x = o :=
sorry

/-!
3.3 (2 points). Lift the addition function on ℕ to `eonat`. 

What does the "addition table" for `eonat` look like? 
That is, what are e+e, o+o, e+o, and o+e? 
Prove two of these identities. 
-/

def add : eonat → eonat → eonat :=
sorry 


end LoVe