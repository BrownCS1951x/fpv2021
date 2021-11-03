/-

# Chapter 12: complex numbers playground 

This file contains some scattered code from the Ch 12 lectures,
where we attempted to build a bit of API around the complex numbers.

-/

import algebra.group.basic 
import data.real.basic
import analysis.special_functions.trigonometric

section
variables {α β : Type} [group α] [group β]
  (f : α → β)
  (hf : ∀ a b : α, f (a*b) = f a * f b)

include hf

lemma f_one_eq_one :
  f 1 = 1 := 
begin 
  have h1 : f (1 * 1) = f 1 * f 1 := hf 1 1,
  rw one_mul at h1,
  rw self_eq_mul_left at h1,
  -- simp at h1,
  assumption
end 
#check @f_one_eq_one
lemma f_inv_eq_inv  :
  ∀ a, f (a⁻¹) = (f a)⁻¹ :=
begin
  intro a,
  have h1 : f a * f (a⁻¹)  = 1 := begin 
    rw [← hf, mul_right_inv],
    apply f_one_eq_one,
    apply hf
  end,
  exact (inv_eq_of_mul_eq_one h1).symm
end
end 

namespace new 

structure complex : Type :=
(r im : ℝ)

def add (c1 c2 : complex) : complex :=
{ r := c1.r + c2.r, im := c1.im + c2.im }

def neg (c : complex) : complex :=
{ r := -c.r, im := -c.im }

def mul (c1 c2 : complex) : complex :=
{ r := c1.r*c2.r - c1.im*c2.im, im := c1.r*c2.im + c1.im*c2.r  }

instance : comm_ring complex :=
{ add := add,
  mul := mul,
  zero := {r := 0, im := 0},
  one := {r := 1, im := 0},
  neg := neg, 
  add_comm := sorry,
  add_assoc := sorry,
  zero_add := sorry,
  add_zero := sorry,
  add_left_neg := sorry,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  mul_comm := sorry }

lemma mul_eq (c1 c2 : complex) : 
  c1 * c2 = { r := c1.r*c2.r - c1.im*c2.im, im := c1.r*c2.im + c1.im*c2.r } :=
by refl

def conjugate (a : complex) : complex :=
{ r := a.r, im := - a.im }

theorem mul_conjugate (a : complex) : (a * conjugate a).im = 0 :=
begin
  cases a,
  simp [conjugate, mul_eq],
  ring
end

-- returns (angle, radius)
noncomputable def to_polar (c : complex) : ℝ × ℝ :=
(real.arctan (c.im / c.r), real.sqrt (c.r^2 + c.im^2))

noncomputable def from_polar (angle radius : ℝ) : complex :=
{ r := radius * real.cos angle, im := radius * real.sin angle }

example (angle radius : ℝ) (h_rad : radius > 0) (h_angle1 : -(real.pi / 2) < angle)
  (h_angle2 : angle < real.pi / 2): 
  to_polar (from_polar angle radius) = (angle, radius) :=
begin 
  simp [to_polar, from_polar],
  split,
  { calc 
    real.arctan (radius * real.sin angle / (radius * real.cos angle)) = 
      real.arctan (real.sin angle / real.cos angle): _
    ... = real.arctan (real.tan angle) : _
    ... = angle : _,
    
    { rw mul_div_mul_left,
      linarith },
    { rw real.tan_eq_sin_div_cos },
    { rw real.arctan_tan, assumption, assumption }
     },
  { rw [← eq_of_sq_eq_sq, real.sq_sqrt]
    -- we should be able to finish the remaining stuff 
  }
end

def of_real (r : ℝ) : complex :=
{ r := r, im := 0 }

instance : has_coe ℝ complex :=
{ coe := of_real }

example (r : ℝ) (c : complex) : c + r = c + r :=
by refl

end new 
