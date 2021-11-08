import ..lectures.love05_inductive_predicates_demo


/-! # LoVe Homework 11: Logical Foundations of Mathematics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Even Numbers as a Subtype

Usually, the most convenient way to represent even natural numbers is to use the
larger type `ℕ`, which also includes the odd natural numbers. If we want to
quantify only over even numbers `n`, we can add an assumption `even n` to our
lemma statement.

An alternative is to encode evenness in the type, using a subtype. We will
explore this approach.

1.1 (1 point). Define the type `evℕ` of even natural numbers, using the `even`
predicate introduced in the lecture 5 demo. -/

#print even

def evℕ : Type :=
sorry

/-! 1.2 (1 point). Prove the following lemma about the `even` predicate. You will
need it to answer question 1.3. -/

lemma even.add {m n : ℕ} (hm : even m) (hn : even n) :
  even (m + n) :=
sorry

/-! 1.3 (1 point). Define zero and addition of even numbers by filling in the
`sorry` placeholders. -/

def evℕ.zero : evℕ :=
sorry

def evℕ.add (m n : evℕ) : evℕ :=
sorry

/-! 1.4 (3 points). Prove that addition of even numbers is commutative and
associative, and has 0 as an identity element. -/

lemma evℕ.add_comm (m n : evℕ) :
  evℕ.add m n = evℕ.add n m :=
sorry

lemma evℕ.add_assoc (l m n : evℕ) :
  evℕ.add (evℕ.add l m) n = evℕ.add l (evℕ.add m n) :=
sorry

lemma evℕ.add_iden_left (n : evℕ) :
  evℕ.add evℕ.zero n = n :=
sorry

lemma evℕ.add_iden_right (n : evℕ) :
  evℕ.add n evℕ.zero = n :=
sorry



/- ## Question 2 (6 points): Multisets as a Quotient Type
A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.
Finite multisets can be defined as a quotient over lists. We start with the
type `list α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.
The `list.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `decidable_eq` type class. For this reason, the definitions and lemmas
below all take `[decidable_eq α]` as type class argument.

2.1 (1 point). Provide the missing proof below. -/

@[instance] def multiset.rel (α : Type) [decidable_eq α] : setoid (list α) :=
{ r     := λas bs, ∀x, list.count x as = list.count x bs,
  iseqv :=
    sorry }

/- 2.2 (1 point). Define the type of multisets as the quotient over the
relation `multiset.rel`. -/

def multiset (α : Type) [decidable_eq α] : Type :=
sorry

/- 2.3 (2 points). Now we have a type `multiset α` but no operations on it.
Basic operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum of two multisets (`A ⊎ B` for
any multisets `A` and `B`). The sum should be defined so that the multiplicities
of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.
Fill in the `sorry` placeholders below to implement the multiset union operation.
operations. -/

def multiset.empty {α : Type} [decidable_eq α] : multiset α :=
⟦[]⟧


def multiset.singleton {α : Type} [decidable_eq α] (a : α) : multiset α :=
⟦[a]⟧


def multiset.union {α : Type} [decidable_eq α] :
  multiset α → multiset α → multiset α :=
quotient.lift₂
  sorry
  sorry

/- 2.4 (2 points). Prove that `multiset.union` is commutative and associative. -/

lemma multiset.union_comm {α : Type} [decidable_eq α] (A B : multiset α) :
  multiset.union A B = multiset.union B A :=
sorry

lemma multiset.union_assoc {α : Type} [decidable_eq α] (A B C : multiset α) :
  multiset.union (multiset.union A B) C =
  multiset.union A (multiset.union B C) :=
sorry

/-! ## Question 3 (2 points + 1 bonus point): Hilbert Choice

3.1 (1 bonus point). Prove the following lemma. -/

lemma exists_minimal_arg.aux (f : ℕ → ℕ) :
  ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
| x m eq :=
  begin
    cases' classical.em (∃n, f n < x),
    sorry, sorry
  end

/-! Now this interesting lemma falls off: -/

lemma exists_minimal_arg (f : ℕ → ℕ) :
  ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
exists_minimal_arg.aux f _ 0 (by refl)

/-! 3.2 (1 point). Use what you learned in the lecture to define the following
function, which returns the (or an) index of the minimal element in `f`'s
image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
sorry

/-! 3.3 (1 point). Prove the following characteristic lemma about your
definition. -/

lemma minimal_arg_spec (f : ℕ → ℕ) :
  ∀i : ℕ, f (minimal_arg f) ≤ f i :=
sorry

end LoVe
