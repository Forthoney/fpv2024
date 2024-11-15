import LoVe.Lectures.LoVe14_RationalAndRealNumbers_Demo

/- # FPV Homework 9: Rationals, Reals, Quotients

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/

namespace LoVe

/-

## Question 1 (4 points): Cauchy Sequences

1.1 (4 points). In the demo, we sorry'ed the proof that the sum of two Cauchy
sequences is Cauchy. Prove this!

Hint: depending on how you approach this, you might want to do a long calc-mode
proof. Recall that calc-mode proofs look as follows:
-/

lemma quarter_pos {x : ℚ} (hx : 0 < x) : 0 < x / 4 :=
by
  have hx2 : 0 < x / 2 := half_pos hx
  calc 0 < (x / 2) / 2 := half_pos hx2
       _ = x / (2 * 2) := by ring
       _ = x / 4       := by ring

lemma sum_is_cauchy (f g : ℕ → ℚ) (hf : IsCauchySeq f) (hg : IsCauchySeq g) :
  IsCauchySeq (λ n => f n + g n) :=
  sorry

/-
## Question 2 (4 points): Operations on the Reals

2.1 (3 points). In the demo, we proved `add_comm` on the reals by first proving
it for Cauchy sequences and then lifting this proof. Follow this same procedure
to prove a lemma `zero_add` that says that `0 + x = x` for any real number `x`.
State the lemma yourself (along with any helper lemmas you may need -- we suggest
defining something like `add_def`, proved by `rfl`)! -/

open LoVe.CauchySeq

-- Write your answer to 2.1 here


/- 2.2 (1 point). Every rational number corresponds to a real number. Define
this coercion. -/

instance ratRealCoe : Coe ℚ Real :=
{ coe :=
  sorry }


namespace Dedekind
/-
## Question 3 (16 points): Dedekind Cuts


In class, we defined the real numbers with a quotient on Cauchy sequence.
In the end, we mentioned that there are many ways to define real numbers.
If you have taken an analysis class, you will most likely be introduced to
the concept of Dedekind Cuts. Loosely, a real `r ∈ ℝ` is defined as the
open set

`{x : ℚ | x < r}`

with the `r` being the supremum (least upper bound) of the set.
Of course, this definition is not precise, since it uses the real number `r`
to define itself! We'll make it clearer below.

This definition is geometrically pleasing, conveying the idea that "Reals
fill the number line". However, it may not be as easy to define in Lean.

Different from questions encountered before where we provide some type of
structure to the proof, in this question, we will not give much structure,
and you need to make design choices yourself. This may include designing
the `structure`, thinking of what `lemma`s you need, look for theorems
yourself and use `instance` to your advantage to provide with syntactic
sugar. We will only guide you through the key ideas.
This will hopefully give you some idea of what a math-oriented final project
will feel like.

We **STRONGLY SUGGEST** you **READ EVERYTHING** before you start writing
any definitions and proofs. This will give you a fuller picture about what
you need to do, as your definitions do matter A LOT to how easy proofs will
be.


-/

/-!
### 3.1 (2 points): Defining Dedekind Cuts

We first formalize Dedekind cuts. We suggest using the definition in `rudin`
 (p. 17):
`https://web.math.ucsb.edu/~agboola/teaching/2021/winter/122A/rudin.pdf`

We restate it here:

A subset `α ⊂ ℚ` is called a *cut* if it satisfies the following properties:
1. *Nontrivial*: `α` is not empty and `α ≠ ℚ`
2. *Closed Downwards*: If `p ∈ α`, `q ∈ ℚ`, and `q < p`, then `q ∈ α`
3. *Open Upwards*: If `p ∈ α`, then `p > r` for some `r ∈ α`

Recall that `Set α` in Lean represents, mathematically, a *subset* of the
type `α`.
 -/

example : Set ℚ := {q : ℚ | q > 5 ∧ q < 10}

/-
Your task: define the type `dReal` of Dedekind cuts.
-/

axiom dReal : Type -- replace this with your definition

/-!
### 3.2 (3 points): Coercion from Reals

Rational Numbers are automatically Dedekind cuts. Consider a rational number
`p : ℚ`; the set that represets it is

`π = { r : ℚ | r < p }`

1. Define a function `Rat.todReal` that converts `ℚ` to `dReal`.

At some point, you will want to prove that this set satisfies the properties
required by `dReal`. This will include a proof for `π` being open-upwards.
The proof sketch for this is the following:
Given any `s ∈ π`, define `r = (s + p) / 2`, show that `s < r < p`.

2. Define `dReal.zero`.

You may want to write a few more lemmas to make your life easier later, but
if you cannot think of one, it is fine. If you get stuck, you can always
come back later and add them.

In particular, we find it convenient to talk about *membership* of a
rational number in a cut.
Consider defining `instance : Membership ℚ (dReal) := ...`

-/


def Rat.todReal : ℚ → dReal :=
  sorry

instance : Coe ℚ dReal := ⟨Rat.todReal⟩

def dReal.zero : dReal :=
  sorry



/-!
### 3.3 (4 points): State and prove lemmas

`rudin` also provided two lemmas "as a direct consequence" of the
definition. State them and prove them.

For any Dedekind cut `α` and rationals `p, q`:
1. If `p ∈ α` and `q ∉ α` then `q > p`
2. If `r ∉ α` and `r < s` then `s ∉ α`

-/

-- Write your lemmas here

/-!
### 3.4 (5 points): Define Addition

Define addition as

`α + β = { p + q | ∃ p ∈ α, q ∈ β }`.
-/

def dReal.add (a b: dReal) : dReal := sorry


-- los

/-! ### 3.5 (2 points): Define Negation (Additive Inverses)

For some cut `α ⊂ ℚ`, think about how you would go defining its negation
`-α`. Remember the geometric meaning of a cut. Check your solution
with `rudin`.

We do *not* require you to prove that negation is actually a Dedekind cut;
just define the underlying set. You can `sorry` out the proof obligations.
Take these on for bonus points if you feel like it!
-/

-- define this:
def dReal.negCut (a : dReal) : Set ℚ :=
  sorry

-- you don't need to define this!
def dReal.neg (a : dReal) : dReal := sorry



/-!
### 3.6 (street cred): Defining Commutative Group under Addition

There's a lot more you could go on to define. An obvious target:
showing that `dReal` is a commutative group!

**This is a bonus challenge** and can be quite time consuming.
We strongly recommend using lots of helper lemmas if you take this on!

The `nsmul` and `zsmul` fields are annoying implementation details.
We have filled these in for you.

-/


instance : AddCommGroup dReal where
  add := dReal.add
  add_assoc := sorry
  zero := dReal.zero
  zero_add := sorry
  add_zero := sorry
  nsmul := @nsmulRec _ ⟨dReal.zero⟩ ⟨dReal.add⟩
  neg := dReal.neg
  zsmul :=
    @zsmulRec _ ⟨dReal.zero⟩ ⟨dReal.add⟩ ⟨dReal.neg⟩
      (@nsmulRec _ ⟨dReal.zero⟩ ⟨dReal.add⟩)
  add_left_neg := sorry
  add_comm := sorry

end Dedekind

end LoVe
