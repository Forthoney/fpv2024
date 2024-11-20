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
  IsCauchySeq (λ n => f n + g n) := by
  rw[IsCauchySeq]
  rw[IsCauchySeq] at hf hg

  intro ε εPositive

  cases hf (ε / 4) (quarter_pos εPositive) with
  | intro N₁ hN₁ =>
    cases hg (ε / 4) (quarter_pos εPositive) with
    | intro N₂ hN₂ =>
      let N := max N₁ N₂
      apply Exists.intro N
      intro m mLowerBound

      have hf : |f N - f m| < ε / 2 := by
        calc
          |f N - f m| = |(f N - f N₁) + (f N₁ - f m)| := by
            congr
            linarith
          _ ≤ |f N - f N₁| + |f N₁ - f m| := by
            apply abs_add (f N - f N₁) (f N₁ - f m)
          _ < ε / 4 + |f N₁ - f m| := by
            simp
            calc
              |f N - f N₁| = |f N₁ - f N| := by
                exact abs_sub_comm (f N) (f N₁)
              _ < ε / 4 := by
                apply hN₁
                exact Nat.le_max_left N₁ N₂
          _ < ε / 4 + ε / 4 := by
            simp
            apply hN₁
            exact le_of_max_le_left mLowerBound
          _ = ε / 2 := by
            linarith

      have hg : |g N - g m| < ε / 2 := by
        calc
          |g N -g m| = |(g N - g N₂) + (g N₂ - g m)| := by
            congr
            linarith
          _ ≤ |g N - g N₂| + |g N₂ - g m| := by
            apply abs_add (g N - g N₂) (g N₂ - g m)
          _ < ε / 4 + |g N₂ - g m| := by
            simp
            calc
              |g N - g N₂| = |g N₂ - g N| := by
                exact abs_sub_comm (g N) (g N₂)
              _ < ε / 4 := by
                apply hN₂
                exact Nat.le_max_right N₁ N₂
          _ < ε / 4 + ε / 4 := by
            simp
            apply hN₂
            exact le_of_max_le_right mLowerBound
          _ = ε / 2 := by
            linarith

      calc
        |f N + g N - (f m + g m)| = |(f N - f m) + (g N - g m)| := by
          rw[sub_add_eq_sub_sub]
          congr
          linarith
        _ ≤ |f N - f m| + |g N - g m| := by
          apply abs_add (f N - f m) (g N - g m)
        _ < ε / 2 + |g N - g m| := by
          simp
          exact hf
        _ < ε / 2 + ε / 2 := by
          apply add_lt_add_left
          exact hg
        _ = ε := by linarith
  done

/-
## Question 2 (4 points): Operations on the Reals

2.1 (3 points). In the demo, we proved `add_comm` on the reals by first proving
it for Cauchy sequences and then lifting this proof. Follow this same procedure
to prove a lemma `zero_add` that says that `0 + x = x` for any real number `x`.
State the lemma yourself (along with any helper lemmas you may need -- we suggest
defining something like `add_def`, proved by `rfl`)! -/

open LoVe.CauchySeq

theorem Cauchy_add_def (a b : CauchySeq) :
  a + b ≈ ⟨λ n => a.val n + b.val n, sum_is_cauchy a.val b.val a.property b.property⟩ := by
  exact Setoid.refl (a + b)

lemma Cauchy_zero_add (a : CauchySeq) : CauchySeq.const 0 + a ≈ a := by
  intro ε εLowerBound
  cases a with
  | mk val converge =>
    use (converge ε εLowerBound).choose
    intro m mGrN
    let lhs := |seqOf (const 0 + ⟨val, converge⟩) m - seqOf ⟨val, converge⟩ m|
    calc
      lhs = |seqOf (const 0) m + seqOf ⟨val, converge⟩ m - seqOf ⟨val, converge⟩ m| := by congr
      _ = |seqOf (const 0) m| := by simp
      _ = |0| := by rw[const, seqOf]
      _ < ε := εLowerBound


-- Write your answer to 2.1 here
lemma zero_add (x : Real) : 0 + x = x :=
  Quotient.inductionOn x (λ a ↦ Quotient.sound (Cauchy_zero_add a))

/- 2.2 (1 point). Every rational number corresponds to a real number. Define
this coercion. -/

instance ratRealCoe : Coe ℚ Real :=
{ coe := λ x ↦ ⟦CauchySeq.const x⟧ }


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
3. *Open Upwards*: If `p ∈ α`, then `p < r` for some `r ∈ α`

Recall that `Set α` in Lean represents, mathematically, a *subset* of the
type `α`.
 -/

example : Set ℚ := {q : ℚ | q > 5 ∧ q < 10}

/-
Your task: define the type `dReal` of Dedekind cuts.
-/


structure dReal where
  cut : Set ℚ
  nontrivial : cut.Nonempty ∧ ∃ x : ℚ, x ∉ cut
  closed_upwards : ∀ p q : ℚ, p ∈ cut → q < p → q ∈ cut
  open_upwards : ∀ p ∈ cut, ∃ q ∈ cut, p < q

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
  λ x ↦ {
    α := {r : ℚ | r < x}
    nontrivial := by
      apply And.intro
      {
        rw[Set.Nonempty]
        use x - 1
        apply Set.mem_setOf.mpr
        exact sub_one_lt x
      }
      {
        use x + 1
        aesop
      }
    closed_upwards := by
      intro p q p_mem q_less_p
      simp
      exact gt_trans p_mem q_less_p
    open_upwards := by
      intro p p_mem
      use p - 1
      apply And.intro
      simp
      exact gt_trans p_mem (sub_one_lt p)
      exact sub_one_lt p
  }

instance : Coe ℚ dReal := ⟨Rat.todReal⟩

def dReal.zero : dReal := Rat.todReal 0



/-!
### 3.3 (4 points): State and prove lemmas

`rudin` also provided two lemmas "as a direct consequence" of the
definition. State them and prove them.

For any Dedekind cut `α` and rationals `p, q`:
1. If `p ∈ α` and `q ∉ α` then `q > p`
2. If `r ∉ α` and `r < s` then `s ∉ α`

-/
lemma dReal.mem_to_ineq (s : dReal) (p q : ℚ) : p ∈ s.cut → q ∉ s.cut → q > p := by
  intro p_mem q_nmem
  apply Classical.byContradiction
  intro assum
  if eq: q = p then
    rw[eq] at q_nmem
    contradiction
  else
    have q_mem : q ∈ s.cut := by
      apply s.closed_upwards p q p_mem
      apply lt_of_le_of_ne (le_of_not_lt assum) eq
    contradiction


lemma dReal.ineq_to_mem (s : dReal) (p q : ℚ) : p ∉ s.cut → p < q → q ∉ s.cut := by
  intro p_nmem p_less_q
  apply Classical.byContradiction
  intro assum
  simp at assum
  have con: p ∈ s.cut := s.closed_upwards q p assum p_less_q
  contradiction


/-!
### 3.4 (5 points): Define Addition

Define addition as

`α + β = { p + q | ∃ p ∈ α, q ∈ β }`.
-/

lemma dReal.no_larger (α : dReal) (p : ℚ) :
  p ∉ α.cut → ¬(∃ p' ∈ α.cut, p < p') := by
  intro pNinCut h
  let p' := h.choose
  have pInCut : p ∈ α.cut := by
    apply α.closed_upwards p'
    apply h.choose_spec.left
    apply h.choose_spec.right
  contradiction

lemma dReal.all_smaller (α : dReal) (p : ℚ) :
  p ∉ α.cut → ∀ p' ∈ α.cut, p' < p := by
  intro pNinCut p'
  exact fun a => mem_to_ineq α p' p a pNinCut


def dReal.add (α β: dReal) : dReal :=
  {
    cut := {p + q | (p ∈ α.cut) (q ∈ β.cut)}
    nontrivial := by
      apply And.intro
      {
        have p_ex : ∃ p, p ∈ α.cut := α.nontrivial.left
        have q_ex : ∃ q, q ∈ β.cut := β.nontrivial.left
        use p_ex.choose + q_ex.choose
        apply Set.mem_setOf.mpr
        use p_ex.choose
        apply And.intro
        apply p_ex.choose_spec
        use q_ex.choose
        apply And.intro
        apply q_ex.choose_spec
        rfl
      }
      {
        have p_nex : ∃ p, p ∉ α.cut := α.nontrivial.right
        have q_nex : ∃ q, q ∉ β.cut := β.nontrivial.right
        let p := p_nex.choose
        let q := q_nex.choose
        use p + q
        have all_smaller : ∀ p' ∈ α.cut, ∀ q' ∈ β.cut, p' + q' < p + q := by
          intro p' p'_mem q' q'_mem
          calc
            p' + q' < p + q' := by
              simp
              apply α.all_smaller p p_nex.choose_spec p' p'_mem
            _ < p + q := by
              simp
              apply β.all_smaller q q_nex.choose_spec q' q'_mem
        simp
        exact fun x a x_1 a_1 => ne_of_lt (all_smaller x a x_1 a_1)
      }
    closed_upwards := by
      intro x y x_mem x_less_y
      simp at x_mem
      let p := x_mem.choose
      let q := x_mem.choose_spec.right.choose
      let q_spec := x_mem.choose_spec.right.choose_spec
      simp
      use p
      apply And.intro
      apply x_mem.choose_spec.left
      use y - p
      apply And.intro
      {
        have q_val : q = x - p := by
          apply eq_sub_of_add_eq'
          apply q_spec.right
        have yp_less_q : y - p < q := by
          rw[q_val]
          exact sub_lt_sub_right x_less_y p
        exact β.closed_upwards q (y - p) q_spec.left yp_less_q
      }
      {simp}
    open_upwards := by
      intro x x_mem
      let p := x_mem.choose
      let q := x_mem.choose_spec.right.choose
      let q_spec := x_mem.choose_spec.right.choose_spec

      have p'_ex := α.open_upwards p x_mem.choose_spec.left
      have q'_ex := β.open_upwards q q_spec.left

      let p' := p'_ex.choose
      let q' := q'_ex.choose
      use p' + q'
      apply And.intro
      simp
      use p'
      apply And.intro
      apply p'_ex.choose_spec.left
      use q'
      apply And.intro
      apply q'_ex.choose_spec.left
      rfl
      calc
        x = p + q := by
          apply eq_comm.mp
          exact q_spec.right
        _ < p' + q := by
          simp
          exact p'_ex.choose_spec.right
        _ < p' + q' := by
          simp
          exact q'_ex.choose_spec.right
  }


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
