import Mathlib

namespace new

structure Complex : Type where
  real : ℝ
  im   : ℝ

#check Complex.real

def Complex.add (a b : Complex) : Complex where
  real := a.real + b.real
  im   := a.im + b.im

-- (x + iy)*(z + iw) = ((xz - wy) + i(zy + xw) )
def Complex.mul (a b : Complex) : Complex where
  real := a.real * b.real - a.im * b.im
  im   := a.im*b.real + a.real*b.im

def zero : Complex where
  real := 0
  im := 0

lemma zero_add (a : Complex) : Complex.add zero a = a := by
  simp [zero, Complex.add]

def Complex.neg (a : Complex) : Complex where
  real := -a.real
  im := -a.im

instance : CommRing Complex where
  add := Complex.add
  add_assoc := _
  zero := zero
  zero_add := zero_add
  add_zero := _
  nsmul := @nsmulRec _ ⟨zero⟩ ⟨Complex.add⟩
  add_comm := _
  mul := Complex.mul
  left_distrib := _
  right_distrib := _
  zero_mul := _
  mul_zero := _
  mul_assoc := _
  one := {real := 1, im := 0}
  one_mul := _
  mul_one := _
  neg := Complex.neg
  zsmul := @zsmulRec _ ⟨zero⟩ ⟨Complex.add⟩ ⟨Complex.neg⟩ ( @nsmulRec _ ⟨zero⟩ ⟨Complex.add⟩)
  add_left_neg := _
  mul_comm := _




example (a b : Complex) : a + b = b + a := by ring

example (a b : ℕ) : (a : Complex) + b = b + a := add_comm _ _


structure Polar : Type where
  angle : ℝ
  magnitude : ℝ
  -- angle_above : -Real.pi / 2 < angle
  -- angle_below : Real.pi / 2 > angle
  -- magnitude_nonneg : 0 ≤ magnitude

#check Complex.tan
noncomputable def Complex.toPolar (a : Complex) : Polar where
  angle := Real.arctan (a.im / a.real)
  magnitude := Real.sqrt (a.real^2 + a.im^2)
  -- magnitude_nonneg := by exact Real.sqrt_nonneg (a.real ^ 2 + a.im ^ 2)
  -- angle_nonneg := by exact?

noncomputable def Polar.toComplex (p : Polar) : Complex where
  real := p.magnitude * Real.cos p.angle
  im := p.magnitude * Real.sin p.angle

theorem to_and_from (p : Polar)
  (hangle1 : -(Real.pi / 2) < p.angle)
  (hangle2 : (Real.pi / 2) > p.angle)
  (hmag : p.magnitude > 0) : p.toComplex.toPolar = p := by
  cases' p with angle magnitude
  simp [Complex.toPolar, Polar.toComplex]
  constructor
  { rw [mul_div_mul_left, ← Real.tan_eq_sin_div_cos]
    rw [Real.arctan_tan]
    all_goals linarith }
  { suffices : (magnitude * Real.cos angle)^2 + (magnitude * Real.sin angle)^2 = magnitude^2
    { rw [this]
      refine Real.sqrt_sq ?mk.right.h
      linarith }
    { have : (Real.sin angle)^2 + (Real.cos angle)^2 = 1 :=
        Real.sin_sq_add_cos_sq angle
      linear_combination magnitude ^ 2 * this }
   }

def Complex.reals : Set Complex :=
  {c : Complex | c.im = 0}

#check Complex.reals
#check (Set.univ : Set Complex)

#check Inter.inter

example {s t : Set Complex} : s ∩ Complex.reals = Complex.reals ∪ t := by
  simp [Complex.reals]

def realFn : ↑(Complex.reals ∪ Set.univ) → ℝ :=
  _ --fun ⟨x, hx⟩ => x.real

#check Set.Elem

end new
