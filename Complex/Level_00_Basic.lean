/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import everything about the real numbers
import Mathlib.Data.Real.Basic

/-!
# The complex numbers

We define the complex numbers, and prove that they are a ring.

We also "extract some basic API" (e.g. we prove that
two complex numbers are equal iff they have the same
real and imaginary parts)

This file has no `sorry`s in. All of the other levels:

`Level_01_of_real.lean`
`Level_02_I.lean`
`Level_03_conj.lean`
`Level_04_norm_sq.lean`
`Level_05_field.lean`
`Level_06_alg_closed.lean`

have sorrys, indicating puzzles to be solved.

# Main Definitions

`zero` : the complex number 0
`one` : the complex number 1
`add` -- addition of two complex numbers
`neg` -- negation of a complex number
`mul` -- multiplication of two complex numbers

# Main Theorem

`comm_ring` : The complex numbers are a commutative ring.

-/

/-- A complex number is defined to be a structure consisting of two real
  numbers, the real part and the imaginary part of the complex numberd. -/
@[ext]
structure complex where
  re : ℝ
  im : ℝ

--@[ext] annotation automatically tells lean two instances are equal when their components are equal.
#check complex.ext

-- Let's use the usual notation for the complex numbers
notation "ℂ" => complex

#check complex.mk 10 20

-- You make the complex number with real part 3 and imaginary part 4 like this:
example : ℂ := complex.mk 3 4

-- Or like this:
example : ℂ := ⟨3, 4⟩

-- They all give the same complex number.
example : complex.mk 3 4 = ⟨3, 4⟩ := by rfl

-- All of our definitions, like `zero` and `one`, will all
-- live in the `complex` namespace.

namespace complex

-- If you have a complex number, then you can get its real and 
-- imaginary parts with the `re` and `im` functions.
-- Note that re(mk 3 4) = 3 is no longer available.

example : ℝ := (mk 3 4).re

-- Before we start making the basic 
-- We now prove the basic theorems and make the basic definitions for
-- complex numbers. For example, we will define addition and multiplication on
-- the complex numbers, and prove that it is a commutative ring.
-- TODO fix

/-! # Defining the ring structure on ℂ -/

-- Our main goal is to prove that the complexes are a ring. Let's
-- define the structure first; the zero, one, addition and multiplication
-- on the complexes. 

/-! ## zero (0) -/

/-- The complex number with real part 0 and imaginary part 0 -/

instance : Zero complex :=
  ⟨⟨0, 0⟩⟩

-- Let's prove the two basic properties, both of which are true by definition,
-- and then tag them with the appropriate attributes.
@[simp]
theorem zero_re : (0 : complex).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : complex).im = 0 :=
  rfl  

/-! ## one (1) -/

-- Now let's do the same thing for 1.

/-- The complex number with real part 1 and imaginary part 0 -/
instance : One complex :=
  ⟨⟨1, 0⟩⟩

-- name the basic properties and tag them with `simp`
@[simp]
theorem one_re : (1 : complex).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : complex).im = 0 :=
  rfl


/-! ## add (+) -/

-- Now let's define addition

/-- addition `z+w` of complex numbers -/

instance : Add complex :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

-- basic properties
@[simp]
theorem add_re (x y : complex) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : complex) : (x + y).im = x.im + y.im :=
  rfl

/-! ## neg (-) -/

-- negation

/-- The negation `-z` of a complex number `z` -/
instance : Neg complex :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

-- how neg interacts with re and im
@[simp]
theorem neg_re (x : complex) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : complex) : (-x).im = -x.im :=
  rfl

/-! ## mul (*) -/

-- multiplication

/-- Multiplication `z*w` of two complex numbers -/
instance : Mul complex :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

-- how `mul` reacts with `re` and `im`
@[simp]
theorem mul_re (x y : complex) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : complex) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

/-! ## Example of what `simp` can now do

example (a b c : ℂ) :
  re(a*(b+c)) = re(a) * (re(b) + re(c)) - im(a) * (im(b) + im(c)) :=
begin
  simp,
end

-/

/-! # Theorem:  The complex numbers are a commutative ring

Proof: we've defined all the structure, and every axiom can be checked by
reducing it to checking real and imaginary parts with `ext`, expanding
everything out with `simp`, and then using the fact that the real numbers are
a commutative ring (which we already know)

-/

/-- The complex numbers are a commutative ring -/
instance instCommRing : CommRing ℂ where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  add_left_neg := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intro
    ext <;> simp
  mul_zero := by
    intro
    ext <;> simp

instance : Nontrivial complex := by
  use 0, 1
  rw [Ne, complex.ext_iff]
  simp

end complex

/-!

# some last comments on the `simp` tactic

Some equalities, even if obvious, had to be given names, because we want `simp`
to be able to use them. In short, the `simp` tactic tries to solve
goals of the form A = B, when `refl` doesn't work (i.e. the goals are
not definitionally equal) but when any mathematician would be able
to simplify A and B via "obvious" steps such as `0 + x = x` or
`⟨z.re, z.im⟩ = z`. These things are sometimes not true by definition,
but they should be tagged as being well-known ways to simplify an equality.
When building our API for the complex numbers, if we prove a theorem of the
form `A = B` where `B` is a bit simpler than `A`, we should probably
tag it with the `@[simp]` attribute, so `simp` can use it.

Note: `simp` does *not* prove "all simple things". It proves *equalities*.
It proves `A = B` when, and only when, it can do it by applying 
its "simplification rules", where a simplification rule is simply a proof
of a theorem of the form `A = B` and `B` is simpler than `A`.  
-/