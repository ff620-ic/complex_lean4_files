/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard
Thanks: Imperial College London, leanprover-community
-/

-- import level 1
import Complex.Level_01_of_real

/-! 

# Level 2: I 

I find it unbelievable that we have written quite a lot of code about the
complex numbers and we've still never defined i, or j, or I, or $$\sqrt{-1}$$,
or whatever it's called.  Why don't you supply the definition, and make the
basic API?

All the proofs below are sorried. You can try them in tactic mode
by replacing `sorry` with `begin end` and then starting to write 
tactics in the `begin end` block.
-/

namespace complex

/-- complex.I is the square root of -1 above the imaginary axis -/
def I : ℂ := ⟨0, 1⟩

/-

 Easy lemmas, tagged with `simp` so Lean can prove things about `I` by equating
 real and imaginary parts.
 
-/

/-- re(I) = 0 -/
@[simp] lemma I_re : I.re = 0 := rfl

/-- im(I) = 1 -/
@[simp] lemma I_im : I.im = 1 := rfl

/-- I*I = -1 -/
@[simp] lemma I_mul_I : I * I = -1 := by simp

lemma mk_eq_add_mul_I (a b : ℝ) : (⟨a, b⟩ : ℂ) = a + b * I := by simp

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z := by simp

/-
  Bonus level. Hint: don't forget ext_iff. It's defined
  in complex.basic and its type is below.
   
  ext_iff : ∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
-/

/-- I is non-zero -/
lemma I_ne_zero : (I : ℂ) ≠ 0 := by simp

end complex