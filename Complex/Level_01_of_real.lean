/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- import the definition and basic properties of ℂ
import Complex.Level_00_Basic

/-! # Level 1 : the map from ℝ to ℂ

This file sets up the coercion from the reals to the complexes,
sending `r` to `⟨r, 0⟩`. Mathematically it is straightforward.

All the proofs below are sorried. You can try them in tactic mode
by replacing `sorry` with `begin sorry end` and then starting to write 
tactics in the `begin end` block.

-/

namespace complex

-- fill in the definition of the map below,
-- sending the real number r to the complex number ⟨r, 0⟩

/-- The canonical map from ℝ to ℂ. -/
def of_real (r : ℝ) : ℂ := ⟨r, 0⟩

/-
We make this map into a *coercion*, which means that if `(r : ℝ)` is a real
number, then `(r : ℂ)` or `(↑r : ℂ)` will indicate the corresponding
complex number with no imaginary part. This is the notation we shall
use in our `simp` lemmas.
-/

/-- The coercion from ℝ to ℂ sending `r` to the complex number `⟨r, 0⟩` -/
instance : Coe ℝ ℂ := ⟨of_real⟩

/-
As usual, we need to train the `simp` tactic. But we also need to train
the `norm_cast` tactic. The `norm_cast` tactic enables Lean to prove
results like r^2=2*s for reals `r` and `s`, if it knows that
`(r : ℂ)^2 = 2*(s : ℂ)`. Such results are intuitive for matheamticians
but involve "invisible maps" in Lean. But unfortunately we haven’t figure
out how to use norm_cast in following theorems and lemmas.
-/
@[simp]
lemma of_real_re (r : ℝ) : ((r : ℝ) : ℂ).re = r :=
  rfl

--@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r :=
--begin
  --refl
--end

@[simp]
lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl
-- The map from the reals to the complexes is injective, something we
-- write in iff form so `simp` can use it; `simp` also works on `iff` goals.
attribute [simp] complex.ext_iff

@[simp]
theorem of_real_inj {r s : ℝ} : (r : ℂ) = s ↔ r = s := 
  ⟨congr_arg re, congr_arg _⟩

/-
We now go through all the basic constants and constructions we've defined so
far, namely 0, 1, +, -, *, and tell the simplifier how they behave with respect
to this new function. 
-/

/-! ## zero -/

@[simp]
theorem of_real_zero : ((0 : ℝ) : ℂ) = 0 := 
  rfl

--equals zero iff r=0
@[simp]
theorem of_real_eq_zero {r : ℝ} : (r : ℂ) = 0 ↔ r = 0 :=
  of_real_inj

theorem of_real_ne_zero {r : ℝ} : (r : ℂ) ≠ 0 ↔ r ≠ 0 :=
  not_congr of_real_eq_zero

/-! ## one -/
@[simp]
theorem of_real_one : ((1 : ℝ) : ℂ) = 1 := 
  rfl

/-! ## add -/
@[simp]
theorem of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s := by
  simp

/-! ## neg -/
@[simp]
lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := by
  simp

/-! ## mul -/
@[simp]
lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := by
  simp

/-- The canonical ring homomorphism from ℝ to ℂ -/
def Of_real : ℝ →+* ℂ :=
{ toFun := of_real, -- use the coercion from ℝ to ℂ
  map_zero' := of_real_zero,
  map_one' := of_real_one,
  map_add' := of_real_add,
  map_mul' := of_real_mul,
}

/-
@[simp] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
  rfl

@[simp] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r :=
  rfl

bit0 and bit1 deprecated.
-/
end complex