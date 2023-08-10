import Mathlib.Data.Real.Basic

structure complex where
re : ℝ
im : ℝ

notation "ℂ" => complex

#check complex.mk 10 20

example : ℂ := complex.mk 3 4

example : ℂ := ⟨3, 4⟩

example : complex.mk 3 4 = ⟨3, 4⟩ := by rfl

namespace complex

--example : re(mk 3 4) = 3 := by rfl

def zero : ℂ := ⟨0, 0⟩

instance : OfNat ℂ := ⟨zero⟩

def one : ℂ := ⟨1, 0⟩

instance : HasOne ℂ := ⟨one⟩

def add (z w : ℂ) : ℂ := ⟨z.re + w.re, z.im + w.im⟩

def mul (z w : ℂ) : ℂ := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

