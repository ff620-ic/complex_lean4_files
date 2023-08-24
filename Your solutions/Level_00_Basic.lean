import Mathlib.Data.Real.Basic

@[ext]
structure complex where
  re : ℝ
  im : ℝ

#check complex.ext

notation "ℂ" => complex

#check complex.mk 10 20

example : ℂ := complex.mk 3 4

example : ℂ := ⟨3, 4⟩

example : complex.mk 3 4 = ⟨3, 4⟩ := by rfl

namespace complex

example : ℝ := (mk 3 4).re

instance : Zero complex :=
  ⟨⟨0, 0⟩⟩

instance : One complex :=
  ⟨⟨1, 0⟩⟩

instance : Neg complex :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Add complex :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Mul complex :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

@[simp]
theorem zero_re : (0 : complex).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : complex).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : complex).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : complex).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : complex) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : complex) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : complex) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : complex) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : complex) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : complex) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

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

