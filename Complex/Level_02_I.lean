import Complex.Level_01_of_real

namespace complex

def I : ℂ := ⟨0, 1⟩

@[simp] lemma I_re : I.re = 0 := rfl

@[simp] lemma I_im : I.im = 1 := rfl

@[simp] lemma I_mul_I : I * I = -1 := rfl

lemma mk_eq_add_mul_I (a b : ℝ) : (⟨a, b⟩ : ℂ) = a + b * I := rfl

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z := rfl

lemma I_ne_zero : (I : ℂ) ≠ 0 := simp[I_im, I_re, zero_re, zero_im]

end complex