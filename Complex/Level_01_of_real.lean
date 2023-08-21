import Complex.Level_00_Basic

namespace complex

def of_real (r : ℝ) : ℂ := ⟨r, 0⟩

instance : Coe ℝ ℂ := ⟨of_real⟩

@[simp, norm_cast]
lemma of_real_re (r : ℝ) : (r : ℂ).re = r := 
  by rw [of_real, complex.re]

--@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r :=
--begin
  --refl
--end

@[simp, norm_cast]
lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl
--@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

attribute [simp] complex.ext_iff

@[simp, norm_cast]
theorem of_real_inj {r s : ℝ} : (r : ℂ) = s ↔ r = s := 
  ⟨congr_arg re, congr_arg _⟩

@[simp]
theorem of_real_zero : ((0 : ℝ) : ℂ) = 0 := 
  rfl

--@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp]
theorem of_real_eq_zero {r : ℝ} : (r : ℂ) = 0 ↔ r = 0 :=
  of_real_inj

theorem of_real_ne_zero {r : ℝ} : (r : ℂ) ≠ 0 ↔ r ≠ 0 :=
  not_congr of_real_eq_zero

@[simp]
theorem of_real_one : ((1 : ℝ) : ℂ) = 1 := 
  rfl

@[simp, norm_cast]
theorem of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  rfl

@[simp, norm_cast]
lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := 
  complex.ext (neg_re _) (neg_im _)

@[simp, norm_cast]
lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  complex.ext (mul_re _ _) (mul_im _ _)
