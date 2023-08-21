import Complex.Level_00_Basic

namespace complex

def of_real (r : ℝ) : ℂ := ⟨r, 0⟩

instance : Coe ℝ ℂ := ⟨of_real⟩

@[simp]
theorem of_real_re (r : ℝ) : (r : ℂ).re = r := 
  rfl

--@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r :=
--begin
  --refl
--end

@[simp]
theorem of_real_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl

--@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

attribute [simp] complex.ext_iff

@[simp]
theorem of_real_inj {r s : ℝ} : (r : ℂ) = s ↔ r = s := 
  rfl


@[simp]
theorem of_real_zero : ((0 : ℝ) : ℂ) = 0 := 
  rfl

--@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp]
theorem of_real_eq_zero {r : ℝ} : (r : ℂ) = 0 ↔ r = 0 :=
  rfl

@[simp, norm_cast] theorem of_real_one : ((1 : ℝ) : ℂ) = 1 := 
  rfl

@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  rfl

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
  rfl

