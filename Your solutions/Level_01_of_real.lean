import Complex.Level_00_Basic

namespace complex

def of_real (r : ℝ) : ℂ := sorry

instance : Coe ℝ ℂ := ⟨of_real⟩

@[simp]
lemma of_real_re (r : ℝ) : ((r : ℝ) : ℂ).re = r :=
  sorry

--@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r :=
--begin
  --refl
--end

@[simp]
lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 :=
  sorry
--@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

attribute [simp] complex.ext_iff

@[simp]
theorem of_real_inj {r s : ℝ} : (r : ℂ) = s ↔ r = s := 
  sorry

@[simp]
theorem of_real_zero : ((0 : ℝ) : ℂ) = 0 := 
  sorry

--@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp]
theorem of_real_eq_zero {r : ℝ} : (r : ℂ) = 0 ↔ r = 0 :=
  sorry

theorem of_real_ne_zero {r : ℝ} : (r : ℂ) ≠ 0 ↔ r ≠ 0 :=
  sorry

@[simp]
theorem of_real_one : ((1 : ℝ) : ℂ) = 1 := 
  sorry

@[simp]
theorem of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s := by
  sorry

@[simp]
lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := by
  sorry

@[simp]
lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := by
  sorry

def Of_real : ℝ →+* ℂ :=
{ toFun := of_real, -- use the coercion from ℝ to ℂ
  map_zero' := of_real_zero,
  map_one' := of_real_one,
  map_add' := of_real_add,
  map_mul' := of_real_mul,
}


@[simp] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
  rfl

@[simp] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r :=
  rfl

end complex