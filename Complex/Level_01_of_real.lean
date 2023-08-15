import Complex.Level_00_Basic

namespace complex

def of_real (r : ℝ) : ℂ := ⟨r, 0⟩

instance : has_coe ℝ ℂ := ⟨of_real⟩