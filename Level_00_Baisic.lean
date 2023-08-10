structure complex where
re : Nat
im : Nat

notation "ℂ" => complex

#check complex.mk 10 20

def zero : ℂ := ⟨0, 0⟩

instance : HasZero ℂ := ⟨zero⟩

def one : ℂ := ⟨1, 0⟩

instance : HasOne ℂ := ⟨one⟩

def add (z w : ℂ) : ℂ := ⟨z.re + w.re, z.im + w.im⟩

def mul (z w : ℂ) : ℂ := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

