variable (X : Type)

def f : ℕ → ℕ := λ x, x + 1

include X

def g : ℕ → ℕ := λ x, x + 1

omit X

def h : ℕ → ℕ := λ x, x + 1

#check f -- f : ℕ → ℕ
#check g -- g : Type → ℕ → ℕ
#check h -- h : ℕ → ℕ