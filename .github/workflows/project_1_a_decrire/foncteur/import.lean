import tactic
import data.sum

def map_from_sum {A B C : Type} (f : A → C) (g : B → C) : (A ⊕ B) → C := by suggest
/- There are no applicable declarations
state:
A B C : Type,
f : A → C,
g : B → C
⊢ A ⊕ B → C -/