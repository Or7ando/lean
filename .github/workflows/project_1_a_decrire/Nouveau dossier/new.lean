import ring_theory.algebra
import tactic.ring
import tactic.ring_exp
import data.polynomial
import data.finsupp
import data.zmod.basic
import tactic.ring
import algebra.category.CommRing.basic
import foncteur.structure_comax
open zmod
@[reducible] def R : Type := zmod(15)
def  eval  : ℤ  → R := 
    λ n, n 
#eval eval(19)
open co_maxi
def A :=  co_maxi.comax.gluing_data   (6 : R)(-5 : R ) (1 : R) (-1 : R) 1 ⟨ 1,1, by ring⟩ ⟨⟨ 1,1, by ring⟩, 1,by ring⟩ ---  6 * 1 + (-5) *1 = 1,  ,m = 1 cause  6 × 5 = 0
--- The gluing point is 4 because 4 mod 3 = 1 and 4 mod 5 = -1,    
#print A._proof_1 -- where is 4 ???  exact {to_descent_data := ⟨t,m,proof_m⟩, s := vf *s_f * f^m+ vg*s_g*g^m, N_f := m, N_g := m, proof_n_plus_m_f_g := Y},
-- Can I execute my proof ?? or it's a stupid idea ? -- i give Lean all the calculus so he have the answer ! ! ! But where ??? 
#print A
