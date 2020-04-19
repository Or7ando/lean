
import category_theory.comma
import category_theory.limits.shapes.finite_limits
import category_theory.yoneda
import order.complete_lattice
import data.set.lattice  
import .comma
import algebra.category.CommRing
import category_theory.types

universes  u

local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  

structure Pre_sieves (X : Ringᵒᵖ ) := 
(S : set unop X)
(I := ideal.span S)
(Hyp : 1 ∈ I)


-- create set of over. 
-- 
-- def ring_sieve (R : Ring)(PS : Pre-sieves) : sieve := 
{
    arrow := { f  : (over X) // ∃ s ∈ PS.S, ∃ u ∈ R,  f s * u = 1} 
}