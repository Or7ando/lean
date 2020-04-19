import linear_algebra.basic
import algebra.group.hom
import group_representation 
universe variables u v w w'
open group
open linear_map   
open linear_equiv
open submodule 
open linear_map.general_linear_group

namespace irreductible_representation
variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'}
  [group G] [ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

variables (ρ : group_representation G R M)
structure sub_rep (ρ : group_representation G R M) := 
(p : submodule R M)
(stability : ∀ g : G, ∀ x : p, ( ⟦ ρ ⟧  g) x ∈ p )
instance has_coe : has_coe(sub_rep ρ) (submodule R M) := ⟨ λ ρ', ρ'.p⟩ 
def is_trivial_sub_rep  (ρ : group_representation G R M) (ρ' : sub_rep ρ) :=  (ρ'.p = ⊤) ∨ (ρ'.p = ⊥)
def Irreductible (ρ : group_representation G R M) := ∀ (ρ' : sub_rep ρ), is_trivial_sub_rep  ρ ρ' 
/-
     I don't know if it's ok theorem the hypothesis m≠ 0 stress me it's not a good condition (trivial ring problem)
-/
theorem lemme_de_Schur' (ρ : group_representation G R M)(ρ' :group_representation G R M')
[hyp : Irreductible ρ][hyp' : Irreductible ρ'] (f : ρ ⟶₁ ρ') (𝓁 : R)(m0 : M) (not_zero : f.linear_map m0 ≠ 0) : 
group_representation.equiv ρ ρ' 
:= { f := { to_fun := f.linear_map,
  add := f.linear_map.add,
  smul := f.linear_map.smul,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry},
  commute := sorry, } 



-- theorem lemme_de_Schur (ρ : group_representation G R M)(ρ' :group_representation G R M)
-- [hyp : Irreductible ρ][hyp' : Irreductible ρ'] (f : ρ ⟶₁ ρ') (𝓁 : R)(m0 : M)(m0 ≠ 0)
--  (spectral : f.linear_map m0 = 𝓁  • m0) :    ∀ m : M, f.linear_map m = 𝓁 • m := 
-- begin 
--           -- we need lemma ! 
--           sorry,
-- end 
end irreductible_representation