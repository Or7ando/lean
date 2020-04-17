/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import linear_algebra.basic
import algebra.group.hom
/- we will probably need to import other files soon too, like `linear_algebra.finite_dimensional`. -/
-- set_option trace.simplify true
run_cmd mk_simp_attr `RW_REP
meta def rw_simp  : tactic unit :=
`[  try {simp only with RW_REP}]
run_cmd add_interactive [`rw_simp]

universe variables u v w w'
open group
open linear_map 
open linear_equiv
open submodule 
open linear_map.general_linear_group

attribute [RW_REP] coe_add coe_neg coe_smul coe_mk subtype.eta
namespace NOTATION
notation  `GL`                := general_linear_group
notation  `L`:80 f :80        := general_linear_group.to_linear_map f
notation  `F`:80 f :82        := general_linear_group.to_fun f   --- add in mathlib 
notation  a` ⊚ `:80 b:80      := linear_map.comp a b
end NOTATION
/- maybe needs a shorter name -/
/-- A representation of a group `G` is an `R`-module `M` with a group homomorphisme from  `G` to
  `GL(M)`. Normally `M` is a vector space, but we don't need that for the definition. -/

def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M] [module R M] :
  Type* :=  G →* GL R M
open NOTATION
variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'}
  [group G] [ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

instance : has_coe_to_fun (group_representation G R M) := ⟨_, λ g, g.to_fun⟩   --- 
namespace MY_TEST

variables (f  : M →ₗ[R] M) ( x y : M) 
variables (ρ : group_representation G R M)
include ρ 
example : f (x+ y) = f(x)+f(y) :=  f.add x y  

@[RW_REP] theorem   linearity (g : G ) (x y : M): (L ρ g) (x+y) = (L ρ g) (x) +  (L ρ g) (y) := 
begin exact (L ρ g).add x y end

@[RW_REP] theorem   smul' (g : G) (m : M) (r : R) : (L ρ g) (r • m) = r • ((L ρ g) m) := begin 
     exact (L ρ g).smul r m,
end
variables  (g g' : G) 

variables (p : submodule R M)
#check linear_map.comp (L ρ g)  (L ρ g')
#check (L ρ (g * g'))
#check (F ρ (g * g')) x
lemma F_linearity (x y : M) (g : G) : (F ρ g) (x+y) = (F ρ g) x + (F ρ g) y := begin 
     exact (L ρ g).add x y,   --- the same for L !  
end 

variables (h : ∀ x : M, ∀ g : G,  (L ρ  g) x ∈ p)

--- le mécanisme est le suivant : 
--- ρ : G →* GL R M 
--- le problème étant que :: c'est un morphsime de groupe  mais c'est une structure
--- GL R M donc convertion merdique via L 
--- Il y a ⇑ 

theorem L_to_F  (g : G)(x : M) : (F ρ g) x = (L ρ g) x := rfl 

@[RW_REP]lemma mul_to_composition_of_linear_map (ρ : group_representation G R M) ( g g' : G) :
     L ρ (g * g')  = (L ρ g)  ⊚ (L ρ g') := 
begin 
     rw ρ.map_mul, exact rfl,
end
#check    F (ρ g) 
#check    L ρ g 
#check    ρ g
#check    ρ 
#check    ρ.1

@[RW_REP]lemma mul_to_composition_of_function (ρ : group_representation G R M) ( g g' : G) :
F ρ (g * g')  = (F ρ g)  ∘  (F ρ g') := begin 
 rw ρ.map_mul, exact rfl, 
end
-- @[RW_REP]lemma L_to_F (g : G) :  (L ρ g).to_fun = (F ρ g) := rfl

example :   F ρ (g * g') = (F ρ g) ∘  (F ρ g')    := begin rw_simp, end
example :   L ρ (g * g') = (L ρ g) ⊚   (L ρ g')  := begin rw_simp, end
lemma mul_one (ρ : group_representation G R M) : (L ρ 1) = 1 := begin 
rw ρ.map_one, exact rfl,
end
end MY_TEST

namespace group_representation 
/- do we want this instance? Then we don't have to write `(ρ g).1 x` instead of `ρ g x`. -/
instance : has_coe (general_linear_group R M) (M →ₗ[R] M) := ⟨λ x, x.1⟩
protected structure morphism (ρ : group_representation G R M) (π : group_representation G R M') :
  Type (max w w') :=
  (f : M →ₗ[R] M')
  (commute : ∀(g : G), f ∘ ρ g  = π g ∘ f)
protected structure equiv (ρ : group_representation G R M) (π : group_representation G R M') :
  Type (max w w') :=
  (f : M ≃ₗ[R] M')
  (commute : ∀(g : G), f ∘ ρ g = π g ∘ f)

variables (ρ : group_representation G R M)
variables (g g' : G)(x : M)
-- example (x y : M) (g : G) :  ρ  g (x+y)= ρ g x + ρ g y := begin rw (L ρ g).add x y, end 
namespace stability  
/-
     We define the notion of stable submodule. 
     We make a sub-representation.
     ligne  384 algebra module submodule (conduit)
     il y a des lemmes de convertions.
 -/
variables {ρ1 : group_representation G R M}{p : submodule R M}
/-
     Strategy maths : We have ρ g x ∈ p for x ∈ p so 
     you have a map : ρ' g : p → p ... linear_map, invertible (restriction of ρ g⁻¹ ) and trivial trivial trivial 
     For lean : this is not trivial. We have to verify some stuff. 
     Lemma to try to deal with convertion  
-/
lemma sub_module.eq_trans (x y : M) (hx : x ∈ p)(hy : y ∈ p) :  
(x : M) = (y : M) →  (⟨x,hx⟩ : p)   = (⟨ y,hy⟩ : p )  := begin 
     intros,congr ; try { assumption },
end 
-- lemma sub_module_val (x : M) (hx : x ∈ p) : (⟨x,hx ⟩ : p).val = (x : M) := rfl

def stable_sub_module (ρ : group_representation G R M)(p : submodule R M) :=   ∀ g : G, ∀ x : p, (L ρ g) x ∈ p 
/-
     First Step : we define G → (p →ₗ[R] p)
-/

def restriction (h : stable_sub_module ρ p) : G → (p →ₗ[R] p)  := λ g, begin
     exact {
          to_fun    := λ x, ⟨(L ρ g ) x, h g x⟩,  
          add       := begin  intros x y, rw_simp, exact rfl, end,  
          smul      := begin intro c, intros x, rw_simp, exact rfl, end
     }, 
end
open MY_TEST
@[RW_REP]lemma restriction_ext (h : stable_sub_module ρ p) (y : p) 
: ((L ρ g) y : M ) = (restriction ρ h g y : M) := rfl 
def  restriction_equiv (h : stable_sub_module ρ p) (g : G) :  (p ≃ p) :=  
{ to_fun := (restriction ρ h g),
  inv_fun := (restriction ρ h g⁻¹),
  left_inv := begin intros x,rcases x with ⟨ζ,hyp ⟩,
                    apply sub_module.eq_trans,
                    rw ← restriction_ext,rw_simp,
                    rw [← comp_apply,←  mul_to_composition_of_linear_map, inv_mul_self, ρ.map_one],
                    exact rfl,end,
  right_inv := begin 
               intros x,
               rcases x with ⟨ζ,hyp⟩,
               apply sub_module.eq_trans,rw ← restriction_ext, rw  ← comp_apply,rw_simp,
               rw  ← mul_to_composition_of_linear_map, rw mul_inv_self g, rw MY_TEST.mul_one,exact rfl,
  end }
def Restriction (h : stable_sub_module ρ p) (g : G) : p ≃ₗ[R] p :=
 { .. restriction ρ h g, .. restriction_equiv ρ h g}

def sub_representation (h : stable_sub_module ρ p) : group_representation G R p := 
{ to_fun := λ g, of_linear_equiv (Restriction ρ h g),
  map_one' := begin 
                rw units.ext_iff,ext,rcases x,rw_simp,
                apply sub_module.eq_trans,rw MY_TEST.mul_one,exact rfl,
               end,
  map_mul' := begin intros g1 g2,rw units.ext_iff, ext, rcases x,
                    apply sub_module.eq_trans,rw_simp,rw of_linear_equiv_val, 
                    rw  mul_to_composition_of_linear_map,
                    rw comp_apply, exact rfl,
 end }
end stability


-- notation ρ1 `_|` p := restriction ρ1 p 
end group_representation