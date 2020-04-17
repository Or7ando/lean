/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import linear_algebra.basic
import algebra.group.hom
/- we will probably need to import other files soon too, like `linear_algebra.finite_dimensional`. -/
set_option trace.simplify true
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
notation `GL`  := general_linear_group
notation  `L`:80 f :80:= general_linear_group.to_linear_map f
notation  `F`:80 f :82:= general_linear_group.to_fun f 
notation  a` ⊚ `:80 b:80 := linear_map.comp a b
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

example :   F ρ (g * g') = (F ρ g) ∘  (F ρ g')  := begin rw_simp, end
example :   L ρ (g * g') = (L ρ g) ⊚   (L ρ g')  := begin rw_simp, end


lemma joujou (x y : M)(g : G) (p : submodule R M) (hx : x ∈ p)(hy : y ∈ p): true := begin 
     let z :=(⟨x,hx⟩+⟨y,hy⟩ : p),  
     let i := (L ρ g) x, 
     trivial,
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
     Lemma to try to deal with convertion  
-/
lemma sub_module.eq_trans (x y : M) (hx : x ∈ p)(hy : y ∈ p) :  
(x : M) = (y : M) →  (⟨x,hx⟩ : p)   = (⟨ y,hy⟩ : p )  := begin 
     intros,congr ; try { assumption },
end 
lemma sub_module_val (x : M) (hx : x ∈ p) : (⟨x,hx ⟩ : p).val = (x : M) := rfl

def stable_sub_module (ρ1 : group_representation G R M)(p : submodule R M) := 
      ∀ g : G, ∀ x : p, ρ1 g x ∈ p 
/-
     Etudier un peu la notion de stability ! 
-/

lemma add_conv    (x y : M)(g : G) :  ρ1 g (x+y) = ρ1 g x + ρ1 g y :=   (ρ1 g : M →ₗ[R] M ).add  x y 
lemma scalar_conv (x : M)(r : R) : ρ1 g ( r • x) =  r • ρ1 g x :=    (ρ1 g : M →ₗ[R] M).smul r x 

def restriction (h : stable_sub_module ρ1 p) : G → (p →ₗ[R] p)  := λ g, begin
     exact {
          to_fun := λ x,⟨ρ1 g x, h g x⟩,  
          add := begin  
                    intros x y,
                    apply sub_module.eq_trans,
                    iterate 2 {rw sub_module_val},
                   rw_simp,
               end,  
          smul := begin       
               intro c, intros x, apply sub_module.eq_trans,  iterate 1 {rw sub_module_val}, submodule_simp,--simp,
          end}, 
end
/-
     important rfl lemma 
-/
#print group
#print function.left_inverse
section Restriction 
variables (h : stable_sub_module ρ1 p)
@[REPRESENTATION]lemma restriction_ext (h : stable_sub_module ρ1 p)(g :G)(x : p)   : 
(restriction h g).to_fun x  =   (⟨ρ1 g x, h g x⟩) := rfl  
lemma rest_is_lin_equiv (h : stable_sub_module ρ1 p) (g : G) : p ≃ₗ[R] p :=  begin 
     exact linear_equiv.mk  
          (restriction h g).to_fun
          (restriction h g).add
          (restriction h g).smul 
          ((restriction h g⁻¹).to_fun)
          (begin 
               intros x,rcases x, rw restriction_ext,rw restriction_ext,
               submodule_simp,apply sub_module.eq_trans,rw ←  rho_apply,
               rw inv_mul_self g,
               rw ρ1.map_one,exact rfl,
          end)
          (begin intros x,rcases x, rw restriction_ext,rw restriction_ext,
               submodule_simp,apply sub_module.eq_trans,rw ←  rho_apply,
               rw mul_inv_self g,
               rw ρ1.map_one,exact rfl, end ), 
end
lemma rest_is_lin_equiv_fun (h : stable_sub_module ρ1 p) (g : G) : (rest_is_lin_equiv h g).to_fun =
(restriction h g).to_fun := by apply_instance begin 
     ext,rw restriction_ext,
end 
theorem sub_to_fun (h : stable_sub_module ρ1 p) :  G → GL R p := begin  
     intros g,
     exact general_linear_group.of_linear_equiv (rest_is_lin_equiv h g),
 end
 lemma sub_to_fun_val (h : stable_sub_module ρ1 p) (g :G) : (sub_to_fun h g).val = restriction h g := 
 begin 
     dunfold sub_to_fun,rw of_linear_equiv_val,
     end
 lemma sub_to_fun_apply (h : stable_sub_module ρ1 p) (g : G)  (x : p): 
       ((general_linear_equiv R p).to_equiv (sub_to_fun h g)).to_linear_map  x =  
       (⟨ρ1 g (x : M), h g x⟩ : p):= 
        begin 
        rw general_linear_equiv_to_linear_map,
        sorry, end

/-
Next step make sub_to_fun a group morphism ! 
-/
#check is_group_hom 
/-
@[class, priority 100, to_additive to_additive.value_type.mk (name.mk_string "is_add_group_hom" name.anonymous) (option.none.{0} string), priority 100, to_additive_aux name.mk_string "is_add_group_hom" name.anonymous]
structure is_group_hom : Π {α : Type u} {β : Type v} [_inst_1 : group α] [_inst_2 : group β], (α → β) → Prop
fields:
is_group_hom.to_is_mul_hom : ∀ {α : Type u} {β : Type v} [_inst_1 : group α] [_inst_2 : group β] {f : α → β} [c : is_group_hom f],
  is_mul_hom f
-/
lemma map_mul' (g g' : G) :   sub_to_fun h (g * g') = sub_to_fun  h g * sub_to_fun h g' := begin 
sorry,
end
end Restriction 
end stability

-- def to_linear_equivalence (g : G)( h : stable_sub_module ρ1 p) : p ≃ₗ[R] p := 
-- begin 
--     exact  of_linear 
--     (of h g)(of h g⁻¹)
--     (begin ext,apply set_coe.ext,sorry, end)
--     (sorry),
-- end




-- notation ρ1 `_|` p := restriction ρ1 p 
end group_representation