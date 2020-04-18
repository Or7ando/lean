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
`[  try {simp only with RW_REP}, try {exact rfl}]
run_cmd add_interactive [`rw_simp]

universe variables u v w w'
open group
open linear_map   
open linear_equiv
open submodule 
open linear_map.general_linear_group
/-
     I thinck i add three  lemma into  mathlib  line 1922 at the file linear_algebra.bassic 
def to_linear_map (f : general_linear_group R M) : M →ₗ[R] M :=(to_linear_equiv f).to_linear_map 
def to_linear_map_inv (f : general_linear_group R M) :  
M →ₗ[R] M := (to_linear_equiv f⁻¹).to_linear_map
def to_fun (f : general_linear_group R M) : M → M :=  f.val 
-/
attribute [RW_REP] coe_add coe_neg coe_smul coe_mk subtype.eta   eq.symm
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
-- open NOTATION
variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'}
  [group G] [ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

instance : has_coe_to_fun (group_representation G R M) := ⟨_, λ g, g.to_fun⟩   --- 
def has_coe_to (ρ : group_representation G R M) : G → (M →ₗ[R] M ) := λ g, L ρ g  
notation  `⟦` ρ `⟧` :=  has_coe_to ρ  
namespace MY_TEST
variables (f  : M →ₗ[R] M) ( x y : M) 
variables (ρ : group_representation G R M)
include ρ 
example : f (x+ y) = f(x)+f(y) :=  f.add x y  

@[RW_REP] theorem   linearity (g : G ) (x y : M): ⟦ ρ ⟧ g (x+y) = ⟦ρ⟧ g (x) + ⟦ρ⟧ g (y) := 
begin exact (⟦ρ⟧ g).add x y end

@[RW_REP] theorem   smul' (g : G)  (r : R)(m : M) : (⟦ ρ⟧  g) (r • m) = r • ((⟦ ρ ⟧  g) m) := begin 
     exact ( ⟦ ρ ⟧ g).smul r m,
end
variables  (g g' : G) 

variables (p : submodule R M)

@[RW_REP]lemma F_linearity (x y : M) (g : G) : (F ρ g) (x+y) = (F ρ g) x + (F ρ g) y := begin 
     exact (L ρ g).add x y,   --- the same for L !  
end 

variables (h : ∀ x : M, ∀ g : G,  (L ρ  g) x ∈ p)

--- le mécanisme est le suivant : 
--- ρ : G →* GL R M 
--- le problème étant que :: c'est un morphsime de groupe  mais c'est une structure
--- GL R M donc convertion merdique via L 
--- Il y a ⇑ 

theorem L_to_F  (g : G)(x : M) : (F ρ g) x = ⟦ρ⟧ g x := rfl 

example (ρ : group_representation G R M) ( g g' : G) : ρ (g * g') = ρ g * ρ g' := ρ.map_mul g g' 
@[RW_REP]lemma rmap_mul (ρ : group_representation G R M) ( g g' : G) :
      ⟦ ρ ⟧  (g * g')  =  ⟦ρ⟧  g   ⊚  ⟦ ρ ⟧  g' := 
begin 
     ext, rw comp_apply, iterate 3{rw ← L_to_F}, rw ρ.map_mul,exact rfl,
end
-- @[RW_REP]lemma rmap_mul' (ρ : group_representation G R M) ( g g' : G) :
--           ⟦ρ⟧  g   ⊚  ⟦ ρ ⟧  g' = ⟦ ρ ⟧  (g * g') := 
-- begin 
--      ext, rw comp_apply, iterate 3{rw ← L_to_F}, rw ρ.map_mul,exact rfl,
-- end
@[RW_REP] lemma rmap_one (ρ : group_representation G R M)  :
      ⟦ ρ ⟧  (1)  =  linear_map.id := begin 
      ext,rw ← L_to_F,rw ρ.map_one,exact rfl,
      end 
@[RW_REP] lemma rmap_inv_mul (ρ : group_representation G R M)(g: G)  :
      ⟦ ρ ⟧  (g * g⁻¹ )  =  linear_map.id := begin 
      rw mul_inv_self,exact rmap_one ρ,
      end   
@[RW_REP] lemma rmap_mul_inv (ρ : group_representation G R M)(g: G)  :
      ⟦ ρ ⟧  (g⁻¹  * g )  =  linear_map.id := begin 
      rw inv_mul_self,exact rmap_one ρ,
      end  
@[RW_REP] lemma rmap_inv' (ρ : group_representation G R M) (g : G) : 
     ⟦ρ⟧  g   ⊚  ⟦ ρ ⟧  g⁻¹  = linear_map.id := begin 
          rw ← rmap_mul,exact rmap_inv_mul ρ g,
     end
@[RW_REP] lemma rmap_inv''(ρ : group_representation G R M) (g : G) : 
     ⟦ρ⟧  g⁻¹    ⊚  ⟦ ρ ⟧  g  = linear_map.id := begin 
          rw ← rmap_mul,exact rmap_mul_inv ρ g ,
     end
@[RW_REP] lemma rmap_inv_apply'' (ρ : group_representation G R M) (g : G)(x : M) : 
     (⟦ρ⟧  g⁻¹    ⊚  ⟦ ρ ⟧  g ) x = x := begin 
          rw rmap_inv'',exact rfl,
     end
@[RW_REP] lemma rmap_inv_apply' (ρ : group_representation G R M) (g : G)(x : M) : 
     (⟦ρ⟧  g    ⊚  ⟦ ρ ⟧  g⁻¹  ) x = x := begin 
          rw rmap_inv',exact rfl,
     end
def has_inv (ρ : group_representation G R M)(g : G) :  M ≃ₗ[R]  M :=  { 
     to_fun := ⟦ ρ ⟧ g , 
     add := linearity ρ g , 
     smul :=  smul' ρ g,
     inv_fun :=  ⟦ ρ ⟧ g⁻¹, 
     left_inv :=  rmap_inv_apply'' ρ g,  
     right_inv :=  rmap_inv_apply' ρ g
}
-- @[RW_REP] lemma rmap_inv (ρ : group_representation G R M)(g : G) :  -- 207 
--      ⟦ ρ ⟧ g⁻¹ =  to_linear_map_inv (has_inv' ρ g )   := begin 
--           ext, 
--           sorry, 
--      end 
@[RW_REP]lemma star_is_oo (ρ : group_representation G R M) ( g g' : G) :
      ⟦ρ⟧  g   ⊚  ⟦ ρ ⟧  g'  =  ⟦ρ⟧  g   *  ⟦ ρ ⟧  g' :=  by rw_simp


@[RW_REP]lemma rmap_map_assoc (ρ : group_representation G R M)( g1 g2 g3 : G) : ⟦ρ⟧ (g1 * g2 *g3)  =
     ⟦ρ⟧ (g1) ⊚  (⟦ρ⟧  g2 ⊚   ⟦ρ⟧ g3)  := 
begin
      rw  group.mul_assoc,rw rmap_mul,rw rmap_mul,
     -- rw_simp,
end
example (ρ : group_representation G R M)( g1 g2 g3 g4 : G) : ⟦ρ⟧ (g1 * (g2 *g3 * g4))  =
     ⟦ρ⟧ (g1) ⊚  (⟦ρ⟧  g2 ⊚   ⟦ρ⟧ g3) * ⟦ ρ ⟧ g4  := 
begin

     rw_simp,
end
@[RW_REP]lemma times_to_oo (ρ : group_representation G R M)( g g' : G) :  ⟦ ρ ⟧  (g * g')  =  ⟦ρ⟧  g  *  ⟦ ρ ⟧  g' := begin 
     rw_simp, 
end
example (ρ : group_representation G R M)( g1 g2 g3 : G) : ⟦ρ⟧ (g1 * g2 *g3)  =
     ⟦ρ⟧ (g1) ⊚  ⟦ρ⟧  g2  *   ⟦ρ⟧ g3  := 
begin
     rw_simp,  
end
@[RW_REP]lemma mul_to_composition_of_function (ρ : group_representation G R M) ( g g' : G) :
 ⟦ ρ⟧  (g * g')  = ( ⟦ ρ⟧  g )  *  (⟦  ρ ⟧  g') := begin 
  rw_simp, 
end
@[RW_REP]lemma mixte_linearity (ρ : group_representation G R M) ( g g' : G) (x y : M) (r : R): 
       ⟦ ρ⟧  (g * g') (x+r • y) = ⟦ ρ ⟧ g ( ⟦ ρ ⟧ g' x )+ r • ⟦ ρ ⟧ g ( ⟦ ρ ⟧ g' y ) := begin
          iterate 2 {rw ← comp_apply},rw_simp, rw ← rmap_mul,
end
-- @[RW_REP]lemma L_to_F (g : G) :  (L ρ g).to_fun = (F ρ g) := rfl


example :    ⟦ ρ ⟧  (g * g') = (L ρ g) ⊚   (L ρ g')  := by rw_simp
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
@[RW_REP]lemma sub_module.eq_trans (x y : M) (hx : x ∈ p)(hy : y ∈ p) :  
(x : M) = (y : M) →  (⟨x,hx⟩ : p)   = (⟨ y,hy⟩ : p )  := begin 
     intros,congr ; try { assumption },
end 
@[RW_REP] lemma sub_module.eq_trans' (x y : p) : (x : M) = (y : M) → x = y := begin
          intros,rcases x,rcases y,congr; try {assumption},
end
-- lemma sub_module_val (x : M) (hx : x ∈ p) : (⟨x,hx ⟩ : p).val = (x : M) := rfl

def stable_sub_module (ρ : group_representation G R M)(p : submodule R M) :=  
                     ∀ g : G, ∀ x : p, (L ρ g) x ∈ p 
/-
     First Step : we define G → (p →ₗ[R] p)
-/

def restriction (h : stable_sub_module ρ p) : G → (p →ₗ[R] p)  := λ g, begin
     exact {
          to_fun    := λ x, ⟨( ⟦ ρ⟧  g ) x, h g x⟩,  
          add       := begin  intros x y, rw_simp, end,  
          smul      := begin intro c, intros x, rw_simp, end
     }, 
end
open MY_TEST
@[RW_REP]lemma restriction_ext (h : stable_sub_module ρ p) (y : p) 
: (( ⟦ρ⟧  g) y : M ) = (restriction ρ h g y : M) := rfl 
@[RW_REP]lemma restriction_ext' (h : stable_sub_module ρ p) (y : p) 
:   (restriction ρ h g y : M) = (( ⟦ρ⟧  g) y : M ) := rfl 
def  restriction_equiv (h : stable_sub_module ρ p) (g : G) :  (p ≃ p) :=   
{ to_fun := (restriction ρ h g),
  inv_fun := (restriction ρ h g⁻¹),
  left_inv := begin 
               intros x,
                    apply sub_module.eq_trans',
                    iterate 2 {rw ← restriction_ext},
                    rw ← comp_apply,
                    apply rmap_inv_apply'',
                    -- rw [← comp_apply,←  mul_to_composition_of_linear_map, inv_mul_self, ρ.map_one],
                    -- exact rfl,end,
               end
  , right_inv := begin 
               intros x,
               apply sub_module.eq_trans',  
               iterate 2 {rw ← restriction_ext}, 
               rw  ← comp_apply, 
               apply rmap_inv_apply',
  end }
def Restriction (h : stable_sub_module ρ p) (g : G) : p ≃ₗ[R] p :=
 { .. restriction ρ h g, .. restriction_equiv ρ h g}


def sub_representation (h : stable_sub_module ρ p) : group_representation G R p := 
{ to_fun := λ g, of_linear_equiv (Restriction ρ h g),
  map_one' := begin 
               rw units.ext_iff, --- Creer un helper pour la sous structure car c'est chiant
               ext,rcases x,
               apply sub_module.eq_trans,
                rw rmap_one,exact rfl,
               end,
  map_mul' := begin intros g1 g2,rw units.ext_iff, ext, rcases x,
                    apply sub_module.eq_trans,rw_simp,rw of_linear_equiv_val, 
                    rw rmap_mul,
                    rw comp_apply, exact rfl,
 end }
 variables (h : stable_sub_module ρ p)
 #check sub_representation ρ h
 notation ρ `/`h := sub_representation ρ h 
 #check  ⟦ ρ / h⟧  g
 @[RW_REP]lemma sub_representation.val (ρ : group_representation G R M) (h : stable_sub_module ρ p)( x : p) : 
     (⟦ρ⟧ g ) x.val = ( ⟦ ρ / h ⟧  g) x    := rfl
 
@[RW_REP] lemma rw_sub_module_action_to (ρ : group_representation G R M) (h : stable_sub_module ρ p) (x : p) : 
     (⟦ρ ⟧ g) x = ⟦ρ / h⟧ g x :=  
     begin 
          -- rw_simp, --- joke :D
          exact rfl, 
     end
example (ρ : group_representation G R M) (h : stable_sub_module ρ p) (x y : p)(r : R) (g g' : G): true := 
     begin 
          have R : ⟦ ρ ⟧ g ( ⟦ ρ ⟧ g' x )+ r • ⟦ ρ ⟧ g ( ⟦ ρ ⟧ g' y ) =   ⟦ ρ / h ⟧ (g * g') (x+ r • y),  
               iterate 2 {rw ← comp_apply}, rw ← rmap_mul,rw ← smul',rw ← linearity,rw_simp,  
          trivial, 
          end 
end stability
end group_representation