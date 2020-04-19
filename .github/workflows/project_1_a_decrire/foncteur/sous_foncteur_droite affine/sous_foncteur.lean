import algebra.category.CommRing.basic
import algebra.ring
import tactic
import data.polynomial
import algebra.ring
import category_theory.types
import data.int.basic
universes v u 
open CommRing
open is_ring_hom
open category_theory
open polynomial
open int
/--
## The goal is study the set of solution of polynomial equation in one variable ! We form a functor  V_P : CommRing → Type v 
##    For all ring 
## 
-/

variables(R : Type v)[comm_ring R](P : polynomial ℤ)
structure V  (R: Type v)[comm_ring R] :=      --  set of solution of P(x) = 0  with x in R    
(x : R)                                       --  if φ : R → R' is a ring morphism then we have application
(certif : eval₂(int.cast) (x) (P) = 0 )       --  φ : V(P)(R) → V(P(R')    
@[ext]lemma ext : ∀ {ζ1 ζ2 : V P R}, ζ1.x = ζ2.x →  ζ1 = ζ2 := λ ζ1 ζ2,  
begin
  cases ζ1,                                        
  cases ζ2,
  intro h,
  congr ; try { assumption },
end
namespace commute_hom
lemma commute_hom  (P : polynomial ℤ)(R :Type v)[comm_ring R] (R' : Type v)[comm_ring R'] (f : R → R') [is_ring_hom f]
(x : R) : eval₂ int.cast (f x) P = f (eval₂ int.cast x P) := begin
    have H : eval₂ (f ∘ int.cast) (f x) P = f (eval₂ int.cast (x) P), 
            rw ←  hom_eval₂  P  int.cast f x,
    have G : f ∘ int.cast = int.cast,
        exact (int.eq_cast') (f ∘ int.cast),
    rw G at H,assumption,
end

end commute_hom
definition map_V {R : Type v} [comm_ring R] {R' : Type v}[comm_ring R'] (f : R → R') [is_ring_hom f] : (V P R) → (V P R') := λ ζ,begin 
exact  {x := f ζ.x, certif := 
begin
    have H : eval₂ (f ∘ int.cast) (f ζ.x) P = f (eval₂ int.cast (ζ.x) P), 
        rw ←  hom_eval₂  P  int.cast f ζ.x,
    have G : f ∘ int.cast = int.cast,
        exact (int.eq_cast') (f ∘ int.cast),
    rw G at H,
    rw H,
    have cer : eval₂ int.cast ζ.x P =0,
        exact ζ.certif, 
    rw cer,
    exact map_zero f,
    end}
end
lemma map_V_comp {R : Type v} [comm_ring R] {R' : Type v}[comm_ring R'] (f : R → R') [is_ring_hom f](ζ : V P R) : (map_V P f ζ).x = f ζ.x := rfl
def V_i : CommRing ⥤ Type v :=  
{ obj := λ R, V P R,
  map := λ R R' f, map_V P  f, 
  map_id' := λ R, begin 
    apply funext,
    intro ζ,
    ext,
    rw types_id,
    rw map_V_comp,
    exact rfl,
   end, 
  map_comp' := λ R R' R'' f g,
  begin 
    apply funext, 
    intro ζ, 
    ext, 
    rw map_V_comp,
    rw types_comp,
    rw map_V_comp,
    rw map_V_comp,
    exact rfl,
 end
}
def  F :=  (V_i P).obj 
#print F 