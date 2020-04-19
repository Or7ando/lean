import category_theory.functor_category -- this transitively imports
import algebra.category.CommRing.basic
import algebra.ring
open CommRing
open is_ring_hom
open nat
universes v u  -- the order matters (see below)
/--
## Category of Commutative Ring : Functor A.
## Define a functor. We first define two functions : 
## 1. obj'
## 2. map'
##  construction ! 
--/ 
lemma power_commute_with_morph  (A B : CommRing)(f : A ⟶ B)(n : ℕ) : ∀ x : A, f( x^n ) = (f x)^n := λ x,
            nat.rec_on n (show  f(x^0) = (f x)^0, {rw [pow_zero x,pow_zero (f x)], exact map_one f,})
                         (assume n, assume rec_hyp : f(x^n) = (f(x))^n,
                                 show f(x^(n+1)) = (f(x))^(n+1),{rw [pow_succ x n,pow_succ (f(x)) n,← rec_hyp],exact map_mul (f)})
            
def A_obj' (R : CommRing) : Type v := R     
def A_map'  (X Y : CommRing)( f : ring_hom X Y) :A_obj' X → A_obj' Y  := begin 
  intros x,
  use  f x,
  end
def A : CommRing ⥤ Type v :=  
{ obj := A_obj',
  map := A_map',  
}
#print A