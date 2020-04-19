import category_theory.functor_category -- this transitively imports
import algebra.category.CommRing.basic
import algebra.ring
import category_theory.natural_transformation
import category_theory.types
open CommRing
open is_ring_hom
open nat
universes v u  -- the order matters (see below)
/--
## Category of Commutative Ring : Functor of nilpotent.
## Define a functor. We first define two functions : 
## 1. obj'
## 2. map'
##  construction ! 


#print "hello" 
def φ  :   nil3 ⟶  A := { 
    app := λ R,Nat_tu(R)
    -- naturality' := begin 
    --     intros R R' f,
    --     sorry, 
    --     end 
}
#print φ 
-/
lemma power_commute_with_morph  (A B : CommRing)(f : A ⟶ B)(n : ℕ) : ∀ x : A, f( x^n ) = (f x)^n := λ x,
            nat.rec_on n (show  f(x^0) = (f x)^0, {rw [pow_zero x,pow_zero (f x)], exact map_one f,})
                         (assume n, assume rec_hyp : f(x^n) = (f(x))^n,
                                 show f(x^(n+1)) = (f(x))^(n+1),{rw [pow_succ x n,pow_succ (f(x)) n,← rec_hyp],exact map_mul (f)})
            
def nil_obj'(n : ℕ)  (R : CommRing) : Type v := { η  : R | η^n = 0 }  
def nil_map'(n : ℕ)  (X Y : CommRing)( f : ring_hom X Y) : nil_obj'(n) X → nil_obj'(n) Y  := begin 
  intros x,
  cases x with η certificat,
  have t : η^n = 0,
    exact certificat,
    have H : ( f η  ) ^n = 0,
        rw ←  power_commute_with_morph,
        rw t,
        exact map_zero f,
        use (f η), assumption,
  end

def Nil(n: ℕ) : CommRing ⥤ Type v :=  
{ obj := nil_obj'(n),
  map := nil_map'(n),  
}
def nil3 := Nil(3)
#check Nil
def A_obj' (R : CommRing) : Type v := (R : Type v)   
def A_map'  (X Y : CommRing)( f : ring_hom X Y) :A_obj' X → A_obj' Y  := 
begin 
  intros x,
  use  f x,
  end
def A : CommRing ⥤ Type v :=  
{ obj := A_obj'
  map := A_map' 
}
#check A 
#print 14
lemma Nat_tu   (R : CommRing) :  nil3.obj(R) ⟶ A.obj(R) :=  
    begin 
        rw category_theory.types_hom,
        intro x,
        cases x with e certificat,
        use e, 
    end
#print 16 