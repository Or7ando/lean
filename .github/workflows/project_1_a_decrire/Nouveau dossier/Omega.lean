import ring_theory.algebra
import data.polynomial
import tactic
import data.polynomial
import algebra.category.CommRing.basic
import data.finsupp
open category_theory
open functor
open CommRing
open polynomial
open algebra 
open finsupp
universes v u  
local notation ` Ring `     :=    CommRing.{u}
local notation ` Set  `     :=    Type u   


def 𝔸  (α : Type u) [comm_ring α]  : Set := α  
namespace 𝔸
 def map (α : Type u)(β : Type u)[comm_ring α][comm_ring β] (f : α →+* β) : 𝔸 ( α ) → 𝔸 ( β )  := 
       λ a : 𝔸(α),  f a  
end 𝔸 

def 𝕆 : Ring ⥤ Ring  := functor.id Ring  


@[reducible] def Ω (α : Type u)[comm_ring α] :=
submodule α α 
namespace Ω 
def map (α : Type u)(β : Type u)[comm_ring α][comm_ring β] (f : α →+* β) : Ω ( α ) → Ω ( β )  := 
  λ (I :  Ω( α )), ideal.span (f '' I)


def  At :  Ring  ⥤  Set :=
{ obj :=   λ R :Ring, 𝔸(R),
  map :=   λ α β f ,  f, 
}


def Ω₀ (α : Type)[comm_ring α] :=  finset α 



def fr  [comm_ring α] : Ω₀(α) →  Ω(α) := (λ s : Ω₀(α)), ideal.span(s.to_set)

  

end

---- p ∈ Z[X]  →  ι p ∈ R[X]  avec  ι : ℤ → R   
noncomputable def ι (p : polynomial ℤ)  {R : Ring} : R → R := λ t, eval t (map (to_fun R) p) 

def β (R :  Alg ) : ℤ → R := to_fun (R) 

noncomputable def ι₁  {R : Ring} :  polynomial ℤ  →   polynomial R :=
 λ P : polynomial ℤ,  map_range  (to_fun R) ( is_add_group_hom.map_zero (to_fun R)) (P) 

---   Ca permet d'obtenir une notation sympathique ! 
---   Maintenant : on souhait prouver un théormee  Pour tout f : A ⟶ B 
---   f (ι (p) x) = ι p f(x) 
---   En gros, il agit de voir un morphisme 
---   iota : A → B → C   →  A[X] →R B[X] →R C[X]  


structure Idem (p : polynomial ℤ) (R : Ring) := 
      (t : R)  
      (certificat : ι(p) t   = 0)  


#print idem 
end

@[reducible] def Ω (α : Type u)[comm_ring α] :=
submodule α α 

namespace Ω

def map (α : Type u)(β : Type u)[comm_ring α][comm_ring β] (f : α →+* β) : Ω ( α ) → Ω ( β )  := 
  λ (I :  Ω( α )), ideal.span (f '' I)

def Ω₀ (α : Type)[comm_ring α] :=  finset α 


def fr  [comm_ring α] : Ω₀(α) →  Ω(α) := λ s : Ω₀(α), ideal.span(s.to_set)
  
end Ω 
namespace 𝔸 
end 𝔸 
