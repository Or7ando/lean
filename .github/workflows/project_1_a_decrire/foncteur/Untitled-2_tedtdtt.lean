import ring_theory.algebra
import data.polynomial
import tactic
import algebra.category.CommRing.basic
import data.finsupp
open CommRing
open finsupp finset lattice
open algebra 
open finsupp

namespace tr 

end tr


---          Goal : Soit φ : Z → R un morphisme d'anneau, soit P un polynôme ℤ[X]  et x ∈ R, alors φ(P(x)) = P(φ(x))  !
namespace cal
    variables ( R : Type)[comm_ring R]
    open polynomial
    def Q  := (x+1)^2+13*y^2
    #eval  (λ y : ℤ , Q (y) (y)) (3)
        structure my_polynomial(R : Type) [comm_ring R] := (P : ℕ → R) 
    constants A : ℤ  
    variables (φ : ring_hom ℤ R)

    def extension : polynomial ℤ → polynomial R := 
        λ P, begin
            have P := (X : polynomial ℤ), 
                set Q := P+1,


        end
def T := begin 
    have t := coeff_coe_to_fun (X+1),
    end
#print a
end cal 

/--
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
      (certificat : ι(p) t   = 0)  -/