import tactic.ring
import tactic.ring_exp
import algebra.category.CommRing.basic

open CommRing

---          Goal : understand the notion of structure with a little exemple !
namespace co_maxi         
structure comax {R : Type}(a b: R) [comm_ring R] :=   
(u : R)(v : R)
(certificat : a * u + b * v = (1 : R))
#print comax
open is_ring_hom  --- to have acces map_mul map_one 
def comp (A B: Type)(φ : A → B)[comm_ring A][comm_ring B][is_ring_hom φ] (a b : A) : (comax a b) → comax (φ a) (φ b) := λ ⟨u_ab,v_ab,certificat_ab⟩, --- {} or ⟨ ⟩ λ OBJET and then OBJET.u etc 
    begin
        have certificat : (φ a) * (φ u_ab) + (φ b) * (φ v_ab) = 1,          -- It's trivial ring identity, but i have to control ! 
            rw [ ←  map_mul φ, ← map_mul φ , ← map_add φ,certificat_ab],
            apply map_one,
        exact {u := φ u_ab,v := φ v_ab,certificat := certificat},            --- the constructor of structure  : i thinck better than  ⟨  ⟩ 
    end
---  How to make comp beautiful fonctorial ? 
---  goal execute the proof with an example.
---  For the moment we deal with zmod ring !
 
end co_maxi
namespace Exemple
--- This is a closed universe   
#print Ring
--- but we have access to the primitive structure
#print co_maxi.comax -- we have to co_maxi. first to acces comax ! 

end Exemple 
open co_maxi