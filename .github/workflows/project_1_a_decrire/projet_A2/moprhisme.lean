import .X
import .action_Idem_X
import category_theory.natural_transformation
import category_theory.types
import data.quot
open CommRing
open X
open A2
open A2_disc
open idem_action_X
namespace π 
variables (R : Type)[comm_ring R]
#check (A(R)).r
/--
##  X :=  R ↦ { (x,y) ∈ A^2 ∣ (x-y)^2 inversible}   we define   π : X ⟹ A2_disc    (x,y) →  (x+y, xy) 
##            We want to show that the group of automorphism of  π  is Idem(R) and 
-/
def π {R : Type }[comm_ring R] : X(R) → A2_disc(R) :=  λ η, begin     
            have H : (η.x + η.y) * (η.x + η.y)  -↑4 * (η.x* η.y) = (η.x - η.y)^2,
                ring,simp,ring,
            have certif : ((η.x + η.y) * (η.x + η.y)  -↑4 * (η.x* η.y)) * η.inv = 1, 
                rw H, 
                exact η.certif,     
            exact { ζ :=  {a := η.x + η.y, b := η.x * η.y},
                    inv_disc := η.inv,
                    certif_disc := certif},
        end
lemma Γ (R : CommRing) :  𝕏.obj(R) →  𝔸2_disc.obj(R) :=   π 
lemma Γ_im_x {R : CommRing} (η  : X R) : (π  η ).ζ.a = η.x +η.y := rfl
lemma Γ_im_y {R : CommRing} (η  : X R) : (π η ).ζ.b = η.x *η.y := rfl
lemma naturality'' (A B : CommRing)(f : A ⟶   B) :(𝕏.map f  ≫  π ) = ( π  ≫  𝔸2_disc.map (f)) := begin 
    rw [category_theory.types_comp,category_theory.types_comp],
    funext,
    have T : (π  ∘ 𝕏.map f) x =  π  (( 𝕏.map f) x),   ---- faire des lemmes !!! 
        exact rfl,
    rw T,
    have T' : (𝔸2_disc.map f ∘ π ) x = (𝔸2_disc.map f)(π  x),
        exact rfl,
    have T'' : 𝔸2_disc.map f  = map_A2_disc f ,
        exact rfl,
    have T''' : 𝕏.map f = map_X f,
        exact rfl,
    rw T',
    rw T'',
    rw T''',
    ext,
    rw Γ_im_x (map_X f (x)),
    rw  A2_disc.map_comp_a (f) (π x),
    rw Γ_im_x (x),
    rw map_comp_x,
    rw map_comp_y,
    rw ← ring_hom.map_add f,
    rw Γ_im_y,
    rw map_comp_b,
    rw Γ_im_y (x),
    rw map_comp_x,
    rw map_comp_y,
    rw ← ring_hom.map_mul,
end   
def φ  :   𝕏  ⟶  𝔸2_disc  := { 
    app := λ R, π ,
    naturality' :=  naturality'',
}
#print φ 
#check φ 
end π 
namespace fiber_π 
open π 
def fiber_π  (R : Type )[comm_ring R] :  A2_disc R → set (X(R)) :=   λ ζ, {η : X(R) | π (η) = ζ } 
end fiber_π 
open  fiber_π 

#print fiber_π  