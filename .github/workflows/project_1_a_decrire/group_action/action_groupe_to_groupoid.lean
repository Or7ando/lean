import group_theory.group_action
import algebra.group
import category_theory.category.Groupoid
/--
## Let G be a group and X a G-set (i.e a set with an G action), we make the so called 'action groupoid' 
## This is a category with obj  : X and for x y ∈ X, hom(x,y) = Transporteur (x,y)  := { g ∈ G | g • x = y} 
##  The composition is given by the group law.    
-/

def Transporteur (G : Type )[group G](X : Type )[mul_action  G X] (x y : X) : set G  := { g : G | g • x = y}
lemma mem_transporteur (G : Type )[group G](X : Type )[mul_action  G X] (x y : X)(g : G) : 
        (g ∈ Transporteur G X x y) ↔ g • x = y :=
        begin 
            split,
            intro,
            cases a, 
            exact rfl, ---------- Grrrrouhhhhhhhhh :  how to simplify 
            intro,
            cases a,
            exact rfl,
        end
section Transposteur 
parameters (G : Type )[group G](X : Type )[mul_action  G X]
def one_in_transporteur : ∀ x y : X, (1 : G) ∈ (Transporteur G X x y) ↔ (x = y) := 
    begin 
        intros x y,
        rw mem_transporteur  (G) (X) (x) (y) (1),
        split,
        intro,
        cases a,
        exact eq.symm (one_smul G x ),
        intro,
        cases a,
        exact one_smul G x,
    end 
lemma transporteur_comp (x y z : X) : (Transporteur G X  x y) → (Transporteur G X y z ) → (Transporteur G X x z) := 
    λ ⟨g,proof_g⟩ ⟨h, proof_h⟩,  begin  
        have H : (h * g) • x = z,
            rw mul_smul,
            rw mem_transporteur at proof_g,
            rw proof_g,
            rw mem_transporteur at proof_h,
            rw proof_h,
        use (h * g),
        exact H,
    end
lemma transporteur_inv (x y : X) : (Transporteur G X x y) → (Transporteur G X y x) := 
λ ⟨g,proof_g⟩, begin 
    rw mem_transporteur at proof_g, 
    have H : x = g⁻¹ • y,
        rw ← proof_g,
        rw ←  mul_smul,
        rw  inv_mul_self,
        rw one_smul,
    use g⁻¹,
    exact eq.symm H,
end 
end Transposteur
open category_theory
section
variables (G : Type )[group G](X : Type)[mul_action  G X]

end
