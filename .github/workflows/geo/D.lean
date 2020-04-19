import .global
import .ideals
universe u
local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  
open CommRing

namespace D 
variables (R :Ring)
variables (S : set R)

def D_obj (A : Ring) := {ζ :  R ⟶ A | (1 : A) ∈ ideal.map (ζ) (ideal.span S)}
@[ext]lemma ext  (A : Ring)(ζ1 :  D_obj R S A)(ζ2 : D_obj R S A) : ζ1.val =ζ2.val → ζ1 = ζ2 :=
begin
          intro h, 
          cases ζ1, 
          cases ζ2,
          congr ; try { assumption },
end
def D_map (A B : Ring) (ψ : A ⟶ B) : D_obj R S A → D_obj R S B := λ ζ, 
begin 
    exact {val := ζ.val ≫ ψ , property := begin
          unfold D_obj, 
          have t : ideal.map (ζ.val ≫ ψ) (ideal.span S) = ideal.map ψ  (ideal.map (ζ.val)  (ideal.span S)),
               rw ideal.ideal_comp,
          have T2 :  ψ (1 : A) ∈ ideal.map ψ (ideal.map (ζ.val)  (ideal.span S)),
               exact ideal.mem_map_of_mem ζ.property ,
          rw ← t at T2, 
          erw  ψ.map_one at T2,
          use T2,
    end }
end
lemma D_map_comp (A B : Ring) (ψ : A ⟶ B) (ζ : D_obj R S A) : (D_map R S A B ψ ζ).val = ζ.val ≫ ψ := rfl
lemma D_map_one (A : Ring) (ζ : D_obj R S A) : D_map R S A A (𝟙 A) ζ  = ζ := begin 
     ext,
     rw D_map,
     exact rfl,
end
def D (S : set R) : Ring ⥤ Set :=
{
     obj := λ A, D_obj R S A,
     map := D_map R S,
     map_id' := λ A, begin 
          funext, rw D_map_one, exact rfl,
     end 
}
end D