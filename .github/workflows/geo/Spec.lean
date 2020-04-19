import .global
universes  u

local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  

namespace Spec
variables (R : Ring)

def Spec   : Ring  ⥤ Set  := 
{
  obj :=  λ A : Ring ,   R ⟶  A,
  map :=  λ A B : Ring, λ ψ : A ⟶ B, λ ζ :  R ⟶ A,  ζ ≫ ψ,  
}
lemma Spec.obj.ext (A : Ring) : (Spec R).obj A = (R ⟶ A) := rfl
lemma Spec.map.ext (A B : Ring)(ψ : A ⟶ B) (ζ : R ⟶ A): (Spec R).map ψ ζ =  ring_hom.comp ψ  ζ  := rfl 

end Spec