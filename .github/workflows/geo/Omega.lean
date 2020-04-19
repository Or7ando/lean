import .global
import .ideals
universes  u

local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  

namespace Omega
def Ω_obj (A : Ring):= ideal A 
def Ω_map (A B :Ring)(ψ : A ⟶ B) : Ω_obj A → Ω_obj B:= λ I,begin 
  exact ideal.map ψ I,
end
def Ω : Ring ⥤ Set := 
{
  obj := λ A, ideal A,
  map := λ A B ψ, ideal.map ψ,
  map_id' := λ A, begin 
    funext I,  
    exact ideal.ideal_id A I,
  end,
  map_comp' := λ X Y Z  f g, begin
    funext I,   
    exact ideal.ideal_comp X Y Z I f g,   
end,
}
-- instance (A : Ring) : has_mem(Ω.obj(A)) := ⟨λ x,  ⟩ 
end Omega
namespace Omega_2 
open Omega
variables (A :Ring)
def square_ideal_app (A : Ring) : ideal A → ideal A := λ I, begin
  exact (I * I),
end 
def square_ideal_naturality (A B :Ring) (ψ : A ⟶ B)  : 
    Ω.map ψ ≫ square_ideal_app B = square_ideal_app A ≫ Ω.map ψ := begin 
    rw [category_theory.types_comp,category_theory.types_comp],
    funext  I, 
    rw [ show (Ω.map ψ ∘ square_ideal_app A) I = ideal.map ψ (I * I),from rfl,ideal.map_mul ψ I I],
    exact rfl,
    end
def square_ideal :  Ω  ⟶ Ω := 
{ 
    app := λ A : Ring, square_ideal_app A,
    naturality' := square_ideal_naturality, 
}
end Omega_2
-- namespace ONE 
-- def ONE_map  (A B : Ring) (ψ : A ⟶ B) : (⊥ : ideal A) → (⊥ : ideal B) 
-- := λ I, begin
--   have Hyp : ideal.map ψ (⊥)  = ⊥ , 
--     exact ideal.map_bot ψ,
--     exact ideal.map ψ I,
--  end
-- def ONE : Ring ⥤ Set := 
-- {
--   obj := λ A, {I : ideal A | I = ⊥ },
--   map := ONE_map,
-- --   map_id' := λ A, begin 
-- --     funext I,  
-- --     exact ideal.ideal_id A I,
-- --   end,
-- --   map_comp' := λ X Y Z  f g, begin
-- --     funext I,   
-- --     exact ideal.ideal_comp X Y Z I f g,   
-- -- end,
-- }
-- end ONE



