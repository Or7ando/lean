import .global
import ring_theory.ideals
import ring_theory.ideal_operations
universes  u

local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  

namespace ideal
lemma ideal_id (A : Ring) (I : ideal A) : ideal.map (𝟙 A)I = I := 
begin 
  have g : set.image (𝟙 A) I = (I : set A),
    exact set.image_id ↑I,
    unfold ideal.map,
    rw g,
    exact ideal.span_eq I,
end
lemma ideal_comp (A B C : Ring)(I : ideal A) (f : A ⟶  B) (g : B ⟶  C)  :
  ideal.map (f ≫ g) I = ideal.map g (ideal.map f I) :=
le_antisymm
  (ideal.map_le_iff_le_comap.2 $ λ x hxI, ideal.mem_map_of_mem $ ideal.mem_map_of_mem hxI)
  (ideal.map_le_iff_le_comap.2 $ ideal.map_le_iff_le_comap.2 $ λ x hxI, ideal.mem_map_of_mem hxI)
end ideal