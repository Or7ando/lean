import .A2
import category_theory.functor_category 
import algebra.category.CommRing.basic 
universes v u
open A2
def map_A2 {A B :Type v}[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] : A2 A → A2 B := λ ζ,  begin  
    use { a := f ζ.a, b := f ζ.b},
end 
variables (A B :Type v)[comm_ring A][comm_ring B]
def map_a_b (f : A →  B)[is_ring_hom  f] (ζ : A2 A)  : (map_A2 (f) ζ).a = f ζ.a  ∧ (map_A2 (f) ζ).b = f ζ.b := 
begin 
        split, 
        exact rfl,
        exact rfl,
end
def 𝔸2 : CommRing ⥤ Type v :=  
{ obj := λ R, A2 R,
  map := λ R R' f, map_A2 f, 
--   map_id' := λ R, begin
--      funext,
--      rw category_theory.types_id,
--      ext,
--      exact rfl,
--      exact rfl,
--      end,
}
#print 𝔸2 
#print 𝔸2._proof_2
/--
theorem 𝔸2._proof_2 : ∀ (X : CommRing), map_A2 ⇑(𝟙 X) = 𝟙 (A2 ↥X) :=
λ (X : CommRing),
  id
    (λ (X : CommRing),
       funext
         (λ (x : A2 ↥X),
            id
              (λ (X : CommRing) (x : A2 ↥X),
                 ext (eq.refl (map_A2 ⇑(𝟙 X) x).a) (eq.refl (map_A2 ⇑(𝟙 X) x).b))
              X
              x))
    X
-/





















