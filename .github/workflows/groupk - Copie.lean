import category_theory.limits.limits
import category_theory.limits.shapes
import category_theory.yoneda
import category_theory.opposites
import category_theory.types
import category_theory.limits.types
-- set_option trace.simplify.rewrite true
run_cmd mk_simp_attr `PRODUCT    -----  BOF BOF  
meta def PRODUCT_CAT  : tactic unit :=
`[  try {simp only with PRODUCT}]
run_cmd add_interactive [`PRODUCT_CAT]

universes v u
open category_theory
open category_theory.limits
open category_theory.category
open opposite

namespace Product_stuff
open category_theory.limits
notation f ` ⊗ `:20 g :20     := limits.prod.map f g  ---- 20 comprendre les choses ici 
notation `T`C :20              := (terminal C) 
notation  `T`X : 20            := (terminal.from X)
notation  f ` | `:20 g :20     :=  prod.lift f g
notation  `π1`                 := limits.prod.fst 
notation  `π2`                 := limits.prod.snd


variables (C : Type u)
variables [𝒞 : category.{v} C]
variables  [has_binary_products.{v} C][has_terminal.{v} C]
include 𝒞

example  {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) : ( f | g) ≫ π1 = f  :=  prod.lift_fst  C f g 
/-
     we can type π : A ⨯ B ⟶ B if we need 
-/
example  {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) : ( f | g) ≫ (π2 : A ⨯ B ⟶ B) = g := prod.lift_snd C f g 

example  {A X Y : C} {a b : A ⟶ X ⨯ Y} (h1 : a ≫ π1  = b ≫ π1 ) (h2 : a ≫ π2  = b ≫ π2)  : a = b :=  prod.hom_ext C h1 h2
 


 lemma Identity (A B : C) : ( π1 | π2 ) = 𝟙 (A ⨯ B) := begin
     apply prod.hom_ext,
     rw id_comp,
     rw prod.lift_fst,
     rw id_comp,
     rw prod.lift_snd,
end
/-!
# h ≫ (f | g)  = (h ≫ f | h ≫ g)
!-/ 
lemma prod.left_composition {Z' Z A B : C}(h : Z' ⟶ Z)(f : Z ⟶ A)(g : Z ⟶ B)  : 
               h ≫ (f | g)  = (h ≫ f | h ≫ g) := 
begin
     apply prod.hom_ext,   --- Le right member is of the form ( | )  composition π1 π2 
     slice_lhs 1 3 {
          rw prod.lift_fst,
     },
     rw prod.lift_fst, 
     slice_lhs 2 3 {
          rw prod.lift_snd,
     },
     rw prod.lift_snd,
end
lemma prod.map_fst{X Y Z W : C}(f  : X ⟶ Y)(g  : Z ⟶ W) : 
      (f ⊗ g) ≫ (π1 : Y ⨯ W ⟶ Y) = π1  ≫ f :=  limit.map_π (map_pair f g) walking_pair.left
lemma prod.map_snd{X Y Z W : C}(f  : X ⟶ Y)(g  : Z ⟶ W) :  
(f ⊗ g) ≫ π2 = π2 ≫ g :=   limit.map_π (map_pair f g) walking_pair.right
/-
(f ⊗ g) = ( π1  ≫ f | π2 ≫ g ) 
-/
lemma  prod.otimes_is_prod {X Y Z W : C}(f  : X ⟶ Y)(g  : Z ⟶ W) : 
     (f ⊗ g) = ( π1  ≫ f | π2 ≫ g ) := 
begin
     apply prod.hom_ext,
     rw [prod.map_fst,prod.lift_fst],
     rw [prod.map_snd,prod.lift_snd],
end
/-
(f1 ⊗ g1) = (f2 ⊗ g2) →   π1  ≫ f1 = (π1 : X ⨯ Z ⟶ X)  ≫ f2
-/
lemma prod.map_ext{X Y Z W : C}(f1 f2  : X ⟶ Y)(g1 g2  : Z ⟶ W) :  (f1 ⊗ g1) = (f2 ⊗ g2) → 
     π1  ≫ f1 = (π1 : X ⨯ Z ⟶ X)  ≫ f2 := 
     λ certif, begin 
     rw ← prod.map_fst C( f1)  (g1),
     rw ← prod.map_fst C (f2)  (g2),
     rw certif,
end
lemma prod.map_eq {X Y Z W : C}(f1 f2  : X ⟶ Y)(g1 g2  : Z ⟶ W) :
 ((π1 : X ⨯ Z ⟶ X) ≫ f1 = (π1 : X ⨯ Z ⟶ X)  ≫ f2) →
 ((π2 : X ⨯ Z ⟶ Z) ≫ g1 = (π2 : X ⨯ Z ⟶ Z)  ≫ g2) → ((f1 ⊗ g1) = (f2 ⊗ g2)) :=
  λ certif1 certif2, begin
     iterate 2 {rw prod.otimes_is_prod},
--     PRODUCT_CAT,
    rw certif1, rw certif2,
end
/-
(f1 | f2) ≫ (g1 ⊗ g2)  = (f1 ≫ g1 | f2 ≫ g2 )
-/
lemma prod.prod_comp_otimes {A1 A2 X1 X2 Z: C} (f1 :  Z ⟶ A1)(f2  : Z ⟶ A2) 
(g1 :A1  ⟶  X1 )(g2 : A2 ⟶ X2) :
     (f1 | f2) ≫ (g1 ⊗ g2)  = (f1 ≫ g1 | f2 ≫ g2 ) := begin 

     apply prod.hom_ext,
     rw prod.otimes_is_prod,
     iterate 1 {rw prod.lift_fst},
     slice_lhs 2  3{
          rw prod.lift_fst,
     },
     slice_lhs 1 2 {
          rw prod.lift_fst,
     },
     tidy,
     end
end Product_stuff