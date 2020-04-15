import to_product
open category_theory
open opposite
open category_theory.limits
open category_theory.category
open Product_stuff
universes v u
variables {C : Type u}
variables [𝒞 : category.{v} C]
variables  [has_binary_products.{v} C][has_terminal.{v} C]
include 𝒞

namespace Yoneda
def Yo (R : C)(A :C) := (yoneda.obj A).obj (op R)
def Yo_ (R : C) {A B : C}(φ : A ⟶ B) := ((yoneda.map φ).app (op R) : Yo R A ⟶ Yo R B)
notation R`⟦`:33 A`⟧`:21 := Yo R A  
notation  R`<`:100 φ`>`   := Yo_ R φ

lemma apply_to_composition {R : C}{Z K :C}(f :  R ⟶ Z)(g : Z ⟶ K) : 
     R < g > f = f ≫ g := rfl 
lemma composition_to_apply {R : C}{Z K :C}(f :  R ⟶ Z)(g : Z ⟶ K) : 
   f ≫ g  =   (R < g > f)  := rfl 
lemma id (R : C)(A : C) : R < 𝟙 A > = 𝟙 (R⟦ A⟧ ) := begin 
     funext,
     exact comp_id g,
     -- have T : ((yoneda.map (𝟙 A)).app (op R)) g = (g ≫ (𝟙 A)),
end 


def Yoneda_preserve_product (Y : C)(A B : C) :
     Y ⟦ A ⨯ B ⟧  ≅ Y ⟦ A ⟧  ⨯ Y⟦ B ⟧   := 
{ hom := (Y< π1 > | Y <π2>),
  inv := λ g : (Y ⟶ A) ⨯ (Y ⟶ B),
    ( (π1 : (Y ⟶ A) ⨯ (Y ⟶ B) ⟶ (Y ⟶ A)) g |  (π2 : (Y ⟶ A) ⨯ (Y ⟶ B) ⟶ (Y ⟶ B)) g  ) 
      ,  --- g ≫ π1 
  hom_inv_id' := begin
     funext g,
     rw types_comp_apply,
     apply prod.hom_ext,
     rw prod.lift_fst,
     rw ←  types_comp_apply (Y < π1> | Y < π2>)  π1 g,
     rw prod.lift_fst,
     exact rfl,
     -- rw apply_to_composition,
     -- rw types_id,
     tidy,
  end,
   inv_hom_id' := begin
    apply prod.hom_ext,
    rw assoc, 
    rw prod.lift_fst,funext ζ , 
    rw types_comp_apply,rw apply_to_composition,
    rw prod.lift_fst,
    exact rfl,
    rw assoc,
    rw prod.lift_snd,funext ζ,
     rw types_comp_apply, 
    rw apply_to_composition,
    rw prod.lift_snd,
    exact rfl,
  end
}

-- def Yoneda_preserve_product (Y : C)(A B : C) :
--      Y ⟦ A ⨯ B ⟧  ≅ Y ⟦ A ⟧  ⨯ Y⟦ B ⟧   := 
-- { hom := prod.lift
--     (λ f, f ≫ π1)
--     (λ f, f ≫ π2),
--   inv := λ f : (Y ⟶ A) ⨯ (Y ⟶ B),
--     (prod.lift
--       ((@category_theory.limits.prod.fst _ _ (Y ⟶ A) (Y ⟶ B) _ : ((Y ⟶ A) ⨯ (Y ⟶ B)) → (Y ⟶ A)) f)
--       ((@category_theory.limits.prod.snd _ _ (Y ⟶ A) _ _ : ((Y ⟶ A) ⨯ (Y ⟶ B)) → (Y ⟶ B)) f : Y ⟶ B)),
--   hom_inv_id' := begin
--     ext f,
--     cases j,   --- HERE
--     { simp, refl},
--     { simp, refl}
--   end,
--   inv_hom_id' := begin
--     apply prod.hom_ext,
--     { rw assoc, rw prod.lift_fst, obviously},
--     { rw assoc, rw prod.lift_snd, obviously}
--   end
-- }
--- Here it just sugar 

lemma composition (R : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : 
          R < f ≫ g > =  R< f > ≫ R < g >
 :=  begin 
     funext ζ,
     rw apply_to_composition,
     rw types_comp_apply,
     iterate 2 {rw apply_to_composition},
     exact eq.symm  ( assoc ζ f  g),
 end
def convertion {R : C}{A : C}(g : R⟦ A⟧ ) : R ⟶ A := g 

def Preserve.product_up_to_iso (R : C)(A B : C) : R⟦A ⨯ B⟧  ≅ R⟦A⟧  ⨯ R⟦B⟧ := Yoneda_preserve_product R A B
lemma Preserve.product.hom (R : C)(A B : C) : 
     (Preserve.product_up_to_iso R A B).hom =  (R < π1  > | R < π2 > ) := rfl

lemma Preserve.prod_morphism (R : C)(A B : C)(X :C)(f : X ⟶ A)(g : X ⟶ B) :
      R < (f | g) > ≫ (R < π1  > | R < π2 >) =  (R < f > | R < g >) :=  -- the  ≫  is  :/   
     begin 
          rw prod.left_composition,
          iterate 2 {rw [← composition]},
          rw prod.lift_fst,
          rw prod.lift_snd,
     end

lemma  Preserve.otimes_morphism (R : C){ X Y Z K :C}(f : X ⟶ Y )(g : Z ⟶ K) : 
 (R < π1 > | R < π2 >)  ≫ ( R < f > ⊗ R < g > ) =  R < (f ⊗ g) >  ≫ (R < π1 > |R < π2 >)    :=
  begin 
     rw prod.prod_comp_otimes,
     rw prod.otimes_is_prod,
     rw prod.left_composition,
     rw ← composition,
     rw ← composition,
     slice_rhs 2 3 {
          rw ← composition,
          rw prod.lift_snd,
     },
     slice_rhs 1 1 {
          rw ← composition,
          rw prod.lift_fst,
     },
end
lemma prod_apply {R :C}{A Y Z : C }(ζ : R ⟦ A ⟧)  (f : A ⟶ Y)(g : A ⟶ Y) : 
     ( R< (f | g) >) ζ = (R < f > ζ | R < g > ζ ) := 
          begin
               rw apply_to_composition,
               rw prod.left_composition,
               iterate 2 {rw apply_to_composition},
          end 
lemma otimes_apply {R :C}{A1 A2 Y Z : C }(ζ1 : R ⟦ A1 ⟧)(ζ2 : R⟦ A2 ⟧ )
 (f1 : A1 ⟶ Y)(f2 : A2 ⟶ Z) : 
          R < (f1 ⊗ f2 ) > (ζ1 | ζ2) = ( R < f1 > ζ1 | R < f2 > ζ2 ) :=
 begin
     rw apply_to_composition,
     rw prod.prod_comp_otimes,
     exact rfl,  
 end 
 end Yoneda