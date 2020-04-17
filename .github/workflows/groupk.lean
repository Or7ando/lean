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
namespace lem --------------------------------------------------------------------
variables {C : Type u}
variables [𝒞 : category.{v} C]
variables  [has_binary_products.{v} C][has_terminal.{v} C]
include 𝒞
attribute [PRODUCT] category.assoc category.id_comp category.comp_id 
@[PRODUCT] lemma prod_left_def {X Y : C} : limit.π (pair X Y) walking_pair.left = limits.prod.fst := rfl
@[PRODUCT] lemma prod_right_def {X Y : C} : limit.π (pair X Y) walking_pair.right = limits.prod.snd := rfl
lemma prod.hom_ext {A X Y : C} {a b : A ⟶ X ⨯ Y} (h1 : a ≫ limits.prod.fst = b ≫ limits.prod.fst) (h2 : a ≫ limits.prod.snd = b ≫ limits.prod.snd) : a = b :=
begin
  apply limit.hom_ext,
  rintros (_ | _),
  rw prod_left_def,
  exact h1,  
  rw prod_right_def,
  exact h2,
end
@[PRODUCT, reassoc] lemma lem.prod.lift_fst {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) : prod.lift f g ≫ category_theory.limits.prod.fst = f :=
limit.lift_π (binary_fan.mk f g) _

attribute [PRODUCT] lem.prod.lift_fst_assoc

@[PRODUCT,reassoc]lemma lem.prod.lift_snd {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) : prod.lift f g ≫ category_theory.limits.prod.snd = g :=
limit.lift_π (binary_fan.mk f g) _
attribute [PRODUCT] lem.prod.lift_snd_assoc
end lem
namespace Product_stuff
notation f ` ⊗ `:20 g :20 := category_theory.limits.prod.map f g  ---- 20 
notation  `T`C :20 := (terminal C) 
notation   `T`X : 20 := (terminal.from X)
notation f ` | `:20 g :20 :=  prod.lift f g
notation `π1` := limits.prod.fst 
notation `π2` := limits.prod.snd


variables {C : Type u}
variables [𝒞 : category.{v} C]
variables [has_binary_products.{v} C][has_terminal.{v} C]
include 𝒞
variables (X :C)
open lem           -------------------------------------------------------
/-
     π notation for projection 
-/
example  {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) : ( f | g) ≫ π1 = f  :=   lem.prod.lift_fst f g 
/-
     we can type π : A ⨯ B ⟶ B if we need 
-/
example  {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) : ( f | g) ≫ (π2 : A ⨯ B ⟶ B) = g := lem.prod.lift_snd f g 

example  {A X Y : C} {a b : A ⟶ X ⨯ Y} (h1 : a ≫ π1  = b ≫ π1 ) (h2 : a ≫ π2  = b ≫ π2)  : a = b :=  prod.hom_ext h1 h2

-- use the tatict 
example  {Y A B : C} (f : Y ⟶ A) (g : Y ⟶ B) : ( f | g) ≫ (π2 : A ⨯ B ⟶ B) = g := by PRODUCT_CAT

@[PRODUCT]lemma prod.left_composition{Z' Z A B : C}(h : Z' ⟶ Z)(f : Z ⟶ A)(g : Z ⟶ B)  : 
               h ≫ (f | g)  = (h ≫ f | h ≫ g) := 
begin
     apply lem.prod.hom_ext,   --- Le right member is of the form ( | )  composition π1 π2 
     -- PRODUCT_CAT,  PRODUCT_CAT,  --- here assoc 
     rw assoc,
     rw lem.prod.lift_fst,
     rw lem.prod.lift_fst,
     rw lem.prod.lift_snd,
     rw assoc,
     rw lem.prod.lift_snd,
end
-- #print notation
@[PRODUCT,reassoc]lemma prod.map_first{X Y Z W : C}(f  : X ⟶ Y)(g  : Z ⟶ W) :  (f ⊗ g) ≫ (π1 : Y ⨯ W ⟶ Y) = π1  ≫ f :=  begin 
     exact limit.map_π (map_pair f g) walking_pair.left,
end
attribute [PRODUCT] prod.map_first_assoc
@[PRODUCT,reassoc]lemma prod.map_second{X Y Z W : C}(f  : X ⟶ Y)(g  : Z ⟶ W) :  (f ⊗ g) ≫ π2 = π2 ≫ g :=  begin 
     exact limit.map_π (map_pair f g) walking_pair.right,
end
attribute [PRODUCT] prod.map_second_assoc
@[PRODUCT]lemma  prod.otimes_is_prod {X Y Z W : C}(f  : X ⟶ Y)(g  : Z ⟶ W) : (f ⊗ g) = ( π1  ≫ f | π2 ≫ g ) := begin
     apply prod.hom_ext,
     PRODUCT_CAT, PRODUCT_CAT,
     -- rw lem.prod.lift_fst,
     -- rw prod.map_first,
     -- rw lem.prod.lift_snd,
     -- rw prod.map_second,
end
-- notation π1`(`X `x` Y`)` := (limits.prod.fst : X⨯Y ⟶ X)
@[PRODUCT]lemma prod.map_ext{X Y Z W : C}(f1 f2  : X ⟶ Y)(g1 g2  : Z ⟶ W) :  (f1 ⊗ g1) = (f2 ⊗ g2) → 
(π1 : X ⨯ Z ⟶ X) ≫ f1 = (π1 : X ⨯ Z ⟶ X)  ≫ f2 := λ certif, begin 
     iterate 2 {rw prod.otimes_is_prod at certif},
     rw ← prod.map_first ( f1)  (g1),
     rw ← prod.map_first ( f2)  (g2),
     iterate 2 {rw prod.otimes_is_prod},
     rw certif,
end
lemma prod.map_eq {X Y Z W : C}(f1 f2  : X ⟶ Y)(g1 g2  : Z ⟶ W) :
 ((π1 : X ⨯ Z ⟶ X) ≫ f1 = (π1 : X ⨯ Z ⟶ X)  ≫ f2) →
 ((π2 : X ⨯ Z ⟶ Z) ≫ g1 = (π2 : X ⨯ Z ⟶ Z)  ≫ g2) → ((f1 ⊗ g1) = (f2 ⊗ g2)) := λ certif1 certif2, begin
     iterate 2 {rw prod.otimes_is_prod},
--     PRODUCT_CAT,
    rw certif1, rw certif2,
end



@[PRODUCT,reassoc]lemma prod.prod_otimes {X Y Z : C} (f :  Y ⟶ X) (g : X ⟶ Z ) : 
     (f | 𝟙 Y) ≫ (g ⊗ (𝟙 Y)) = (f ≫ g | 𝟙 Y) := 
     
begin 
     apply prod.hom_ext,
     PRODUCT_CAT,PRODUCT_CAT,     ---------------------- PROBLEME With the tatict HEEEEEEERRRRRRE 
     -- rw [lem.prod.lift_fst],
     -- rw  assoc, 
     -- rw prod.map_first,
     -- rw ← assoc,               ----- ← assoc here  Problem ? 
     -- rw lem.prod.lift_fst,          
     -- tidy, -- super - power tidy 
end
attribute [PRODUCT] prod.prod_otimes_assoc

@[PRODUCT,reassoc] lemma prod.prod_comp_otimes {A1 A2 X1 X2 Z: C} (f1 :  Z ⟶ A1)(f2  : Z ⟶ A2) 
(g1 :A1  ⟶  X1 )(g2 : A2 ⟶ X2) :
     (f1 | f2) ≫ (g1 ⊗ g2)  = (f1 ≫ g1 | f2 ≫ g2 ) := begin 
     apply prod.hom_ext,
     PRODUCT_CAT,PRODUCT_CAT,
     end
attribute [PRODUCT] prod.prod_comp_otimes_assoc

def Yo (R : C)(A :C) := (yoneda.obj A).obj (op R)
def Yo_ (R : C) {A B : C}(φ : A ⟶ B) := ((yoneda.map φ).app (op R) : Yo R A ⟶ Yo R B)
-- Good notation for yoneda stuff : 
-- We fix V : C and we denote by    
-- R[X] := yoneda.obj X).obj (op R) and φ : A  ⟶ B (in C) R ⟦  φ ⟧   : R⟦ A⟧  → R⟦ B⟧  in type v 
notation R`⟦`A`⟧`:20 := Yo R A  -- notation ?? 
notation R`<`φ`>`:20   := Yo_ R φ  -- 
def Yoneda_preserve_product (Y : C)(A B : C) :
     Y ⟦ A ⨯ B ⟧  ≅ Y ⟦ A ⟧  ⨯ Y⟦ B ⟧   := 
{ hom := prod.lift
    (λ f, f ≫ π1)
    (λ f, f ≫ π2),
  inv := λ f : (Y ⟶ A) ⨯ (Y ⟶ B),
    (prod.lift
      ((@category_theory.limits.prod.fst _ _ (Y ⟶ A) (Y ⟶ B) _ : ((Y ⟶ A) ⨯ (Y ⟶ B)) → (Y ⟶ A)) f)
      ((@category_theory.limits.prod.snd _ _ (Y ⟶ A) _ _ : ((Y ⟶ A) ⨯ (Y ⟶ B)) → (Y ⟶ B)) f : Y ⟶ B)),
  hom_inv_id' := begin
    ext f,
    cases j,
    { simp, refl},
    { simp, refl}
  end,
  inv_hom_id' := begin
    apply lem.prod.hom_ext,
    { rw assoc, rw lem.lem.prod.lift_fst, obviously},
    { rw assoc, rw lem.lem.prod.lift_snd, obviously}
  end
}
--- Here it just sugar 
@[PRODUCT]lemma yoneda_sugar.composition (R : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : R < f ≫ g > =( R< f >) ≫ (R < g >) 
 :=  begin 
     unfold Yo_, 
     simp,
 end
def yoneda_sugar.conv {R : C}{A : C}(g : R⟦ A⟧ ) : R ⟶ A := g 
def yoneda_sugar.prod (R : C)(A B : C) : R⟦ A ⨯ B⟧  ≅ R⟦ A⟧  ⨯ R⟦ B⟧ := begin 
     exact Yoneda_preserve_product R A B,
end
@[PRODUCT]lemma yoneda_sugar.prod.hom (R : C)(A B : C) : 
     (yoneda_sugar.prod R A B).hom =  (R < (π1  : A ⨯ B ⟶ A) > | R < (π2  : A ⨯ B ⟶ B)> ) := rfl

@[PRODUCT]lemma yoneda_sugar.prod.first (R : C)(A B : C) :
 (yoneda_sugar.prod R A B).hom ≫ π1 = (R < π1 >) := 
 begin
     exact rfl,
 end
 @[PRODUCT]lemma yoneda_sugar.prod.hom_inv (R : C)(A B : C) : 
     (yoneda_sugar.prod R A B).hom ≫ (yoneda_sugar.prod R A B).inv = 𝟙 (R⟦ A ⨯ B⟧) := 
     (Yoneda_preserve_product R A B).hom_inv_id'
 @[PRODUCT]lemma yoneda_sugar.prod.inv_hom (R : C)(A B : C) : 
     (yoneda_sugar.prod R A B).inv ≫ (yoneda_sugar.prod R A B).hom = 𝟙 (R⟦ A⟧  ⨯ R⟦ B⟧) := 
     (Yoneda_preserve_product R A B).inv_hom_id'
 @[PRODUCT]lemma yoneda_sugar.prod.second (R : C)(A B : C) : 
  (yoneda_sugar.prod R A B).hom ≫ limits.prod.snd = (R < limits.prod.snd >) := rfl

@[PRODUCT]lemma yoneda_sugar.id (R : C)(A : C) : R < 𝟙 A > = 𝟙 (R⟦ A⟧ ) := begin 
     funext,
     exact comp_id C g,
     -- have T : ((yoneda.map (𝟙 A)).app (op R)) g = (g ≫ (𝟙 A)),
end 



lemma yoneda_sugar_prod (R : C)(A B : C)(X :C)(f : X ⟶ A)(g : X ⟶ B) :
      R < (f | g) > ≫ (yoneda_sugar.prod R A B).hom  =  (R < f > | R < g > ) :=  -- the  ≫  is  :/   
     begin 
          PRODUCT_CAT,
          -- rw  yoneda_sugar.prod.hom R A B,
          -- rw prod.left_composition,
          iterate 2 {rw ← yoneda_sugar.composition},   -- rw ← is the problem ? 
          rw lem.lem.prod.lift_fst,
          rw lem.lem.prod.lift_snd,
     end




@[PRODUCT]lemma yoneda_sugar_prod_inv (R : C)(A B : C)(X :C)(f : X ⟶ A)(g : X ⟶ B) : 
     R < (f | g) >   =  (R < f > | R < g > ) ≫ (yoneda_sugar.prod R A B).inv :=
     begin 
          PRODUCT_CAT,  -- noting
          rw ← yoneda_sugar_prod,
          rw assoc,
          rw yoneda_sugar.prod.hom_inv,
          exact rfl,
     end 



lemma  yoneda_sugar.otimes (R : C){Y Z K :C}(f : X ⟶ Y )(g : Z ⟶ K) : 
 ( R < (f ⊗ g) > ) = (yoneda_sugar.prod  _ _ _).hom ≫ ((R<f>) ⊗ R<g>) ≫ (yoneda_sugar.prod _ _ _ ).inv := begin 
     PRODUCT_CAT,
     -- iterate 2 {rw prod.otimes_is_prod},
     -- rw  yoneda_sugar.prod.hom,
     -- iterate 1 {rw yoneda_sugar_prod_inv},
     rw ← assoc,
     rw prod.left_composition,
     rw ← assoc,
     rw lem.prod.lift_fst,
     rw ← assoc,
     rw lem.prod.lift_snd,
     -- rw yoneda_sugar.composition,
     -- rw yoneda_sugar.composition,
end

@[PRODUCT]lemma yonega_sugar.one_otimes (R :C)(X Y Z: C) (f : X ⟶ Y) : 
 (((yoneda_sugar.prod R Z X).inv) ≫ (R <(𝟙 Z ⊗ f ) > ) ≫ (yoneda_sugar.prod R Z Y).hom) = (𝟙 (R⟦Z⟧) ⊗ R<f >) := begin
     rw yoneda_sugar.otimes,
     iterate 3 {rw ← assoc},
     rw yoneda_sugar.prod.inv_hom,
     rw id_comp,
     rw assoc,
     rw yoneda_sugar.prod.inv_hom,
     rw ← yoneda_sugar.id,
     simp, 
 end
lemma yonega_sugar.one_otimes' (R :C)(X Y Z: C) (f : X ⟶ Y) : 
 ( (R <(𝟙 Z ⊗ f ) > ) ≫ (yoneda_sugar.prod R Z Y).hom) = ((yoneda_sugar.prod R Z X).hom) ≫ (𝟙 (R⟦Z⟧) ⊗ R < f >) := begin
     iterate 2{ rw yoneda_sugar.prod.hom},
     rw prod.left_composition,
     iterate 2{ rw ← yoneda_sugar.composition},
     rw prod.map_first,
     rw prod.map_second,
     rw comp_id,
     rw prod.otimes_is_prod,rw prod.left_composition,rw ← assoc, 
     rw lem.prod.lift_fst,rw ←  assoc,rw lem.prod.lift_snd,rw comp_id,
     rw yoneda_sugar.composition,
 end


-- def Y (R : C)(A :C) := (yoneda.obj A).obj (op R)
-- def Y_ (R : C) {A B : C}(φ : A ⟶ B) := ((yoneda.map φ).app (op R) : Y R A ⟶ Y R B)
-- -- Good notation for yoneda stuff : 
-- -- We fix V : C and we denote by    
-- -- R[X] := yoneda.obj X).obj (op R) and φ : A  ⟶ B (in C) R ⟦  φ ⟧   : R[A] → R[B]  in type v 
-- notation R`[`A`]`:20 := Y R A  -- notation ?? 
-- notation R`<`φ`>`:20   := Y_ R φ  -- 
-- def Yoneda_preserve_product (Y : C)(A B : C) :
--      Y[A ⨯ B] ≅ (Y[A]) ⨯ (Y[B]) :=
-- { hom := prod.lift
--     (λ f, f ≫ π1)
--     (λ f, f ≫ π2),
--   inv := λ f : (Y ⟶ A) ⨯ (Y ⟶ B),
--     (prod.lift
--       ((@category_theory.limits.prod.fst _ _ (Y ⟶ A) (Y ⟶ B) _ : ((Y ⟶ A) ⨯ (Y ⟶ B)) → (Y ⟶ A)) f)
--       ((@category_theory.limits.prod.snd _ _ (Y ⟶ A) _ _ : ((Y ⟶ A) ⨯ (Y ⟶ B)) → (Y ⟶ B)) f : Y ⟶ B)),
--   hom_inv_id' := begin
--     ext f,
--     cases j,
--     { simp, refl},
--     { simp, refl}
--   end,
--   inv_hom_id' := begin
--     apply lem.prod.hom_ext,
--     { rw assoc, rw lem.lem.prod.lift_fst, obviously},
--     { rw assoc, rw lem.lem.prod.lift_snd, obviously}
--   end
-- }

-- --- Here it just sugar 
-- @[PRODUCT,reassoc]lemma yoneda_sugar.composition (R : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : R < f ≫ g > =( R< f >) ≫ (R < g >) 
--  :=  begin 
--      unfold Y_, 
--      simp,
--  end
--  attribute [PRODUCT] yoneda_sugar.composition_assoc
--  @[PRODUCT,reassoc]lemma yoneda_sugar.composition_rev (R : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : 
--  ( R< f >) ≫ (R < g >) =  (R < f ≫ g > ) 
--  :=  begin 
--      unfold Y_, 
--      simp,
--  end
--  attribute [PRODUCT] yoneda_sugar.composition_rev_assoc
-- def yoneda_sugar.conv {R : C}{A : C}(g : R[A]) : R ⟶ A := g 
-- def yoneda_sugar.prod (R : C)(A B : C) : R[A ⨯ B] ≅ R[A] ⨯ R[B] := begin 
--      exact Yoneda_preserve_product R A B,
-- end
-- @[PRODUCT]lemma yoneda_sugar.prod.hom (R : C)(A B : C) : 
--      (yoneda_sugar.prod R A B).hom =  (R < (π1 : A ⨯ B ⟶ A) > | R < (π2 : A ⨯ B ⟶ B)> ) := rfl

-- @[PRODUCT,reassoc]lemma yoneda_sugar.prod.first (R : C)(A B : C) :
--  (yoneda_sugar.prod R A B).hom ≫ π1  = (R < π1 >) := 
--  begin
--      exact rfl,
--  end
--  attribute [PRODUCT] yoneda_sugar.prod.first_assoc
--  @[PRODUCT,reassoc]lemma yoneda_sugar.prod.hom_inv (R : C)(A B : C) : 
--      (yoneda_sugar.prod R A B).hom ≫ (yoneda_sugar.prod R A B).inv = 𝟙 (R[ A ⨯ B]) := 
--      (Yoneda_preserve_product R A B).hom_inv_id'
--  attribute [PRODUCT] yoneda_sugar.prod.hom_inv_assoc
--  @[PRODUCT,reassoc]lemma yoneda_sugar.prod.inv_hom (R : C)(A B : C) : 
--      (yoneda_sugar.prod R A B).inv ≫ (yoneda_sugar.prod R A B).hom = 𝟙 ( R [A]  ⨯ R[B]) := 
--      (Yoneda_preserve_product R A B).inv_hom_id'
--       attribute [PRODUCT] yoneda_sugar.prod.inv_hom_assoc
--  @[PRODUCT,reassoc]lemma yoneda_sugar.prod.second (R : C)(A B : C) : 
--   (yoneda_sugar.prod R A B).hom ≫ π2 = (R < (π2 : A ⨯ B ⟶ B) >) := rfl
-- attribute [PRODUCT] yoneda_sugar.prod.second_assoc
-- @[PRODUCT]lemma yoneda_sugar.id (R : C)(A : C) : R < 𝟙 A > = 𝟙 ( R [A] ) := begin 
--      funext,
--      exact comp_id C g,
--      -- have T : ((yoneda.map (𝟙 A)).app (op R)) g = (g ≫ (𝟙 A)),  
-- end 
-- @[PRODUCT,reassoc,refl]lemma yoneda_sugar_prod (R : C)(A B : C)(X :C)(f : X ⟶ A)(g : X ⟶ B) :
--       R < (f | g) > ≫ (yoneda_sugar.prod R A B).hom  =  (R < f > | R < g > ) :=  -- the  ≫  is  :/   
--      begin 
--            PRODUCT_CAT,
--           -- rw  yoneda_sugar.prod.hom R A B,
--           -- rw prod.left_composition,
--           -- iterate 2 {rw ← yoneda_sugar.composition},   -- rw ← is the problem ? 
--           -- PRODUCT_CAT,
--           -- rw lem.lem.prod.lift_fst,
--           -- rw lem.lem.prod.lift_snd,  
--      end
-- attribute [PRODUCT] yoneda_sugar_prod_assoc
-- @[PRODUCT]lemma yoneda_sugar_prod_inv (R : C)(A B : C)(X :C)(f : X ⟶ A)(g : X ⟶ B) : 
--      R < (f | g) >   =  (R < f > | R < g > ) ≫ (yoneda_sugar.prod R A B).inv :=
--      begin 
--           PRODUCT_CAT,  -- noting   HERE PROBLEM the tatic do nothing 
--           rw ← yoneda_sugar_prod,
--           rw assoc,
--           rw yoneda_sugar.prod.hom_inv,
--           exact rfl,
--      end 
-- @[PRODUCT]lemma  yoneda_sugar.otimes (R : C){Y Z K :C}(f : X ⟶ Y )(g : Z ⟶ K) : 
--  ( R < (f ⊗ g) > ) = (yoneda_sugar.prod  _ _ _).hom ≫ ((R<f>) ⊗ R<g>) ≫ (yoneda_sugar.prod _ _ _ ).inv := begin 
--      -- PRODUCT_CAT,
--      iterate 2 {rw prod.otimes_is_prod},
--      rw  yoneda_sugar.prod.hom,
--      iterate 1 {rw yoneda_sugar_prod_inv},
--      rw ← assoc,
--      rw prod.left_composition,
--      rw ← assoc,
--      rw lem.prod.lift_fst,
--      rw ← assoc,
--      rw lem.prod.lift_snd,
--      rw yoneda_sugar.composition,
--      rw yoneda_sugar.composition,
--      exact rfl,
-- end
-- @[PRODUCT]lemma yonega_sugar.one_otimes (R :C)(X Y Z: C) (f : X ⟶ Y) : 
--  (((yoneda_sugar.prod R Z X).inv) ≫ (R <(𝟙 Z ⊗ f ) > ) ≫ (yoneda_sugar.prod R Z Y).hom) = (𝟙 (R[Z]) ⊗ R < f >) := begin
--      rw yoneda_sugar.otimes,
--      iterate 3 {rw ← assoc},
--      rw yoneda_sugar.prod.inv_hom,
--      rw id_comp,
--      rw assoc,
--      rw yoneda_sugar.prod.inv_hom,  
--      rw ← yoneda_sugar.id,
--      simp, 
--  end
-- lemma yonega_sugar.one_otimes' (R :C)(X Y Z: C) (f : X ⟶ Y) : 
--  ( (R <(𝟙 Z ⊗ f ) > ) ≫ (yoneda_sugar.prod R Z Y).hom) = ((yoneda_sugar.prod R Z X).hom) ≫ (𝟙 (R[Z]) ⊗ R < f >) := begin
--      iterate 2{ rw yoneda_sugar.prod.hom},
--      rw prod.left_composition,
--      iterate 2{ rw ← yoneda_sugar.composition},
--      rw prod.map_first,
--      rw prod.map_second,
--      rw comp_id,
--      rw prod.otimes_is_prod,rw prod.left_composition,rw ← assoc, 
--      rw lem.prod.lift_fst,rw ←  assoc,rw lem.prod.lift_snd,rw comp_id,
--      rw yoneda_sugar.composition,
--      exact rfl,
--  end
--  end Product_stuff
 