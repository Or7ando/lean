import to_product
import sugar_yoneda
import category_theory.limits.limits
import category_theory.limits.shapes
universes v u   
open Product_stuff
open Yoneda 
/-
The goal is define group obj in a category.
          reference : Douady : Algebre et théories galoisiennes page 45
          exemple : in the category of presheaf.
          in Ring ? Idem ?
     contexte : 𝒞 a un objet final et a les produit finis !
Pour coder μ X × X ⟶ X  We see that has X ⟶ T cospan f f)

-/
-- notation         f ` ⊗ `:20 g :20 := category_theory.limits.prod.map f g
-- notation         `T`C :20 := (terminal C)
-- notation         `T`X : 20 := (terminal.from X)
-- notation         f ` | `:20 g :20 :=  prod.lift f g
/-!
#     notations : 
#         T C       :  C           (objet terminal) 
#         (f | g)   :  Z ⟶ X ⨯ Y  
#         T X       :  X ⟶ T C
#         (f ⊗ g)  :  Z1 ⨯ Z2 ⟶ X1 ⨯ X2 
!-/

structure group_obj (C : Type u)[ 𝒞 : category.{v} C ] [ (has_binary_products.{v} C) ] [ (has_terminal.{v} C) ] :=
(X : C)
(μ : X ⨯ X ⟶ X)
(inv : X ⟶ X)
(ε :  T C ⟶ X)
(hyp_one_mul  :  (T X | 𝟙 X) ≫ (ε ⊗ 𝟙 X) ≫  μ  = 𝟙 X)
(hyp_mul_one  :  (𝟙 X | T X) ≫ ( 𝟙 X ⊗ ε) ≫ μ  = 𝟙 X)
(hyp_inv_mul  :  (inv | 𝟙 X) ≫  μ = (T X) ≫ ε )
(hyp_assoc    :  (μ ⊗ 𝟙 X) ≫ (μ) = (prod.associator X X X).hom ≫ (𝟙 X ⊗ μ)  ≫ μ )   -- (a *b) * c = (a * (b * c))

variables (C : Type u)
variables [𝒞 : category.{v} C]
variables  [has_binary_products.{v} C][has_terminal.{v} C]
include 𝒞
instance coee : has_coe (group_obj C) C := ⟨λ F, F.X⟩
variables (G : group_obj C)
include G
-- we start by rewriting a little 
lemma mul_one' : (𝟙 G.X | T G.X) ≫ ( 𝟙 G.X ⊗ G.ε) ≫ G.μ  = (𝟙 G.X  | (T G.X) ≫ G.ε) ≫ G.μ :=
begin
     rw ← assoc,
     rw prod.prod_comp_otimes,
     rw comp_id,
end
lemma one_mul' : (T G.X | 𝟙 G.X) ≫ (G.ε ⊗ 𝟙 G.X) ≫  G.μ  = ((T G.X) ≫ G.ε | 𝟙 G.X) ≫ G.μ := 
begin 
     rw ← assoc,
     rw prod.prod_comp_otimes,
     rw comp_id,
end 
lemma one_mul_R (R A : C) (ζ : R⟦G.X⟧ ): R < ((T G.X) ≫ G.ε | 𝟙 G.X) ≫ G.μ > ζ  =  ζ := begin 
     rw ← one_mul',rw G.hyp_one_mul,rw yoneda_sugar.id,exact rfl,
end
lemma mul_one_R (R A : C) (ζ : R⟦G.X⟧ ): R < ( 𝟙 G.X | (T G.X) ≫ G.ε ) ≫ G.μ > ζ  =  ζ := 
begin
     rw ← mul_one', rw G.hyp_mul_one,rw yoneda_sugar.id,exact rfl, 
 end
def one   (R : C) : R ⟦(G.X) ⟧  :=  
begin                                   ---- ici l'unité est R<ε> (T G.X) l'image du terminal 
     exact (terminal.from R ≫ G.ε),
end
def mul (R : C) : R⟦ G.X⟧   → R⟦ G.X⟧  → R ⟦ G.X ⟧  :=  λ g1 g2, 
begin 
     let φ := ( g1 | g2),
     let β := (R< (G.μ) > : R⟦ G.X ⨯ G.X⟧  ⟶ R⟦G.X⟧),
     exact β φ,
end
variables (R : C)
include R
instance yoneda_mul : has_mul (R⟦ G.X⟧) := ⟨mul C G R ⟩ 
instance yoneda_one : has_one (R⟦ G.X⟧) := ⟨one C G R ⟩
@[PRODUCT]lemma mul_comp (a b : R ⟦ G.X⟧ ) : a * b = (R < G.μ >) (a | b) := rfl -- priority R < g.μ > (a | b) not ()
@[PRODUCT]lemma one_comp :  (1 : R ⟦ G.X ⟧) = terminal.from R ≫ G.ε := rfl

@[PRODUCT]lemma yoneda_sugar.apply_comp (G : group_obj C){R : C}{Z K :C}(f :  R ⟶ Z)(g : Z ⟶ K) : 
     R < g > (f) = f ≫ g := rfl


lemma yoneda_sugar_right_apply {R :C}{A Y Z : C }(ζ : R ⟦ A ⟧)  (f : A ⟶ Y)(g : A ⟶ Y) : 
     ( R< (f | g) >) ζ = (R < f > ζ | R < g > ζ ) := 
          begin 
               rw yoneda_sugar.apply_comp C G,
               rw prod.left_composition,
               iterate 2 {rw yoneda_sugar.apply_comp  C G },
          end 
lemma yoneda_sugar_otimes_apply {R :C}{A1 A2 Y Z : C }(ζ1 : R ⟦ A1 ⟧)(ζ2 : R⟦ A2 ⟧ )
 (f1 : A1 ⟶ Y)(f2 : A2 ⟶ Z) : 
  R < (f1 ⊗ f2 ) > (ζ1 | ζ2) = ( R < f1 > ζ1 | R < f2 > ζ2  ) :=
 begin
     rw yoneda_sugar.apply_comp C G,
     rw prod.prod_comp_otimes,exact rfl,  
 end 
notation Y `⟶•`  := T Y 
@[PRODUCT]lemma Terminal_comp{Y : C} ( a : R ⟶ Y) : a ≫ (Y ⟶•) = (R ⟶•) := 
by exact subsingleton.elim (a ≫ T Y) (T R)
@[PRODUCT]lemma lemmeF (a : R⟦ G.X ⟧) :

   (R < ( (T G.X) ≫ G.ε | 𝟙 G.X)> ) a =  ((T R) ≫ G.ε | a)  := 
begin
     rw yoneda_sugar_right_apply C  G,
     rw yoneda_sugar.apply_comp,rw ← assoc,
     rw Terminal_comp,rw yoneda_sugar.id,exact rfl,
     use G, use G, use R,
     -- rw ← Maxi_triviality,
     -- rw types_comp,
     -- tidy, rw Maxi_triviality,rw Yoneda_Maxi,rw Yoneda_Maxi,rw prod.left_composition,
     -- rw comp_id,rw ← assoc, rw Terminal_comp,exact rfl,iterate 3 {assumption},
end

@[PRODUCT]def one_mulf' (ζ  : R⟦G.X ⟧) :    1 * ζ  = ζ  := begin
     rw mul_comp,rw one_comp, --- (T X | 𝟙 X) ≫ (ε ⊗ 𝟙 X) ≫  μ  = 𝟙 X)
     let V := one_mul_R C G R R ζ,
     let r := R <G.μ>,
     rw [yoneda_sugar.apply_comp,← assoc,prod.left_composition,comp_id,
     ← assoc,Terminal_comp,← yoneda_sugar.apply_comp] at V, 
     exact V,
     use G, use G, use G,
end
@[PRODUCT]def mul_onef'(ζ : R⟦G.X ⟧)  : ζ * 1 = ζ := begin 
     rw mul_comp,rw one_comp,
     have V := mul_one_R C G R R ζ,
     rw [yoneda_sugar.apply_comp,← assoc,prod.left_composition,comp_id,← assoc,Terminal_comp,← yoneda_sugar.apply_comp] at V,
     exact V,
     use G, use G ,use G,
end 
@[PRODUCT]def inv' (R :C) : R⟦ G.X⟧ → R⟦ G.X⟧   := λ  ζ, begin 
     exact R<G.inv> ζ, 
end
instance yoneda_inv (R :C) : has_inv (R⟦G.X⟧) := ⟨inv' C G R⟩
@[PRODUCT]lemma  inv_comp (ζ : R ⟦ G.X⟧ ) : ζ⁻¹  =  (R<G.inv>) ζ  := rfl
@[PRODUCT]lemma mul_left_inv' (ζ : R ⟦ G.X ⟧) : (ζ⁻¹ * ζ ) = 1 :=  begin 
     rw inv_comp,rw mul_comp,rw one_comp, rw yoneda_sugar.apply_comp,
     have V : R< (G.inv | 𝟙 G.X )   ≫  G.μ> ζ = (R<(T G.X) ≫ G.ε>) ζ ,
          rw G.hyp_inv_mul,
     rw [yoneda_sugar.apply_comp,yoneda_sugar.apply_comp,← assoc,
     prod.left_composition,comp_id,← assoc,Terminal_comp,← yoneda_sugar.apply_comp C G ζ G.inv] at V,
     assumption, use G, use G, use G, use G,
end
lemma Grall (a b c : R ⟦G.X ⟧) : R < (prod.associator G.X G.X G.X).hom ≫ (𝟙 G.X ⊗ G.μ) ≫ G.μ> (a | b | c) 
     =(R < G.μ>) (a | (R < G.μ> (b | c))) := begin 
     tidy,
     rw [yoneda_sugar.apply_comp, ← assoc,prod.left_composition,
     ← assoc,prod.prod_comp_otimes,yoneda_sugar.apply_comp,yoneda_sugar.apply_comp],
     iterate 3 {swap,use G},
     rw comp_id,tidy,PRODUCT_CAT,
     rw [← assoc,prod.left_composition,prod.lift_snd (a | b) c, ← assoc, prod.lift_fst,prod.lift_snd],
end 
-- (hyp_mul_inv  :  (inv | 𝟙 X ) ≫  μ = (T X) ≫ ε )
lemma mul_assoc' (a b c : R ⟦G.X ⟧) : a * b *c = a * ( b * c ) := begin 
     iterate 4 { rw mul_comp}, PRODUCT_CAT,
     have ASSOC : R<((G.μ ⊗ (𝟙 G.X)) ≫ (G.μ)) >(a | b | c) = (R<(prod.associator G.X G.X G.X).hom ≫ (𝟙 G.X ⊗ G.μ)  ≫ G.μ>) (a | b | c),
          rw G.hyp_assoc,
     rw [yoneda_sugar.apply_comp,← assoc,prod.prod_comp_otimes,comp_id,
     ← yoneda_sugar.apply_comp, ← yoneda_sugar.apply_comp] at ASSOC,
     iterate 3 {swap,use G},
     have G_hyp : R < (prod.associator G.X G.X G.X).hom ≫ (𝟙 G.X ⊗ G.μ) ≫ G.μ> (a | b | c) 
     =(R < G.μ>) (a | (R < G.μ> (b | c))),
          exact Grall C G R a b c ,
       rw G_hyp at ASSOC,assumption,
     -- R<(prod.associator G.X G.X G.X).hom ≫ (𝟙 G.X ⊗ G.μ)  ≫ G.μ> (a | b | c),

end

instance : group (R⟦G.X⟧) :=  
{    
     mul := has_mul.mul,
     mul_assoc := mul_assoc' C G R,
     one    := (1 : R⟦ G.X⟧),
     mul_one := mul_onef' C G R,
     one_mul := one_mulf' C G R,
     inv  := inv' C G R,
     mul_left_inv := mul_left_inv' C G R,
} 

