import  .groupk
open category_theory
open category_theory.limits
open category_theory.category
universes v u
open Product_stuff    
namespace GROUP_OBJ
structure group_obj (C : Type u)[𝒞 : category.{v} C][has_binary_products.{v} C][has_terminal.{v} C] :=
(X : C)
(μ : X ⨯ X ⟶ X)
(inv : X ⟶ X)
(ε :  T C ⟶ X)
(hyp_one_mul  :  (T X | 𝟙 X) ≫ (ε ⊗ 𝟙 X) ≫  μ  = 𝟙 X)
(hyp_mul_one  :  (𝟙 X | T X) ≫ ( 𝟙 X ⊗ ε) ≫ μ  = 𝟙 X)
(hyp_mul_inv  :  (𝟙 X | inv) ≫  μ = (T X) ≫ ε )
(hyp_assoc    :  (μ ⊗ 𝟙 X) ≫ (μ) = (prod.associator X X X).hom ≫ (𝟙 X ⊗ μ)  ≫ μ )   -- (a *b) * c = (a * (b * c))


#print "ger"
structure  Rr (C : Type u)[𝒞 : category.{v} C][has_binary_products.{v} C][has_terminal.{v} C] := 
#print notation
open lem 
#print notation
-- structure group_obj (C : Type u)[𝒞 : category.{v} C][has_binary_products.{v} C][has_terminal.{v} C] :=
-- (X            :  C)
-- (μ            :  X ⨯ X ⟶ X)
-- (inv          :  X ⟶ X) 
-- (ε            :  T C ⟶ X)
-- (hyp_one_mul  :  (T X | 𝟙 X) ≫ (ε ⊗ 𝟙 X) ≫  μ  = 𝟙 X) 
-- (hyp_mul_one  :  (𝟙 X | T X) ≫ ( 𝟙 X ⊗ ε) ≫ μ  = 𝟙 X)
-- (hyp_mul_inv  :  (𝟙 X | inv) ≫  μ = (T X) ≫ ε )   
-- (hyp_assoc    :  (μ ⊗ 𝟙 X) ≫ (μ) = (prod.associator X X X).hom ≫ (𝟙 X ⊗ μ)  ≫ μ )   -- (a *b) * c = (a * (b * c))

-- variables {C : Type u}
-- variables [𝒞 : category.{v} C]
-- variables  [has_binary_products.{v} C][has_terminal.{v} C]
-- include 𝒞 
-- instance coee : has_coe (group_obj C) C := ⟨λ F, F.X⟩ 
-- variables (G : group_obj C)
-- #eval 2+2 
-- /-
-- First Goal : make a instance of group on the point Hom (Y, G)  = G(Y) 
-- -/

-- --  Idea  Fix R : We have (Γ × Γ )(R ) ≃  Γ (R) × Γ (R) : Let g1 g2 ∈ Γ (R)
-- --   we get φ  ∈ (Γ × Γ) R. Next : 
-- --  ε : Γ × Γ  → Γ give  β  : (Γ × Γ) R → Γ R via Yoneda.map  finaly : β φ is ok !  
-- --   
-- --
-- -- 

-- def one   (R : C) : R[G.X] :=  
-- begin 
--      exact (terminal.from R ≫ G.ε),
-- end

-- def mul (R : C) : R[G.X] → R[G.X] → R[G.X] :=  λ g1 g2, 
-- begin 
--      let φ := ( g1 | g2),
--      -- let γ := (prod.mk g1 g2 : (yoneda.obj G.X).obj (op R) × (yoneda.obj G.X).obj (op R)), -- × versus ⨯  
--      -- let θ :=  (Yoneda_preserve_product R G.X G.X ).inv,
--      let β := (R< (G.μ) > : R[G.X ⨯ G.X] ⟶ R[G.X]),
--      exact β φ,
-- end
-- variables (R : C)
-- include R
-- instance yoneda_mul : has_mul (R[(G : C)]) := ⟨mul G R ⟩ 
-- instance yoneda_one : has_one (R[(G :C)]) := ⟨one G R ⟩
-- lemma mul_comp (a b : R [(G : C)] ) : a * b = (R < G.μ >) (a | b) := rfl -- priority R < g.μ > (a | b) not ()
-- lemma one_comp :  (1 : (R[(G : C)])) = terminal.from R ≫ G.ε := rfl
-- #print group 
-- -- group.mul : Π {α : Type u} [c : group α], α → α → α
-- -- group.mul_assoc : ∀ {α : Type u} [c : group α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
-- -- group.one : Π (α : Type u) [c : group α], α
-- -- group.one_mul : ∀ {α : Type u} [c : group α] (a : α), 1 * a = a
-- -- group.mul_one : ∀ {α : Type u} [c : group α] (a : α), a * 1 = a
-- -- group.inv : Π {α : Type u} [c : group α], α → α
-- -- group.mul_left_inv : ∀ {α : Type u} [c : group α] (a : α), a⁻¹ * a = 1
-- -- lemma pre_des (R: C) : (R < T G.X> | 𝟙 (R[G.X])) ≫ (R < G.ε > ⊗ 𝟙 (R[G.X])) =  (( R < T G.X>  ≫ (R < G.ε>)) | 𝟙 (R[G.X])) := 
-- -- begin exact destruction (R < T G.X>) (R < G.ε >), end
-- def one_mul' (a : R[(G : C)]) :  1 * a = a := begin
-- sorry,
--      -- rw mul_comp,rw one_comp,
--      -- --  (hyp_one_mul  :  (T X | 𝟙 X) ≫ (ε ⊗ 𝟙 X) ≫  μ  = 𝟙 X) 
--      -- have V : (R <(T G.X | 𝟙 G.X)>) ≫ (R<(G.ε ⊗ 𝟙 G.X)>) ≫  (R<G.μ>)  = (R<𝟙 G.X>),
--      --      rw ← yoneda_sugar.composition,rw ← yoneda_sugar.composition,
--      --      rw G.hyp_one_mul,
--      -- rw yoneda_sugar_prod_inv at V,rw ← assoc at V,
--      -- rw yoneda_sugar.otimes at V, 
--      -- have hyp : (((R < T G.X> | R < 𝟙 G.X>) ≫ (yoneda_sugar.prod R (T C) G.X).inv) ≫
--      --     (yoneda_sugar.prod R (T C) G.X).hom ≫
--      --       (R < G.ε> ⊗ R < 𝟙 G.X>) ≫ (yoneda_sugar.prod R G.X G.X).inv) ≫
--      --  (R < G.μ>) = (((R < T G.X> | R < 𝟙 G.X>) ≫ ((yoneda_sugar.prod R (T C) G.X).inv) ≫
--      --     (yoneda_sugar.prod R (T C) G.X).hom) ≫
--      --       (R < G.ε> ⊗ R < 𝟙 G.X>) ≫ (yoneda_sugar.prod R G.X G.X).inv) ≫
--      --  (R < G.μ>), 
--      --      simp,
--      -- rw yoneda_sugar.prod.inv_hom at hyp,rw hyp at V, 
--      -- -- rw yoneda_sugar.id at V,have V' : (𝟙 (R[(G : C)])) a = a, exact rfl,
--      -- -- erw ←  V at V', rw ← V', 
--      -- have fact_2 : ((R < T G.X> | R < 𝟙 G.X>) ≫ 𝟙 (R[T C] ⨯ R[G.X])) = (R < T G.X> | R < 𝟙 G.X>), 
--      --      simp,
--      -- rw fact_2 at V,
--      -- have fact_3 : ((R < T G.X> | R < 𝟙 G.X>) ≫ (R < G.ε> ⊗ R < 𝟙 G.X>) ≫ (yoneda_sugar.prod R G.X G.X).inv) ≫
--      --  (R < G.μ>) = (((R < T G.X> | R < 𝟙 G.X>) ≫ (R < G.ε> ⊗ R < 𝟙 G.X>)) ≫ (yoneda_sugar.prod R G.X G.X).inv) ≫
--      --  (R < G.μ>), sorry,
--      --  rw yoneda_sugar.id at fact_3,
--      -- rw pre_des R at fact_3, 
--      -- -- rw destruction(R < T G.X>) (R < G.ε>) at fact_3,
--      -- sorry, -- tooooooooo difficult for the moment !!!! 
-- end
 end GROUP_OBJ