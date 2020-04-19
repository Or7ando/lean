import .global
import .Omega
import .Spec
import category_theory.functor_category
import category_theory.natural_transformation
open category_theory
open Omega
open Spec
universes u

local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  
local notation `Presheaf` := Ring ⥤ Set
variables (X : Presheaf)(Y : Presheaf)

structure open_imersion { Y X : Ring ⥤ Set} (ι : Y ⟶  X)  := 
(χ  : nat_trans X  Ω ) 
(mono_ι : ∀ A :  Ring, mono (ι.app A))
(Hyp_1 : ∀ A : Ring, ∀ y : Y.obj(A), χ.app(A)  ( ι.app(A) y ) = (⊤ : ideal A))
(Hyp_2 : ∀ A : Ring, ∀ x : X.obj(A), χ.app(A) x = (⊤ : ideal A) → ∃ y : Y.obj(A), ι.app A y = x)

structure closed_imersion {X Y : Ring ⥤ Set} (ι : nat_trans Y  X) := 
(χ  : nat_trans X  Ω ) 
(mono_ι : ∀ A :  Ring, mono (ι.app A))
(Hyp_1 : ∀ A : Ring, ∀ y : Y.obj(A), (χ.app(A) (ι.app(A) y)) = (⊥  : ideal A))
(Hyp_2 : ∀ A : Ring, ∀ x : X.obj(A), χ.app(A) x = (⊥ : ideal A) → ∃ y : Y.obj(A), ι.app A y = x)

lemma open_imersion_is_mono (ι : Y ⟶  X) : open_imersion  ι  →  ∀ A :  Ring, mono (ι.app A)  :=λ U, U.mono_ι 
lemma closed_imersion_is_mono (ι : Y ⟶  X) : closed_imersion  ι  →  ∀ A :  Ring, mono (ι.app A)  :=λ U, U.mono_ι 

structure sieves (X : Presheaf) :=
(Y : Presheaf)
(ι : nat_trans Y X)
(mono_ι : ∀ A : Ring, mono (ι.app A))

structure covering_familly (R : Ring) :=
(U : sieves $ Spec R)
(Hyp : ∃ S : set R, ∀ A : Ring, ∀ y : U.Y.obj A, ∃ s ∈ S,  ((U.ι.app A)(y)).to_fun (s) = 1)


structure matching_familly (X : Presheaf)(A : Ring) := 
(F : covering_familly A)
(β : nat_trans F.U.Y X)




---  Je dois définir quoi ? 
---  Pour R un anneau, je dois définir la notion de sous-foncteur couvrant de (Spec R)
--- C'est  ∪ (s : S) D(s) pour s ⊂ R 
--- definir la notion de topology de grothendieck sur Ring^(op) ≃ AFF = spec (Yoneda)  


structure covers (X : Presheaf) := 
(U : sieves X)

 

structure Open (X : Presheaf) := 
(U : sieves X)
(χ  :  nat_trans X Ω ) 
(Hyp_1 : ∀ A : Ring, ∀ y : U.Y.obj(A), χ.app(A)  ( U.ι.app(A) y ) = (⊤ : ideal A))
(Hyp_2 : ∀ A : Ring, ∀ x : X.obj(A), χ.app(A) x = (⊤ : ideal A) → ∃ y : U.Y.obj(A), U.ι.app A y = x)





variables (ι : Y ⟶  X)
#check Open

-- variables (U1 : Open X)(U2 : Open X)
-- def  intersection : Open X → Open X →  Open X := λ U1 U2, begin sorry, end 