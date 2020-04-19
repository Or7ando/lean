import tactic.ring
import tactic.ring_exp
import algebra.category.CommRing.basic
open category_theory
open functor
open CommRing
--          open algebra 
--          open finsupp
universes v u  
local notation ` Ring `     :=    CommRing.{u}
-- We start to define the affine line over ℤ ! This is a forget full foncteur Ring → Set 
local notation ` Set  `     :=    Type u 

namespace 𝔸
def  obj  (α : Type u) [comm_ring α]  : Set := α  
def map (α : Type u)(β : Type u)[comm_ring α][comm_ring β] (f : α →+* β) : obj ( α ) → obj ( β )  := 
       λ a : obj(α),  f a  
end 𝔸 
def  𝔸  :  Ring  ⥤  Set :=
    { 
            obj   :=    λ R :Ring, 𝔸.obj(R),
            map   :=    λ α β f,  f, 
}

-- The structure sheaf of ring of affine line over ℤ ! 

def 𝕆 : Ring ⥤ Ring  := functor.id Ring   --   non generic version of 𝒪 ! 
#print Ring.has_forget_to_AddCommGroup     ---- try to construct the additive group Gₐ by convertion ! 
-- We now want to proof that 𝔸 is a local fonctor 
-- This mean  :  ∀ R : Ring, for all finite familly (r_1 ... r_n) s.t exists u_1 ... u_n st  ∑ u_i r_i =1, for all 
--      s_1 ... s_n ∈ Loc A_(s_i) s.t they matcth in the localisation s_ij, exists unique 
--              s ∈ R s.t (s)_(r_i) = s_i   (comaximal-gluing L for localisation)
--  Perhaps : use the library of localisation 
--  
--  This mean : 𝔸 is a sheaf for global Zariski topology on Ringᵒᵖ   ! 
--- We start by somme lemma about co-maximal elements  
-- --

namespace study
universes U V 
variables (R : Type U)[comm_ring.{U} R](φ : R → R → Prop)
local infix ⊥ := φ  

def symm := ∀  ⦃a b⦄  , (a ⊥ b) → (b ⊥ a)  

def stab_mul := ∀ ⦃a b c⦄ ,   (a ⊥ c) → (b ⊥ c) → ((a * b) ⊥ c)

def co_max_type := (symm R φ) ∧ (stab_mul R  φ)

end study

open study
universes U V 
variables(R : Type U)[comm_ring.{U} R](φ : R → R → Prop)[co_max_type R φ ]

local infix ⊥ :=  φ  
lemma power_2 (a b : R) :    (a ⊥ b) →  (b ⊥ a) := 
            φ.has_symm 



---   Mettre en place une induction ! 
---   ensuite : 
---         aba trick 
--- 
---  Maintenant on s'amuse de manière formelle en créant une instance ! 


noncomputable def ι (p : polynomial ℤ)  {R : Ring} : R → R := λ t, eval t (map (to_fun R) p) 

def β (R :  Alg ) : ℤ → R := to_fun (R) 

noncomputable def ι₁  {R : Ring} :  polynomial ℤ  →   polynomial R :=
 λ P : polynomial ℤ,  map_range  (to_fun R) ( is_add_group_hom.map_zero (to_fun R)) (P) 

---   Ca permet d'obtenir une notation sympathique ! 
---   Maintenant : on souhait prouver un théormee  Pour tout f : A ⟶ B 
---   f (ι (p) x) = ι p f(x) 
---   En gros, il agit de voir un morphisme 
---   iota : A → B → C   →  A[X] →R B[X] →R C[X]  

    --- fonctor of point of Z[X] / p ... the subfonctor of 𝔸 s t  p(x) = 0  (certificate) 
    --- There is no automatic conversion so ι do the job 
    --- The property is that φ ι (p) t = ι (p) φ(t) 
    --- in a fonctorial way : this give the proof that Idem(p) is a fonctor ... but i Lean it's difficult  
structure Idem (p : polynomial ℤ) (R : Ring) := 
      (t : R)  
      (certificat : ι(p) t   = 0)   --- lean notation are not good for maths ! ! ! ! !  


@[reducible] def Ω (α : Type u)[comm_ring α] :=    --- subobjet classifier to speack open
submodule α α                                      --- and close subfonctor ! Fiber product construstion 

namespace Ω

def map (α : Type u)(β : Type u)[comm_ring α][comm_ring β] (f : α →+* β) : Ω ( α ) → Ω ( β )  := 
  λ (I :  Ω( α )), ideal.span (f '' I)

def Ω₀ (α : Type)[comm_ring α] :=  finset α            --- finite version for finite presentation 


def fr  [comm_ring α] : Ω₀(α) →  Ω(α) := λ s : Ω₀(α), ideal.span(s.to_set)
 
end Ω 



have T := (a^n) * (a^(k) * u) + b * v = a^(n+k) * u + b * v, by 
                    calc 
                        (a^n) * (a^(k) * u) + b * v = a^(n+k) * u + b * v               : by ring_exp,
                have H := (a^n) * (a^(k) * u) + b * v = 1, from 
                    calc 
                    (a^n) * (a^(k) * u) + b * v = a^(n+k) * u + b * v : T
                    ...                         = 1                                 : by sorry,
                exact ⟨ (a^k * u),  v , H ⟩ ,

