import category_theory.comma
import algebra.category.CommRing
import .global
import .ideals
import .Omega
import data.opposite
import ring_theory.ideals
import  .src.sieve
import  .src.grothendieck 
import ring_theory.localization
open category_theory
open localization  ---362 
open opposite
universes u
local notation `Ring` := CommRing.{u}
local notation `Aff`  := Ringᵒᵖ
local notation `Set` :=  Type u  

namespace ideals
--- Starting we ideal lemma   
/-   
     f (S) ⊆ f <S>
-/
lemma set_image_S_subset_set_image_span_S (A B : Ring )(f : A ⟶ B) (S : set A) : 
        set.image f S ⊆  set.image f (ideal.span S) :=  
begin
    apply set.image_subset,
    exact ideal.subset_span,
end 
/-
    < f⁻¹ S > ⊆ f⁻¹ < S >  
-/
lemma inverse_image_ideal (A B : Ring)(f : A ⟶ B)(S : set B) : 
    ideal.span (set.preimage f S) ≤  ideal.comap f (ideal.span S) := 
    begin 
        rw ideal.span_le,   -- span S \leq I ↔  S ≤ I
        apply set.preimage_mono ideal.subset_span,
    end
/-
    < f (S) > = < f<S> >
-/
lemma ideal.map_span_eq_span_image(A B : Ring )(f : A ⟶ B) (S : set A):
    ideal.span (set.image f S) = ideal.map f (ideal.span S) := 
begin 
    apply le_antisymm,    
    exact ideal.span_mono (set_image_S_subset_set_image_span_S A B f S),
    exact ideal.map_le_iff_le_comap.2 (ideal.span_le.2 (set.image_subset_iff.1 (ideal.subset_span))),
end
/-
  < S >   = ⊤ →  <f S > = ⊤  
-/
lemma top_ideal_map {A B : Ring}(f : A ⟶ B)(S : set A) :
ideal.span S = ⊤ → ideal.span (set.image f S) = ⊤ := λ certif,
begin 
    rw ideal.map_span_eq_span_image,
    rw certif,
    exact ideal.map_top f,
end

end ideals
open ideals
namespace Pre_sieves
--
-- on va definir un famille de sous-ensemble d'un anneau qui va nous donner des covering_familly
structure covering_familly (X : Aff) := 
-- idée base ring (base_ring := X.unop)
-- (S : set base_ring)
-- (I:= ideal.span S)   ----refaire !!!! tout !!! 
-- (co_max : I = ⊤) 
(S : set (X.unop))
(co_maximality : ideal.span S = ⊤)

/-
Accessor 
-/
def to_ring (X : Aff) : Ring := X.unop  
def to_set{X :Aff} (P : covering_familly X) : set (to_ring X) := P.S
lemma to_set_ext{X :Aff} (P : covering_familly X) : to_set P = P.S := rfl
def base_ring{X : Aff}(P : covering_familly X) : Ring := to_ring X
def Ideal{X : Aff}(P : covering_familly X) : ideal $ base_ring P := ideal.span $ to_set P 

@[ext] lemma ext (X : Aff) (P Q : covering_familly X) : P.S = Q.S → P = Q  := 
    begin
        intros h1,cases P,cases Q,
        congr ; try { assumption },
    end
lemma exten {X : Aff} (P Q : covering_familly X) : P = Q ↔ P.S =Q.S := begin 
     split,intro,congr; try {assumption},
     exact ext X P Q,
end
def pull_back{X Y : Aff}(f : Y ⟶ X) (P : covering_familly X) : covering_familly(Y)  := begin
 exact {S := set.image f.unop P.S, co_maximality := top_ideal_map f.unop P.S P.co_maximality},
end
infix  `#`   := pull_back
-- local notation prefix  f♯P := (pull_back f P)
lemma pull_back_ext {X Y : Aff}(f : Y ⟶ X)(P : covering_familly X):
          ( f # P).S  = set.image f.unop P.S := rfl
/-
Test for a covering_familly to be eq to pull-back. 
-/
theorem pull_back_eq {X Y : Aff}(f : Y ⟶ X)(P : covering_familly X)(Q_Y : covering_familly Y) : 
        f # P = Q_Y ↔ set.image f.unop P.S = Q_Y.S := 
    begin
          split, 
               intros, subst a, rw pull_back_ext,
               intros, apply ext, rw ← a,rw ← to_set_ext,exact pull_back_ext f P,
    end
end  Pre_sieves

open Pre_sieves

def sieves_of (X : Aff) (P : covering_familly X) :=  
       { f : over X | ∃ s : P.S, ideal.map (f.hom.unop) (ideal.span ({s} : set X.unop)) = ⊤ } 

lemma simply {A B :Ring}(f  : A ⟶ B)(s : A) : ideal.map (f)(ideal.span({s} : set A)) = ideal.span( {f s} : set B) :=
begin 
     have hyp : set.image f ({s} : set A) = ({f s} : set B),
     exact set.image_singleton,
     rw ← hyp,
     exact eq.symm ( ideal.map_span_eq_span_image A B f {s}),
end 
-- La définition est alors :
-- def sieves_of' (X : Aff) (P : covering_familly X) := 
--      { f : over X | ∃ s : P.S, ideal.span ({f.hom s.val} : set (f.left.unop))   = ⊤ }
lemma mem_sieves (X : Aff) (P : covering_familly X)(f : over X) : (
∃ s : P.S, ideal.map (f.hom.unop) (ideal.span ({s} : set X.unop)) = ⊤) →   f ∈ (sieves_of X P) := λ hyp, hyp 

lemma sieves_mem {X : Aff} {P : covering_familly X}{f : over X} : f ∈ (sieves_of X P) → 
(∃ s : P.S, ideal.map (f.hom.unop) (ideal.span ({s} : set X.unop)) = ⊤) := λ hyp,hyp

def subs (X : Aff) (P : covering_familly X) : 
∀ (f : over X) (hyp : f ∈ (sieves_of X P)) (Z : Aff) (g : Z ⟶ f.left),
 (over.mk (g ≫ f.hom)) ∈ (sieves_of X P) := 
begin 
     intros, apply mem_sieves, rw over.mk_hom, 
     rcases hyp with ⟨s, hyp_su⟩, use s,
     show ideal.map (f.hom.unop ≫ g.unop) (ideal.span ({s} : set X.unop)) = ⊤,
          rw [ideal.ideal_comp,hyp_su],
          exact ideal.map_top g.unop,
end  

instance (X : Aff) : has_coe (covering_familly X)  (sieve X) := ⟨λ P, {arrows := sieves_of X P,subs := subs X P}⟩


lemma arrows_comp {X :Aff}(P : covering_familly X) : sieves_of X P = (P : sieve X).arrows := rfl 
theorem  has_coe_is_equiv {X : Aff} (P Q : covering_familly X)  : P = Q → (P : sieve X) = (Q : sieve X) :=  
---  si S(P) = S(Q) alors les sieves sont égaux : évident sieve X est défini unniquement à l'aide de S. La 
---  réciproque est fausse !  
begin 
     intros,
     rw exten at a,
     apply sieve.extensionality,
     iterate 2{ rw ← arrows_comp},
     ext f,
     split,
     intros hyp, apply mem_sieves,rcases hyp with ⟨ s, hyp_s ⟩,use s.val, rw ← a, exact s.property,exact hyp_s,
     intros hyp, apply mem_sieves,rcases hyp with ⟨ s, hyp_s ⟩,use s.val, rw  a, exact s.property,exact hyp_s,
end

def Aff_sieves {X : Aff }(P : covering_familly X) : sieve(X) := {arrows := sieves_of X P,subs := subs X P}
def Aff_sieves_arrow {X : Aff}(P : covering_familly X) : (Aff_sieves  P).arrows = sieves_of X P := rfl
def mem_Aff_sieves {X : Aff}(P : covering_familly X)( f : over X) : f ∈ sieves_of X P   →  f ∈ Aff_sieves P := 
begin 
     intros,
     show f ∈ (Aff_sieves P).arrows,
          rw Aff_sieves_arrow,
          assumption,
end
/-
Fondamental theorem  : le faire mieux avec Aff_sieves ! 
-/

-- trop complexe niveau écriture ce n'est pas fluide ! c'est un peu mieux mais pas encore ! 
-- Niveau mathmatique : 
--   Soit X Y deux affines. h : Y ⟶ X un morphisme. P un recouvrement de X donné par la famille 
--    S := P.S de l'anneau X.unop. Soit maintenant f / Y i.e f : Z ⟶ Y dans Aff. 
--    alors (Z ⟶ Y ⟶ X) ∈ (P : sieve X) ssi f ∈ (h # P) 
-- Il sz'agit du petit calcul. 
-- Soit s ∈ X.unop, alors f h (s) engendre l'idéal plein de X.unop alors f s'  := f (h(s)) engendre le plein

theorem pull_back_stability {X Y: Aff}(h : Y ⟶ X) (P : covering_familly X)(f : over Y) :
 (over.mk (f.hom ≫ h)) ∈  (P : sieve X)  →  f ∈ ( (h # P) : sieve Y)  := 
λ fh_hyp, begin 
     apply mem_sieves,
     rcases  sieves_mem  fh_hyp with ⟨s,hyp_s⟩,
     rw [over.mk_hom,unop_comp,ideal.ideal_comp,simply] at hyp_s,
     use h.unop s.val,
        rw pull_back_ext,
        exact set.mem_image_of_mem h.unop s.property,
     exact hyp_s,
end
theorem pull_back_stability'{X Y: Aff}(h : Y ⟶ X) (P : covering_familly X)(f : over Y) :
  f ∈ ( ( h#P) : sieve Y) → (over.mk (f.hom ≫ h)) ∈  (P  : sieve X) := begin 
     intros hyp,
     apply mem_sieves,
     rw [over.mk_hom,unop_comp],
     rcases hyp with ⟨ ⟨ s,prop⟩,certif⟩,
     rcases  set.mem_image_iff_bex.1 prop with ⟨w,⟨h_p,hu⟩⟩,  -- s = h(w)  w ∈ S
     use w,exact h_p,
     rw ideal.ideal_comp,
     rw simply,
     show ideal.map ( f.hom.unop) (ideal.span {h.unop w}) = ⊤,
     rw hu,exact certif,
end

--- changement de fichier  !!!! 
/- 
Zariski
-/

axiom Localisation_axiom_1 (X : Aff)(s : unop X) : 
∃ f : over X, ideal.map f.hom.unop (ideal.span({s})) = ⊤ 


def Zariski_topology (X : Aff)  :=  {S : sieve X | ∃ P : covering_familly X, S = P} 


lemma mem_Zariski ( X : Aff) (S : sieve X) : 
S ∈ Zariski_topology( X)  ↔  ∃  P : covering_familly X, S =  P :=  iff.rfl 

lemma Zariski_construct {X : Aff} (S : sieve X) :  (∃  P : covering_familly X, S =  P) → S ∈ Zariski_topology X := 
 (mem_Zariski X S).2
lemma Zariski {X : Aff}(S : sieve X) : 
     S ∈ Zariski_topology( X)  →  ∃  P : covering_familly X, S =  P  := (mem_Zariski X S).1

lemma Zariski_cover {X : Aff}(P : covering_familly X) : (P : sieve X) ∈ Zariski_topology(X):= begin
use P,
end

-- constructor  
def Zariski_cover_of  {X : Aff} (P : covering_familly X) : Zariski_topology(X) := 
{val := (P : sieve X), property := begin use P, end }

lemma Zariski_cover_val{X :Aff} (P : covering_familly X) : (Zariski_cover_of P).val = P := rfl

def max_P (X : Aff) : covering_familly X := {S := {(1 : unop X)}, co_maximality := ideal.span_singleton_one}
lemma map_P_S (X : Aff) :  (max_P X).S = {(1 : unop X)} := rfl

lemma id_in_max (X : Aff) : over.mk (𝟙 X) ∈ (max_P X : sieve X) := 
begin 
     -- apply mem_sieves,
     use 1,exact set.mem_singleton 1,
     show ideal.map (𝟙 X.unop) (ideal.span {1})  = ⊤,
          rw ideal.ideal_id, exact ideal.span_singleton_one,
end

/-
Idée mise en place :
     id : X → X in max + sub
-/
lemma eqmax {X : Aff}(S : sieve X) : S = ⊤ ↔ (over.mk (𝟙 X) ∈ S) := 
begin
     split, intro,rw a,trivial,
     exact sieve.top_of_has_id,
 end 

lemma max_is_max(X : Aff) :   (max_P(X) : sieve X) = ⊤ := begin 
    exact (eqmax _).2 (id_in_max X),
end

lemma pull_back_comp {X Y : Aff} (P : covering_familly X) (h : Y ⟶ X) :   
    sieve.pullback (P : sieve X) h =  ( h # P : sieve Y ) := 
begin 
    ext f,  --- ici l'histoire des arrows !!
    show f ∈ (sieve.pullback (P : sieve X) h) ↔ f ∈ (h#P : sieve Y),
        split,
        intros hyp,apply pull_back_stability, rw ← sieve.pullback_def2 h,exact hyp,
        intros,rw sieve.pullback_def2 h,apply pull_back_stability',exact a,
end
lemma pull_back_of_max (X Y :Aff) (f : Y ⟶ X) :  (f # (max_P X) : sieve Y) = (max_P Y : sieve Y) := begin
     rw max_is_max,
     apply (eqmax _).2,
     apply pull_back_stability,rw max_is_max,trivial,
end
-- definir l'appartenant a grothendieck topology
#print grothendieck
def stab'  (X Y : Aff) (S ∈ Zariski_topology X) (h : Y ⟶ X) : 
            sieve.pullback S h ∈ Zariski_topology(Y) := 
    begin 
        apply Zariski_construct,
        cases H with P Hyp,
        use pull_back h P,
        subst Hyp ,
        exact pull_back_comp P h,
    end
-- il nous faut étudier un peu les choses ! 
-- Par exemple l'hypothèse :  (f : over X),  sieve.pullback R f.fom ∈ Zariski(f.left) 
--    f :  Z    →  X, il existe  (S(Z) set Z) tel que sieve.pullback R f.hom = Ring sieve S(Z)
--     g Z' → Z, g f ∈ R ↔  ∃ s_Z  g s_Z inversible 
--
-- 

-- le premier lemme ca être le suivant : 



def trans' (X : Aff)(S ∈ Zariski_topology X)(R : sieve X) : (∀(f : over X), f ∈ S → 
sieve.pullback R f.hom ∈  Zariski_topology(f.left)) → (R ∈ Zariski_topology(X)) := 
begin
     intros hyp,
     apply Zariski_construct,
     rcases H with ⟨P,hyp_P⟩,

 sorry, 
end