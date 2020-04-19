import category_theory.comma
import algebra.category.CommRing
import .global
import .ideals
import .Omega
import data.opposite
import ring_theory.ideals
import  .src.sieve
import  .src.grothendieck 
open category_theory
open opposite
universes u
local notation `Ring` := CommRing.{u}
local notation `Aff`  := Ringᵒᵖ
local notation `Set` :=  Type u  

--- The goals is to define Zariski topology on Aff := Ringᵒᵖ 
--- We use the definition on Topos theory ! 
--- Starting we ideal lemma   

namespace ideals
lemma set_image_S_subset_set_image_span_S (A B : Ring )(f : A ⟶ B) (S : set A) : 
set.image f S ⊆  set.image f (ideal.span S) :=  
begin
    apply set.image_subset,
    exact ideal.subset_span ,
end 

lemma ideal.map_span_eq_span_image(A B : Ring )(f : A ⟶ B) (S : set A):
    ideal.span (set.image f S) = ideal.map f (ideal.span S) := 
begin 
    apply le_antisymm,
    exact ideal.span_mono (set_image_S_subset_set_image_span_S A B f S),
    exact ideal.map_le_iff_le_comap.2 (ideal.span_le.2 (set.image_subset_iff.1 (ideal.subset_span))),
end

-- idée 
-- Profiter de ⊤ 

lemma top_ideal_map (A B : Ring)(f : A ⟶ B)(S : set A) :
ideal.span S = ⊤ → ideal.span (set.image f S) = ⊤ := λ certif,
begin 
    rw ideal.map_span_eq_span_image,
    rw certif,
    exact ideal.map_top f,
end



lemma one_ideal_map {A  B : Ring}(f : A ⟶ B)(S : set A) : 
(1 : A) ∈ ideal.span S → (1 : B) ∈ ideal.span( set.image f S) := λ P, begin 
have hyp : f 1  ∈ ideal.span (set.image f S),
        rw ideal.map_span_eq_span_image,
        apply ideal.mem_map_of_mem,
        exact P,
    rw  f.map_one at hyp,
    assumption, 
end
end ideals
open ideals



namespace Pre_sieves
structure Presieves (X : Aff) := 
(S : set (X.unop))
(co_maximality : (1 : X.unop) ∈ ideal.span S)


@[ext] lemma ext (X : Aff) (P Q : Presieves X) : P.S = Q.S → P = Q  := 
    begin
        intros h1,
        cases P,
        cases Q,
        congr ; try { assumption },
    end
def pull_back{X Y : Aff}(f : Y ⟶ X) : Presieves(X) → Presieves(Y)  := λ P, begin
 exact {S := set.image f.unop P.S, co_maximality := one_ideal_map f.unop P.S P.co_maximality},
 end
lemma pull_back_ext {X Y : Aff}(f : Y ⟶ X)(P : Presieves X): (pull_back f P).S = set.image f.unop P.S := rfl
/-
Test for a Presieves to be eq to pull-back. 
-/
theorem pull_back_eq {X Y : Aff}(f : Y ⟶ X)(P : Presieves X)(Q_Y : Presieves Y) : 
        pull_back f P = Q_Y ↔ set.image f.unop P.S = Q_Y.S := 
    begin
        split, 
        intros, subst a, rw pull_back_ext,
            intros, apply ext, rw pull_back_ext, assumption,
    end
/- 
    Direct image of a presieves. 
-/
lemma inverse_image_ideal (A B : Ring)(f : A ⟶ B)(S : set B) : 
    ideal.span (set.preimage f S) ≤  ideal.comap f (ideal.span S) := 
    begin 
        rw ideal.span_le,   -- span S \leq I ↔  S ≤ I
        apply set.preimage_mono ideal.subset_span,
    end

def direct_image (X Y : Aff) (P : Presieves Y) (h : Y ⟶ X) : Presieves(X) := 
begin
    -- inverse image 
    -- h : R(X) ⟶ R(Y)  and P : set R(Y) with 1 ∈ ideal.span P.S 
    -- i take :  P' := { comap h S }
    have hyp : (1 : X.unop) ∈ ideal.span (set.preimage h.unop (ideal.span(P.S))),
        apply ideal.subset_span,
        rw  set.mem_preimage, 
    have F : (has_hom.hom.unop h) 1 = (1 : Y.unop),
        exact h.unop.map_one,
    have j : (1 : Y.unop) ∈ ideal.span P.S,
        exact P.co_maximality,
    rw ← F at j,
    assumption,
    have hyp2 : (ideal.span (set.preimage h.unop (ideal.span(P.S))) : set X.unop) = set.preimage h.unop (ideal.span(P.S)),


    -- exact {S := set.preimage h.unop P.S, co_maximality := hyp},
end
end  Pre_sieves

open Pre_sieves
def sieves_of (X : Aff) (P : Presieves X) :=  
{ f : over X |∃ s : P.S, ∃ u : unop f.left,  ((f.hom s.val * u ) : unop f.left ) = 1 } 

-- Ici le plus simple va être de faire appel à units ! 
-- 
lemma mem_sieves (X : Aff) (P : Presieves X)(f : over X) : (
∃ s : P.S, ∃ u : unop f.left, ((f.hom s.val * u ) : unop f.left ) = 1) →   f ∈ (sieves_of X P) := λ hyp, hyp 

lemma sieves_mem {X : Aff} {P : Presieves X}{f : over X} : f ∈ (sieves_of X P) → 
(∃ s : P.S,∃ u : unop f.left, ((f.hom s.val * u ) : unop f.left ) = 1) := λ hyp,hyp

def subs (X : Aff) (P : Presieves X) : 
∀ (f : over X) (hyp : f ∈ (sieves_of X P)) (Z : Aff) (g : Z ⟶ f.left),
 (over.mk (g ≫ f.hom)) ∈ (sieves_of X P) := 
begin 
    intros, apply mem_sieves, rw over.mk_hom, rcases hyp with ⟨s,u, hyp_su⟩, use s, use g u,
    show  g.unop( f.hom(s.val)) * g.unop (u) = (1 : unop Z), 
        rw ← g.unop.map_mul (f.hom s.val) u,rw hyp_su,
        exact g.unop.map_one,
end  

def Aff_sieves (X : Aff )(P : Presieves X) : sieve(X) := {arrows := sieves_of X P,subs := subs X P}
def Aff_sieves_arrow (X : Aff )(P : Presieves X) : (Aff_sieves X P).arrows = sieves_of X P := rfl

/-
Fondamental theorem  : le faire mieux avec Aff_sieves ! 
-/
theorem pull_back_stability{X Y: Aff}(h : Y ⟶ X) (S : Presieves X)(f : over Y) :
 (over.mk (f.hom ≫ h)) ∈ Aff_sieves X S  →  f ∈ (Aff_sieves Y (pull_back h S))  := 
λ fh_hyp, begin 
    rcases  sieves_mem  fh_hyp with s,
    apply mem_sieves,
    use h.unop s,
        rw pull_back_ext,
        exact set.mem_image_of_mem h.unop s.property,
    exact h_1,
end
theorem pull_back_stability'{X Y: Aff}(h : Y ⟶ X) (S : Presieves X)(f : over Y) :
  f ∈ (Aff_sieves Y (pull_back h S)) → (over.mk (f.hom ≫ h)) ∈ Aff_sieves X S := 
λ fh_hyp, begin 
    rcases  sieves_mem  fh_hyp with hs,
    apply mem_sieves,
    cases  set.mem_image_iff_bex.1 hs.property with s hyp_s,
    use s,
    rcases hyp_s with hyp_hs,
    exact hyp_hs,
    rcases hyp_s with hyp_hs,
    rw ← hyp_s_h at h_1,
    exact h_1,
end
/- 
Zariski
-/

def Zariski_topology( X : Aff)  :=  {S : sieve X | ∃ P : Presieves X, S = Aff_sieves X P} 

lemma mem_Zariski ( X : Aff) (S : sieve X) : 
S ∈ Zariski_topology( X) →  ∃  P : Presieves X, S = Aff_sieves X P := λ SS, 
begin
cases SS with a t,
use a,
exact t,
end
lemma mem_Zariski_ ( X : Aff) (S : sieve X) : (∃  P : Presieves X, S = Aff_sieves X P) → 
S ∈ Zariski_topology( X)  := λ hyp, hyp

def Zariski_of (X : Aff) : Presieves X → Zariski_topology(X) := λ S,begin
use Aff_sieves X S, 
unfold Zariski_topology,
split,
show Aff_sieves X S = Aff_sieves X S,
    exact rfl,
end 
-- But : prouver que Zariski Topology is grothendieck topology ! 
-- Il nous faut parler du sieves max 
def max'(X : Aff) : sieve X := Zariski_of (X) ({S := {(1 : unop X)}, co_maximality := 
begin 
    apply ideal.subset_span,
    exact set.mem_singleton 1,
end  })
lemma max_is_max(X : Aff) :  max'(X) = ⊤ := begin 
    ext f,
    split,intros, trivial,
    intros hyp, apply mem_sieves, use 1,exact set.mem_singleton 1,use 1,rw mul_one,
    exact f.hom.unop.map_one,
end

lemma pull_back_comp (X Y : Aff) (P : Presieves X) (h : Y ⟶ X) :   
    sieve.pullback (Aff_sieves X P) h = Aff_sieves Y (pull_back h P) := 
begin 
    ext f,
    split,
        intros hyp,apply pull_back_stability, rw ← sieve.pullback_def2 h,exact hyp,
        intros, show f ∈ sieve.pullback (Aff_sieves X P) h,
                    rw sieve.pullback_def2 h, apply pull_back_stability',exact a,
end


#print grothendieck
def stab'  (X Y : Aff) (S ∈ Zariski_topology X) (h : Y ⟶ X) : 
            sieve.pullback S h ∈ Zariski_topology(Y) := 
    begin 
        apply mem_Zariski_ Y,
        cases H with P Hyp,
        use pull_back h P,
        subst Hyp ,
        exact pull_back_comp X Y P h ,
    end
-- il nous faut étudier un peu les choses ! 
-- Par exemple l'hypothèse :  (f : over X),  sieve.pullback R f.fom ∈ Zariski(f.left) 
--    f :  Z    →  X, il existe  (S(Z) set Z) tel que sieve.pullback R f.hom = Ring sieve S(Z)
--     g Z' → Z, g f ∈ R ↔  ∃ s_Z  g s_Z inversible 


def trans' (X : Aff)(S ∈ Zariski_topology X)(R : sieve X) : (∀(f : over X), f ∈ S → 
sieve.pullback R f.hom ∈  Zariski_topology(f.left)) → (R ∈ Zariski_topology(X)) := 
begin
 sorry, 
end

