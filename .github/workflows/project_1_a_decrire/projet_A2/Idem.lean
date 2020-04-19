import algebra.category.CommRing.basic
import algebra.ring
import tactic
import category_theory.concrete_category.bundled_hom
import category_theory.functor_category -- this transitively imports
import algebra.ring
import category_theory.types
import .A2_disc
open category_theory
/--
##  It's the group functor  Idem,  
##  e1 × e2 = e1 e2 + (1-e1)(1-e2)
-/
structure Idem (R : Type ) [comm_ring R] :=
(e  : R)
(certif :  e * e = e)
namespace  Idem   
 variables {R : Type }[comm_ring R]
    section                               --   ""
    /- extention lemma : E = E' ↔  E.e = E'.e
    -/
    @[ext]lemma ext : ∀ {g1 g2 : Idem R}, g1.e = g2.e → g1 = g2 := λ g1 g2, 
        begin
            intros h1 ,
            cases g1,                                         
            cases g2, 
            congr ; try { assumption },   --- 
        end
    lemma idem_to_sym (E :Idem R) : (2*E.e-1)^2 = 1 :=
    begin 
        have T : (2*E.e-1)^2 = 4*(E.e*E.e)-4*E.e+1,
            ring,
        rw [T,E.certif],ring,
    end
    -- We start to define one element : neutral element 
    def one  : Idem (R) := {e := 1,  certif := mul_one 1}
    instance : has_one (Idem R) := ⟨one⟩
    -- lemma !
    lemma one_e : (1 : Idem(R)).e = 1 := rfl
    -- comm ring calculation ! 
    lemma alg_calc (a b : R) : (a * b + (1 - a) * (1 - b)) * (a * b + (1 - a) * (1 - b)) =(a * a) * (b * b) +
                         ((1 - a) * (1 - a)) * ((1 - b) * (1 - b)) + 2* (a* (1 - a)) * (b*(1 - b)) := by ring
        
    lemma compl_e (E : Idem R) : (1-E.e) * (1-E.e)  = (1-E.e)  := 
        begin 
            have H : (1-E.e) * (1-E.e) = 1- 2 * E.e + E.e *E.e,
                ring,
            rw E.certif at H,
            rw H,
            ring,
        end
    /-   e → 1-e 
    -/ 
    def ortho : Idem R → Idem R := λ E, 
        begin 
            exact {e := 1-E.e, certif := compl_e E}
        end
    lemma ortho_comp (E : Idem R) : (ortho E).e = 1-E.e := rfl
    lemma ortho_is_involution (E : Idem R) : ortho (ortho E) = E := 
    begin 
        ext,
        rw ortho_comp,
        rw ortho_comp,
        ring,
    end 

    lemma ortho_e (E : Idem R) : E.e * (1-E.e) = 0 := 
        begin 
            rw [mul_sub_left_distrib,mul_one,E.certif],
            exact sub_self E.e,
        end
    def mul_map' : Idem (R) →  Idem (R) → Idem (R) := λ g1 g2, begin
        exact { e := g1.e * g2.e + ((1 : R) -g1.e) * ((1 : R)-g2.e),certif := begin 
            rw [alg_calc g1.e g2.e,ortho_e g1,g1.certif,g2.certif,mul_zero,zero_mul,add_zero,compl_e g1,compl_e g2], end }
    end 
    instance : inhabited (Idem R) := ⟨1⟩

    instance : has_mul (Idem R) := ⟨Idem.mul_map'⟩

    lemma e_comp (g1 g2 : Idem R) : (g1 * g2).e = g1.e * g2.e+((1 :R)-g1.e) * ((1 : R)-g2.e) :=  rfl

    def mul_inv : Idem R → Idem R := λ g, g

    instance : has_inv (Idem R) := ⟨Idem.mul_inv⟩

    lemma e_comp_inv (g : Idem R) : (g⁻¹).e =g.e  :=  rfl
    meta def AGL_ring : tactic unit :=
            `[simp only [one_e, e_comp ,e_comp_inv], ring]

    run_cmd add_interactive [`AGL_ring]

def mul_one'  (g : Idem R) :  g * 1 = g := begin ext; AGL_ring, end 
def one_mul' (g : Idem R)  : 1 * g = g := begin ext ;AGL_ring, end
def mul_assoc' (g1 g2 g3 : Idem R) :  (g1 * g2) * g3 = g1 * (g2 * g3) := begin ext; AGL_ring, end   

lemma mul_right_inv' (g : Idem R) : g * g⁻¹ = 1 :=
   begin 
        ext, 
        rw [e_comp,e_comp_inv,g.certif,compl_e,one_e],
        simp,
    end 

 lemma mul_left_inv' (g : Idem R) :  g⁻¹ * g = 1 :=
    begin
        ext,
        rw [e_comp,e_comp_inv,g.certif,compl_e,one_e],
        simp,
    end
instance : group (Idem R) := 
  { mul             := mul_map',
    one             := 1,
    one_mul         := one_mul',
    mul_one         := mul_one',
    inv             :=  mul_inv,
    mul_assoc       := mul_assoc',
    mul_left_inv    := mul_left_inv',}

open CommRing
open is_ring_hom
variables {R' : Type }[comm_ring R'] (f : R →  R')[is_ring_hom f]
def hom_map (f : R →  R')[is_ring_hom f] : Idem (R) → Idem (R') := λ g, 
    { 
        e := f g.e,
        certif := begin rw [← map_mul (f),g.certif], end 
    }
lemma e_comp_hom (g : Idem R) : (hom_map (f) (g)).e = f g.e := rfl
meta def idem_hom : tactic unit :=
`[simp only [map_add f,map_mul f,map_sub f,map_one f,e_comp_hom,e_comp]]

run_cmd add_interactive [`idem_hom]
lemma hom_map_group_comp  (g1 g2 : Idem R) :
     hom_map (f) (g1 * g2) = (hom_map (f) g1) * hom_map (f) g2  := begin 
        ext,
        idem_hom,  
        -- rw [e_comp_hom,e_comp,map_add f,map_mul f,map_mul f,map_sub f,map_sub f,map_one f],
     end

lemma hom_map_one : hom_map f (1) = 1 :=
begin
    ext,
    exact map_one f,
end
def map : (Idem R) →*  (Idem R') :=   monoid_hom.mk' (hom_map f) (hom_map_group_comp f)  
def Idem_ : CommRing ⥤ Group  :=  
{ obj := λ R, Group.of (Idem R), 
  map := λ R R' f, (map f), 
}
end 
#print Idem_
namespace Idem.calculus
    open nat
    lemma idem_comb (a : R) (E : Idem R) : E.e * a + (1 - E.e) * a = a := by ring
    lemma localy_eq (a b : R) (E : Idem R) : E.e * a = E.e * b → ((1 : R)-E.e ) * a = ((1 : R)-E.e)*b →  a = b := λ h1 h2, begin
        have H : E.e * a + (1 - E.e) * a = E.e * b+(1 - E.e) * b, 
            rw [h1,h2],
        rw idem_comb (a) (E) at H,
        rw idem_comb (b) (E) at H,
        exact H,
    end
    lemma square_idem (a : R) (E : Idem R) : a^2 = (E.e * a - (1-E.e) * a)^2 := 
    begin 
        have H : (E.e * a - (1 - E.e) * a) ^ 2 = (E.e * E.e) * (a * a) - 2 * (a * a) * (E.e * (1-E.e)) + (a*a)*((1-E.e)*(1-E.e)),
            ring,
        rw E.certif at H,
        rw ortho_e E at H,
        rw compl_e E at H,
        rw H,
        ring,
    end 

end Idem.calculus
end Idem