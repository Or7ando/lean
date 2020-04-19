import algebra.category.CommRing.basic
import algebra.ring
import tactic
import category_theory.functor_category -- this transitively imports
import algebra.ring
import category_theory.types
universes v u 
/--
## This is the groupe AGL_1(R) : x ↦  ax + b invertible i.e with a inveritible !  The goal is to make
## into a groupe for composition !
-/
structure AGL_1 ( R : Type v) [comm_ring R] :=
(a b  : R)
(y : R)
(certif :  a * y = 1)

namespace AGL_1
section
variables {R : Type v} [comm_ring R]

@[ext]
lemma ext : ∀ {g1 g2 : AGL_1 R}, g1.a = g2.a → g1.b = g2.b → g1 = g2 := λ g1 g2, --- it's ok ? just don't use Bracket ? 
begin
  intros h1 h2,
  cases g1,                                         ---  difficult i have to analyse ! 
  cases g2,
  congr ; try { assumption },
  change g1_a = g2_a at h1,
  rw h1 at g1_certif,
  apply_fun (*) g2_y at g1_certif,
  rwa [← mul_assoc, mul_comm g2_y, g2_certif, one_mul, mul_one] at g1_certif,
end

def one  : AGL_1(R) := {a := 1, b:=0, y := 1, certif := mul_one 1}
instance  : has_one (AGL_1 R) := ⟨one⟩
lemma one_a : (1 : AGL_1(R)).a = 1 := rfl
lemma one_b : (1 : AGL_1(R)).b = 0 := rfl
def of (r : R) : AGL_1(R) := {a := 1, b := r, y := 1, certif := mul_one 1}

lemma one_eq_of_one : one = of (0 : R) := rfl

 def mul_map' : AGL_1(R) → AGL_1 (R) → AGL_1(R) := λ g1 g2,
{ a := g1.a * g2.a,
  b := g1.a * g2.b + g1.b,
  y := g1.y * g2.y ,
  certif := begin
    have H : g1.a * g2.a * (g1.y * g2.y) = (g1.a * g1.y)  * (g2.a * g2.y), 
        ring,
    rw H,
    rw [g1.certif,g2.certif],
    exact one_mul 1,
  end}

instance : inhabited (AGL_1 R) := ⟨1⟩

instance : has_mul (AGL_1 R) := ⟨AGL_1.mul_map'⟩

lemma a_comp (g1 g2 : AGL_1 R) : (g1 * g2).a = g1.a * g2.a :=  rfl
lemma b_comp (g1 g2 : AGL_1 R) : (g1 * g2).b = g1.a * g2.b + g1.b := rfl

meta def AGL_ring : tactic unit :=
`[simp only [one_a, one_b, a_comp, b_comp], ring]

run_cmd add_interactive [`AGL_ring]

def mul_inv : AGL_1 R → AGL_1 R := λ g,    --- change here ?  
{ a := g.y,
  b:= - g.y * g.b,
  y := g.a ,
  certif := begin  rw  mul_comm, exact g.certif, end  }

instance : has_inv (AGL_1 R) := ⟨AGL_1.mul_inv⟩

lemma a_comp_inv (g : AGL_1 R) : (g⁻¹).a =g.y  :=  rfl
lemma b_comp_inv (g : AGL_1 R) : (g⁻¹).b = - g.y * g.b  := rfl

def Rotation (R : Type v)[comm_ring R]  (a : R) (y : R):   ( a * y = 1 ) → AGL_1(R) :=
λ certif, {a := a, b := 0, y := y, certif := certif}

def mul_one'  (g : AGL_1 R) :  g * 1 = g := begin ext; AGL_ring, end 
def one_mul' (g : AGL_1 R)  : 1 * g = g := begin ext ;AGL_ring, end
def mul_assoc' (g1 g2 g3 : AGL_1 R) :  (g1 * g2) * g3 = g1 * (g2 * g3) := 
    begin 
        ext; AGL_ring,
    end   
instance [has_repr R] : has_repr (AGL_1 (R))  := ⟨λ x, repr (x.a) ++ " X + " ++ repr (x.b)⟩
lemma mul_right_inv' (g : AGL_1 R) : g * g⁻¹ = 1 :=begin
    ext,
    rw [a_comp,a_comp_inv], exact g.certif,
    rw [b_comp,b_comp_inv,← mul_assoc,one_b,mul_comm,mul_neg_eq_neg_mul_symm,g.certif],
    ring,
 end
 lemma mul_left_inv' (g : AGL_1 R) :  g⁻¹ * g = 1 :=begin
    ext,
    rw [a_comp,a_comp_inv, mul_comm], 
    exact g.certif,
    rw [b_comp,one_b,a_comp_inv,mul_comm,b_comp_inv], 
    ring,
 end
#eval of (3 : ℤ) * of(4 : ℤ)
instance : group (AGL_1 R) := 
  { mul             := mul_map',
    one             := 1,
    one_mul         := one_mul',
    mul_one         := mul_one',
    inv             :=  mul_inv,
    mul_assoc       := mul_assoc',
    mul_left_inv    := mul_left_inv',}
open CommRing
open is_ring_hom
variables (R' : Type v)[comm_ring R'] (f : R →  R')[is_ring_hom f]
def hom_map (R' : Type v) [comm_ring R'](f : R →  R')[is_ring_hom f] : AGL_1 R → AGL_1 R' := λ g, 
    { 
        a := f g.a,
        b := f g.b,
        y := f g.y,
        certif := begin rw [← map_mul (f),g.certif], exact map_one f, 
        end 
    }
lemma a_comp_hom (g : AGL_1 R) : (hom_map (R') (f) (g)).a = f g.a := rfl
lemma b_comp_hom (g : AGL_1 R) : (hom_map (R') (f) (g)).b = f g.b := rfl
lemma y_comp_hom (g : AGL_1 R) : (hom_map (R') (f) (g)).y = f g.y := rfl

lemma hom_map_group_comp (R' : Type v) [comm_ring R'](f : R → R')[is_ring_hom f] (g1 g2 : AGL_1 R) :
     hom_map (R')(f) (g1 * g2) = hom_map(R') (f) g1 * hom_map (R')(f) g2  := begin 
        ext, 
        rw [a_comp,a_comp_hom,a_comp_hom,a_comp_hom,a_comp],
        exact map_mul f,
        rw [b_comp,b_comp_hom,b_comp_hom,b_comp_hom,a_comp_hom,b_comp,← map_mul f,← map_add f],
     end

lemma hom_map_one (R' : Type v)[comm_ring R'](f : R → R')[is_ring_hom f] (g1 g2 : AGL_1 R) : hom_map R' (f) (1) = 1 :=
begin
    ext,
    rw [a_comp_hom,one_a,one_a],
    exact map_one f,
    rw [b_comp_hom,one_b,one_b],
    exact  map_zero f, 
end
def AGL__1 : CommRing ⥤ Type v :=  
{ obj := λ R, AGL_1 R, 
  map := λ R R' f, hom_map R' f, 
}
end 
#print AGL__1
end AGL_1