import algebra.category.CommRing.basic
import algebra.ring
/--
## This is the groupe AGL_1(R) : x ↦  ax + b invertible i.e with a inveritible !  The goal is to make 
## into a groupe for composition ! 
-/
structure AGL_1 ( R : Type) [comm_ring R] :=  mk {} ::
(a b  : R)
(y : R)
(certif :  a * y = 1)
namespace AGL_1 
section

  parameters (R : Type)[comm_ring R]
  theorem ext  (g_1 g_2 : AGL_1( R )) : (g_1 = g_2) ↔ 
        g_1.a = g_2.a ∧
        g_1.b = g_2.b ∧ 
        g_1.y = g_2.y := 
        begin 
            split,
            intro,
            split,
            exact congr_arg AGL_1.a a,
            split, 
            exact congr_arg AGL_1.b a,
            exact congr_arg AGL_1.y a,

        end 
    def one  : AGL_1(R) := {a := 1 ,b:=0, y := 1, certif := mul_one 1}
    instance  : has_one (AGL_1 R) := ⟨one⟩   
def of (r : R) : AGL_1(R) := {a := 1, b := r, y := 1, certif := mul_one 1} 

lemma one_eq_of_one : one = of (0) := rfl

protected def mul_map' : AGL_1(R) → AGL_1 (R) → AGL_1(R) := λ ⟨a1,b1,y1,certif_1⟩ ⟨a2,b2,y2,certif_2⟩,
 begin 
    have certif_ : (a1 * a2) * (y2 * y1) = 1,
        rw ←  mul_assoc (a1 * a2) y2 y1,
        rw  mul_assoc a1 a2 y2,
        rw certif_2,
        rw mul_one, 
        rw certif_1,
    exact {a := a1 * a2, b := a1 * b2 + b1, y := y2 * y1 , certif := certif_},
 end
instance : inhabited (AGL_1 R) := ⟨1⟩  

instance : has_mul (AGL_1 R) := ⟨mul_map'⟩

protected def mul_inv : AGL_1 R → AGL_1 R := λ ⟨a,b,y, certif⟩,
    begin 
        exact {a := y, b:= -y * b , y := a , certif := begin rw mul_comm at certif, assumption end }
    end 
instance : has_inv (AGL_1 R) := ⟨ mul_inv⟩

def Rotation (R : Type)[comm_ring R]  (a : R) (y : R):   ( a * y = 1 ) → AGL_1(R) :=  λ certif, begin 
exact {a := a, b := 0, y := y, certif := certif}, end

def mul_one' : ∀ g : AGL_1 R, g * 1 = g :=  λ ⟨a1,b1,y1,certif_1⟩, begin  --- i thinck it's ok g * 1 cause has_instance mul !
    have certif_a : a1 * 1 = a1,
        exact mul_one a1,
    have certif_b : a1 * 0 + b1 = b1,  
        rw [mul_zero,zero_add],
    have certif_y : 1 * y1 = y1,
        exact one_mul y1,
    have  certif_certif : (a1 * 1) * (1 * y1) = a1 * y1,
        rw [mul_one,one_mul],
    sorry,  ---  I don't know what i have to do :D 
end 
end 
end AGL_1
