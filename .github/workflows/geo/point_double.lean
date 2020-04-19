import tactic
import algebra.category.CommRing.basic
variables (R : Type)[comm_ring R]
structure R_exp := 
(a_0 : R)
(a_e : R)

namespace R_exp
mk_simp_attribute R_exp_ " trivial simplification "
meta def R_exp__ring : tactic unit :=
`[iterate 2 { simp only with R_exp_,ring}]

run_cmd add_interactive [`R_exp__ring]
@[ext] lemma ext : ∀ {g1 g2 : R_exp R}, g1.a_0 = g2.a_0 →  g1.a_e = g2.a_e  → g1 = g2 := λ g1 g2, 
        begin
            intros h1,
            intros h2,
            cases g1,                                         
            cases g2, 
            congr ; try { assumption },   --- 
        end
local notation R`[ε]` := R_exp R

def mod_ε (a : R[ε]) : R := a.a_0

instance has_coe :  has_coe(R[ε]) R := ⟨mod_ε(R)⟩  -- ? bof 
/-
a ↦ a+ 0 ε 
-/
def of(r : R) : R[ε] := {a_0 := r, a_e := 0}
@[R_exp_]lemma of_ext_0 (r : R) : ((of R r).a_0 = r)  := rfl
@[R_exp_]lemma of_ext_e (r : R) : ((of R r).a_e = 0)  := rfl
@[R_exp_]lemma coe_of (r : R) : ((of R r) : R) = r := rfl

/-
element : ε qui va vérifier :   ε^2 = 0
-/
def ε : R[ε]  := {a_0 := (0 : R), a_e := (1 : R)}
@[R_exp_]lemma ε_ext_0 : (ε R).a_0 = 0  := rfl
@[R_exp_]lemma ε_ext_e : (ε R).a_e = 1  := rfl

/-
Element !: 0
-/
def zero : R[ε] := of R (0 : R)
instance : has_zero (R[ε] ) := ⟨zero R⟩

@[R_exp_]lemma zero_ext_0 : (0 : R[ε]).a_0 = 0  := rfl
@[R_exp_]lemma zero_ext_e : (0 : R[ε]).a_e = 0  := rfl

/-
Addition : 
-/
def add' :  (R[ε]) → (R[ε]) →  (R[ε]) := λ a b,  {a_0 := a.a_0+b.a_0, a_e := a.a_e +b.a_e}
instance : has_add (R[ε]) := ⟨add' R⟩
@[R_exp_]lemma add_ext_0 (a b : R[ε]) : (a+b).a_0 = a.a_0+ b.a_0 := rfl
@[R_exp_]lemma add_ext_e (a b : R[ε]) : (a+b).a_e = a.a_e+ b.a_e := rfl
/-
We want to show that add' give to R[ε] abelian group structure
we print the axiom ! 
-/
#print add_comm_group
/-
There is a lot of axiom 
add_comm_group.add : Π {α : Type u} [c : add_comm_group α], α → α → α
add_comm_group.add_assoc : ∀ {α : Type u} [c : add_comm_group α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
add_comm_group.zero : Π (α : Type u) [c : add_comm_group α], α
add_comm_group.zero_add : ∀ {α : Type u} [c : add_comm_group α] (a : α), 0 + a = a
add_comm_group.add_zero : ∀ {α : Type u} [c : add_comm_group α] (a : α), a + 0 = a
add_comm_group.neg : Π {α : Type u} [c : add_comm_group α], α → α
add_comm_group.add_left_neg : ∀ {α : Type u} [c : add_comm_group α] (a : α), -a + a = 0
add_comm_group.add_comm : ∀ {α : Type u} [c : add_comm_group α] (a b : α), a + b = b + a
-/
def neg' :  (R[ε]) → (R[ε]) := λ a, {a_0 := - a.a_0, a_e := -a.a_e}

instance : has_neg(R[ε]) := ⟨neg' R⟩
@[R_exp_]lemma neg_ext_0 (a : R[ε]) : (-a).a_0 = -a.a_0  := rfl
@[R_exp_]lemma neg_ext_e (a : R[ε]) : (-a).a_e = -a.a_e  := rfl


lemma add_assoc' (a b c : R[ε]) : a + b + c = a+(b+c) := begin ext, R_exp__ring, end 
lemma zero_add' (a : R[ε]) : 0 + a = a:= begin ext, R_exp__ring, end
lemma add_zero' (a : R[ε]) : a+ 0 = a:= begin ext, R_exp__ring, end
lemma add_left_neg'  (a : R[ε]) :  -a + a = 0 := begin ext,R_exp__ring, end
lemma add_comm'   (a b : R[ε]) :  a + b = b + a :=begin ext,R_exp__ring,end 

#print comm_ring
/-
structure comm_ring : Type u → Type u
fields:
comm_ring.add : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.add_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
comm_ring.zero : Π (α : Type u) [c : comm_ring α], α
comm_ring.zero_add : ∀ {α : Type u} [c : comm_ring α] (a : α), 0 + a = a
comm_ring.add_zero : ∀ {α : Type u} [c : comm_ring α] (a : α), a + 0 = a
comm_ring.neg : Π {α : Type u} [c : comm_ring α], α → α
comm_ring.add_left_neg : ∀ {α : Type u} [c : comm_ring α] (a : α), -a + a = 0
comm_ring.add_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a + b = b + a
comm_ring.mul : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.mul_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
comm_ring.one : Π (α : Type u) [c : comm_ring α], α
comm_ring.one_mul : ∀ {α : Type u} [c : comm_ring α] (a : α), 1 * a = a
comm_ring.mul_one : ∀ {α : Type u} [c : comm_ring α] (a : α), a * 1 = a
comm_ring.left_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * (b + c_1) = a * b + a * c_1
comm_ring.right_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), (a + b) * c_1 = a * c_1 + b * c_1
comm_ring.mul_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a * b = b * a
-/
def mul'  : (R[ε]) → (R[ε]) →  (R[ε]) := λ a b,begin exact
{a_0 := a.a_0 * b.a_0, a_e := a.a_0 * b.a_e+ a.a_e * b.a_0}
end
instance : has_mul (R[ε]) := ⟨mul' R⟩
@[R_exp_]lemma mul_ext_0 (a b : R[ε]) : (a * b).a_0 = a.a_0 * b.a_0 := rfl
@[R_exp_]lemma mul_ext_e (a b : R[ε]) : (a*b).a_e =a.a_0 * b.a_e+ a.a_e * b.a_0 := rfl
lemma mul_assoc' ( a b c : R[ε]) : a * b * c = a * (b * c) := begin ext, R_exp__ring, end 

def one  : R[ε] := of R (1 : R)

instance : has_one (R[ε] ) := ⟨one R⟩
@[R_exp_]lemma one_ext_0 : (1 : R[ε]).a_0 = 1  := rfl
@[R_exp_]lemma one_ext_e : (1 : R[ε]).a_e = 0  := rfl

lemma one_mul' (a : R[ε]) : 1 * a = a := begin ext, R_exp__ring,end
lemma mul_one' (a : R[ε]) : a * 1 = a := begin ext, R_exp__ring,end
lemma left_distrib' (a b c :  R[ε]) :  a * (b + c) = a * b + a * c := begin ext, R_exp__ring,end 
lemma right_distrib' (a b c :  R[ε]) :  (a + b) *c = a * c + b * c := begin ext, R_exp__ring,end 
lemma mul_comm' (a b : R[ε]) :  a * b = b * a := begin ext, R_exp__ring, end

instance : comm_ring (R[ε]) := 
  { add                  := add' R,
    add_assoc            := add_assoc' R,
    zero                 := 0,
    zero_add             := zero_add' R,
    add_zero             := add_zero' R,
    neg                  := neg' R,
    add_left_neg         := add_left_neg' R,
    add_comm             := add_comm' R,
    mul                  := mul' R, 
    mul_assoc            := mul_assoc' R,
    one                  := 1,
    one_mul              := one_mul' R,
    mul_one              := mul_one' R,
    left_distrib         := left_distrib' R, 
    right_distrib        := right_distrib' R,
    mul_comm             := mul_comm' R,
    }

variables (A B : Type)[comm_ring A][comm_ring B](f : ring_hom A B) 
def map {A B : Type}[comm_ring A][comm_ring B](f : ring_hom A B) :  (A[ε]) → (B[ε]) :=  λ a, begin 
 exact {a_0 := f a.a_0, a_e := f a.a_e},
end 
@[R_exp_]lemma map_ext_0 (f : ring_hom A B) (a : A[ε]): (map f a).a_0  = f a.a_0 := rfl
@[R_exp_]lemma map_ext_e (f : ring_hom A B) (a : A[ε]): (map f a).a_e  = f a.a_e := rfl
@[R_exp_]lemma map_one {A B : Type}[comm_ring A][comm_ring B](f : ring_hom A B) : (map f 1) = 1 := begin
ext,
rw [map_ext_0,one_ext_0,one_ext_0],
rw f.map_one,
rw [map_ext_e,one_ext_e,one_ext_e],
rw f.map_zero,
end
@[R_exp_]lemma map_zero {A B : Type}[comm_ring A][comm_ring B](f : ring_hom A B) : (map f 0) = 0 := begin
ext,
rw [map_ext_0,zero_ext_0,zero_ext_0],
rw f.map_zero,
rw [map_ext_e,zero_ext_e,zero_ext_e],
rw f.map_zero,
end
@[R_exp_]lemma map_add {A B : Type}[comm_ring A][comm_ring B](f : ring_hom A B) (a b : A[ε]) : 
(map f (a+b)) = map f a + map f b := begin
ext, rw [map_ext_0,add_ext_0,add_ext_0,f.map_add,map_ext_0,map_ext_0],
rw [map_ext_e,add_ext_e,add_ext_e,f.map_add,map_ext_e,map_ext_e],
end
@[R_exp_]lemma map_mul {A B : Type}[comm_ring A][comm_ring B](f : ring_hom A B) (a b : A[ε]) : 
(map f (a * b)) = map f a * map f b := begin 
ext, rw [map_ext_0,mul_ext_0,mul_ext_0,f.map_mul,map_ext_0,map_ext_0],
rw [map_ext_e,mul_ext_e,f.map_add,mul_ext_e,f.map_mul,f.map_mul,map_ext_0,map_ext_e,map_ext_e,map_ext_0],
end
instance has_repr [has_repr R] : has_repr(R[ε])  := ⟨λ x,   repr x.a_0 ++ "+" ++ repr x.a_e ++ "ε"⟩
def e  := ε(ℤ)  
#print ring_hom.mk
def map_ (f : ring_hom A B) :=  ring_hom.mk (map f) (map_one f) (map_mul f) (map_zero f) (map_add f)
def Rε  : CommRing ⥤ CommRing  :=  
{ obj := λ R, CommRing.of( R_exp R), 
  map := λ R R' f,  (map_  R R' f), 
}
#print Rε
theorem representable (A : CommRing)(a : A) : (a^2 = 0) → (ℤ [ε]) →  A := λ certificat x, begin 
exact x.a_0+a*x.a_e,
end 

end R_exp