import tactic.ring
import tactic.ring
import data.polynomial
import algebra.category.CommRing.basic
open category_theory
open functor
open CommRing
open polynomial


universe u
variable {R : Type u}


structure Gm (R : Type u) [comm_ring R] :=   --- Object ?
(val : R)
(inv : R)
(val_inv : val * inv = 1)
(inv_val : inv * val = 1)
namespace Gm
variables [comm_ring R]
------    My universe
instance : has_coe (Gm R) R := ⟨val⟩    ---- ici c'est la valeur de l'unité dans R instance ???
--- Exemple of Gm element !
def Nil_lemma_for_fun___D(a : R) : (a * a = (0 : R)) → Gm R :=
    begin
        --- My favorite commutative lemma : η^2 =0 → (1+η) × (1-η) = 1 so 1+η ∈ Gm(R) :D
        ---                               :
        intro h,
        let val_inv : (1+a)* (1-a) = 1, from
            calc
                (1+a) * (1-a) = 1*1  - a*a        : by rw [eq.symm (mul_self_sub_mul_self_eq (1) (a))]
                ...           = 1*1  - 0          : by exact congr_arg (λ l, 1*1 - l)  (h)
                ...           = 1                 : by simp,
        let inv_val : (1-a)* (1+a)= 1, from
            calc
                (1-a) * (1+a) = (1+a) * (1-a)    : by rw mul_comm
                ...          = 1                 : val_inv,
        exact ⟨1+a,1-a, val_inv,inv_val⟩
    end

protected def  linv (x : Gm R) : (Gm R) := ⟨x.inv,x.val,x.inv_val,x.val_inv⟩
--- Perhaps i can drop inv_val cause commutativity (all Ring are commutative :D)
/-- Gm herite de la structure de la multiplication de R -/
protected def mul (u₁ u₂ : Gm R) : Gm R :=
⟨u₁.val * u₂.val,
u₂.inv * u₁.inv,
have u₁.val * (u₂.val * u₂.inv) * u₁.inv = 1, by
begin
    let a  := u₁.val,
    let b  := u₂.val,
    let b' := u₂.inv,
    let a' := u₁.inv,
    show  a * (b * b') * a' = 1, from
        calc
            a * ( b * b' ) * a' =  (a * 1) * a'     : by exact congr_arg (λ l, a * l  * a')  (u₂.val_inv)
            ...                 =   a * a'          : by rw mul_one a
            ...                 =   1               : by rw u₁.val_inv,
end,
by simpa only [mul_assoc],
have u₂.inv * (u₁.inv *u₁.val) * u₂.val  = 1, by
begin
    let b'  := u₁.val,
    let a'  := u₂.val,
    let a   := u₂.inv,
    let b   := u₁.inv,
    show  a * (b * b') * a' = 1, from
        calc
            a * ( b * b' ) * a' =  (a * 1) * a'     : by exact congr_arg (λ l, a * l  * a')  (u₁.inv_val)
            ...                 =   a * a'          : by rw mul_one a
            ...                 =   1               : by rw u₂.inv_val,
end,
by simpa only [mul_assoc],  -- what is simpa  = Sympathique ???
⟩
instance : has_mul (Gm R) := ⟨Gm.mul⟩
instance : has_one (Gm R) := ⟨⟨1, 1, mul_one 1, one_mul 1⟩⟩
instance : has_inv (Gm R) := ⟨Gm.linv⟩
end Gm