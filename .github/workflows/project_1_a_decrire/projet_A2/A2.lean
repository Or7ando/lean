import algebra.category.CommRing.basic
import algebra.ring
import tactic
open CommRing
universes v u 

structure A2 (R : Type v)[comm_ring R] := 
(a : R)
(b : R)

namespace A2
    section
        variables {R : Type v} [comm_ring R]  
@[ext]lemma ext :  ∀ {ζ1 ζ2 : A2 R}, (ζ1.a = ζ2.a) → (ζ1.b = ζ2.b) → ζ1 = ζ2 := λ ζ1 ζ2,
    begin 
        intros h1 h2,
        cases ζ1,
        cases ζ2,
        -- let y := A2.mk ζ1_a ζ1_b,
        --     have j : y.a = ζ1_a,
        --         exact rfl,
            exact congr (congr_arg mk h1) h2,
        -- congr ; try { assumption },   --- ici je ne comprends pas trop ! Comment prouver les choses sans tatics 
    end

    end  --- end section comprendre ? 
end A2 