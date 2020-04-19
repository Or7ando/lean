import .X
import .Idem
import group_theory.group_action
open X
namespace idem_action_X
def mul_action' (R : Type)[comm_ring R] : Idem(R) → X(R) → X(R) := λ g η,
begin
    exact {
        x := g.e * (η.x-η.y)  +  η .y,
        y := η.x + g.e * (η .y -η.x) ,
        inv := η.inv,
        certif := 
            begin 
                have h : g.e * (η.x - η.y) + η.y - (η.x + g.e * (η.y - η.x)) = g.e * (η.x - η.y) - (1-g.e) * (η.x - η.y),
                  ring,
                rw h,
                rw ← Idem.Idem.calculus.square_idem,
                exact η.certif,
            end 
    }
end
instance (R : Type)[comm_ring R] : has_scalar (Idem(R)) (X(R)) := ⟨mul_action' R⟩ 
variables (R :Type)[comm_ring R]
lemma mul_action_comp_x  (g : Idem R)  (η : X R): (g • η).x = g.e * (η.x-η.y)  +  η.y  :=  rfl
lemma mul_action_comp_y  (g : Idem R)  (η : X R): (g • η).y = η.x + g.e * (η .y -η.x)  :=  rfl
lemma mul_action_comp_inv  (g : Idem R)  (η : X R): (g • η).inv = η.inv   :=  rfl
--- Ecrire un revriter ! 
open Idem
open X
meta def idem_ring : tactic unit :=
`[simp only [one_e, mul_action_comp_x,mul_action_comp_y, e_comp], ring]

run_cmd add_interactive [`idem_ring]
def one_smul' (η : X R) : (1 : Idem R) •  η = η  := begin 
    ext ; idem_ring,
end  
def mul_smul' (g1 g2 : Idem R) (η : X(R)) : (g1 * g2) • η  = g1 • g2 • η :=
begin 
    ext ; idem_ring,
end
instance (R : Type)[comm_ring R]: mul_action (Idem R) (X(R)) := ⟨ one_smul' R, mul_smul' R⟩
open mul_action
def A := orbit_rel (Idem (R)) (X(R))
#check (A(R)).r


end idem_action_X
