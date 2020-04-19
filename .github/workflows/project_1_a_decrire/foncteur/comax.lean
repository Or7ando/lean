import tactic.ring
import tactic.ring_exp
import algebra.category.CommRing.basic

open CommRing

universes v u  
local notation ` Ring `     :=    CommRing.{u}
local notation ` Set  `     :=    Type u 

---          Study of co-maximal familly ! I do the job why two elements for the moment  ! 
---          This is good file ! 
namespace co_maxi
variables (R : Type u) [comm_ring.{u} R ] 

def co_max  (a b : R)    := 
             ∃ u v :  R,    a * u + b * v = 1 

local infix     ⊥  :=  co_max R   --- notation 
lemma one_perp (a : R)    :  1 ⊥ a :=   --- with 1 * 1 + a * 0 = 1 
begin 
    have h: 1 * 1 + a * 0 = 1,
        rw [one_mul,mul_zero,add_zero],
    use ⟨1,0,h⟩
end
lemma symm (a b : R) : (a ⊥ b) →  (b ⊥ a)  :=   --- a u + b v = 1 → b v + a u = 1 
    λ ⟨u,v,k⟩,    
        begin   
            have  t :  b * v + a * u = 1, 
                rw add_comm,  assumption,
            use ⟨v,u,t⟩,
        end 

lemma abab_trick (a b c : R) : (a ⊥ c) → (b ⊥ c) → (a * b) ⊥ c :=    ---  Trick to simplify proof !  if a ⊥ c and b ⊥ c then ab ⊥ c  from calculus !  
    λ ⟨ua,va,ka⟩  ⟨ub,vb,kb⟩, 
        begin 
            have J : (a * b) * ( ua * ub) + c * ( a * ua * vb + va * b * ub + va * c * vb) = 1,
                 by calc 
                    (a * b) * ( ua * ub) + c * ( a * ua * vb + va * b * ub + va * c * vb)  =  (a * ua + c * va) * (b * ub + c * vb) : by ring_exp
                    ...                                                                    =   1                                    : by rw [ka,kb, one_mul],
        use ⟨ ua * ub,  a * ua * vb + va * b * ub + va * c * vb , J⟩,
        end
---- We do the big calculus, now is trivial induction !  
---- for exemple a ⊥ c →  a^2 ⊥ c  using abab_trick a a c !  induction ... 
open nat
lemma star (a  b : R) (n : nat):   (a ⊥ b) → ((a^n) ⊥ b)  := 
    λ u,
        nat.rec_on n
                (show  (a^0) ⊥ b, {rw pow_zero a, apply one_perp, })
                (assume n, assume re : ((a^n) ⊥ b), show (a^(n+1)) ⊥ b,
                       {rw pow_succ a n,apply abab_trick, assumption,assumption})

theorem My_favorite_localisation_lemma (a b : R) (n m : nat) : (a ⊥ b) → (a^n) ⊥ (b^m) :=                 --- the goals 
    λ u, begin  
        apply star,
        apply symm,    -- is there a repeat method ? How to programme such method ? 
        apply star,
        apply symm,
        assumption,
    end
---- 
---     We want to proof 𝔸 is a local functor : a scheaf for global Zariski for Affᵒᵖ. 
----   ( Note 𝔸 is structural for Ring so if you do the job for 𝔸 you do the job for all ring i.e Spec R := Hom(R,•) is a scheme (in sense of functorial geometry)
---    (ref Jantzen : 'algebraic group and representation' the first chapter) for all ring R : i can explain) ! 
---                 for the moment only with 2-covering famillies 
---     There is two axioms : 
---             1/ Separation : (for two elements ONLY)
---                      let R : comm_ring
---                      Let f,g ∈ R :  f ⊥ g. 
---                      Let a ∈ R : 
---                             ∃ m n : ℕ,  f^m a = 0 ∧  g^n a = 0   --- i.e a = 0 in localisation  {f^k k ∈ N⋆} and   {g^k k ∈ N⋆}
---                      Since f ⊥ g , we have f^m ⊥ b^n 
---                      Have (u,v) s.t   f^m u + g^n v = 1
---                      multipliying by a give f^m au  + g^n a v = a  so 0 = a ! 
---    Note : i don't use Localisation library for the moment (i have to study) !  
theorem Separation_axiom (a : R) (f g : R) : f ⊥ g → ( ∃ m n : ℕ, f^m * a = 0 ∧ g^n * a = 0 )   →   a = 0  :=  λ certif  ⟨m,n,proof⟩,
begin 
    have H : (f^m) ⊥ (g^n),
        apply My_favorite_localisation_lemma,
        assumption,
    rcases H with ⟨ua,va,ka⟩,
        apply eq.symm,
        have H :  0  = (f ^ m * a* ua  +  g ^ n *a * va),
            rw [proof.1,proof.2],
            apply eq.symm,
            rw [zero_mul,zero_mul,add_zero],
        have G : (f ^ m * a* ua  +  g ^ n *a * va) = (f ^ m * ua  +  g ^ n  * va) * a,
        ring,
        rewrite [H,G,ka,one_mul a], 
end 
---   Gluing_axiome : 
---
set_option class.instance_max_depth 20
theorem gluing_data (f g : R)(s_f s_g : R) (n : ℕ) :
         f ⊥ g → (∃ m : ℕ, f^m * g^(n+m) * s_f = g^m * f^(n+m) * s_g) →  (∃ s : R, ∃ N_f N_g : ℕ, f^(N_f+n) * s = f^N_f * s_f ∧  g^(N_g+n) * s = g^N_g * s_g) := 
         λ certif ⟨m,proof_m⟩, begin
            have H: (f^(n+m)) ⊥ (g^(n+m)),
                apply My_favorite_localisation_lemma,
                assumption,
            rcases H with ⟨vf,vg,proof_n_plus_m_f_g⟩,
            existsi [vf *s_f * f^m+ vg*s_g*g^m,m,m],
                split,
                    have H : f ^ (m + n) * (vf * s_f * f ^ m + vg * s_g * g ^ m) =   ( f ^ (n + m)* vf * s_f * f ^ m +  g ^ m *f ^ (n + m) *s_g * vg), 
                        ring_exp,
                        rw [H,eq.symm proof_m],
                            have B : f ^ (n + m) * vf * s_f * f ^ m + f ^ m * g ^ (n + m) * s_f * vg = f^m *s_f *(f ^ (n + m) * vf + g ^ (n + m) * vg), 
                            ring, 
                            rw [B,proof_n_plus_m_f_g,mul_one], 
                    have H : g ^ (m + n) * (vf * s_f * f ^ m + vg * s_g * g ^ m) =      f ^ m *g ^ (n+m) *s_f *vf + g ^ m* g ^ (n + m) * vg * s_g,
                        ring_exp,
                    rw [H,proof_m],
                        have B : g ^ m * f ^ (n + m) * s_g * vf + g ^ m * g ^ (n + m) * vg * s_g = g^m * s_g *(f ^ (n + m) * vf + g ^ (n + m) * vg ), 
                        ring,
                        rw [B,proof_n_plus_m_f_g,mul_one],
end

#explode gluing_data

end co_maxi
