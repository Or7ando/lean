import tactic.ring
import tactic.ring_exp
import data.finset
import data.finsupp
import data.nat.choose
import algebra.category.CommRing.basic
import data.fin
import data.finset
open CommRing
open finset

---          Goal : understand the notion of structure with a little exemple !
namespace co_maxi         
structure comax {R : Type*}[comm_ring R] (a b : R)  :=   --- ici c'est est ce que a et b sont comaximaux 
(u : R)(v : R)
(certificat : a * u + b * v = (1 : R))
#print comax
local infix     ⊥  :=  comax   --- notation 
structure comax_hom (A : Type*) (B : Type*)[comm_ring A] [comm_ring B] (a1 a2: A)(b1 b2 : B) :=
    (hom : ring_hom A  B)
    (hom_comp_point : hom a1 = b1 ∧ (hom a2 = b2))


open is_ring_hom  --- to have acces map_mul map_one 
def comp (A B: Type)(φ : A → B)[comm_ring A][comm_ring B][is_ring_hom φ] (a b : A) : (comax a b) → comax (φ a) (φ b) := λ ⟨u_ab,v_ab,certificat_ab⟩, --- {} or ⟨ ⟩ λ OBJET and then OBJET.u etc 
    begin
        have certificat : (φ a) * (φ u_ab) + (φ b) * (φ v_ab) = 1,          -- It's trivial ring identity, but i have to control ! 
            rw [ ←  map_mul φ, ← map_mul φ , ← map_add φ,certificat_ab],
            apply map_one,
        exact {u := φ u_ab,v := φ v_ab,certificat := certificat},            --- the constructor of structure  : i thinck better than  ⟨  ⟩ 
    end

end co_maxi
namespace Exemple
--- This is a closed universe   
#print Ring
--- but we have access to the primitive structure
#print co_maxi.comax -- we have to co_maxi. first to acces comax ! 
end Exemple 
open co_maxi
namespace comax
section 
parameters  {R : Type}[comm_ring R]
parameters (a b c : R)
local infix     ⊥  :=  comax   --- notation 


def symm  :  (a) ⊥  (b)  →   (b) ⊥ (a)   :=   --- a u + b v = 1 → b v + a u = 1 
    λ ⟨u,v,certificat⟩,    
        begin   
            have  t :  b * v + a * u = 1, 
                rw add_comm,  assumption,
            use ⟨v,u,t⟩,
        end 
lemma one_perp  :  1 ⊥ a :=   --- with 1 * 1 + a * 0 = 1 
begin 
    have h: 1 * 1 + a * 0 = 1,
        rw [one_mul,mul_zero,add_zero],
    use ⟨1,0,h⟩
end
lemma abab_trick : (a ⊥ c) → (b ⊥ c) → (a * b) ⊥ c :=    ---  Trick to simplify proof !  if a ⊥ c and b ⊥ c then ab ⊥ c  from calculus !  
    λ ⟨ua,va,ka⟩  ⟨ub,vb,kb⟩, 
        begin 
            have J : (a * b) * ( ua * ub) + c * ( a * ua * vb + va * b * ub + va * c * vb) = 1,
                 by calc 
                    (a * b) * ( ua * ub) + c * ( a * ua * vb + va * b * ub + va * c * vb)  =  (a * ua + c * va) * (b * ub + c * vb) : by ring_exp
                    ...                                                                    =   1                                    : by rw [ka,kb, one_mul],
        use ⟨ ua * ub,  a * ua * vb + va * b * ub + va * c * vb , J⟩,
        end
open nat
lemma star (a  b : R) (n : nat):   (a ⊥ b) → ((a^n) ⊥ b)  := 
    λ u,
        nat.rec_on n
                (show  (a^0) ⊥ b, {rw pow_zero a, apply one_perp, })
                (assume n, assume re : ((a^n) ⊥ b), show (a^(n+1)) ⊥ b,
                       {rw pow_succ a n,apply abab_trick, assumption,assumption})

theorem My_favorite_localisation_lemma (n m : nat) : (a ⊥ b) → (a^n) ⊥ (b^m) :=                 --- the goals 
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
parameters (f g : R)

structure localy_zero (a : R) extends  comax(f)(g) := 
(m : ℕ)(n : ℕ)
(proof_localy_zero : f^m * a = 0 ∧ g^n * a = 0)

theorem Separation_axiom (a : R) : f ⊥ g → localy_zero (a)   →   a = 0  :=  λ coma ⟨t,m,n,proof_localy_zero ⟩,
begin 
     have H : (f^m) ⊥ (g^n),
        apply My_favorite_localisation_lemma,
        assumption,
    rcases H with ⟨ua,va,ka⟩,
        apply eq.symm,
        have H :  0  = (f ^ m * a* ua  +  g ^ n *a * va),
            rw [proof_localy_zero.1,proof_localy_zero.2],
            apply eq.symm,
            rw [zero_mul,zero_mul,add_zero],
        have G : (f ^ m * a* ua  +  g ^ n *a * va) = (f ^ m * ua  +  g ^ n  * va) * a,
        ring,
        rewrite [H,G,ka,one_mul a], 
end 
---   Gluing_axiome : 
---
structure descent_data (s_f s_g : R)(n : ℕ) extends f ⊥ g  :=    --- comment est structuré la notion de desc
(m : ℕ)                                                                      ---   F : N →₀ R  + certiticat F^⊥ : N →₀ R  co-max 
(proof_m : f^m * g^(n+m) * s_f = g^m * f^(n+m) * s_g )                       ---   là j'ai accées a des fonctions touts faites 
                                                                             ---    --->  F,  :::  s_F : ℕ  → R  et  n_F : N → ℕ   
                                                                             ---    ' ζ_f :=  s_f / f^n_f ' (data)
parameters s_f s_g : R                                                       ---    descent data + ∃ m_f t q  (f,g) ---> certificat f g
parameters n : ℕ                                                             ---   

structure effective_descente_data  extends descent_data s_f  s_g n:=
( s : R)
(N_f : ℕ) (N_g : ℕ)
(proof_n_plus_m_f_g : f^(N_f+n) * s = f^N_f * s_f ∧  g^(N_g+n) * s = g^N_g * s_g)


set_option class.instance_max_depth 20
theorem gluing_data  :   f ⊥ g →      descent_data s_f s_g n    →   effective_descente_data  := 
         λ comma,λ y, 
            begin
                rcases comma with ⟨u,v,proof_of_comax⟩,
                rcases y with ⟨t,m,proof_m⟩,  
                have H: (f^(n+m)) ⊥ (g^(n+m)),
                    apply My_favorite_localisation_lemma,
                assumption,
            rcases H with ⟨vf,vg,proof_n_plus_m_f_g⟩,

            have H1 : f ^ (m + n) * (vf * s_f * f ^ m + vg * s_g * g ^ m) =   ( f ^ (n + m)* vf * s_f * f ^ m +  g ^ m *f ^ (n + m) *s_g * vg), 
                        ring_exp,
                        
            have B1 : f ^ (n + m) * vf * s_f * f ^ m + f ^ m * g ^ (n + m) * s_f * vg = f^m *s_f *(f ^ (n + m) * vf + g ^ (n + m) * vg), 
                           ring, 
            
            have H2 : g ^ (m + n) * (vf * s_f * f ^ m + vg * s_g * g ^ m) =      f ^ m *g ^ (n+m) *s_f *vf + g ^ m* g ^ (n + m) * vg * s_g,
                  ring_exp,

            have B2 : g ^ m * f ^ (n + m) * s_g * vf + g ^ m * g ^ (n + m) * vg * s_g = g^m * s_g *(f ^ (n + m) * vf + g ^ (n + m) * vg ), 
                      ring,
            have Y : f^(m+n) * (vf *s_f * f^m+ vg*s_g*g^m) = f^m * s_f ∧  g^(m+n) * (vf *s_f * f^m+ vg*s_g*g^m) = g^m * s_g,
                split,
                rw [H1,eq.symm proof_m,B1,proof_n_plus_m_f_g,mul_one],
                rw [H2,proof_m,B2, proof_n_plus_m_f_g,mul_one],
            exact {to_descent_data := ⟨t,m,proof_m⟩, s := vf *s_f * f^m+ vg*s_g*g^m, N_f := m, N_g := m, proof_n_plus_m_f_g := Y},
end

#check gluing_data

end co_maxi


