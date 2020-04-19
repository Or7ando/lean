import .sous_foncteur
import category_theory.elements
import .A2
open category_theory
open A2 
open int
-- universes  v u
lemma int_commute_with_morph  {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f](n : ℕ) : ∀ x : A, f( n*x ) = n *(f x) := λ x,
    nat.rec_on n (show  f(0*x) = 0* (f x), {rw [zero_mul,zero_mul], exact is_ring_hom.map_zero f, })
        (assume n, assume rec_hyp : f(n * x) = n *(f x),
            show f( (n+1)*x) = (n+1)*(f(x)),{
                rw [right_distrib,right_distrib,one_mul,one_mul,← rec_hyp,is_ring_hom.map_add f],
            })
structure A2_disc(R : Type )[comm_ring R] :=
(ζ : A2 R)
(inv_disc : R)
(certif_disc : (ζ.a * ζ.a - ↑4 * ζ.b ) * inv_disc = 1)
namespace A2_disc 
section
variables {R : Type } [comm_ring R]
--- idée faire des lemmes simplificateurs ! 
lemma disc :  ∀ {ζ1 ζ2 : A2_disc R}, ζ1.ζ = ζ2.ζ → ((ζ1.ζ.a = ζ2.ζ.a) ∧ (ζ1.ζ.b = ζ2.ζ.b)) := 
begin 
    intros ζ1 ζ2,
    intro h, 
    split,
    apply congr_arg, assumption,
    apply congr_arg, assumption,
end 
lemma disc_ :  ∀ {ζ1 ζ2 : A2_disc R}, ζ1.ζ = ζ2.ζ  →  (ζ1.ζ.a * ζ1.ζ.a - ↑4 * ζ1.ζ.b ) = (ζ2.ζ.a * ζ2.ζ.a - ↑4 * ζ2.ζ.b ) := 
begin 
    intros ζ1 ζ2,
    intro h,
    have H : ((ζ1.ζ.a = ζ2.ζ.a) ∧ (ζ1.ζ.b = ζ2.ζ.b)),
        apply disc,
        assumption,
    rw H.1,
    rw H.2,
end 
    lemma inverse_unique (a b c d: R) : a * c = 1 → d * b = 1 → a = d → c = b := λ h1 h2 h3, begin  --- remettre dans l'ordre
        have : c = (a * b) * c,
            rw h3,
            rw h2,
            rw one_mul c,
        rw this,
        rw [mul_assoc, mul_comm b c,← mul_assoc,h1, one_mul],
        end 
    @[ext] lemma ext :  ∀ {ζ1 ζ2 : A2_disc R}, (ζ1.ζ  = ζ2.ζ)  → ζ1 = ζ2 := λ ζ1 ζ2,
        begin 
            intro h, 
            cases ζ1, 
            cases ζ2,
            congr ; try { assumption },
            apply inverse_unique,
            exact ζ1_certif_disc,
            exact ζ2_certif_disc,
            exact  disc_ h,
        end 
open is_ring_hom
def map_A2_disc {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] : A2_disc A → A2_disc B := λ η,  begin  
    have  h : ((f η.ζ.a) * (f η.ζ.a)  - (  ↑4 * (f η.ζ.b ))) * (f η.inv_disc) = 1,
            have j :    f( ↑4* η.ζ.b) = ↑4 * (f η.ζ.b ),
                exact int_commute_with_morph f (4) (η.ζ.b),
            rw [← j,← map_mul f,← map_sub f,← map_mul f,η.certif_disc],
            exact map_one f,
    exact { ζ := {a := f η.ζ.a, b := f η.ζ.b},
          inv_disc :=  f η.inv_disc,
          certif_disc :=  h,},
    end
lemma map_comp_a {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] (ζ : A2_disc (A) ) : (map_A2_disc f ζ).ζ.a = f ζ.ζ.a := rfl
lemma map_comp_b {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] (ζ : A2_disc (A) ) : (map_A2_disc f ζ).ζ.b = f ζ.ζ.b := rfl
lemma map_comp_inv_disc {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] (ζ : A2_disc (A) ) : (map_A2_disc f ζ).inv_disc = f ζ.inv_disc := rfl
def 𝔸2_disc: CommRing ⥤ Type  :=  
{ obj := λ R, A2_disc R,
  map := λ R R' f, map_A2_disc f, 
}

-- def A :=   (functor.elements) (𝔸2_disc)
end 
end A2_disc
