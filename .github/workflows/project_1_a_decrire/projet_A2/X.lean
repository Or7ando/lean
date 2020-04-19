import .A2_disc
open A2_disc
open is_ring_hom
lemma power_commute_with_morph  {A B :Type}[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f](n : ℕ) : ∀ x : A, f( x^n ) = (f x)^n := λ x,
    nat.rec_on n (show  f(x^0) = (f x)^0, {rw [pow_zero x,pow_zero (f x)], exact map_one f,})
        (assume n, assume rec_hyp : f(x^n) = (f(x))^n,
            show f(x^(n+1)) = (f(x))^(n+1),{rw [pow_succ x n,pow_succ (f(x)) n,← rec_hyp],exact map_mul (f)})
structure X (R : Type)[comm_ring R] :=  
    (x y : R) 
    (inv  : R)
    (certif : (x-y)^2 * inv = 1) 
namespace X
    section
        variables {R : Type} [comm_ring R]
        lemma diec_certif : ∀ {ζ1 ζ2 : X R}, (ζ1.x  = ζ2.x) →  (ζ1.y  = ζ2.y) → (ζ1.x - ζ1.y)^2 =  (ζ2.x - ζ2.y)^2 := 
        begin   
            intros ζ1 ζ2,
            intros h1 h2, 
            rw [h1,h2],
        end 
        @[ext] lemma ext  : ∀ {ζ1 ζ2 : X R}, (ζ1.x  = ζ2.x) →  (ζ1.y  = ζ2.y)  → ζ1 = ζ2 := λ ζ1 ζ2, 
        begin 
            intro hx, 
            intro hy,
            cases ζ1, 
            cases ζ2,  
            congr; try {assumption},
            apply A2_disc.inverse_unique,
            exact ζ1_certif, 
            exact ζ2_certif,
            exact diec_certif hx hy,
        end 
        
        def map_X {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] : X A → X B := λ η, 
            begin
                exact {x := f η.x, y := f η.y, inv := f η.inv,certif := 
                begin
                    rw [← map_sub f,← power_commute_with_morph f,← map_mul f,η.certif],
                    exact map_one f, 
                end    }
            end
        lemma map_comp_x {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] (ζ : X (A) ) : (map_X f ζ).x = f ζ.x := rfl
        lemma map_comp_y {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] (ζ : X (A) ) : (map_X f ζ).y = f ζ.y := rfl
        lemma map_comp_inv {A B :Type }[comm_ring A][comm_ring B](f : A →  B)[is_ring_hom  f] (ζ : X (A) ) :
            (map_X f ζ).inv = f ζ.inv := rfl    
        def 𝕏 : CommRing ⥤ Type :=  
        { obj := λ R, X R,
        map := λ R R' f, map_X f, 
        }
    end 
    #print 𝕏 
end X