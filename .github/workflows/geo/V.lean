import .global
universe u
local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  
open CommRing
namespace V_definition
variables (R : Ring)


def V_obj (S : set R)(A : Ring) : Type u := { ζ : ring_hom R A | ∀ x ∈ S, ζ (x)  = 0}  


lemma mem_V_obj (R : Ring) (S : set R)(A : Ring)(ζ: ring_hom R A) : (∀ x ∈ S, ζ (x) = 0) →   V_obj(R)(S)(A) :=
begin 
  intros h,
  exact {val := ζ, property := h}, 
end
lemma V_mem (S :set R)(A :Ring)(ζ : V_obj(R)(S)(A)) : ∀ x  ∈ S, ζ.val x = 0 := begin 
  exact ζ.property, 
end 
@[ext]lemma  ext ( R : Ring) (S : set R)(A : Ring)(ζ1 ζ2 : V_obj R S A) : ζ1.val = ζ2.val → ζ1 = ζ2 :=
begin 
            intro h, 
            cases ζ1, 
            cases ζ2,
            congr ; try { assumption },
end

def V_map (S : set R)(A B : Ring) (ψ : A ⟶ B) : V_obj(R)(S)(A) → V_obj(R)(S)(B) := λ ζ, begin 
   have Hypx : ∀ x ∈ S, ψ (ζ.val x) = 0,
      intros x h,
      rw V_mem,
      exact ψ.map_zero,
      assumption,
    exact {val :=  (ring_hom.comp ψ ( ζ.val )), property := Hypx},
end
lemma comp_val (S : set R)(A B : Ring) (ψ : A ⟶ B)(ζ : V_obj R S A) : 
 ((V_map R S A B ψ) ζ).val = ring_hom.comp ψ ζ.val := rfl
lemma one_val (S : set R)(A : Ring)(ζ : V_obj R S A) : ((V_map R S A A (𝟙A)) ζ).val = ζ.val := 
begin
     rw comp_val,
     ext,
     rw [ring_hom.comp_apply],
     exact rfl,
end
def V (S : set R) : Ring ⥤  Type u := begin
exact {
  obj := λ A : Ring, V_obj R S A, 
  map := λ A B : Ring, λ ψ : A ⟶ B, V_map R S A B ψ,   
  map_id' := λ A : Ring, begin 
     funext,
     ext,
     rw one_val,
     exact rfl,
  end 
   }
end
end V_definition