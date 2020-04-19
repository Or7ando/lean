import linear_algebra.basic
import algebra.group.hom
import group_representation 
universe variables u v w w'
open group
open linear_map   
open linear_equiv
open submodule 
open MY_TEST group_representation
open linear_map.general_linear_group

/-
     But montrer que l'on peut construire une équivalence à partir d'un morphisme et d'une equivalence lineaire
protected structure equiv (ρ : group_representation G R M) (π : group_representation G R M') :
  Type (max w w') :=
  (f : M ≃ₗ[R] M')
  (commute : ∀(g : G), f ∘ ⟦ ρ ⟧  g = ⟦π⟧  g ∘ f)
-/
variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'}
  [group G] [ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M'] (ρ : group_representation G R M)
  (ρ' : group_representation G R M')

def symm_equiv  (φ : group_representation.equiv ρ ρ') : group_representation.equiv ρ' ρ := 
{ f := linear_equiv.symm φ.f,
  commute := begin 
               intros g, 
               have hyp1 :    (φ : M →ₗ[R] M')  ⊚ (⟦ρ⟧ g⁻¹)= (⟦ρ' ⟧ g⁻¹) ⊚  (φ : M →ₗ[R] M'), 
                    exact φ.commute g⁻¹,
               rw coersion_lin, rw_simp,
               have hyp2 : (⟦ρ⟧ g) ⊚ (inv φ) ⊚ ↑φ ⊚ ⟦ρ⟧ g⁻¹ =  (⟦ρ⟧ g) ⊚ (inv φ ) ⊚ ⟦ρ'⟧ g⁻¹ ⊚ ↑φ,
                         rw comp_assoc,rw hyp1,rw ← comp_assoc,
               iterate 2 {rw  comp_assoc at hyp2},
                rw  ← comp_assoc (inv φ) (↑φ : M →ₗ[R] M') (⟦ρ⟧ g⁻¹) at hyp2,   
                         
          end }
-- (inv φ) ⊚  (φ :  M →ₗ[R] M')  =  linear_map.id