import group_representation
import linear_algebra.determinant
import linear_algebra.matrix
open linear_map
open MY_TEST              ------------------- cvlasse de matrice n'est pas opérationnelle !
universe variables u v w 
open matrix
variables {G : Type u} {R : Type v} [group G] [comm_ring R] 
variables {n : Type u} [fintype n] [decidable_eq n] 
variables (ρ : group_representation G R (n → R))
variables (g : G)   
def to_matrix' (ρ : group_representation G R (n → R))(g : G) :  matrix n n R :=  to_matrix (⟦ρ ⟧ g) 
lemma proof_strategy (A B : matrix n n R) : to_lin A = to_lin B → A = B := begin 
     intro hyp,
     have RR : to_matrix (to_lin A) = to_matrix (to_lin B),
          congr',
     iterate 2 {rw  to_lin_to_matrix  at RR},
     exact RR,
end
def χ (ρ : group_representation G R (n → R)) : G →  R := λ g,  matrix.trace n R R (to_matrix  (⟦ ρ ⟧  g))


lemma to_matrix_mul (g1 g2 : G) : 
to_matrix (⟦ρ ⟧ g1) * to_matrix (⟦ρ ⟧ g2) = to_matrix (⟦ρ ⟧ (g1 * g2) ) := begin 
     apply proof_strategy,
     rw mul_eq_mul,
     rw mul_to_lin,
     iterate 2 {rw  to_matrix_to_lin },
     rw ← rmap_mul,
     rw to_matrix_to_lin,
end  
lemma to_matrix_one : to_matrix (⟦ρ⟧ 1) = 1 := begin 
     rw rmap_one,
     apply proof_strategy,
     rw to_matrix_to_lin,
     rw to_lin_one,
end
lemma χ_comm :  ∀ t s : G, χ ρ (t * s ) = χ ρ (s * t) := begin 
     intros s t,
     unfold χ, rw ← to_matrix_mul,
     rw mul_eq_mul,
     rw trace_mul_comm,
     rw ←  mul_eq_mul,
     rw to_matrix_mul,  
end
theorem central_function : ∀ t s : G, χ ρ (t*s*t⁻¹ ) = χ ρ s := begin 
     intros s t, 
     rw  mul_assoc,
     rw χ_comm ρ  s (t * s⁻¹),
     rw  mul_assoc,
     rw inv_mul_self,rw group.mul_one, 
end
theorem χ_one : χ ρ 1 =  fintype.card n := begin 
     unfold χ, rw to_matrix_one, rw trace_one,
end

/-
     For the moment not nice matrix strategy i have to lear a little 
-/
lemma to_matrix_id : to_matrix (linear_map.id : (n →  R)→ₗ(n → R)) = (1 : matrix n n R) := begin 
     apply proof_strategy,
     rw to_lin_one,
     rw to_matrix_to_lin,
end
lemma det_mul' (g1  g2 : G) : det (to_matrix (⟦ρ ⟧ g1)) * det (to_matrix (⟦ρ ⟧ g2)) = det (to_matrix (⟦ρ ⟧ (g1*g2))) :=
begin
     rw ← det_mul,rw ← mul_eq_mul,rw to_matrix_mul,
end
lemma one_mul' (g : G) :   det (to_matrix (⟦ρ ⟧ g)) * det (to_matrix (⟦ρ ⟧ g⁻¹ )) = (1 : R) := begin 
     rw det_mul',rw_simp,rw to_matrix_id,rw det_one,
end
