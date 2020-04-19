import group_representation
universe variables u v w 

namespace trivial_representation
/-
     Construction of trivial let (R : Ring) M module,  ρ : G →ₗ GL R M given by identity  
-/
def trivial_representation  (G :Type u)(R : Type v)(M : Type w)[group G] [ring R] [add_comm_group M] [module R M] 
          : group_representation G R M := {
                    to_fun := λ g, 1,
                    map_one' := rfl,
                    map_mul' := λ _ _, one_mul 1}

 end trivial_representation