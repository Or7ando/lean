import .global
import .Spec
open Spec
universes  u

local notation `Ring` := CommRing.{u}
local notation `Set` :=  Type u  
namespace INITIAL_OBJ
def initial := Spec ℤ 

end INITIAL_OBJ