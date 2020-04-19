
set_option profiler true

open polynomial

example (R : Type) [comm_ring R] (x : R) :
  (1 + x^2 + x^4 + x^6) * (1 + x) = 1+x+x^2+x^3+x^4+x^5+x^6+x^7 :=
by ring -- 5 seconds

example (R : Type) [comm_ring R] :
  (1 + X^2 + X^4 + X^6 : polynomial R) * (1 + X) = 1+X+X^2+X^3+X^4+X^5+X^6+X^7 :=
by ring -- 18 seconds