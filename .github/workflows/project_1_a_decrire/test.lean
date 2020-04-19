example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
  conv
  begin          -- | a * (b * c) = a * (c * b)
    to_lhs,      -- | a * (b * c)
    congr,       -- 2 goals : | a and | b * c
    skip,        -- | b * c
    rw mul_comm, -- | c * b
  end
end
example : (λ x : ℕ, 0 + x) = (λ x, x) :=
begin
  conv
  begin           -- | (λ (x : ℕ), 0 + x) = λ (x : ℕ), x
    to_lhs,       -- | λ (x : ℕ), 0 + x
    funext,       -- | 0 + x
    rw zero_add,  -- | x
  end
end
example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
conv in (b*c)
begin          -- | b * c
  rw mul_comm, -- | c * b
end
end
meta def find_matching_type (e : expr) : list expr → tactic expr
| []         := tactic.failed
| (H :: Hs)  := do t ← tactic.infer_type H,
                   (tactic.unify e t >> return H) <|> find_matching_type Hs
meta def my_assumption : tactic unit :=
do { ctx ← tactic.local_context,
     t   ← tactic.target,
     find_matching_type t ctx >>= tactic.exact }
<|> tactic.fail "my_assumption tactic failed"
meta def my_first_tactic : tactic unit := tactic.trace "Hello, World."
meta def trace_goal' : tactic unit :=
do
 goal ← tactic.target,
 tactic.trace goal
example : 3 =2+1:=
begin
   trace_goal',
  trivial,
end

