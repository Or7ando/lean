import algebra.ring
import tactic
import order.bounded_lattice
/--
##  It's the group functor  idem,
##  e1 × e2 = e1 e2 + (1-e1)(1-e2)
-/
structure idem (R : Type ) [comm_ring R] :=
(e : R)
(certif : e * e = e)

namespace idem

variables {R : Type} [comm_ring R]

/-! extension lemma : E = E' ↔  E.e = E'.e -/
@[ext] lemma ext : ∀ {g1 g2 : idem R}, g1.e = g2.e → g1 = g2
| ⟨_, _⟩ ⟨_, _⟩ := λ h, by congr; exact h

-- add a coercion from `idem R` to `R`
instance : has_coe (idem R) R := ⟨e⟩

-- Now if `E : idem R` you can just talk about `E : R` and this is the same as `↑E : R`
-- You don't have to put `E.e` any more

@[simp] theorem certif_def (E : idem R) : (E : R) * E = E := E.certif

def bot : idem R := {e := 0, certif := mul_zero 0}

instance : has_bot (idem R) := ⟨bot⟩

def inf (E F : idem R) : idem R :=
{ e := E * F,
  certif := by rw [(show ((E : R) * F) * (E * F) = E * E * (F * F), by ring), E.certif_def, F.certif_def]
}

-- `\glb` notation ⊓
instance : has_inf (idem R) := ⟨inf⟩

lemma inf_comm {E F : idem R} : E ⊓ F = F ⊓ E := by ext; apply mul_comm

@[simp] lemma inf_def (E F : idem R) : (↑(E ⊓ F) : R) = E * F := rfl

def le (E F : idem R) := E ⊓ F = E

-- ≤ notation
instance : has_le (idem R) := ⟨le⟩

@[simp] theorem le_def (E F : idem R) : E ≤ F ↔ (E : R) * F = E :=
⟨λ h, begin change E ⊓ F = E at h, show (E ⊓ F).e = E.e, rw h end, @ext _ _ (E ⊓ F) E⟩

instance : partial_order (idem R) :=
{ le := (≤),
  le_refl := λ E, begin ext, exact E.certif end,
  le_trans := λ E F G hEF hFG, begin
    ext,
    show (E : R) * G = E,
    rw le_def at hEF hFG,
    suffices : (E : R) * F * G = E,
    { rwa hEF at this},
    rw [mul_assoc, hFG, hEF],
  end,
  le_antisymm := λ E F hEF hFE, begin
    change E ⊓ F = E at hEF,
    rw [←hEF, inf_comm],
    exact hFE
  end }

lemma bot_le {E : idem R} : ⊥ ≤ E :=
begin
  ext,
  exact zero_mul _,
end

lemma inf_le_left {E F : idem R} : E ⊓ F ≤ E :=
begin
  suffices : (E : R) * F * E = E * F,
    simpa using this,
  rw [mul_comm, ←mul_assoc, E.certif_def],
end

lemma inf_le_right {E F : idem R} : E ⊓ F ≤ F := by rw [inf_comm]; apply inf_le_left

lemma le_inf {E F G : idem R} (hEF : E ≤ F) (hEG : E ≤ G) : E ≤ F ⊓ G :=
begin
  suffices : (E : R) * (F * G) = E,
    simpa using this,
  rw le_def at hEF hEG,
  rw [←mul_assoc, hEF, hEG],
end

instance : order_bot (idem R) :=
{ bot_le := λ _, bot_le, ..idem.has_bot, ..idem.partial_order}

instance : semilattice_inf_bot (idem R) :=
{ inf_le_left := λ _ _, inf_le_left,
  inf_le_right := λ _ _, inf_le_right,
  le_inf := λ _ _ _, le_inf,
  ..idem.has_inf, ..idem.order_bot
}

-- Should automation generate semilattice_sup_top instance
-- after this definition of inv,
-- and inv_inv and le_of_inv_le_inv?

def inv (E : idem R) : idem R :=
{ e := 1 - E,
  certif := begin
    rw [(show ((1 : R) - E) * (1 - E) = 1 - 2 * E + E * E, by ring), certif_def],
    ring,
  end
}

-- ⁻¹ notation for `inv`
instance : has_inv (idem R) := ⟨inv⟩

@[simp] theorem inv_def (E : idem R) : (↑E⁻¹ : R) = 1 - E := rfl

@[simp] theorem inv_inv (E : idem R) : E⁻¹⁻¹ = E :=
begin
  cases E with e he,
  ext,
  show 1 - (1 - e) = e,
  ring,
end

theorem eq_of_inv_eq (E F : idem R) : E⁻¹ = F⁻¹ → E = F :=
begin
  intro h,
  rw ←inv_inv E,
  rw h,
  exact inv_inv F
end

theorem le_of_inv_le_inv (E F : idem R) : E⁻¹ ≤ F⁻¹ → F ≤ E :=
begin
  intro h,
  rw le_def at h ⊢,
  have h2 : ((1 : R) - E) * (1 - F) = 1 - E,
    simpa using h,
  rw [show ((1 : R) - E) * (1 - F) = F * E - (E + F - 1), by ring, sub_eq_iff_eq_add] at h2,
  rw h2,
  ring
end

theorem inv_le_inv_of_le {E F : idem R} : E ≤ F → F⁻¹ ≤ E⁻¹ :=
begin
  intro h,
  apply le_of_inv_le_inv,
  simp [h],
end

-- I want the next part to be automatically generated
def sup (E F : idem R) := (F⁻¹ ⊓ E⁻¹)⁻¹

-- ⊔ notation (\lub)
instance : has_sup (idem R) := ⟨sup⟩

@[simp] theorem sup_def (E F : idem R) : E ⊔ F = (F⁻¹ ⊓ E⁻¹)⁻¹ := rfl

def top : idem R := ⊥⁻¹

-- ⊤ notation (\top)
instance : has_top (idem R) := ⟨top⟩

@[simp] theorem top_def : (⊤ : idem R) = ⊥⁻¹ := rfl

@[simp] theorem inv_top : (⊤ : idem R)⁻¹ = ⊥ :=
begin
  apply eq_of_inv_eq,
  simp,
end

theorem le_top {E : idem R} : E ≤ ⊤ :=
begin
  apply le_of_inv_le_inv,
  convert bot_le,
  simp,
end

instance : order_top (idem R) :=
{ le_top := λ _, le_top, ..idem.has_top, ..idem.partial_order}

-- a machine could write these
instance: semilattice_sup_top (idem R) :=
{ le_sup_left := λ E F, begin
    apply le_of_inv_le_inv,
    rw sup_def,
    rw inv_inv,
    apply inf_le_right,
  end,
  le_sup_right := λ E F, begin
    apply le_of_inv_le_inv,
    rw sup_def,
    rw inv_inv,
    apply inf_le_left,
  end,
  sup_le := λ E F G hEF hFG, begin
    apply le_of_inv_le_inv,
    rw sup_def,
    rw inv_inv,
    apply le_inf (inv_le_inv_of_le hFG) (inv_le_inv_of_le hEF),
  end,
  ..idem.has_sup, ..idem.order_top
}

instance : bounded_lattice (idem R) :=
{
  ..idem.semilattice_inf_bot, ..idem.semilattice_sup_top
}