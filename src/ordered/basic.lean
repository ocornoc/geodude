/-
  Copyright 2020 Grayson Burton
  License available in the LICENSE file.
-/
import data.set tactic .between .convex

section
universe u
parameters {α : Type u} [has_betweenness α]

/-- The dimensionality proposition states that, for a specified dimension `d`,
    given any list of `d + 1` points, there is some point that's linearly
    independent to any line formed by points in the convex hull of that list.
    
    This is a generalization of "there are two distinct points", "for any given
    line there's a point that's not collinear to it", "for any given plane
    there's a point that's not coplanar to it", etc. -/
def dimensionality (d : ℕ) (vs : vector α d.succ) : Prop :=
∃ p, lin_indep p $ convex_hull {z | z ∈ vs.val}

@[simp]
theorem dimensionality.dim_def (d : ℕ) (vs : vector α d.succ) :
  dimensionality d vs = ∃ p, lin_indep p $ convex_hull {z | z ∈ vs.val} :=
rfl

end

/-- Ordered geometry, without an axiom of dimension. -/
class {u} ordered_geo_nodim (α : Type u) extends has_betweenness α :=
(collin {p q r x : α} : r ≠ x → r ∈ line p q → x ∈ line p q →
  p ∈ line r x)
--(ex_not_collin (p q : α) : ∃ r, r ∉ line p q)
(pasch {p q r x y : α} : ¬ triangle.degenerate p q r →
  between q r x → between r y p → ∃ z ∈ line x y, between p z q)
-- not all of the axioms btw, it's just a placeholder

/-- Ordered geometry, indexed by a dimension `d` for which the appropriate
    axioms of dimensionality apply for any list of points at most `d` long. -/
class {u} ordered_geo (α : Type u) (d : ℕ) extends ordered_geo_nodim α :=
(dimality {d' : fin d} (vs : vector α d'.val.succ) : dimensionality d'.val vs)

class {u} ordered_geo_inf (α : Type u) extends ordered_geo_nodim α :=
(inf_dimality {d : ℕ} (vs : vector α d.succ) : dimensionality d vs)

section
universe u
parameter {α : Type u}
namespace ordered_geo
/-- If `α` is an ordered geometry in dimension `d₁`, then it's also an ordered
    geometry in every dimension `d₂ < d₁`. -/
instance all_lower {d₁ : ℕ} [ordered_geo α d₁] {d₂ : ℕ} (h : d₂ < d₁) : ordered_geo α d₂ :=
⟨λ d, begin
  have h' := @dimality α _ _ (fin.cast_le (le_of_lt h) d),
  rwa fin.cast_le_val _ (le_of_lt h) at h'
end⟩

/-- For any point, there exists another point that's not equal to it. -/
theorem ex_not_eq [ordered_geo α 1] (p : α) : ∃ q, p ≠ q :=
begin
  let l := [p],
  have hl : l.length = (0 : fin 1).val.succ := dec_trivial,
  have h := dimality ⟨l, hl⟩,
  cases h with w h,
  use w,
  simp only [list.mem_singleton] at h,
  specialize h p p (convex_hull.of_set rfl) (convex_hull.of_set rfl),
  change _ ∉ _ at h,
  rwa [line.single_self, set.mem_singleton_iff, eq_comm] at h
end

/-- For any line, there exists a point that's not collinear to it. -/
theorem ex_not_collin [ordered_geo α 2] (p q : α) : ∃ r, r ∉ line p q :=
begin
  let l := [p, q],
  have hl : l.length = (1 : fin 2).val.succ := dec_trivial,
  have h := dimality ⟨l, hl⟩,
  cases h with w h,
  use w,
  specialize h p q (convex_hull.of_set $ or.inl rfl),
  exact h (convex_hull.of_set $ or.inr $ list.mem_singleton_self _)
end

end ordered_geo
end

section
universe u
parameters {α : Type u} [ordered_geo_inf α]
namespace ordered_geo_inf
/-- An ∞-dimensional ordered geometry is also an `n`-dimensional ordered geometry for
    any `n`. -/
instance ordered_geo_subspace {d : ℕ} : ordered_geo α d :=
⟨λ _, inf_dimality⟩

end ordered_geo_inf
end
