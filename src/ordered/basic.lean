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

/-- A simplex is nondegenerate iff, for every two endpoints and point `p`, if
    both endpoints are distinct from `p`, then all three points are not
    collinear to each other. -/
def nondegen_simplex (l : list α) : Prop :=
∀ v₁ v₂ v₃ ∈ l, v₂ ≠ v₁ → v₂ ≠ v₃ → ¬ collinear v₁ v₃ v₂

/-- For any set `S`, `S₁` and `S₂` form a dependent bipartition of `S` iff
    their union `S₁ ∪ S₂ = S` and there is no point in one that is between two
    points of another. -/
def dep_biparition (s s₁ s₂ : set α) : Prop :=
s₁ ∪ s₂ = s ∧ (∀ p ∈ s₁, ¬ ∃ q r ∈ s₂, between q p r) ∧
  (∀ p ∈ s₂, ¬ ∃ q r ∈ s₁, between q p r)

end

/-- Ordered geometry, without an axiom of dimension. -/
class {u} ordered_geo_nodim (α : Type u) extends has_betweenness α, inhabited α :=
(pasch₁ {v₁ v₂ : α} (v₃ v₄ ∈ line v₁ v₂) : v₃ ≠ v₄ → v₁ ∈ line v₃ v₄)
(pasch₂ {v₁ v₂ v₃ v₄ v₅ : α} : ¬ nondegen_simplex [v₁, v₂, v₃] → between v₂ v₃ v₄ →
  between v₃ v₅ v₂ → ∃ z ∈ line v₄ v₅, between v₁ z v₂)
(dedekind {p q : α} {s₁ s₂ : set α} : nonempty s₁ → nonempty s₂ →
  dep_biparition (line p q) s₁ s₂ →
    (∃ v₁ ∈ s₁, ∀ (v₂ ∈ s₁ \ {v₁}) (v₃ ∈ s₂), between v₂ v₁ v₃)
    ∨ (∃ v₁ ∈ s₂, ∀ (v₂ ∈ s₂ \ {v₁}) (v₃ ∈ s₁), between v₂ v₁ v₃))

/-- Ordered geometry, indexed by a dimension `d` for which the appropriate
    axioms of dimensionality apply for any nonempty list of points at most
    `d+1` long. -/
class {u} ordered_geo (α : Type u) (d : ℕ) extends ordered_geo_nodim α :=
(dimality {d' : ℕ} (h : d' < d) (vs : vector α d'.succ) : dimensionality d' vs)
(all_in_space : ∀ {vs : vector α (d + 2)}, nondegen_simplex vs.val →
  ∀ v₁, ∃ v₂ v₃ ∈ convex_hull {p | p ∈ vs.val}, collinear v₁ v₂ v₃)

/-- An infinite ordered geometry, with the property that the axiom of
    dimensionality holds for any dimension. -/
class {u} ordered_geo_inf (α : Type u) extends ordered_geo_nodim α :=
(inf_dimality {d : ℕ} (vs : vector α d.succ) : dimensionality d vs)

section
universe u
parameter {α : Type u}
namespace ordered_geo

/-- For any point, there exists another point that's not equal to it. -/
theorem ex_not_eq {d : ℕ} [ordered_geo α $ d + 1] (p : α) : ∃ q, p ≠ q :=
begin
  cases dimality (dec_trivial : 0 < d + 1) ⟨[p], dec_trivial⟩ with w h,
  use w,
  simp only [list.mem_singleton] at h,
  specialize h p p (convex_hull.of_set rfl) (convex_hull.of_set rfl),
  change _ ∉ _ at h,
  rwa [line.single_self, set.mem_singleton_iff, eq_comm] at h
end

instance {d : ℕ} [ordered_geo α $ d + 1] : nontrivial α :=
⟨⟨arbitrary α, @ex_not_eq d _ _⟩⟩

/-- For any line, there exists a point that's not in it. -/
theorem ex_not_on_line {d : ℕ} [ordered_geo α $ d + 2] (p q : α) :
  ∃ r, r ∉ line p q :=
begin
  cases dimality (dec_trivial : 1 < d + 2) ⟨[p, q], dec_trivial⟩ with w h,
  use w,
  specialize h p q (convex_hull.of_set $ or.inl rfl),
  exact h (convex_hull.of_set $ or.inr $ list.mem_singleton_self _)
end

/-- For any plane, there exists a point that's not in it. -/
theorem ex_not_on_plane {d : ℕ} [ordered_geo α $ d + 3] (p q r : α) :
  ∃ x, x ∉ convex_hull {y | y ∈ [p, q, r]} :=
begin
  cases dimality (dec_trivial : 2 < d + 3) ⟨[p, q, r], dec_trivial⟩ with w h,
  use w,
  exact h.not_mem_of_indep
end

end ordered_geo
end

section
universe u
parameters {α : Type u} [ordered_geo_inf α]
namespace ordered_geo_inf

/-- For any point, there exists another point that's not equal to it. -/
theorem ex_not_eq (p : α) : ∃ q, p ≠ q :=
begin
  cases inf_dimality ⟨[p], rfl⟩ with w h,
  use w,
  simp only [list.mem_singleton] at h,
  specialize h p p (convex_hull.of_set rfl) (convex_hull.of_set rfl),
  change _ ∉ _ at h,
  rwa [line.single_self, set.mem_singleton_iff, eq_comm] at h
end

instance : nontrivial α :=
⟨⟨arbitrary α, ex_not_eq _⟩⟩

/-- For any line, there exists a point that's not in it. -/
theorem ex_not_on_line (p q : α) : ∃ r, r ∉ line p q :=
begin
  cases inf_dimality ⟨[p, q], rfl⟩ with w h,
  use w,
  specialize h p q (convex_hull.of_set $ or.inl rfl),
  exact h (convex_hull.of_set $ or.inr $ list.mem_singleton_self _)
end

/-- For any plane, there exists a point that's not in it. -/
theorem ex_not_on_plane (p q r : α) :
  ∃ x, x ∉ convex_hull {y | y ∈ [p, q, r]} :=
begin
  cases inf_dimality ⟨[p, q, r], rfl⟩ with w h,
  use w,
  exact h.not_mem_of_indep
end

theorem ex_nondegen_simplex (d : ℕ) :
  ∃ vs : vector α (d + 1), nondegen_simplex vs.val :=
begin
  induction d with d hd,
    { refine ⟨⟨[arbitrary α], rfl⟩, _⟩,
      intros _ _ _ hv₁ hv₂ _ h,
      rw list.mem_singleton at hv₁ hv₂,
      rw [hv₁, hv₂] at h,
      contradiction },
  rcases hd with ⟨⟨l, h⟩, hvs⟩,
  rcases inf_dimality ⟨l, h⟩ with ⟨p, hp⟩,
  refine ⟨vector.cons p ⟨l, h⟩, _⟩,
  rw lin_indep at hp,
  intros v₁ v₂ v₃ hv₁ hv₂ hv₃ h₂₁ h₂₃ h,
  simp only [vector.cons_val, subtype.val] at *,
  rw list.mem_cons_iff at hv₁ hv₂ hv₃,
  repeat { induction hv₁ }, repeat { induction hv₂ }, repeat { induction hv₃ },
  repeat { contradiction },
    { rw collinear.eq_ends_iff_eq at h, exact h₂₃ h.symm },
    { apply hp _ _ (convex_hull.of_set hv₂) (convex_hull.of_set hv₃),
      exact ((h.swap).rotate h₂₁.symm).rotate h₂₃ },
    { exact (hp _ _ (convex_hull.of_set hv₁) (convex_hull.of_set hv₃)) h },
    { apply hp _ _ (convex_hull.of_set hv₁) (convex_hull.of_set hv₂),
      exact (h.swap).rotate h₂₁.symm },
    {  }
end

theorem not_all_in_space {d : ℕ} : ¬ ∀ {vs : vector α (d + 2)},
  nondegen_simplex vs.val → ∀ v₁, ∃ v₂ v₃ ∈ convex_hull {p | p ∈ vs.val},
    collinear v₁ v₂ v₃ :=
begin
  intro h,

end

end ordered_geo_inf
end
