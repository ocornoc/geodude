/-
  Copyright 2020 Grayson Burton
  License available in the LICENSE file.
-/

import data.set tactic

private lemma {u} set_ins_comm {α : Type u} (x y : α) :
  ({x, y} : set α) = {y, x} :=
by simp [set.insert_def, or.comm]

/-- A strict betweenness relation. -/
class {u} has_betweenness (α : Type u) : Type u :=
(between : α → α → α → Prop)
(between_extend : ∀ {p q}, p ≠ q → ∃ r, between p q r)
(between_irrefl : ∀ {p q r}, between p q r → p ≠ r)
(between_symm : ∀ {p q r}, between p q r → between r q p)
(between_not_rotate : ∀ {p q r}, between p q r → ¬ between r p q)

/-- `between P Q R` means "`Q` lies in the line segment `PR` and isnt an
    endpoint." -/
def {u} between {α : Type u} [has_betweenness α] :=
@has_betweenness.between α

namespace between
section
universe u
parameters {α : Type u} [has_betweenness α]

/-- For any two distinct points `P`,`Q` there is another point `R` such that
    `Q` is between `P` and `R`. -/
lemma extend {p q : α} : p ≠ q → ∃ r, between p q r :=
has_betweenness.between_extend

lemma ne_of_no_extension {p q : α} : (¬ ∃ r, between p q r) → p = q :=
by contrapose!; exact extend

lemma ne_of_no_extension' {p q : α} : (∀ r, ¬ between p q r) → p = q :=
by contrapose!; exact extend

/-- If `Q` is between `P` and `R`, then `P ≠ R`. -/
protected lemma irrefl {p q r : α} : between p q r → p ≠ r :=
has_betweenness.between_irrefl

lemma not_between_of_eq {p r : α} (q : α) : p = r → ¬ between p q r :=
by contrapose!; exact between.irrefl 

protected lemma symm {p q r : α} : between p q r → between r q p :=
has_betweenness.between_symm

/-- `Q` is between `P` and `R` iff it is between `R` and `P`. -/
lemma symm_iff (p q r : α) : between p q r ↔ between r q p :=
iff.intro between.symm between.symm

/-- If `Q` is between `P` and `R`, then `P` isn't between `R` and `Q`. -/
lemma not_rotate {p q r : α} : between p q r → ¬ between r p q :=
has_betweenness.between_not_rotate

/-- There is no point between `P` and itself. -/
lemma irrefl' (p q : α) : ¬ between p q p :=
not_between_of_eq q rfl

/-- No point is between itself and another point. -/
theorem not_self_between (p q : α) : ¬ between p p q :=
λ h, h.not_rotate h.symm

/-- No point is between itself and another point. -/
theorem not_between_self (p q : α) : ¬ between p q q :=
λ h, not_self_between _ _ h.symm

end
end between

section
universe u
parameters {α : Type u} [has_betweenness α]

/-- A line segment excluding the endpoints -/
def segment (x y : α) : set α := {z | between x z y}

/-- A line segment including the endpoints -/
def interval (x y : α) : set α := segment x y ∪ {x, y}

/-- The ray from `x` to `y`. Excludes `x`. -/
def ray (x y : α) : set α := {z | between z y x} ∪ segment x y ∪ {y}

/-- A line through `x` and `y` -/
def line (x y : α) : set α := interval x y ∪ ray x y ∪ ray y x

/-- `collinear P Q R` means "`R` is on the line `PQ`" -/
def collinear (p q r : α) : Prop := r ∈ line p q

/-- `p` is linearly independent from any two points in `s`. -/
def lin_indep (p : α) (s : set α) : Prop :=
∀ l r ∈ s, ¬ collinear l r p


/-- The edges of the triangle `▵PQR` -/
def triangle (p q r : α) : set α :=
interval p q ∪ interval q r ∪ interval r p

/-- Whether a triangle is degenerate (any vertices are collinear) -/
def triangle.degenerate (p q r : α) : Prop :=
collinear p q r ∨ collinear r p q ∨ collinear q r p

/-- The points between (and including) the edges of a triangle -/
def triangle.inside (p q r : α) : set α :=
{z | ∃ l r ∈ triangle p q r, between l z r} ∪ {p, q, r}

/-- The points strictly between the edges of a triangle -/
def triangle.strict_inside (p q r : α) : set α :=
triangle.inside p q r \ triangle p q r

/-- A plane, as defined by a nondegenerate triangle. -/
def plane {p q r : α} : ¬ triangle.degenerate p q r → set α :=
λ _, {z | ∃ l r ∈ triangle p q r, collinear l r z}

end

section
universe u
parameters {α : Type u} [has_betweenness α]

namespace segment

@[simp]
lemma seg_def (x y : α) : segment x y = {z | between x z y} := rfl

theorem empty_of_same_ends (x : α) : segment x x = ∅ :=
by rw set.eq_empty_iff_forall_not_mem; apply between.irrefl'

theorem end_not_mem_seg_left (x y : α) : x ∉ segment x y :=
between.not_self_between _ _

theorem end_not_mem_seg_right (x y : α) : y ∉ segment x y :=
between.not_between_self _ _

theorem swap (x y : α) : segment x y = segment y x :=
by dsimp; congr; funext; rw between.symm_iff

theorem subs_intrv (x y : α) : segment x y ⊆ interval x y :=
λ _, or.inl

theorem ssubs_intrv (x y : α) : segment x y ⊂ interval x y :=
begin
  rw set.ssubset_iff_subset_ne,
  refine ⟨subs_intrv _ _, λ h₁, _⟩,
  replace h₁ := eq_iff_iff.mp (congr_fun h₁ x),
  apply end_not_mem_seg_left x y,
  exact h₁.mpr (or.inr $ or.inl rfl)
end

theorem seg_subs_ray (x y : α) : segment x y ⊆ ray x y :=
λ _, or.inl ∘ or.inr

theorem seg_ssubs_ray (x y : α) : segment x y ⊂ ray x y :=
begin
  rw set.ssubset_iff_subset_ne,
  refine ⟨seg_subs_ray _ _, λ h₁, _⟩,
  replace h₁ := eq_iff_iff.mp (congr_fun h₁ y),
  apply end_not_mem_seg_right x y,
  exact h₁.mpr (or.inr rfl)
end

end segment

namespace interval

@[simp]
lemma intrv_def (x y : α) :
  interval x y = {z | between x z y ∨ z = x ∨ z = y} :=
rfl

@[simp]
lemma intrv_def' (x y : α) : interval x y = segment x y ∪ {x, y} := rfl

theorem seg_subs (x y : α) : segment x y ⊆ interval x y :=
segment.subs_intrv _ _

@[simp]
theorem single_self (x : α) : interval x x = {x} :=
begin
  rw intrv_def,
  congr,
  funext,
  rw or_self,
  apply or_eq_of_eq_false_left,
  rw eq_false,
  apply between.irrefl'
end

theorem end_mem_intrv_left (x y : α) : x ∈ interval x y :=
or.inr $ or.inl rfl

theorem end_mem_intrv_right (x y : α) : y ∈ interval x y :=
or.inr $ or.inr rfl

theorem seg_ssubs (x y : α) : segment x y ⊂ interval x y :=
segment.ssubs_intrv _ _

theorem swap (x y : α) : interval x y = interval y x :=
by simp only [intrv_def', segment.swap, set_ins_comm]

end interval

namespace ray

@[simp]
lemma ray_def (x y : α) :
  ray x y = {z | between z y x} ∪ segment x y ∪ {y} :=
rfl

@[simp]
theorem single_self (x : α) : ray x x = {x} :=
begin
  rw ray_def,
  funext y,
  apply or_eq_of_eq_false_left,
  apply eq_false_intro,
  change ¬ (_ ∨ _),
  push_neg,
  exact ⟨between.not_between_self _ _, between.irrefl' _ _⟩
end

lemma end_not_mem_ray_left_of_ne {x y : α} : x ≠ y → x ∉ ray x y :=
begin
  intro h,
  rw ray_def,
  change ¬ ((_ ∨ _) ∨ _),
  push_neg,
  exact ⟨⟨between.irrefl' _ _, segment.end_not_mem_seg_left _ _⟩, h⟩
end

lemma ne_of_end_not_mem_ray_left {x y : α} : x ∉ ray x y → x ≠ y :=
begin
  intro h,
  rw ray_def at h,
  change ¬ ((_ ∨ _) ∨ _) at h,
  push_neg at h,
  exact h.right
end

theorem end_not_mem_ray_left_iff_ne (x y : α) : x ≠ y ↔ x ∉ ray x y :=
  iff.intro end_not_mem_ray_left_of_ne ne_of_end_not_mem_ray_left

theorem end_mem_ray_left_iff_eq (x y : α) : x = y ↔ x ∈ ray x y :=
begin
  classical,
  exact not_iff_not.mp (end_not_mem_ray_left_iff_ne _ _)
end

theorem end_mem_ray_right (x y : α) : y ∈ ray x y :=
or.inr rfl

theorem seg_subs (x y : α) : segment x y ⊆ ray x y :=
segment.seg_subs_ray _ _

theorem seg_ssubs (x y : α) : segment x y ⊂ ray x y :=
segment.seg_ssubs_ray _ _

end ray

namespace line

@[simp]
theorem line_def (x y : α) : line x y = interval x y ∪ ray x y ∪ ray y x := rfl

@[simp]
theorem single_self (x : α) : line x x = {x} :=
by simp

theorem swap (x y : α) : line x y = line y x :=
by rw [line_def, interval.swap, set.union_assoc,
       set.union_comm (ray _ _), ←set.union_assoc, line_def]

theorem ray_subs (x y : α) : ray x y ⊆ line x y :=
λ _, or.inl ∘ or.inr

theorem ray_subs' (x y : α) : ray y x ⊆ line x y :=
λ _, or.inr

theorem seg_subs (x y : α) : segment x y ⊆ line x y :=
trans (ray.seg_subs _ _) (ray_subs _ _)

theorem end_mem_line_left (x y : α) : x ∈ line x y :=
or.inr $ ray.end_mem_ray_right _ _

theorem end_mem_line_right (x y : α) : y ∈ line x y :=
or.inl $ or.inr $ ray.end_mem_ray_right _ _

theorem seg_ssubs (x y : α) : segment x y ⊂ line x y :=
begin
  rw set.ssubset_iff_subset_ne,
  refine ⟨seg_subs _ _, λ h, _⟩,
  have hx := end_mem_line_left x y,
  rw ←h at hx,
  exact (segment.end_not_mem_seg_left _ _) hx
end

end line

/-- The convex hull of a set. -/
/- thanks chris hughes -/
inductive convex_hull (s : set α) : set α
| of_set : ∀ {v}, v ∈ s → convex_hull v
| intrv : ∀ {v₁ v₂ v₃}, convex_hull v₁ → convex_hull v₂ →
  v₃ ∈ interval v₁ v₂ → convex_hull v₃

/-- A set is convex if it is equal to its own convex hull. -/
def is_convex (s : set α) : Prop := convex_hull s = s

/-- A set `S` is bound if, for any two points `P` and `Q` in the convex hull of
    `S`, there is a point on the ray `P→Q` and a point on the ray `Q→P` that
    are both not in the convex hull of `S`.
    
    This essentially means that you can draw a boundary that encircles `S`. -/
def bound (s : set α) : Prop :=
∀ v₁ v₂ ∈ convex_hull s,
  (∃ p ∈ ray v₁ v₂, p ∉ convex_hull s)
  ∧ (∃ q ∈ ray v₂ v₁, q ∉ convex_hull s)

/-- The opening of a set `S` is the intersection of `S` with all `segment`s of
    any two points in `S`. For `S` over dense types, this will create an open
    set. -/
def opening (s : set α) : set α := s ∩ ⋃ v₁ v₂ ∈ s, segment v₁ v₂
/-- The boundary of a set `S` is `S` with its opening removed. -/
def boundary (s : set α) : set α := s \ opening s

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

section
universe u
parameters {α : Type u} [has_betweenness α]

@[simp]
theorem is_convex.convex_def (s : set α) : is_convex s = (convex_hull s = s) :=
rfl

@[simp]
theorem opening.opening_def (s : set α) :
  opening s = s ∩ ⋃ v₁ v₂ ∈ s, segment v₁ v₂ :=
rfl

@[simp]
theorem boundary.boundary_def (s : set α) : boundary s = s \ opening s :=
rfl

theorem boundary.subs_s (s : set α) : boundary s ⊆ s :=
λ _, and.left

namespace convex_hull
/-- `x` is in a convex hull of a set iff it's in the original set or it is on a
    line segment between two points that are also in the convex hull. -/
@[simp]
theorem mem_iff {s : set α} (x : α) :
  x ∈ convex_hull s ↔ x ∈ s ∨ ∃ (v₁ v₂ ∈ convex_hull s), x ∈ interval v₁ v₂ :=
begin
  split,
  all_goals { intro h },
    { rcases h with ⟨_, h⟩ | ⟨_, _, _, hv₁, hv₂, h⟩,
        { exact or.inl h },
        { exact or.inr ⟨_, _, hv₁, hv₂, h⟩ }},
    { rcases h with ⟨h⟩ | ⟨_, _, hv₁, hv₂, h⟩,
        { exact of_set h },
        { exact intrv hv₁ hv₂ h }}
end

theorem mem_iff' {s : set α} (x : α) :
  convex_hull s x ↔ x ∈ s ∨ ∃ (v₁ v₂ ∈ convex_hull s), x ∈ interval v₁ v₂ :=
mem_iff x

/-- Taking the convex hull of a convex hull is idempotent. -/
theorem idempotent (s : set α) : convex_hull (convex_hull s) = convex_hull s :=
begin
  funext,
  apply propext,
  split,
  all_goals { intro h },
    { induction h with _ _ _ _ _ _ _ h hv₁ hv₂,
        { assumption },
        { exact intrv hv₁ hv₂ h }},
    { rcases h with ⟨_, h⟩ | ⟨_, _, _, hv₁, hv₂, h⟩,
        { exact of_set (of_set h) },
        { exact intrv (of_set hv₁) (of_set hv₂) h }}
end

/-- Every set is a subset of its convex hull. -/
theorem self_subs_hull (s : set α) : s ⊆ convex_hull s :=
λ _, of_set

/-- If a convex hull of a set `S` is bound, then `S` is also bound. -/
theorem bound_of_hull_bound {s : set α} : bound (convex_hull s) → bound s :=
begin
  intros h _ _ hv₁ hv₂,
  specialize h _ _ (self_subs_hull _ hv₁) (self_subs_hull _ hv₂),
  rwa idempotent at h
end

/-- Every convex hull is convex. -/
theorem convex (s : set α) : is_convex (convex_hull s) :=
idempotent s

/-- If `S₁ ⊆ S₂`, then the convex hull of `S₁` is also a subset of the convex
    hull of `S₂`. -/
theorem is_mono {s t : set α} (hs : s ⊆ t) : convex_hull s ⊆ convex_hull t :=
begin
  intros x h,
  induction h with _ h _ _ _ _ _ h hv₁ hv₂,
    { exact self_subs_hull _ (hs h) },
    { exact intrv hv₁ hv₂ h }
end

/-- If `S₁ ⊂ S₂` and both are convex, then the convex hull of `S₁` is also a
    strict subset of the convex hull of `S₂`. -/
theorem is_mono_convex {s t : set α} (hs : is_convex s) (ht : is_convex t) :
  s ⊂ t → convex_hull s ⊂ convex_hull t :=
λ h, by rw is_convex.convex_def at hs ht; rwa [hs, ht]

/-- If `S₁` and `S₂` are both convex, then `S₁ ⊂ S₂` iff the same is true of
    their convex hulls. -/
theorem iff_ssubs_of_convex {s t : set α} (hs : is_convex s) (ht : is_convex t) :
  s ⊂ t ↔ convex_hull s ⊂ convex_hull t :=
by rw is_convex.convex_def at hs ht; rwa [hs, ht]

end convex_hull

namespace is_convex

/-- Every convex hull is convex. -/
theorem hulls_are_convex (s : set α) : is_convex (convex_hull s) :=
convex_hull.convex s

/-- If `S` is convex, then every point in `s` lies on some line segment in
    `S`. -/
theorem mem_intrv_of_convex {s : set α} :
  is_convex s → ∀ {x}, x ∈ s → ∃ v₁ v₂ ∈ s, x ∈ interval v₁ v₂ :=
begin
  intros hs x h,
  rw convex_def at hs,
  rw ←hs at h,
  rcases h with ⟨_, h⟩ | ⟨_, _, _, hv₁, hv₂, h⟩,
    { exact ⟨x, x, h, h, interval.end_mem_intrv_left _ _⟩ },
  rw ←hs,
  exact ⟨_, _, hv₁, hv₂, h⟩
end

/-- If `S` is convex, then every point in `s` lies on some line segment in
    `S`. -/
theorem iff_mem_intrv_of_convex {s : set α} :
  is_convex s → ∀ {x}, x ∈ s ↔ ∃ v₁ v₂ ∈ s, x ∈ interval v₁ v₂ :=
begin
  intros hs x,
  apply iff.intro (mem_intrv_of_convex hs),
  rw convex_def at hs,
  rintro ⟨_, _, hv₁, hv₂, h⟩,
  rw ←hs at *,
  exact convex_hull.intrv hv₁ hv₂ h
end

/-- A set `S` is convex iff, for any point `x`, `x ∈ S` is equivalent to there
    being two more points in `S` such that `x` is on the line segment between
    them. -/
theorem iff_mem_intrv_iff_convex (s : set α) :
  is_convex s ↔ ∀ {x}, x ∈ s ↔ ∃ v₁ v₂ ∈ s, x ∈ interval v₁ v₂ :=
begin
  apply iff.intro iff_mem_intrv_of_convex,
  intros hs,
  rw convex_def,
  funext,
  apply propext,
  split,
  all_goals { intro h },
    { induction h with _ h₂ _ _ _ _ _ h hv₁ hv₂,
        { assumption },
        { exact hs.mpr ⟨_, _, hv₁, hv₂, h⟩ }},
    { exact convex_hull.of_set h }
end

end is_convex
end

/-
/-- The partial convexation of a set. -/
def partial_convex_hull (s : set α) : ℕ → set α
| 0     := s
| (n+1) := ⋃ v₁ v₂ ∈ partial_convex_hull n, interval v₁ v₂
-/

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
