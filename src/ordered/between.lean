/-
  Copyright 2020 Grayson Burton
  License available in the LICENSE file.
-/

import data.set.basic tactic

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
@has_betweenness.between α _

namespace between
section
universe u
parameters {α : Type u} [has_betweenness α]

/-- For any two distinct points `P`,`Q` there is another point `R` such that
    `Q` is between `P` and `R`. -/
lemma extend {p q : α} : p ≠ q → ∃ r, between p q r :=
has_betweenness.between_extend

lemma eq_of_no_extension {p q : α} : (¬ ∃ r, between p q r) → p = q :=
by contrapose!; exact extend

lemma eq_of_no_extension' {p q : α} : (∀ r, ¬ between p q r) → p = q :=
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

/-- The ray (or half line) from `x` to `y`. Excludes `x`. -/
def ray (x y : α) : set α := {z | between z y x} ∪ segment x y ∪ {y}

/-- A line through `x` and `y` -/
def line (x y : α) : set α := interval x y ∪ ray x y ∪ ray y x

/-- `collinear P Q R` means "There is a line with `p`, `r`, and `q` on it." -/
def collinear (p q r : α) : Prop :=
∃ v₀ v₁, p ∈ line v₀ v₁ ∧ q ∈ line v₀ v₁ ∧ r ∈ line v₀ v₁

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

lemma symm {p q r : α} (h : r ∈ segment p q) : r ∈ segment q p :=
by rwa swap at h

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

theorem seg_subs_line (x y : α) : segment x y ⊆ line x y :=
λ _, or.inl ∘ or.inl ∘ or.inl

theorem seg_ssubs_line (x y : α) : segment x y ⊂ line x y :=
begin
  rw set.ssubset_iff_subset_ne,
  refine ⟨seg_subs_line _ _, λ h₁, _⟩,
  replace h₁ := eq_iff_iff.mp (congr_fun h₁ y),
  apply end_not_mem_seg_right x y,
  exact h₁.mpr (or.inl $ or.inr $ or.inr rfl)
end

theorem ne_ends_of_mem {x y : α} (h : ∃ z, z ∈ segment x y) : x ≠ y :=
begin
  intro he,
  induction he,
  cases h with _ h,
  rw empty_of_same_ends at h,
  exact h
end

theorem ne_left_of_mem {x y z : α} (h : x ∈ segment y z) : x ≠ y :=
λ he, by rw he at h; exact (end_not_mem_seg_left _ _).elim h

theorem ne_right_of_mem {x y z : α} (h : x ∈ segment y z) : x ≠ z :=
λ he, by rw he at h; exact (end_not_mem_seg_right _ _).elim h

theorem not_in_rotate {x y z : α} : z ∈ segment x y → x ∉ segment y z :=
between.not_rotate

theorem not_in_rotate' {x y z : α} : z ∈ segment x y → x ∉ segment z y :=
by rw swap z y; exact not_in_rotate

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

theorem eq_of_mem_same {p q : α} (h : p ∈ interval q q) : p = q :=
by rw single_self at h; exact h

theorem eq_iff_mem_same (p q : α) : p ∈ interval q q ↔ p = q :=
⟨eq_of_mem_same, λ _, by simpa⟩

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
  funext,
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

theorem eq_of_mem_same {x y : α} (h : x ∈ ray y y) : x = y :=
by rw single_self at h; exact h

@[simp]
theorem eq_iff_mem_same (x y : α) : x ∈ ray y y ↔ x = y :=
⟨eq_of_mem_same, λ h, by simp [h]⟩

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
segment.seg_subs_line x y

theorem seg_ssubs (x y : α) : segment x y ⊂ line x y :=
segment.seg_ssubs_line x y

theorem intrv_subs (x y : α) : interval x y ⊆ line x y :=
λ _, or.inl ∘ or.inl

theorem end_mem_line_left (x y : α) : x ∈ line x y :=
or.inr $ ray.end_mem_ray_right _ _

theorem end_mem_line_right (x y : α) : y ∈ line x y :=
or.inl $ or.inr $ ray.end_mem_ray_right _ _

theorem ray_ssubs_of_ne {x y : α} (h : x ≠ y) : ray x y ⊂ line x y :=
begin
  apply set.ssubset_iff_subset_ne.mpr ⟨ray_subs _ _, λ h₁, _⟩,
  rw [ray.end_not_mem_ray_left_iff_ne, h₁] at h,
  exact h (end_mem_line_left _ _)
end

theorem ray_ssubs_of_ne' {x y : α} (h : x ≠ y) : ray y x ⊂ line x y :=
by rw swap; exact ray_ssubs_of_ne h.symm

theorem rotate_of_ne {x y z : α} : x ≠ z → x ∈ line y z → y ∈ line x z :=
by finish using between.symm_iff

@[simp]
theorem rotate_iff_of_ne {x y z : α} :
  x ≠ z → y ≠ z → (x ∈ line y z ↔ y ∈ line x z) :=
λ h₁ h₂, ⟨rotate_of_ne h₁, rotate_of_ne h₂⟩

theorem eq_of_mem_same {x y : α} (h : x ∈ line y y) : x = y :=
begin
  rcases h with ⟨h | h⟩ | h,
    { exact interval.eq_of_mem_same h },
    { exact ray.eq_of_mem_same h },
    { exact ray.eq_of_mem_same h }
end

@[simp]
theorem eq_iff_mem_same (x y : α) : x ∈ line y y ↔ x = y :=
⟨eq_of_mem_same, λ h, by simp [h]⟩

end line

namespace collinear

@[simp]
theorem collin_def (p q r : α) : collinear p q r =
  ∃ v₀ v₁ : α, p ∈ line v₀ v₁ ∧ q ∈ line v₀ v₁ ∧ r ∈ line v₀ v₁ :=
rfl

theorem of_left (p q : α) : collinear p p q :=
⟨p, q, by simp⟩

theorem of_right (p q : α) : collinear p q q :=
⟨p, q, by simp⟩

theorem of_ends (p q : α) : collinear p q p :=
⟨p, q, by simp⟩

theorem of_same (p : α) : collinear p p p :=
of_left p p

theorem swap_iff (p q r : α) : collinear p q r ↔ collinear q p r :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  all_goals
    { rcases h with ⟨_, _, h⟩,
      rw [←and.assoc, @and.comm (_ ∈ _), and.assoc] at h,
      exact ⟨_, _, h⟩ }
end

theorem swap {p q r : α} : collinear p q r → collinear q p r :=
(swap_iff p q r).mp

theorem mem_of_mem_line {p q r : α} (h : p ∈ line q r) : collinear q r p :=
⟨q, r, by simp, by simp, h⟩

theorem mem_of_mem_ray {p q r : α} (h : p ∈ ray q r) : collinear q r p :=
mem_of_mem_line $ line.ray_subs _ _ h

theorem mem_of_mem_ray' {p q r : α} (h : p ∈ ray r q) : collinear q r p :=
mem_of_mem_line $ line.ray_subs' _ _ h

theorem mem_of_mem_intrv {p q r : α} (h : p ∈ interval q r) :
  collinear q r p :=
mem_of_mem_line $ line.intrv_subs _ _ h

theorem rotate' {p q r : α} (h : collinear p q r) : collinear r p q :=
begin
  rcases h with ⟨_, _, h⟩,
  rw [@and.comm (_ ∈ _), and.assoc, @and.comm (_ ∈ _), and.assoc] at h,
  exact ⟨_, _, h⟩
end

theorem rotate {p q r : α} : collinear p q r → collinear q r p :=
rotate' ∘ rotate'

theorem rotate_iff {p q r : α} : collinear p q r ↔ collinear q r p :=
⟨rotate, rotate'⟩

theorem swap_iff' (p q r : α) : collinear p q r ↔ collinear p r q :=
by rw [rotate_iff, swap_iff _ r q, rotate_iff]

theorem of_left' (p q : α) : collinear p p q :=
(of_ends _ _).rotate'

theorem ex_collinear_of_mem {p : α} {s : set α} (h : p ∈ s) :
  ∃ q r ∈ s, collinear p q r :=
⟨_, _, h, h, of_same _⟩

@[simp]
theorem none_collinear_iff_empty (s : set α) :
  (∀ p q r ∈ s, ¬ collinear p q r) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ _ _ hp, _⟩,
    { intro hx, exact h _ _ _ hx hx hx (of_same _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_2 (s : set α) :
  (∀ p q ∈ s, ¬ collinear p p q) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ _ _ hp, _⟩,
    { intro hx, exact h _ _ hx hx (of_same _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_2' (s : set α) :
  (∀ p q ∈ s, ¬ collinear p q q) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ _ _ hp, _⟩,
    { intro hx, exact h _ _ hx hx (of_same _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_2'' (s : set α) :
  (∀ p q ∈ s, ¬ collinear p q p) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ _ _ hp, _⟩,
    { intro hx, exact h _ _ hx hx (of_same _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_fixed_1 (s : set α) (p : α) :
  (∀ q r ∈ s, ¬ collinear p q r) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ _ _ hp, _⟩,
    { intro hx, exact h _ _ hx hx (of_right _ _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_fixed_1' (s : set α) (p : α) :
  (∀ q r ∈ s, ¬ collinear q p r) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ _ _ hp, _⟩,
    { intro hx, exact h _ _ hx hx (of_ends _ _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_fixed_1'' (s : set α) (p : α) :
  (∀ q r ∈ s, ¬ collinear q r p) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ _ _ hp, _⟩,
    { intro hx, exact h _ _ hx hx (of_left _ _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_fixed_2 (s : set α) (p q : α)
  (hq : q ∈ s) : (∀ r ∈ s, ¬ collinear p q r) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ hp, _⟩,
    { intro hx, exact h _ hq (of_right _ _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_fixed_2' (s : set α) (p q : α)
  (hq : q ∈ s) : (∀ r ∈ s, ¬ collinear p r q) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ hp, _⟩,
    { intro hx, exact h _ hq (of_right _ _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

@[simp]
theorem none_collinear_iff_empty_fixed_2'' (s : set α) (p q : α)
  (hq : q ∈ s) : (∀ r ∈ s, ¬ collinear r p q) ↔ s = ∅ :=
begin
  refine ⟨λ h, set.eq_empty_iff_forall_not_mem.mpr $ λ _, _, λ h _ hp, _⟩,
    { intro hx, exact h _ hq (of_ends _ _) },
    { rw h at hp, exact (set.not_mem_empty _).elim hp }
end

end collinear
end
