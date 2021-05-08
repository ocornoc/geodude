/-
  Copyright 2020 Grayson Burton
  License available in the LICENSE file.
-/
import data.set tactic .between

section
universe u
parameters {α : Type u} [has_betweenness α]

/-- The convex hull of a set. -/
/- thanks chris hughes -/
inductive convex_hull (s : set α) : set α
| of_set : ∀ {v}, v ∈ s → convex_hull v
| intrv : ∀ {v₁ v₂ v₃}, convex_hull v₁ → convex_hull v₂ →
  v₃ ∈ interval v₁ v₂ → convex_hull v₃

inductive affine_hull (s : set α) : set α
| of_set : ∀ {v}, v ∈ s → affine_hull v
| of_line : ∀ {v₁ v₂ v₃}, affine_hull v₁ → affine_hull v₂ → v₃ ∈ line v₁ v₂ → affine_hull v₃

def lin_indep_sets (s₁ s₂ : set α) : Prop :=
disjoint (affine_hull s₁) (affine_hull s₂)

def lin_indep (s : set α) : Prop :=
∀ p ∈ s, p ∉ affine_hull (s \ {p})

/-- A set is convex if it is equal to its own convex hull. -/
@[reducible]
def is_convex (s : set α) : Prop :=
convex_hull s = s

@[reducible]
def is_affine (s : set α) : Prop :=
affine_hull s = s

end

section
universe u
parameters {α : Type u} [has_betweenness α]

@[simp]
theorem is_convex.convex_def (s : set α) : is_convex s = (convex_hull s = s) :=
rfl

@[simp]
theorem is_affine.affine_def (s : set α) : is_affine s = (affine_hull s = s) :=
rfl

namespace convex_hull
/-- `x` is in a convex hull of a set iff it's in the original set or it is on a
    line segment between two points that are also in the convex hull. -/
@[simp]
theorem mem_iff {s : set α} (x : α) :
  x ∈ convex_hull s ↔ x ∈ s ∨ ∃ (v₁ v₂ ∈ convex_hull s), x ∈ interval v₁ v₂ :=
begin
  refine ⟨λ h, _, λ h, _⟩,
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
@[simp]
theorem idempotent (s : set α) : convex_hull (convex_hull s) = convex_hull s :=
begin
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _ h, _),
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

theorem eq_of_hull_subs {s : set α} (h : convex_hull s ⊆ s) : is_convex s :=
set.eq_of_subset_of_subset h (self_subs_hull s)

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

@[simp]
theorem of_empty : @convex_hull α _ ∅ = ∅ :=
begin
  apply eq_of_hull_subs (λ _ h, _),
  induction h with _ _ _ _ _ _ _ _ h, { assumption },
  exact (set.not_mem_empty _) h
end

@[simp]
theorem is_empty_iff (s : set α) : (@convex_hull α _ s = ∅) ↔ s = ∅ :=
begin
  refine ⟨λ h, _, λ h, by rw h; exact of_empty⟩,
  rw [←set.subset_empty_iff, ←h],
  apply self_subs_hull
end

@[simp]
theorem of_singleton (p : α) : @convex_hull α _ {p} = {p} :=
begin
  apply eq_of_hull_subs (λ _ h, _),
  induction h with _ h₂ _ _ _ _ _ h hv₁ hv₂, { assumption },
  rw [set.mem_singleton_iff] at hv₁ hv₂, rw [hv₁, hv₂] at h,
  exact interval.eq_of_mem_same h
end

@[simp]
theorem of_univ : @convex_hull α _ set.univ = set.univ :=
set.eq_univ_of_subset (self_subs_hull set.univ) rfl

end convex_hull

namespace affine_hull

/-- `x` is in a affine_hull of a set iff it's in the original set or it is on a line
    between two points that are also in the affine_hull. -/
@[simp]
theorem mem_iff {s : set α} (x : α) : x ∈ affine_hull s ↔ x ∈ s ∨ ∃ (v₁ v₂ ∈ affine_hull s), x ∈ line v₁ v₂ :=
begin
  refine ⟨λ h, _, λ h, _⟩,
    { rcases h with ⟨_, h⟩ | ⟨_, _, _, hv₁, hv₂, h⟩,
        { exact or.inl h },
        { exact or.inr ⟨_, _, hv₁, hv₂, h⟩ }},
    { rcases h with ⟨h⟩ | ⟨_, _, hv₁, hv₂, h⟩,
        { exact of_set h },
        { exact of_line hv₁ hv₂ h }}
end

theorem mem_iff' {s : set α} (x : α) : affine_hull s x ↔ x ∈ s ∨ ∃ (v₁ v₂ ∈ affine_hull s), x ∈ line v₁ v₂ :=
mem_iff x

@[simp]
theorem idempotent (s : set α) : affine_hull (affine_hull s) = affine_hull s :=
begin
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _ h, _),
    { induction h with _ _ _ _ _ _ _ h hv₁ hv₂,
        { assumption },
        { exact of_line hv₁ hv₂ h }},
    { rcases h with ⟨_, h⟩ | ⟨_, _, _, hv₁, hv₂, h⟩,
        { exact of_set (of_set h) },
        { exact of_line (of_set hv₁) (of_set hv₂) h }}
end

/-- Every set is a subset of its affine_hull. -/
theorem self_subs_span (s : set α) : s ⊆ affine_hull s :=
λ _, of_set

/-- If `S₁ ⊆ S₂`, then the affine_hull of `S₁` is also a subset of the affine_hull of `S₂`. -/
theorem is_mono {s t : set α} (hs : s ⊆ t) : affine_hull s ⊆ affine_hull t :=
begin
  intros x h,
  induction h with _ h _ _ _ _ _ h hv₁ hv₂,
    { exact self_subs_span _ (hs h) },
    { exact of_line hv₁ hv₂ h }
    
end

@[simp]
theorem of_empty : @affine_hull α _ ∅ = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros _ h,
  induction h with _ _ _ _ _ _ _ _ h, repeat { assumption }
end

@[simp]
theorem is_empty_iff (s : set α) : (@affine_hull α _ s = ∅) ↔ s = ∅ :=
begin
  refine ⟨λ h, _, λ h, by rw h; exact of_empty⟩,
  rw [←set.subset_empty_iff, ←h],
  apply self_subs_span
end

@[simp]
theorem eq_iff_span_subs (s : set α) : affine_hull s = s ↔ affine_hull s ⊆ s :=
begin
  refine ⟨λ h, by rw h; refl, λ h, set.eq_of_subset_of_subset h _⟩,
  exact self_subs_span _
end

@[simp]
theorem of_singleton (p : α) : @affine_hull α _ {p} = {p} :=
begin
  rw eq_iff_span_subs,
  intros _ h,
  induction h with _ h₂ _ _ _ _ _ h hv₁ hv₂, { assumption },
  rw [set.mem_singleton_iff] at hv₁ hv₂, rw [hv₁, hv₂] at h,
  exact line.eq_of_mem_same h
end

@[simp]
theorem of_univ : @affine_hull α _ set.univ = set.univ :=
set.eq_univ_of_subset (self_subs_span set.univ) rfl

theorem convex_subs_span (s : set α) : convex_hull s ⊆ affine_hull s :=
begin
  intros _ h,
  induction h with _ h _ _ _ _ _ h hv₁ hv₂, { exact of_set h },
  exact of_line hv₁ hv₂ (line.intrv_subs _ _ h)
end

theorem affine (s : set α) : is_affine (affine_hull s) :=
by rw [is_affine, idempotent]


end affine_hull

namespace lin_indep_sets

theorem indep_def (s₁ s₂ : set α) : lin_indep_sets s₁ s₂ = disjoint (affine_hull s₁) (affine_hull s₂) :=
rfl

theorem symm_iff (s₁ s₂ : set α) : lin_indep_sets s₁ s₂ ↔ lin_indep_sets s₂ s₁ :=
by rw [indep_def, indep_def]; exact disjoint.comm

theorem symm {s₁ s₂ : set α} : lin_indep_sets s₁ s₂ → lin_indep_sets s₂ s₁ :=
(symm_iff s₁ s₂).mp

theorem of_empty (s : set α) : lin_indep_sets ∅ s :=
by rw [indep_def, affine_hull.of_empty]; apply set.empty_disjoint

theorem of_empty' (s : set α) : lin_indep_sets s ∅ :=
by rw symm_iff; apply of_empty

@[simp]
theorem of_singletons (p q : α) : @lin_indep_sets α _ {p} {q} ↔ p ≠ q :=
by rw [indep_def, affine_hull.of_singleton, affine_hull.of_singleton, set.disjoint_singleton_left]; refl

@[simp]
theorem of_singleton_left (p : α) (s : set α) : lin_indep_sets {p} s ↔ p ∉ affine_hull s :=
by rw [indep_def, affine_hull.of_singleton, set.disjoint_singleton_left]

@[simp]
theorem of_singleton_right (p : α) (s : set α) : lin_indep_sets s {p} ↔ p ∉ affine_hull s :=
by rw [indep_def, affine_hull.of_singleton, set.disjoint_singleton_right]

end lin_indep_sets

namespace lin_indep

theorem indep_def (s : set α) : lin_indep s = ∀ p ∈ s, p ∉ affine_hull (s \ {p}) :=
rfl

theorem indep_iff_indep_sets (s : set α) : lin_indep s ↔ ∀ p ∈ s, lin_indep_sets {p} (s \ {p}) :=
begin
  rw indep_def,
  refine ⟨λ h _ hp, _, λ h _ hp, _⟩,
    { rw lin_indep_sets.of_singleton_left, exact h _ hp },
    { exact (lin_indep_sets.of_singleton_left _ _).mp (h _ hp) }
end

lemma of_singleton (p : α) : lin_indep ({p} : set α) :=
by intros _ h; induction h; simp

theorem not_iff_ex_in_span (s : set α) : ¬ lin_indep s ↔ ∃ p ∈ s, p ∈ affine_hull (s \ {p}) :=
by rw indep_def; push_neg; tauto

theorem not_iff_ex_in_line (s : set α) :
  ¬ lin_indep s ↔ ∃ (p ∈ s) (q r ∈ affine_hull (s \ {p})), p ∈ line q r :=
begin
  rw not_iff_ex_in_span,
  refine ⟨λ h, _, λ h, _⟩,
    { rcases h with ⟨_, h, h'⟩,
      refine ⟨_, h, _⟩,
      rcases h' with ⟨_, h'⟩ | ⟨_, _, _, h₁, h₂, h'⟩, { exact (h'.right rfl).elim },
      exact ⟨_, _, h₁, h₂, h'⟩ },
    { rcases h with ⟨_, h, _, _, h₀, h₁, h₂⟩, exact ⟨_, h, affine_hull.of_line h₀ h₁ h₂⟩ }
end

theorem of_sup {s₁ s₂ : set α} (h : s₁ ⊆ s₂) (hs₂ : lin_indep s₂) : lin_indep s₁ :=
begin
  rw indep_def at hs₂ ⊢,
  intros _ hp hps,
  specialize hs₂ _ (h hp),
  exact hs₂ ((affine_hull.is_mono $ set.diff_subset_diff_left h) hps)
end

lemma empty : lin_indep (∅ : set α) :=
λ _ h, (set.not_mem_empty _ h).elim

end lin_indep

namespace is_convex

/-- Every convex hull is convex. -/
theorem hulls_are_convex (s : set α) : is_convex (convex_hull s) :=
convex_hull.convex s

theorem ex_set_convex_eq_of_convex {s : set α} (h : is_convex s) : ∃ s', convex_hull s' = s :=
⟨s, h⟩

theorem convex_iff_ex_set_convex_eq (s : set α) : is_convex s ↔ ∃ s', convex_hull s' = s :=
begin
  refine ⟨ex_set_convex_eq_of_convex, _⟩,
  rintro ⟨_, h⟩,
  rw [is_convex, ←h, convex_hull.idempotent]
end

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

theorem of_convex_subs (s : set α) : is_convex s ↔ convex_hull s ⊆ s :=
begin
  refine ⟨λ h _ h', _, λ h, set.eq_of_subset_of_subset h $ convex_hull.self_subs_hull _⟩,
  change _ = _ at h,
  rwa h at h'
end

/-- A set `S` is convex iff, for any point `x`, `x ∈ S` is equivalent to there
    being two more points in `S` such that `x` is on the line segment between
    them. -/
theorem iff_mem_intrv_iff_convex (s : set α) :
  is_convex s ↔ ∀ {x}, x ∈ s ↔ ∃ v₁ v₂ ∈ s, x ∈ interval v₁ v₂ :=
begin
  apply iff.intro iff_mem_intrv_of_convex (λ hs, _),
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _, convex_hull.of_set),
  induction h with _ h₂ _ _ _ _ _ h hv₁ hv₂,
    { assumption },
    { exact hs.mpr ⟨_, _, hv₁, hv₂, h⟩ }
end

theorem intersect_closed {s₁ s₂ : set α} (hs₁ : is_convex s₁) (hs₂ : is_convex s₂) :
  is_convex (s₁ ∩ s₂) :=
begin
  apply (iff_mem_intrv_iff_convex _).mpr (λ _, ⟨λ hp, _, λ hp, _⟩),
    { exact ⟨_, _, hp, hp, interval.end_mem_intrv_left _ _⟩ },
  rcases hp with ⟨_, _, hq, hr, hpqr⟩,
  rw iff_mem_intrv_iff_convex at hs₁ hs₂,
  split,
    { rw hs₁, exact ⟨_, _, hq.left, hr.left, hpqr⟩ },
    { rw hs₂, exact ⟨_, _, hq.right, hr.right, hpqr⟩ }
end

theorem convex_of_ex_hull_eq (s : set α) : is_convex s ↔ ∃ s₁, s = convex_hull s₁ :=
begin
  refine ⟨λ h, ⟨s, eq.symm h⟩, λ h, _⟩,
  cases h with _ h, rw h,
  apply hulls_are_convex
end

protected theorem univ : @is_convex α _ set.univ :=
convex_hull.of_univ

end is_convex

theorem convex_hull.eq_bInter_convex (s : set α) :
  convex_hull s = ⋂ (s₁ ⊇ s) (h : is_convex s₁), s₁ :=
begin
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _ h, _),
    { simp only [is_convex.convex_def, set.mem_Inter],
      intros _ hs₁ hs₂, rw ←hs₂,
      exact convex_hull.is_mono hs₁ h },
    { simp only [set.mem_Inter] at h,
      specialize h _ (convex_hull.self_subs_hull _),
      exact h (is_convex.hulls_are_convex _) }
end

namespace is_affine

/-- Every linear affine_hull is a linear subspace. -/
theorem spans_are_affines (s : set α) : is_affine (affine_hull s) :=
affine_hull.affine s

theorem ex_set_span_eq_of_affine {s : set α} (h : is_affine s) : ∃ s', affine_hull s' = s :=
⟨s, h⟩

theorem affine_iff_ex_set_span_eq (s : set α) : is_affine s ↔ ∃ s', affine_hull s' = s :=
begin
  refine ⟨ex_set_span_eq_of_affine
, _⟩,
  rintro ⟨_, h⟩,
  rw [is_affine
, ←h, affine_hull.idempotent]
end

/-- If `S` is a linear subspace, then every point in `S` lies on some line
    intersecting `S`. -/
theorem mem_line_of_mem {s : set α} (hs : is_affine s) {x : α} (h : x ∈ s) :
  ∃ v₁ v₂ ∈ s, x ∈ line v₁ v₂ :=
⟨_, _, h, h, line.end_mem_line_left _ _⟩

/-- If `S` is a linear subspace, then a point is in `S` iff it is on a line
    intersecting two points in `S`. -/
theorem mem_iff_mem_line {s : set α} (hs : is_affine s) (x : α) :
  x ∈ s ↔ ∃ v₁ v₂ ∈ s, x ∈ line v₁ v₂ :=
begin
  apply iff.intro (mem_line_of_mem hs),
  rw affine_def at hs,
  rintro ⟨_, _, hv₁, hv₂, h⟩,
  rw ←hs at *,
  exact affine_hull.of_line hv₁ hv₂ h
end

/-- A set `S` is a linear subspace iff, for any point `x`, `x ∈ S` is equivalent
    to there being two more points in `S` such that `x` is on the line between
    them. -/
theorem affine_iff_mem_iff_mem_line (s : set α) :
  is_affine
 s ↔ ∀ x, x ∈ s ↔ ∃ v₁ v₂ ∈ s, x ∈ line v₁ v₂ :=
begin
  apply iff.intro mem_iff_mem_line (λ hs, _),
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _, affine_hull.of_set),
  induction h with _ h₂ _ _ _ _ _ h hv₁ hv₂,
    { assumption },
    { exact (hs _).mpr ⟨_, _, hv₁, hv₂, h⟩ }
end

protected theorem is_convex (s : set α) : is_convex $ affine_hull s :=
begin
  apply set.eq_of_subset_of_subset (λ _ h, _) (convex_hull.self_subs_hull _),
  induction h with _ h _ _ _ _ _ h hv₁ hv₂, { assumption },
  exact affine_hull.of_line hv₁ hv₂ (line.intrv_subs _ _ h)
end

protected theorem univ : @is_affine α _ set.univ :=
affine_hull.of_univ

end is_affine

theorem affine_hull.eq_bInter_affine (s : set α) :
  affine_hull s = ⋂ (s₁ ⊇ s) (h : is_affine s₁), s₁ :=
begin
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _ h, _),
    { simp only [is_affine.affine_def, set.mem_Inter],
      intros _ hs₁ hs₂, rw ←hs₂,
      exact affine_hull.is_mono hs₁ h },
    { simp only [set.mem_Inter] at h,
      specialize h _ (affine_hull.self_subs_span _),
      exact h (affine_hull.affine
     _) }
end
end
