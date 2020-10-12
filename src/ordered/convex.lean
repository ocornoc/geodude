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

/-- A set is convex if it is equal to its own convex hull. -/
def is_convex (s : set α) : Prop := convex_hull s = s

end

section
universe u
parameters {α : Type u} [has_betweenness α]

@[simp]
theorem is_convex.convex_def (s : set α) : is_convex s = (convex_hull s = s) :=
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
  apply set.eq_of_subset_of_subset (λ _ h, _) (self_subs_hull _),
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
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _, of_set),
  induction h with _ h₂ _ _ _ _ _ h hv₁ hv₂, { assumption },
  rw [set.mem_singleton_iff] at hv₁ hv₂, rw [hv₁, hv₂] at h,
  exact interval.eq_of_mem_same h
end

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
  apply iff.intro iff_mem_intrv_of_convex (λ hs, _),
  apply set.eq_of_subset_of_subset (λ _ h, _) (λ _, convex_hull.of_set),
  induction h with _ h₂ _ _ _ _ _ h hv₁ hv₂,
      { assumption },
      { exact hs.mpr ⟨_, _, hv₁, hv₂, h⟩ }
end

end is_convex
end
