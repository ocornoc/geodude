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
def lindep_to_simplex (vs : list α) : Prop :=
∃ p, lin_indep p $ convex_hull {z | z ∈ vs}

@[simp]
theorem lindep_to_simplex.dim_def (vs : list α) :
  lindep_to_simplex vs = ∃ p, lin_indep p $ convex_hull {z | z ∈ vs} :=
rfl

/-- A simplex is nondegenerate iff, for every two endpoints and point `p`, if
    both endpoints are distinct from `p`, then all three points are not
    collinear to each other. -/
def nondegen_simplex (l : list α) : Prop :=
l.nodup ∧ ∀ v₁ v₂ v₃ ∈ l, v₂ = v₁ ∨ v₂ = v₃ ∨ ¬ collinear v₁ v₃ v₂

/-- For any set `S`, `S₁` and `S₂` form a dependent bipartition of `S` iff
    their union `S₁ ∪ S₂ = S` and there is no point in one that is between two
    points of the other. -/
def dep_bipartition (s s₁ s₂ : set α) : Prop :=
s₁ ∪ s₂ = s ∧ (∀ p ∈ s₁, ¬ ∃ q r ∈ s₂, between q p r) ∧
  (∀ p ∈ s₂, ¬ ∃ q r ∈ s₁, between q p r)

end

/-- Ordered geometry, without an axiom of dimension. -/
class {u} ordered_geo_nodim (α : Type u) extends has_betweenness α :=
(pasch₁ {v₁ v₂ : α} (v₃ v₄ ∈ line v₁ v₂) : v₃ ≠ v₄ → v₁ ∈ line v₃ v₄)
(pasch₂ {v₁ v₂ v₃ v₄ v₅ : α} : nondegen_simplex [v₁, v₂, v₃] → between v₂ v₃ v₄ →
  between v₃ v₅ v₂ → ∃ z ∈ line v₄ v₅, between v₁ z v₂)
(dedekind {p q : α} {s₁ s₂ : set α} : nonempty s₁ → nonempty s₂ →
  dep_bipartition (line p q) s₁ s₂ →
    (∃ v₁ ∈ s₁, ∀ (v₂ ∈ s₁ \ {v₁}) (v₃ ∈ s₂), between v₂ v₁ v₃)
    ∨ (∃ v₁ ∈ s₂, ∀ (v₂ ∈ s₂ \ {v₁}) (v₃ ∈ s₁), between v₂ v₁ v₃))

/-- Ordered geometry, indexed by a dimension `d` for which the appropriate
    axioms of dimensionality apply for any list of points at most `d` long. -/
class {u} ordered_geo (α : Type u) (d : ℕ) extends ordered_geo_nodim α :=
(lin_simp (vs : list α) : vs.length ≤ d → lindep_to_simplex vs)

/-- Ordered geometry with a finite dimension `d`. This finiteness is shown by
    the property that every non-degenerate convex hull of `d` vertices has two
    points in it that are collinear to any point. -/
class {u} ordered_geo_fin (α : Type u) (d : ℕ) extends ordered_geo α d :=
(all_in_space : ∀ {vs : vector α d.succ}, nondegen_simplex vs.val →
  ∀ v₁, ∃ v₂ v₃ ∈ convex_hull {p | p ∈ vs.val}, collinear v₁ v₂ v₃)

/-- An infinite ordered geometry, with the property that the axiom of
    dimensionality holds for any dimension. -/
class {u} ordered_geo_inf (α : Type u) extends ordered_geo_nodim α :=
(lin_any_simp (vs : list α) : lindep_to_simplex vs)

section
universe u
parameter {α : Type u}
namespace nondegen_simplex
section
parameter [has_betweenness α]

theorem of_subset {l : list α} (hl : nondegen_simplex l) :
  ∀ l₁ <+ l, nondegen_simplex l₁ :=
begin
  intros _ h,
  refine ⟨list.nodup_of_sublist h hl.left, λ _ _ _ hp hq hr, _⟩,
  have hp₁ := list.sublist.subset h hp,
  have hq₁ := list.sublist.subset h hq,
  have hr₁ := list.sublist.subset h hr,
  exact hl.right _ _ _ hp₁ hq₁ hr₁
end

theorem not_of_not_subset {l₁ l : list α} (hl₁ : ¬ nondegen_simplex l₁)
  (hl : l₁ <+ l) : ¬ nondegen_simplex l :=
by revert hl₁; contrapose!; exact λ h, of_subset h _ hl

theorem of_nil : nondegen_simplex (@list.nil α) :=
⟨by simp, by tauto⟩

theorem of_single (x : α) : nondegen_simplex [x] :=
⟨by simp, by finish⟩

end
end nondegen_simplex

namespace ordered_geo

instance (d : ℕ) [ordered_geo α d] : nonempty α :=
(lin_simp [] (dec_trivial : 0 ≤ d)).rec_on $ λ w _, nonempty.intro w

theorem ordered_geo_subspace {d : ℕ} [ordered_geo α d] (d' : ℕ) (h : d' ≤ d) :
  ordered_geo α d' :=
ordered_geo.mk $ λ _ hl, lin_simp _ $ le_trans hl h

lemma ordered_geo_1d (d : ℕ) [ordered_geo α d] : ordered_geo α 0 :=
ordered_geo_subspace _ (dec_trivial : 0 ≤ d)

/-- For any point, there exists another point that's not equal to it. -/
theorem ex_not_eq {d : ℕ} [ordered_geo α $ d + 1] (p : α) : ∃ q, p ≠ q :=
begin
  cases lin_simp [p] (dec_trivial : 1 ≤ d + 1) with w h,
  use w,
  simp only [list.mem_singleton] at h,
  specialize h p p (convex_hull.of_set rfl) (convex_hull.of_set rfl),
  exact h.elim (collinear.of_left' _ _)
end

instance {d : ℕ} [ordered_geo α $ d + 1] : nontrivial α :=
(@nonempty _ $ ordered_geo_1d d.succ).rec_on
  $ λ p, nontrivial.mk ⟨p, @ex_not_eq d _ _⟩

/-- For any line, there exists a point that's not in it. -/
theorem ex_not_on_line {d : ℕ} [ordered_geo α $ d + 2] (p q : α) :
  ∃ r, r ∉ line p q :=
begin
  cases lin_simp [p, q] (dec_trivial : 2 ≤ d + 2) with w h,
  refine ⟨w, λ hw, _⟩,
  specialize h p q (convex_hull.of_set $ or.inl rfl),
  replace hw : collinear p q w := ⟨p, q, by simp, by simp, hw⟩,
  exact (h $ convex_hull.of_set $ by simp).elim hw
end

/-- For any plane, there exists a point that's not in it. -/
theorem ex_not_on_plane {d : ℕ} [ordered_geo α $ d + 3] (p q r : α) :
  ∃ x, x ∉ convex_hull {y | y ∈ [p, q, r]} :=
(lin_simp [p, q, r] (dec_trivial : 3 ≤ d + 3)).rec_on
  $ λ w h, Exists.intro w h.not_mem_of_indep

end ordered_geo
end

section
universe u
parameters {α : Type u} [ordered_geo_inf α]
namespace ordered_geo_inf

instance (d : ℕ) : ordered_geo α d := {lin_simp := λ l _, lin_any_simp l}

/-- For any point, there exists another point that's not equal to it. -/
theorem ex_not_eq (p : α) : ∃ q, p ≠ q :=
@ordered_geo.ex_not_eq _ 0 (ordered_geo _) p

instance : nonempty α := @ordered_geo.nonempty _ 0 _
instance : nontrivial α := @ordered_geo.nontrivial _ 0 _

/-- For any line, there exists a point that's not in it. -/
theorem ex_not_on_line (p q : α) : ∃ r, r ∉ line p q :=
@ordered_geo.ex_not_on_line _ 0 (ordered_geo _) p q

/-- For any plane, there exists a point that's not in it. -/
theorem ex_not_on_plane (p q r : α) :
  ∃ x, x ∉ convex_hull {y | y ∈ [p, q, r]} :=
@ordered_geo.ex_not_on_plane _ 0 (ordered_geo _) p q r

/-- For any potentially-degenerate simplex defined by the vertices `l`, there
    is a point that's not in the convex hull of `l`. -/
lemma ex_point_not_mem_simplex_hull (l : list α) :
  ∃ p, p ∉ convex_hull {q | q ∈ l} :=
begin
  classical,
  by_contra h,
  push_neg at h,
  cases lin_any_simp l with w hw,
  rcases collinear.ex_collinear_of_mem (h w) with ⟨_, _, hp, hq, hpq⟩,
  exact hw _ _ hp hq hpq.rotate
end

theorem psig_nondegen_simplex [inhabited α]
  (hlas : Π vs : list α, lindep_to_simplex_psig vs) (d : ℕ) :
    Σ' vs : vector α d, nondegen_simplex vs.val :=
begin
  induction d with d hd, { exact ⟨vector.nil, nondegen_simplex.of_nil⟩ },
  induction d with d hd,
    { exact ⟨⟨[arbitrary α], rfl⟩, by simp, by finish⟩ },
  rcases hd with ⟨⟨l, h⟩, hvs⟩,
  rcases hlas l with ⟨p, hp⟩,
  suffices : (p :: ⟨l, h⟩ : vector α _).val.nodup,
  refine ⟨vector.cons p ⟨l, h⟩, this, λ v₁ v₂ v₃ hv₁ hv₂ hv₃, _⟩,
  rw lin_indep at hp,
  have : subtype.val (p :: (⟨l, h⟩ : vector _ _)) = p :: l := rfl,
  rw [this, list.mem_cons_iff] at hv₁ hv₂ hv₃,
  rw (rfl : subtype.val (subtype.mk l h) = l) at hvs,
  rw collinear.none_collinear_iff_empty_fixed_1'' at hp,
  rw [convex_hull.is_empty_iff, set.eq_empty_iff_forall_not_mem] at hp,
  have : 0 < l.length := by rw h; exact nat.succ_pos',
  cases list.length_pos_iff_exists_mem.mp this with w hw,
  exact (hp _).elim hw,
  apply list.nodup_cons_of_nodup (λ hp₁, _) hvs.left,
  change p ∈ {z : α | z ∈ subtype.val (⟨l, h⟩ : vector α _)} at hp₁,
  exact lin_indep.not_indep_of_mem (convex_hull.of_set hp₁) hp
end

/-- For any length `d`, there is a nondegenerate simplex with `d` vertices. -/
theorem ex_nondegen_simplex (d : ℕ) :
  ∃ vs : vector α d, nondegen_simplex vs.val :=
begin
  induction d with d hd, { exact ⟨vector.nil, nondegen_simplex.of_nil⟩ },
  induction d with d hd,
    { cases ordered_geo_inf.nonempty with w,
      exact ⟨⟨[w], rfl⟩, by simp, by finish⟩ },
  rcases hd with ⟨⟨l, h⟩, hvs⟩,
  rcases lin_any_simp l with ⟨p, hp⟩,
  suffices : (p :: ⟨l, h⟩ : vector α _).val.nodup,
  refine ⟨vector.cons p ⟨l, h⟩, this, λ v₁ v₂ v₃ hv₁ hv₂ hv₃, _⟩,
  rw lin_indep at hp,
  have : subtype.val (p :: (⟨l, h⟩ : vector _ _)) = p :: l := rfl,
  rw [this, list.mem_cons_iff] at hv₁ hv₂ hv₃,
  rw (rfl : subtype.val (subtype.mk l h) = l) at hvs,
  rw collinear.none_collinear_iff_empty_fixed_1'' at hp,
  rw [convex_hull.is_empty_iff, set.eq_empty_iff_forall_not_mem] at hp,
  have : 0 < l.length := by rw h; exact nat.succ_pos',
  cases list.length_pos_iff_exists_mem.mp this with w hw,
  exact (hp _).elim hw,
  apply list.nodup_cons_of_nodup (λ hp₁, _) hvs.left,
  change p ∈ {z : α | z ∈ subtype.val (⟨l, h⟩ : vector α _)} at hp₁,
  exact lin_indep.not_indep_of_mem (convex_hull.of_set hp₁) hp
end

/-- It's false that for any nondegenerate simplex with `d` vertices and point
    `p`, there are two points in the convex hull of the simplex -/
theorem not_all_in_space (d : ℕ) : ¬ ∀ {vs : vector α d.succ},
  nondegen_simplex vs.val → ∀ v₁, ∃ v₂ v₃ ∈ convex_hull {p | p ∈ vs.val},
    collinear v₁ v₂ v₃ :=
begin
  intro hvs,
  rcases ex_nondegen_simplex (d + 1) with ⟨vs, hl⟩,
  cases ordered_geo_inf.lin_any_simp vs.val with w hw,
  rcases hvs hl w with ⟨_, _, hp, hq, hpq⟩,
  apply hw _ _ hp hq,
  rwa ←collinear.rotate_iff
end

/-- For any `d`, there's a nondegenerate simplex with `d` vertices and a point
    `p` that's linearly independent to the convex hull of the simplex. -/
theorem ex_ndsimp_ex_p_lindep (d : ℕ) : ∃ vs : vector α d.succ,
  nondegen_simplex vs.val ∧ ∃ p, lin_indep p (convex_hull {p | p ∈ vs.val}) :=
begin
  have := not_all_in_space d,
  push_neg at this,
  rcases this with ⟨v, hv1, x, hx⟩,
  refine ⟨v, hv1, x, _⟩,
  rw collinear.none_collinear_iff_empty_fixed_1 at hx,
  rwa [lin_indep.indep_def, collinear.none_collinear_iff_empty_fixed_1'']
end

end ordered_geo_inf
end
