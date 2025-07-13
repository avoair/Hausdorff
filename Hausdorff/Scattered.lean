import Hausdorff.Isomorphisms

open Classical
universe u

/-- We define scattered from the perspective of Cantor's theorem -/
def Scattered (X : LinOrd) : Prop := IsEmpty (ℚ ↪o X)

/-- Any order isomoprhic to a scattered order is scattered -/
lemma scatttered_of_iso_to_scattered (X : LinOrd) (Y : LinOrd) (f : X ≃o Y)
  (h : Scattered Y) : Scattered X := by
  rw [Scattered, <-not_nonempty_iff, <-exists_true_iff_nonempty] at h
  by_contra contra
  rw [Scattered, not_isEmpty_iff] at contra
  rcases contra with ⟨g⟩
  apply h
  use OrderEmbedding_comp g (OrderIso.toOrderEmbedding f)

/-- Well orders are scattered -/
lemma scattered_of_wellFounded (X : LinOrd) : WellFounded X.str.lt → Scattered X := by
  intro hwf
  by_contra h
  rw [Scattered, <-not_nonempty_iff, not_not] at h
  rcases h with ⟨f⟩
  rcases WellFounded.has_min hwf (Set.range f) (Set.range_nonempty f) with ⟨m, h₁, h₂⟩
  let ⟨x, hx⟩ := Set.mem_range.mp h₁
  let ⟨y, hy⟩ := (NoBotOrder.to_noMinOrder ℚ).exists_lt x
  apply h₂ (f y) (by exact Set.mem_range_self y)
  rw [<- hx]
  exact (OrderEmbedding.lt_iff_lt f).mpr hy

/-- Reverse well orders are scattered -/
lemma scattered_of_rev_wellFounded (X : LinOrd) : WellFounded (X.str.swap).lt → Scattered X := by
  intro hwf
  by_contra h
  rw [Scattered, <-not_nonempty_iff, not_not] at h
  rcases h with ⟨f⟩
  rcases WellFounded.has_min hwf (Set.range f) (Set.range_nonempty f) with ⟨m, h₁, h₂⟩
  let ⟨x, hx⟩ := Set.mem_range.mp h₁
  let ⟨y, hy⟩ := (NoTopOrder.to_noMaxOrder ℚ).exists_gt x
  apply h₂ (f y) (by exact Set.mem_range_self y)
  rw [<- hx]
  exact (OrderEmbedding.lt_iff_lt f).mpr hy
