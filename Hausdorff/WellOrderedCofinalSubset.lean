-- Every linear order has a well-ordered, cofinal subset
import Mathlib.Tactic

section
variable {α : Type*} [LinearOrder α]

/-- End extension ordering on sets. A is an end extension of B iff B is an initial segment of A -/
def end_ext (s t : Set α) := s ⊆ t ∧ ∀ x ∈ t \ s, ∀ y ∈ s, y < x

local infix:50 " ≼ " => end_ext

/-- End extension is transitive -/
theorem end_ext_trans (s₁ s₂ s₃ : Set α) (h₁ : s₁ ≼ s₂) (h₂ : s₂ ≼ s₃) : s₁ ≼ s₃ := by
  constructor
  · apply subset_trans h₁.left h₂.left
  · intro y hy x hx
    rcases Classical.em (y ∈ s₂) with h1 | h1
    · exact h₁.right y (And.intro h1 hy.right) x hx
    · exact h₂.right y (And.intro hy.left h1) x (h₁.left hx)
end

/-- Collection of well-founded linear orders of α -/
abbrev WellFoundedSet (α : Type*) [LinearOrder α] := {s : Set α // s.WellFoundedOn (· < ·)}

variable {α : Type*} [LinearOrder α]

/-- end_ext operation specialized to WellFoundedSets -/
def end_ext'  (s t : WellFoundedSet α) := end_ext s.1 t.1
local infix:50 " ≼ " => end_ext'

theorem end_ext_trans' (s₁ s₂ s₃ : WellFoundedSet α) (h₁ : s₁ ≼ s₂) (h₂ : s₂ ≼ s₃) : s₁ ≼ s₃ := by
  apply end_ext_trans s₁.1 s₂.1 s₃.1 h₁ h₂

/-- Given  a set of WellFoundedSet, return the same contents as a set of sets-/
def sets_of_wellFoundedSets (S : Set (WellFoundedSet α)) : Set (Set α) := Set.image (λ x => x.1) S

/-- If x is an element of a union over the image of a WF_convert call, it is
    a member of one of the WellFoundedSet -/
lemma mem_sUnion_of_wellFoundedSets {S : Set (WellFoundedSet α)}
    (x : α) (h: x ∈ ⋃₀ (sets_of_wellFoundedSets S)) : ∃ s ∈ S, x ∈ s.1 := by
  rcases Set.mem_sUnion.mp h with ⟨s, hs⟩
  simp only [sets_of_wellFoundedSets] at hs
  rcases hs.left with ⟨t, ht, _⟩
  subst s; use ⟨t, t.2⟩
  exact And.intro ht hs.right

/-- The union of a chain of WellFoundedSet is well-founded -/
lemma wellFoundedOn_of_chain_sUnion (C : Set (WellFoundedSet α))
    (isChain_C : IsChain (· ≼ ·) C) : (⋃₀ (sets_of_wellFoundedSets C)).WellFoundedOn (· < ·) := by
  rw [Set.wellFoundedOn_iff_no_descending_seq]
  intro f
  by_contra hf_image
  rcases mem_sUnion_of_wellFoundedSets (f 0) (hf_image 0) with ⟨s, hs⟩
  apply Set.wellFoundedOn_iff_no_descending_seq.mp s.2 f
  intro n
  by_contra h
  rcases mem_sUnion_of_wellFoundedSets (f n) (hf_image n) with ⟨t, ht⟩

  have : s ≠ t := by
    intro h₁
    rw [<-h₁] at ht
    apply h ht.right

  rcases isChain_C hs.left ht.left this with h₁ | h₁
  · have : f 0 < f n := by
      exact h₁.right (f n) (And.intro ht.right h) (f 0) hs.right
    exact (Nat.lt_irrefl 0) (lt_of_le_of_lt  (Nat.zero_le n) ((@f.map_rel_iff' 0 n).mp this))
  · apply Set.not_subset_iff_exists_mem_notMem.mpr
    use (f n)
    · exact And.intro ht.right h
    · exact h₁.left

/-- Every linear order has a well ordered, cofinal subset -/
lemma exists_cofinal_wellFoundedOn_subset :
    ∃ (s : Set α), IsCofinal s ∧ s.WellFoundedOn (· < ·) := by
  -- every chain of well orders (ordered by end extension) is bounded
  have zorn_prop (C : Set (WellFoundedSet α)) (hC : IsChain (. ≼ .) C) :
      ∃ (ub : WellFoundedSet α), ∀ a ∈ C, a ≼ ub := by
    use ⟨(⋃₀ (sets_of_wellFoundedSets C)), wellFoundedOn_of_chain_sUnion C hC⟩
    intro a hac
    constructor
    · apply Set.subset_sUnion_of_subset (sets_of_wellFoundedSets C) a
      simp only [subset_refl]
      use a
    · intro x hx y hy
      rcases mem_sUnion_of_wellFoundedSets x hx.left with ⟨c, hc⟩
      rcases eq_or_ne c a with he | hne
      · by_contra
        rw [he] at hc
        exact hx.right hc.right
      · rcases hC hc.left hac hne with h | h
        · by_contra
          exact hx.right (h.left hc.right)
        · exact h.right x (And.intro hc.right hx.right) y hy

  have exists_max_elt : ∃ (m : (WellFoundedSet α)), ∀ (a : (WellFoundedSet α)), m ≼ a → a ≼ m :=
    exists_maximal_of_chains_bounded zorn_prop (end_ext_trans' _ _ _)

  rcases exists_max_elt with ⟨m, hm⟩
  use m
  constructor
  · by_contra not_cof
    simp only [IsCofinal, not_forall, not_exists, not_le] at not_cof
    rcases not_cof with ⟨a, ha⟩
    push_neg at ha

    let m' : WellFoundedSet α := ⟨insert a m.1, Set.WellFoundedOn.insert m.2 a⟩
    have h : m ≼ m' := by
      constructor
      · exact Set.subset_insert a (m.1)
      · intro y hy x hx
        have : y = a := by
          rcases hy.left with h | h
          · exact h
          · by_contra; exact hy.right h
        rw [this]
        exact ha x hx

    have meq : m'.1 = m.1 := by
      exact Set.Subset.antisymm ((hm m' h).left) (h.left)
    exact lt_irrefl a (ha a (Set.insert_eq_self.mp meq))
  · exact m.2
