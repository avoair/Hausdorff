-- A full proof that every linear order has a well-ordered, cofinal subset

import Mathlib.Tactic

section
variable {α : Type*} [LinearOrder α]

/-- End extension ordering on sets. A is an end extension of B iff B is an initial segment of A -/
def end_ext (A B : Set α) := A ⊆ B ∧ ∀ b ∈ (B \ A), ∀ a ∈ A, a < b

local infix:50 " ≼ " => end_ext

theorem end_ext_trans (A B C : Set α): A ≼ B → B ≼ C → A ≼ C := by
  intro hab hbc
  constructor
  · apply subset_trans hab.left hbc.left
  · intro c hc a ha
    have : c ∈ (B \ A) ∨ c ∈ (C \ B) := by  ----- CONDENSE HERE -- ONLY ONE RCASES
      rcases Classical.em (c ∈ B) with h1 | h1
      · left ; exact And.intro h1 hc.right
      · right ; exact And.intro hc.left h1
    rcases this with h1 | h2
    · apply hab.right c h1 _ ha
    · apply hbc.right _ h2
      apply hab.1 ha
end

/-- Collection of well-founded linear orders of α -/
abbrev WellFoundedSet (α : Type*) [LinearOrder α] := {A : Set α // A.WellFoundedOn (· < ·)}

#check Countable
variable {α : Type*} [LinearOrder α]

/-- end_ext operation specialized to WF -/
def end_ext'  (A B : WellFoundedSet α) := end_ext A.1 B.1
local infix:50 " ≼ " => end_ext'

theorem end_ext_trans' (A B C : WellFoundedSet α): A ≼ B → B ≼ C → A ≼ C := by
  apply end_ext_trans

/-- Given  a set of WellFoundedSet, return the same contents as a set of sets-/
def sets_of_wellFoundedSets (α : Type*) [LinearOrder α] (c : Set (WellFoundedSet α)) : Set (Set α)
               := Set.image (λ x => x.1) c

/-- If x is an element of a union over the image of a WF_convert call, it is
    a member of one of the WellFoundedSet -/
lemma mem_sUnion_of_wellFoundedSets {α : Type*} [LinearOrder α] {C : Set (WellFoundedSet α)}
                       (x) (h: x ∈ ⋃₀ (sets_of_wellFoundedSets α C)) : ∃ c ∈ C, x ∈ c.1 := by
  rcases Set.mem_sUnion.mp h with ⟨c₀, hc₀⟩
  simp only [sets_of_wellFoundedSets] at hc₀
  rcases hc₀.left with ⟨c₀', inC, c_eq⟩
  subst c₀; use ⟨c₀', c₀'.2⟩
  exact And.intro inC hc₀.right

/-- The union of a chain of WellFoundedSet is well-founded -/
lemma wellFoundedOn_of_chain_sUnion {α : Type*} [LinearOrder α] (C : Set (WellFoundedSet α))
  (isChain_C : IsChain (. ≼ .) C) : (⋃₀ (sets_of_wellFoundedSets α C)).WellFoundedOn (· < ·) := by
  rw [Set.wellFoundedOn_iff_no_descending_seq]
  intro f
  by_contra hf_image
  rcases mem_sUnion_of_wellFoundedSets (f 0) (hf_image 0) with ⟨c, hc⟩
  apply Set.wellFoundedOn_iff_no_descending_seq.mp c.2 f
  intro n
  by_contra contra
  rcases mem_sUnion_of_wellFoundedSets (f n) (hf_image n) with ⟨c', hc'⟩

  have :c ≠ c' := by
    intro h
    rw [<-h] at hc'
    apply contra hc'.right

  rcases isChain_C hc.left hc'.left this with h1 | h1
  · have : f 0 < f n := by
      exact h1.right (f n) (And.intro hc'.right contra) (f 0) hc.right
    exact (Nat.lt_irrefl 0) (lt_of_le_of_lt  (Nat.zero_le n) ((@f.map_rel_iff' 0 n).mp this))
  · apply Set.not_subset_iff_exists_mem_notMem.mpr
    use (f n)
    · exact And.intro hc'.right contra
    · exact h1.left

/-- Every linear order has a well ordered, cofinal subset -/
lemma exists_cofinal_wellFoundedOn_subset  {α : Type*} [LinearOrder α]:
  ∃ (A : Set α), IsCofinal A ∧ A.WellFoundedOn (· < ·) := by

  -- every chain of well orders (ordered by end extension) is bounded
  have zorn_prop : ∀ (C : Set (WellFoundedSet α)),
                  IsChain (. ≼ .) C
                  → ∃ (ub : WellFoundedSet α), ∀ a ∈ C, a ≼ ub := by
    intro C hC

    let maxwf := (⋃₀ (sets_of_wellFoundedSets α C))
    have maxwf_wf : maxwf.WellFoundedOn (· < ·) := by
      exact wellFoundedOn_of_chain_sUnion C hC

    use ⟨maxwf, maxwf_wf⟩
    intro a hac
    constructor
    · have : ↑a ∈ sets_of_wellFoundedSets α C := by use a
      apply Set.subset_sUnion_of_subset (sets_of_wellFoundedSets α C) a
      simp only [subset_refl]
      exact this
    · intro x hx y hy
      rcases mem_sUnion_of_wellFoundedSets x hx.left with ⟨c, hc⟩
      rcases eq_or_ne c a with eq | neq
      · by_contra _
        rw [eq] at hc
        exact hx.right hc.right
      · specialize hC hc.left hac neq
        rcases hC with h1 | h2
        · by_contra _
          exact hx.right (h1.left hc.right)
        · exact h2.right x (And.intro hc.right hx.right) y hy

  have le_trans_overWF : ∀ {a b c : WellFoundedSet α}, a ≼ b → b ≼ c → a ≼ c := by
    intro a b c hab hbc
    exact end_ext_trans a.1 b.1 c.1 hab hbc

  have max_elt: ∃ (m : (WellFoundedSet α)), ∀ (a : (WellFoundedSet α)), m ≼ a → a ≼ m := by
    exact exists_maximal_of_chains_bounded zorn_prop le_trans_overWF
  rcases max_elt with ⟨M, hM⟩
  use M
  constructor
  · by_contra not_cof
    simp only [IsCofinal, not_forall, not_exists, not_le] at not_cof
    rcases not_cof with ⟨a, ha⟩
    push_neg at ha

    let M' := insert a M.1
    have hM' : M'.WellFoundedOn fun x1 x2 => x1 < x2 := Set.WellFoundedOn.insert M.2 a
    let M'₀ : WellFoundedSet α := ⟨M', hM'⟩
    have h :  M ≼ M'₀ := by
      constructor
      · exact Set.subset_insert a (M.1)
      · intro y hy x hx
        have : y = a := by
          rcases hy.left with h | h
          · exact h
          · by_contra _ ; exact hy.right h
        rw [this]
        exact ha x hx

    have Meq : M'₀.1 = M.1 := by
      exact Set.Subset.antisymm ((hM M'₀ h).left) (h.left)

    have aM : a ∈ M'₀.1 := by
      exact Set.mem_insert a M.1
    rw [Meq] at aM
    exact lt_irrefl a (ha a aM)
  · exact M.2
