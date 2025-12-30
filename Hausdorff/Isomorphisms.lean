import Mathlib.Tactic
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.CountableDenseLinearOrder

open Classical
universe u

/-- shorthand for a Lex Sum as a Linord -/
abbrev dLexOrd (α : LinOrd) (β : α.carrier → LinOrd) : LinOrd :=
  { carrier := Σₗ w, (β w), str := Sigma.Lex.linearOrder }

/-- reverse the ordering on a LinOrd -/
abbrev linOrd_swap (α : LinOrd) : LinOrd := { carrier := α, str := α.str.swap }

/-- The rationals are order isomorphic to any nonempty open interval of the rationals -/
lemma OrderIso_Rat_to_interval (a b : ℚ) (h : a < b): Nonempty (ℚ ≃o {c | a < c ∧ c < b}) := by
  apply @Order.iso_of_countable_dense ℚ {c | a < c ∧ c < b} _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · exact SetCoe.countable {c | a < c ∧ c < b}
  · constructor; intro a' b' h
    let ⟨z, h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense a'.1 b'.1 h
    use ⟨z, And.intro (lt_trans a'.2.left h₁.left) (lt_trans h₁.right b'.2.right)⟩
    exact h₁
  · constructor; intro a'
    let ⟨b', h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense a a'.1 a'.2.left
    use ⟨b', And.intro h₁.left (lt_trans h₁.right a'.2.right)⟩
    exact h₁.right
  · constructor
    intro a'
    let ⟨b', h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense a'.1 b a'.2.right
    use ⟨b', And.intro (lt_trans a'.2.left h₁.left) h₁.right⟩
    exact h₁.left
  · let ⟨c, h₁⟩ := LinearOrderedSemiField.toDenselyOrdered.dense a b h
    exact ⟨c, h₁⟩

/-- If subset of a dLexOrd is contained in a single suborder, it embeds that suborder -/
def embed_dLexOrd {α : LinOrd} {β : α.carrier → LinOrd} (x : α.carrier)
    (s : Set (dLexOrd α β)) (h : ∀ y ∈ s, y.1 = x) :
    s ↪o β x where
  toFun := fun x => h x.1 x.2 ▸ x.1.2
  inj' := by
    rintro ⟨⟨x11, x12⟩, h₁⟩ ⟨⟨x21, x22⟩, h₂⟩
    have : x11 = x := h _ h₁
    subst this
    have : x21 = x11 := h _ h₂
    subst this
    simp_all only [implies_true]
  map_rel_iff' := by
    rintro ⟨⟨x11, x12⟩, h₁⟩ ⟨⟨x21, x22⟩, h₂⟩
    have : x11 = x := h _ h₁
    subst this
    have : x21 = x11 := h _ h₂
    subst this
    rw [Subtype.mk_le_mk, Sigma.Lex.le_def]
    simp

def OrderEmbedding_restrict {α β : Type*} [LE α] [LE β] (f : α ↪o β) (s : Set α) : s ↪o f '' s where
  toFun := fun x => ⟨f x, by simp⟩
  inj' := by
    intro x y
    simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
    exact fun a ↦ SetCoe.ext a
  map_rel_iff' := RelEmbedding.map_rel_iff f

/-- like Finset.coeEmb, but for general Set type-/
def Set.coeEmb {L : LinOrd.{u}} (s : Set L) : s ↪o L where
  toFun := fun x => x
  inj' := by intro _ _ h; exact SetCoe.ext h
  map_rel_iff' := by trivial

/-- If B ⊆ A, B as a Set A is isomorphic to B-/
def linOrd_subtype_iso {L : LinOrd.{u}} (s t : Set L) (h₁ : t ⊆ s) :
  (LinOrd.mk {x : s | x.1 ∈ t}) ≃o (LinOrd.mk t) where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun x => ⟨⟨x.1, h₁ x.2⟩, x.2⟩
  left_inv := by intro _ ; trivial
  right_inv := by intro _ ; trivial
  map_rel_iff' := by trivial

/-- Define a linear order with two elements in the universe u -/
inductive Two : Type u where
  | zero
  | one
deriving Inhabited

namespace Two

/-- le for Two -/
def le : Two → Two → Prop
  | zero, _ => True
  | one, zero => False
  | one, one => True

noncomputable instance : LinearOrder Two where
  le := le
  le_refl := by
    intro x; cases x <;> trivial
  le_trans := by
    intro x y z; rcases x, y, z with ⟨x | x, y | y, z | z⟩
    <;> (intro a b ; trivial)
  lt_iff_le_not_le := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> trivial
  le_antisymm := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (intro a b; trivial)
  le_total := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (simp [le, or_false, or_true])
  toDecidableLE := decRel le
  compare_eq_compareOfLessAndEq := by
    rintro ⟨x | x⟩ ⟨y | y⟩
    <;> trivial

/-- Two as a LinOrd -/
noncomputable abbrev L : LinOrd.{u} := {carrier := Two, str := inferInstance}

/-- Two is finite -/
lemma instFinite : Finite Two := by
  refine finite_iff_exists_equiv_fin.mpr ?_
  use 2
  rw [<-exists_true_iff_nonempty]
  use {
    toFun := fun x => match x with
    | zero => 0
    | one => 1
    invFun := fun x => match x with
    | 0 => zero
    | 1 => one
    left_inv := by intro x; cases x <;> simp
    right_inv := by
      intro x
      match x with
      | 0 => simp
      | 1 => simp }

end Two

/-- Define a linear order with three elements in the universe u -/
inductive Three : Type u where
  | zero
  | one
  | two

deriving Inhabited

namespace Three

/-- le relation for Three -/
def le : Three → Three → Prop
  | zero, _ => True
  | one, zero => False
  | one, _ => True
  | two, two => True
  | two, _ => False

noncomputable instance : LinearOrder Three where
  le := le
  le_refl := by
    intro x; cases x <;> trivial
  le_trans := by
    intro x y z; rcases x, y, z with ⟨x | x, y | y, z | z⟩
    <;> (intro a b ; trivial)
  lt_iff_le_not_le := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> trivial
  le_antisymm := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (intro a b; trivial)
  le_total := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (simp only [le]; trivial)
  toDecidableLE := decRel le
  compare_eq_compareOfLessAndEq := by
    rintro ⟨x | x | x⟩ ⟨y | y | y⟩
    <;> trivial

/-- Three as a LinOrd -/
noncomputable abbrev L : LinOrd.{u} := {carrier := Three, str := inferInstance}

/-- Three is finite -/
lemma instFinite : Finite Three := by
  apply finite_iff_exists_equiv_fin.mpr
  use 3
  rw [<-exists_true_iff_nonempty]
  use {
    toFun := fun x => match x with
    | zero => 0
    | one => 1
    | two => 2
    invFun := fun x => match x with
    | 0 => zero
    | 1 => one
    | 2 => two
    left_inv := by intro x; cases x <;> simp
    right_inv := by
      intro x
      match x with
      | 0 => simp
      | 1 => simp
      | 2 => simp }

end Three

/-- helper function to prevent repeated constructions in proofs with lex sums
    involving Two as the index set -/
def two_map (M N: LinOrd) : Two → LinOrd
  | Two.zero => M
  | Two.one => N

/-- conditions for showing isomorphism to a Lex sum with two elements -/
noncomputable def Two_iso_helper {L : LinOrd.{u}} (s₁ s₂ s₃ : Set L)
    (h₁ : s₁ = s₂ ∪ s₃) (h₂ : ∀ x ∈ s₃, ∀ y ∈ s₂, y < x) :
    LinOrd.mk s₁ ≃o dLexOrd Two.L (two_map (LinOrd.mk s₂) (LinOrd.mk s₃)) where
  toFun := fun ⟨x, hx⟩ =>
    if h : x ∈ s₂ then ⟨Two.zero, ⟨x, h⟩⟩
    else ⟨Two.one, ⟨x, or_iff_not_imp_right.mp (subset_of_eq h₁ hx).symm h⟩⟩
  invFun := fun ⟨x1, x2⟩ =>
    match x1 with
    | Two.zero => ⟨x2.1, (subset_of_eq h₁.symm) (Or.inl x2.2)⟩
    | Two.one => ⟨x2.1, (subset_of_eq h₁.symm) (Or.inr x2.2)⟩
  left_inv := by
    intro ⟨x, hx⟩
    rcases Classical.em (x ∈ s₂) with h | h
    <;> simp only [h, ↓reduceDIte]
  right_inv := by
    rintro ⟨x₁ | x₁, x₂⟩
    · simp
    · simp only [Subtype.coe_eta, dite_eq_right_iff]
      simp only [two_map] at x₂
      intro h
      by_contra
      exact (lt_irrefl x₂.1) (h₂ x₂ x₂.2 x₂.1 h)
  map_rel_iff' := by
    have helper (x y : LinOrd.mk s₁) (hx : x.1 ∈ s₂) (hy : y.1 ∉ s₂) : x ≤ y := by
      apply le_of_lt (h₂ y _ x hx)
      exact or_iff_not_imp_right.mp ((subset_of_eq h₁) y.2).symm hy
    intro x y
    simp
    split_ifs with h₁' h₂' h₃'
    <;>
      simp only [Sigma.Lex.le_def, lt_self_iff_false, exists_const, false_or, or_false,
        reduceCtorEq, IsEmpty.exists_iff]
    · exact ge_iff_le
    · simp only [helper x y h₁' h₂', iff_true]
      exact lt_of_le_not_le trivial fun a ↦ a
    · constructor
      · rintro (h | ⟨h₁, h₂⟩)
      · intro h
        by_contra
        rw [(eq_of_le_of_le (helper y x h₃' h₁') h)] at h₃'
        exact h₁' h₃'
    · exact ge_iff_le

/-- The restriction of an OrderIso to a subset A is order isomorphic to A-/
def OrderIso_restrict {α β : Type*} [LE α] [LE β] (f : α ≃o β) (s : Set α) : s ≃o (f '' s) where
  toFun := fun x => ⟨f x, by simp⟩
  invFun := fun x =>
    ⟨f.symm x.1,
      by
      rcases (Set.mem_image f s x.1).mp x.2 with ⟨y, hy⟩
      rw [<-hy.right, OrderIso.symm_apply_apply]
      exact hy.left⟩
  left_inv := by intro _ ; simp
  right_inv := by intro _ ; simp
  map_rel_iff' := by simp


/-- A swapped dLexOrd is isomorphic to swapping the indexing order and each suborder -/
def Sigma_swap_alt_def {L : LinOrd} (i : L → LinOrd) :
    @OrderIso (linOrd_swap (dLexOrd L i)).carrier
      (dLexOrd (linOrd_swap L) (fun l => linOrd_swap (i l))).carrier
      (linOrd_swap (dLexOrd L i)).str.toLE
      (dLexOrd (linOrd_swap L) (fun l => linOrd_swap (i l))).str.toLE where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_rel_iff' := by
    intro x y
    --- the below lemma is a bit ugly, but i have been unable to use generalize instead
    have (t₁ t₂ : L) (x : (i t₁)) (y : i t₂) (h₁ : t₁ = t₂) (h₂ : t₂ = t₁) :
      h₁ ▸ x ≥ y ↔ x ≥ (h₂ ▸ y) := by subst t₁; simp
    constructor
    · intro h
      change (dLexOrd L i).str.le y x
      rcases Sigma.Lex.le_def.mp h with h₁ | h₁
      · left; exact h₁
      · rcases h₁ with ⟨h₂, h₃⟩
        rw [Sigma.Lex.le_def]
        right; use h₂.symm
        apply (this x.1 y.1 x.2 y.2 _ _).mp h₃
    · intro h
      change (dLexOrd L i).str.le y x at h
      simp only [Sigma.Lex.le_def] at *
      rcases h with h₁ | h₁
      · left; exact h₁
      · rcases h₁ with ⟨h₂, h₃⟩
        right; use h₂.symm
        apply (this x.1 y.1 x.2 y.2 _ _).mpr h₃

/-- If two LinOrds are isomorphic, so are their swapped orders -/
def swap_iso_of_iso {L M : LinOrd} (f : L ≃o M) : linOrd_swap L ≃o linOrd_swap M where
  toFun := f
  invFun := f.symm
  left_inv := OrderIso.symm_apply_apply f
  right_inv := OrderIso.apply_symm_apply f
  map_rel_iff' := f.map_rel_iff'

/-- A LinOrd is isomorphic to the ordered Lex sum of a partition -/
noncomputable def iso_of_sigma_partition {L M : LinOrd} (j : M → Set L)
    (partition : ∀ x : L, ∃! (m : M), x ∈ j m)
    (ordered : ∀ x y, x < y → ∀ x₀ ∈ j x, ∀ y₀ ∈ j y, x₀ < y₀) :
    L ≃o dLexOrd M (fun m : M => LinOrd.mk (j m)) where
  toFun := fun x => ⟨choose (partition x), ⟨x,(choose_spec (partition x)).left⟩⟩
  invFun := fun x => x.2.1
  left_inv := by intro _; simp
  right_inv := by
    rintro ⟨x1, ⟨x21, x22⟩⟩
    simp only
    apply Sigma.ext_iff.mpr
    constructor
    · apply Eq.symm
      apply (choose_spec (partition x21)).right _ x22
    · rw [Subtype.heq_iff_coe_heq rfl]
      simp only
      rw [(choose_spec (partition x21)).right _ x22]
  map_rel_iff' := by
    intro x y
    rw [Sigma.Lex.le_def]
    have helper (px py : M) (hp : px = py) (hx : x ∈ j px) (hy : y ∈ j py) :
      hp ▸ (⟨x, hx⟩ : { x_1 // x_1 ∈ j (px)}) ≤ ⟨y, hy⟩ ↔ x ≤ y := by
      subst px; simp
    constructor
    · rintro (h | ⟨h₁, h₂⟩)
      · apply le_of_lt
        apply ordered _ _ h x _ y
        · exact (choose_spec (partition y)).left
        · exact (choose_spec (partition x)).left
      · exact (helper
                (choose (partition x)) (choose (partition y)) h₁
                (choose_spec (partition x)).left
                (choose_spec (partition y)).left).mp h₂
    · intro h
      rcases lt_or_eq_of_le h with h₁ | h₁
      · have : (choose (partition x)) ≤ (choose (partition y)) := by
          by_contra! h'
          apply not_lt_of_le h
          exact ordered _ _ h' y (choose_spec (partition y)).left x
            (choose_spec (partition x)).left
        rcases lt_or_eq_of_le this with h₂ | h₂
        · exact Or.inl h₂
        · right; use h₂
          exact (helper (choose (partition x)) (choose (partition y)) h₂
                  (choose_spec (partition x)).left
                  (choose_spec (partition y)).left).mpr h
      · subst x; simp

/-- The composition of order embeddings is an order embedding -/
def OrderEmbedding_comp {α β γ: Type*} [Preorder α] [Preorder β] [Preorder γ]
    (f: α ↪o β) (g: β ↪o γ) : α ↪o γ where
  toFun := g ∘ f
  inj' := (EmbeddingLike.comp_injective (⇑f) g).mpr f.inj'
  map_rel_iff' := by simp
