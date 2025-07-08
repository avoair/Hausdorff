import Mathlib.Tactic
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex

open Classical
universe u

/-- shorthand for a Lex Sum as a Linord -/
abbrev dLexOrd (α : LinOrd) (β : α.carrier → LinOrd) : LinOrd :=
  { carrier := Σₗ w, (β w), str := Sigma.Lex.linearOrder }

/-- reverse the ordering on a LinOrd -/
abbrev linOrd_swap (α : LinOrd) : LinOrd := { carrier := α, str := α.str.swap }

/-- If subset of a dLexOrd is contained in a single suborder, it embeds that suborder -/
def embed_dLexOrd {α : LinOrd} {β : α.carrier → LinOrd} (a : α.carrier)
    (B : Set (dLexOrd α β)) (h : ∀ b ∈ B, b.1 = a) :
    B ↪o β a where
  toFun := fun x => h x.1 x.2 ▸ x.1.2
  inj' := by
    rintro ⟨⟨x11, x12⟩, h1⟩ ⟨⟨x21, x22⟩, h2⟩
    have : x11 = a := h _ h1
    subst this
    have : x21 = x11 := h _ h2
    subst this
    simp_all only [implies_true]
  map_rel_iff' := by
    rintro ⟨⟨x11, x12⟩, h1⟩ ⟨⟨x21, x22⟩, h2⟩
    have : x11 = a := h _ h1
    subst this
    have : x21 = x11 := h _ h2
    subst this
    rw [Subtype.mk_le_mk, Sigma.Lex.le_def]
    simp

/-- Equal sub-LinOrds have HEq linear orderings-/
lemma LinearOrder_subtype_HEq {L : LinOrd} {P Q : L → Prop} (h : P = Q): HEq (Subtype.instLinearOrder fun x_1 ↦ P x_1)
  (Subtype.instLinearOrder fun x_1 ↦ Q x_1) := by
  subst h
  rfl

/-- like Finset.coeEmb, but for general Set type-/
def coeEmb {L : LinOrd.{u}} (A : Set L) : A ↪o L where
  toFun := fun x => x
  inj' := by intro _ _ h; exact SetCoe.ext h
  map_rel_iff' := by simp

/-- If B ⊆ A, B as a Set A is isomorphic to B-/
def subtype_iso {L : LinOrd.{u}} (A B : Set L) (h1 : B ⊆ A) :
  (LinOrd.mk {x : A | x.1 ∈ B}) ≃o (LinOrd.mk B) where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun x => ⟨⟨x.1, h1 x.2⟩, x.2⟩
  left_inv := by intro _ ; trivial
  right_inv := by intro _ ; trivial
  map_rel_iff' := by intro _; trivial

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
    intro x y; rcases x, y with ⟨x | x, y | y⟩
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
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> trivial

/-- Three as a LinOrd -/
noncomputable abbrev L : LinOrd.{u} := {carrier := Three, str := inferInstance}

/-- Three is finite -/
lemma instFinite : Finite Three := by
    refine finite_iff_exists_equiv_fin.mpr ?_
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
noncomputable def Two_iso_helper {L : LinOrd.{u}} (A B C : Set L)
  (h1 : A = B ∪ C) (h2 : ∀ c ∈ C, ∀ b ∈ B, b < c) :
  LinOrd.mk A ≃o dLexOrd Two.L (two_map (LinOrd.mk B) (LinOrd.mk C)) where
  toFun := fun ⟨x, hx⟩ =>
    if h : x ∈ B then ⟨Two.zero, ⟨x, h⟩⟩
    else ⟨Two.one, ⟨x, or_iff_not_imp_right.mp (subset_of_eq h1 hx).symm h⟩⟩
  invFun := fun ⟨x1, x2⟩ =>
    match x1 with
    | Two.zero => ⟨x2.1, (subset_of_eq h1.symm) (Or.inl x2.2)⟩
    | Two.one => ⟨x2.1, (subset_of_eq h1.symm) (Or.inr x2.2)⟩
  left_inv := by
    intro ⟨x, hx⟩
    rcases Classical.em (x ∈ B) with h | h
    <;> simp only [h, ↓reduceDIte]
  right_inv := by
    intro ⟨x1, x2⟩
    cases x1
    · simp
    · simp only [Subtype.coe_eta, dite_eq_right_iff];
      intro h
      simp only [two_map] at x2
      by_contra;
      exact (lt_irrefl x2.1) (h2 x2 x2.2 x2.1 h)
  map_rel_iff' := by
    have helper (x y : LinOrd.mk A) (hx : x.1 ∈ B) (hy : y.1 ∉ B) : x ≤ y := by
      apply le_of_lt (h2 y _ x hx)
      exact or_iff_not_imp_right.mp ((subset_of_eq h1) y.2).symm hy
    intro x y
    rcases Classical.em (x.1 ∈ B), Classical.em (y.1 ∈ B) with ⟨hx | hx, hy | hy⟩
    · simp only [hx, hy, Equiv.coe_fn_mk, Sigma.Lex.le_def]
      constructor
      · intro h
        simp [lt_irrefl] at h
        exact h
      · intro h
        right; exact Exists.intro rfl h
    · simp only [hx, hy, Equiv.coe_fn_mk, Sigma.Lex.le_def]
      constructor
      · intro _ ; exact helper x y hx hy
      · intro _;
        left;
        exact lt_of_le_not_le trivial fun a ↦ a
    · simp only [hx, hy, Equiv.coe_fn_mk, Sigma.Lex.le_def]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · by_contra
          apply not_le_of_lt h
          trivial
        · trivial
      · intro h
        by_contra
        rw [(eq_of_le_of_le (helper y x hy hx) h)] at hy
        exact hx hy
    · simp only [Equiv.coe_fn_mk, hx, ↓reduceDIte, hy, Sigma.Lex.le_def]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · by_contra
          exact (and_not_self_iff (Two.one.le Two.one)).mp h
        · exact h2
      · intro h
        right; exact exists_true_left.mpr h

/-- The restriction of an OrderIso to a subset A is order isomorphic to A-/
def OrderIso_restrict {α β : Type*} [LE α] [LE β] (f : α ≃o β) (A : Set α) : A ≃o (f '' A) :=
  {
    toFun := fun x => ⟨f x, by simp⟩
    invFun := fun x => ⟨f.symm x.1,
                        by
                        rcases (Set.mem_image f A x.1).mp x.2 with ⟨y, hy⟩
                        rw [<-hy.right]
                        simp only [OrderIso.symm_apply_apply]
                        exact hy.left⟩
    left_inv := by intro _ ; simp
    right_inv := by intro _ ; simp
    map_rel_iff' := by intro _ _; simp
  }

/-- A swapped dLexOrd is isomorphic to swapping the indexing order and each suborder -/
def Sigma_swap_alt_def {L : LinOrd} (i : L → LinOrd) :
  @OrderIso (linOrd_swap (dLexOrd L i)).carrier (dLexOrd (linOrd_swap L)
  (fun l => linOrd_swap (i l))).carrier
  (linOrd_swap (dLexOrd L i)).str.toLE (dLexOrd (linOrd_swap L)
  (fun l => linOrd_swap (i l))).str.toLE where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_rel_iff' := by
    intro a b
    --- the below lemma is a bit ugly, but i have been unable to use generalize instead
    have (ta tb : L) (a : (i ta)) (b : i tb) (h1 : ta = tb) (h2 : tb = ta) :
      h1 ▸ a ≥ b ↔ a ≥ (h2 ▸ b) := by subst ta ; simp
    constructor
    · intro h
      change (dLexOrd L i).str.le b a
      simp only [Sigma.Lex.le_def] at h
      rcases h with h1 | h1
      · left; exact h1
      · rcases h1 with ⟨h2, h3⟩
        rw [Sigma.Lex.le_def]
        right; use h2.symm
        apply (this a.1 b.1 a.2 b.2 _ _).mp h3
    · intro h
      change (dLexOrd L i).str.le b a at h
      simp only [Sigma.Lex.le_def] at *
      rcases h with h1 | h1
      · left; exact h1
      · rcases h1 with ⟨h2, h3⟩
        right; use h2.symm
        apply (this a.1 b.1 a.2 b.2 _ _).mpr h3

/-- If two LinOrds are isomorphic, so are their swapped orders -/
def swap_iso_of_iso {L M : LinOrd} (f : L ≃o M) : linOrd_swap L ≃o linOrd_swap M where
  toFun := fun x => f x
  invFun := fun x => f.symm x
  left_inv := by intro x; exact OrderIso.symm_apply_apply f x
  right_inv := by intro x; exact OrderIso.apply_symm_apply f x
  map_rel_iff' := by intro x y; exact f.map_rel_iff'

/-- A LinOrd is isomorphic to the ordered Lex sum of a partition -/
noncomputable def iso_of_sigma_partition {L S : LinOrd} (j : S → Set L)
  (partition : ∀ z : L, ∃! (a : S), z ∈ j a)
  (ordered : ∀ a b, a < b → ∀ a_1 ∈ j a, ∀ b_1 ∈ j b, a_1 < b_1) :
  let J := fun s : S => LinOrd.mk (j s)
  L ≃o dLexOrd S J where
  toFun := fun x => ⟨choose (partition x), ⟨x,(choose_spec (partition x)).left⟩⟩
  invFun := fun x => x.2.1
  left_inv := by intro x; simp
  right_inv := by
    rintro ⟨x1, ⟨x21, x22⟩⟩
    simp only
    apply Sigma.ext_iff.mpr
    constructor
    · apply Eq.symm
      apply (choose_spec (partition x21)).right _ x22
    · rw [Subtype.heq_iff_coe_heq rfl ?_]
      simp only [heq_eq_eq]
      rw [<-Set.setOf_inj, subset_antisymm_iff,
            (choose_spec (partition x21)).right _ x22]
      constructor <;> (intro y hy ; exact hy)
  map_rel_iff' := by
    intro x y
    rw [Sigma.Lex.le_def]
    have helper (px py : S) (hp : px = py) (hx : x ∈ j px) (hy : y ∈ j py) :
      hp ▸ (⟨x, hx⟩ : { x_1 // x_1 ∈ j (px)}) ≤ ⟨y, hy⟩ ↔ x ≤ y := by
      subst px ; simp
    constructor
    · intro h
      rcases h with h | h
      · apply le_of_lt
        apply ordered _ _ h x _ y
        apply (choose_spec (partition y)).left
        apply (choose_spec (partition x)).left
      · rcases h with ⟨h1, h2⟩
        exact (helper
          (choose (partition x)) (choose (partition y)) h1
          (choose_spec (partition x)).left
          (choose_spec (partition y)).left).mp h2
    · intro h
      rcases lt_or_eq_of_le h with h1 | h1
      · have : (choose (partition x)) ≤ (choose (partition y)) := by
          by_contra! contra
          apply not_lt_of_le h
          exact ordered _ _ contra y (choose_spec (partition y)).left x
                                     (choose_spec (partition x)).left
        rcases lt_or_eq_of_le this with h2 | h2
        · exact Or.inl h2
        · right; use h2
          exact (helper
            (choose (partition x)) (choose (partition y))
              h2 (choose_spec (partition x)).left
            (choose_spec (partition y)).left).mpr h
      · subst x
        right; simp

/-- Order isomorphism preserves unboundedness -/
lemma unbounded_of_iso_from_unbounded {α β: Type*} [Preorder α] [Preorder β] (h₁: NoMinOrder α)
  (h₂: NoMaxOrder α) (h₃ : Nonempty (α ≃o β)) : NoMinOrder β ∧ NoMaxOrder β := by
  rcases h₃ with ⟨f⟩
  constructor
  · constructor
    intro x
    rcases h₁.exists_lt (f.symm x) with ⟨y, hy⟩
    use f y
    rw [<- OrderIso.symm_apply_apply f y, f.symm.lt_iff_lt] at hy
    exact hy
  · constructor
    intro x
    rcases h₂.exists_gt (f.symm x) with ⟨y, hy⟩
    use f y
    rw [<- OrderIso.symm_apply_apply f y, f.symm.lt_iff_lt] at hy
    exact hy

/-- The composition of order embeddings is an order embedding -/
def comp_is_orderEmb {α β γ: Type*} [Preorder α] [Preorder β] [Preorder γ] (g: β ↪o γ)
  (f: α ↪o β) : α ↪o γ :=
  { toFun := g ∘ f
    inj' := by
      apply (EmbeddingLike.comp_injective (⇑f) g).mpr f.inj'
    map_rel_iff' := by intro _ _; simp }

/-- Order isomoprhism preserves (order) density -/
lemma dense_of_iso_from_dense {α β: Type*} [Preorder α] [Preorder β] (h: DenselyOrdered α) :
  Nonempty (α ≃o β) → DenselyOrdered β := by
  intro h
  rcases h with ⟨f⟩
  constructor
  intro x y h₁
  rcases h.dense (f.symm x) (f.symm y) (f.symm.lt_iff_lt.mpr h₁) with ⟨x, h₂⟩
  use (f x)
  rw [<-OrderIso.symm_apply_apply f x, f.symm.lt_iff_lt, f.symm.lt_iff_lt] at h₂
  exact h₂


-- below is an attempt to prove Two_iso_helper as a corrolary of iso_of_sigma_partition

-- noncomputable def Two_iso_helper' {L : LinOrd.{u}} (A B C : Set L)
--   (h1 : A = B ∪ C) (h2 : ∀ c ∈ C, ∀ b ∈ B, b < c) :
--   LinOrd.mk A ≃o dLexOrd Two.L (two_map (LinOrd.mk B) (LinOrd.mk C)) := by
--   let f := @iso_of_sigma_partition (LinOrd.mk A) Two.L.{u} (g {x | x.1 ∈ B} {x | x.1 ∈ C}) ?_ ?_
--   simp at f
--   apply OrderIso.trans f
--   -- exact {
--   --   toFun := fun ⟨x1, x2⟩ =>
--   --     match x1 with
--   --     | Two.zero => ⟨x1, x2⟩
--   --     | Two.one => ⟨x2.1, (subset_of_eq h1.symm) (Or.inr x2.2)⟩

--   --   if h : x.1 = Two.zero then ⟨x.1, ⟨x.2.1, x⟩⟩


--   --     match x.1 with
--   --     | Two.one => sorry
--   -- }
--   sorry
--   · intro z
--     rcases subset_of_eq h1 z.2 with h | h
--     · use Two.zero
--       constructor
--       · simp [g, h]
--       · intro y hy
--         match y with
--         | Two.zero => rfl
--         | Two.one => by_contra; simp [g] at hy
--                      exact (lt_irrefl z) (h2 _ hy _ h)
--     · use Two.one
--       constructor
--       · simp [g, h]
--       · intro y hy
--         match y with
--         | Two.zero => by_contra; simp [g] at hy
--                       exact (lt_irrefl z) (h2 _ h _ hy)
--         | Two.one => rfl
--   · intro x y hxy z hz v hv
--     have : x = Two.zero ∧ y = Two.one := by
--       match x, y with
--       | Two.one, Two.one => order
--       | Two.one, Two.zero => by_contra; apply (not_le_of_lt hxy); trivial
--       | Two.zero, Two.one => simp
--       | Two.zero, Two.zero => order
--     rcases this with ⟨hx, hy⟩
--     subst x y
--     simp [g] at hz hv
--     exact h2 _ hv _ hz
