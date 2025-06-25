import Mathlib.Tactic
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Batteries.Logic
import Hausdorff.WO_cofinal_subset
import Hausdorff.IsScattered


open Classical
universe u


abbrev dLexOrd (α : LinOrd) (β : α.carrier → LinOrd) : LinOrd :=
  { carrier := Σₗ w, (β w), str := Sigma.Lex.linearOrder }

abbrev LinOrd_swap (α : LinOrd) : LinOrd := { carrier := α, str := α.str.swap }

def embed_dlexord {α : LinOrd} {β : α.carrier → LinOrd} (a : α.carrier)
    (B : Set (dLexOrd α β)) (h : ∀ b ∈ B, b.1 = a) :
    B ↪o β a where
  toFun := fun x => h x.1 x.2 ▸ x.1.2
  inj' := by
    rintro ⟨⟨x11, x12⟩, h1⟩ ⟨⟨x21, x22⟩, h2⟩
    have : x11 = a := h _ h1
    subst this
    have : x21 = x11 := h _ h2
    subst this
    simp_all
  map_rel_iff' := by
    rintro ⟨⟨x11, x12⟩, h1⟩ ⟨⟨x21, x22⟩, h2⟩
    have : x11 = a := h _ h1
    subst this
    have : x21 = x11 := h _ h2
    subst this
    rw [Subtype.mk_le_mk, Sigma.Lex.le_def]; simp

def initial_segment_iso {L M : LinOrd} (f : L ≃o M) (a : L) :
  ({carrier := {x | x ≤ a}, str := inferInstance} : LinOrd) ≃o
    ({carrier := {x | x ≤ f a}, str := inferInstance} : LinOrd) := by
  use {
    toFun := fun x => ⟨f x, by simp ; exact x.2⟩
    invFun := fun x => ⟨f.symm x, by
      apply f.le_iff_le.mp
      simp
      exact x.2⟩
    left_inv := by intro x ; simp
    right_inv := by intro x ; simp
  }
  intro x y
  simp

def subtype_iso {L : LinOrd.{u}} (A B : Set L) (h1 : B ⊆ A) :
  (LinOrd.mk {x : A | x.1 ∈ B}) ≃o (LinOrd.mk B)  := by
  use {
    toFun := fun x => ⟨x.1.1, x.2⟩
    invFun := fun x => ⟨⟨x.1, h1 x.2⟩, x.2⟩
    left_inv := by intro x ; simp
    right_inv := by intro x ; simp
  }
  intro x y; simp

inductive Two : Type u where
  | zero
  | one
deriving Inhabited

namespace Two

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
    <;> simp
  le_antisymm := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (intro a b; trivial)
  le_total := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (simp[le])
  toDecidableLE := decRel le
  -- min_def := sorry -- cn maybe leave out
  -- max_def := sorry
  compare_eq_compareOfLessAndEq := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> trivial

noncomputable abbrev L : LinOrd.{u} := {carrier := Two, str := inferInstance}

lemma finite : Finite Two := by
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

inductive Three : Type u where
  | zero
  | one
  | two

deriving Inhabited

namespace Three

def le : Three → Three → Prop
  | zero, one => True
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
    <;> simp
  le_antisymm := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (intro a b; trivial)
  le_total := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> (simp[le])
  toDecidableLE := decRel le
  compare_eq_compareOfLessAndEq := by
    intro x y; rcases x, y with ⟨x | x, y | y⟩
    <;> trivial

noncomputable abbrev L : LinOrd.{u} := {carrier := Three, str := inferInstance}

lemma finite : Finite Three := by
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

-- abbrev Three : LinOrd.{u} := {carrier := ULift.{u} (Fin 3), str := inferInstance}

-- lemma Three_def (x : Three) : x = 0 ∨ x = 1 ∨ x = 2 := by
--   match x with
--   | 0 => simp
--   | 1 => simp
--   | 2 => simp

def g' (M N: LinOrd) : Two → LinOrd
    | Two.zero => M
    | Two.one => N

-- def g'' (K M N: LinOrd) : Three → LinOrd
--     | ⟨0, _⟩ => K
--     | ⟨1, _⟩ => M
--     | ⟨2, _⟩ => N

-- lemma g''0 {K M N : LinOrd}
--   (y : ({ carrier := Σₗ (w : ↑Three), (g'' K M N w), str := inferInstance } : LinOrd)) :
--   y.1 = 0 → g'' K M N y.1 = K := by intro h ; simp only [g'', h]

-- lemma g''1 {K M N : LinOrd}
--   (y : ({ carrier := Σₗ (w : ↑Three), (g'' K M N w), str := inferInstance } : LinOrd)) :
--   y.1 = 1 → g'' K M N y.1 = M := by intro h ; simp only [g'', h]

-- lemma g''2 {K M N : LinOrd}
--   (y : ({ carrier := Σₗ (w : ↑Three), (g'' K M N w), str := inferInstance } : LinOrd)) :
--   y.1 = 2 → g'' K M N y.1 = N := by intro h ; simp only [g'', h]

set_option maxHeartbeats 1000000
noncomputable def Two_iso_helper {L : LinOrd.{u}} (A B C : Set L)
  (h1 : A = B ∪ C) (h2 : ∀ c ∈ C, ∀ b ∈ B, b < c) :
  LinOrd.mk A ≃o ({ carrier := Σₗ (w : Two), (g' (LinOrd.mk B) (LinOrd.mk C) w),
                    str := Sigma.Lex.linearOrder } : LinOrd) where
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
    <;> simp [h]
  right_inv := by
    intro ⟨x1, x2⟩
    cases x1
    · simp
    · simp; intro h
      simp [g'] at x2
      by_contra;
      exact (lt_irrefl x2.1) (h2 x2 x2.2 x2.1 h)
  map_rel_iff' := by
    have helper (x y : LinOrd.mk A) (hx : x.1 ∈ B) (hy : y.1 ∉ B) : x ≤ y := by
      apply le_of_lt (h2 y _ x hx)
      exact or_iff_not_imp_right.mp ((subset_of_eq h1) y.2).symm hy
    intro x y
    simp
    rcases Classical.em (x.1 ∈ B), Classical.em (y.1 ∈ B) with ⟨hx | hx, hy | hy⟩
    · simp [hx, hy, Sigma.Lex.le_def]
      exact ge_iff_le
    · simp [hx, hy, Sigma.Lex.le_def]
      constructor
      · intro _ ; exact helper x y hx hy
      · intro _; exact lt_of_le_not_le trivial fun a ↦ a
    · simp [hx, hy, Sigma.Lex.le_def]
      constructor
      · intro h
        by_contra
        apply not_le_of_lt h
        trivial
      · intro h
        by_contra;
        rw [(eq_of_le_of_le (helper y x hy hx) h)] at hy
        exact hx hy
    · simp [hx, hy, Sigma.Lex.le_def]
      exact ge_iff_le

def OrderIso_restrict {α β : Type*} [LE α] [LE β] (f : α ≃o β) (A : Set α) : A ≃o (f '' A) :=
  {
    toFun := fun x => ⟨f x, by simp⟩
    invFun := fun x => ⟨f.symm x.1,
                        by
                        rcases (Set.mem_image f A x.1).mp x.2 with ⟨y, hy⟩
                        rw [<-hy.right]; simp; exact hy.left⟩
    left_inv := by intro _ ; simp
    right_inv := by intro _ ; simp
    map_rel_iff' := by intro _ _; simp
  }

def Sigma_swap_alt_def {L : LinOrd} (i : L → LinOrd) :
  @OrderIso (LinOrd_swap (dLexOrd L i)).carrier (dLexOrd (LinOrd_swap L) (fun l => LinOrd_swap (i l))).carrier
    (LinOrd_swap (dLexOrd L i)).str.toLE (dLexOrd (LinOrd_swap L) (fun l => LinOrd_swap (i l))).str.toLE
    where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_rel_iff' := by
    intro a b
    simp
    constructor
    · intro h
      change (dLexOrd L i).str.le b a
      simp [Sigma.Lex.le_def] at h
      rcases h with h1 | h1
      · change L.str.lt b.1 a.1 at h1
        left; exact h1
      · rcases h1 with ⟨h2, h3⟩
        rw [Sigma.Lex.le_def]; right
        use h2.symm
        simp [h2]
        sorry
    · intro h
      change (dLexOrd L i).str.le b a at h
      sorry

def swap_iso_of_iso {L M : LinOrd} (f : L ≃o M) : LinOrd_swap L ≃o LinOrd_swap M where
  toFun := fun x => f x
  invFun := fun x => f.symm x
  left_inv := by intro x; exact OrderIso.symm_apply_apply f x
  right_inv := by intro x; exact OrderIso.apply_symm_apply f x
  map_rel_iff' := by intro x y; exact f.map_rel_iff'

noncomputable def iso_of_sigma_partition {L S : LinOrd} (j : S → Set L)
  (partition : ∀ z : L, ∃! (a : S), z ∈ j a)
  (ordered : ∀ a b, a < b → ∀ a_1 ∈ j a, ∀ b_1 ∈ j b, a_1 < b_1) :
  let J := fun s : S => LinOrd.mk (j s)
  L ≃o dLexOrd S J where
  toFun := fun x => ⟨choose (partition x), ⟨x,(choose_spec (partition x)).left⟩⟩
  invFun := fun x => x.2.1
  left_inv := by intro x; simp
  right_inv := by
    intro x
    rcases x with ⟨x1, ⟨x21, x22⟩⟩
    apply Sigma.ext_iff.mpr
    constructor
    · apply Eq.symm
      apply (choose_spec (partition x21)).right _ x22
    · refine (Subtype.heq_iff_coe_heq rfl ?_).mpr ?_
      · simp
        refine Set.setOf_inj.mp ?_
        apply Set.eq_of_subset_of_subset
        · intro y hy
          rw [(choose_spec (partition x21)).right _ x22]
          exact hy
        · intro y hy
          rw [(choose_spec (partition x21)).right _ x22] at hy
          exact hy
      · simp

  map_rel_iff' := by
    intro x y
    simp
    rw [Sigma.Lex.le_def]
    have helper (px py : S) (hp : px = py) (hx : x ∈ j px) (hy : y ∈ j py) :
      hp ▸ (⟨x, hx⟩ : { x_1 // x_1 ∈ j (px)}) ≤ ⟨y, hy⟩ ↔ x ≤ y := by
      subst px ; simp

    constructor
    · intro h
      rcases h with h | h
      · simp at h
        apply le_of_lt
        apply ordered _ _ h x _ y
        apply (choose_spec (partition y)).left
        apply (choose_spec (partition x)).left
      · rcases h with ⟨h1, h2⟩
        simp at h2; simp at h1
        --generalize ht : choose (partition x) = t at *
        --subst t
        --simp at h2
        exact (helper
            (choose (partition x)) (choose (partition y)) h1 (choose_spec (partition x)).left
            (choose_spec (partition y)).left).mp h2
    · intro h
      simp
      rcases lt_or_eq_of_le h with h1 | h1
      · have : (choose (partition x)) ≤ (choose (partition y)) := by
          by_contra contra
          apply lt_of_not_le at contra
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

-- noncomputable def Two_iso_helper' {L : LinOrd.{u}} (A B C : Set L)
--   (h1 : A = B ∪ C) (h2 : ∀ c ∈ C, ∀ b ∈ B, b < c) :
--   LinOrd.mk A ≃o ({ carrier := Σₗ (w : Two), (g' (LinOrd.mk B) (LinOrd.mk C) w),
--                     str := Sigma.Lex.linearOrder } : LinOrd) := by
--   let g : Two.L.{u} → Set L
--     | Two.zero => B
--     | Two.one => C
--   let p := iso_of_sigma_partition g sorry sorry
--   simp at p
--   sorry
