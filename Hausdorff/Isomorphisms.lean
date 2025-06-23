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

abbrev Two : LinOrd.{u} := {carrier := ULift.{u} (Fin 2), str := inferInstance}
abbrev Three : LinOrd.{u} := {carrier := ULift.{u} (Fin 3), str := inferInstance}

lemma Two_def (x : Two) : x = 0 ∨ x = 1 := by
  match x with
  | 0 => left; rfl
  | 1 => right; rfl

lemma Three_def (x : Three) : x = 0 ∨ x = 1 ∨ x = 2 := by
  match x with
  | 0 => simp
  | 1 => simp
  | 2 => simp

lemma Two_le (x y : Two.{u}) (h : x < y) : x = 0 ∧ y = 1 := by
  rcases Two_def x, Two_def y with ⟨hx | hx, hy | hy⟩
  · by_contra; rw [hx, hy] at h ; exact (lt_irrefl 0) h
  · exact And.intro hx hy
  · by_contra; rw [hx, hy] at h ;
    have : (0 : Two.{u}) ≥ ULift.down.{u+1} 0 := by rfl
    apply not_lt_of_ge this
    exact lt_trans (Fin.zero_lt_one) h
  · by_contra; rw [hx, hy] at h ; exact (lt_irrefl 1) h

def g' (M N: LinOrd) : Two → LinOrd
    | ⟨0, _⟩ => M
    | ⟨1, _⟩ => N

def g'' (K M N: LinOrd) : Three → LinOrd
    | ⟨0, _⟩ => K
    | ⟨1, _⟩ => M
    | ⟨2, _⟩ => N

lemma g''0 {K M N : LinOrd}
  (y : ({ carrier := Σₗ (w : ↑Three), (g'' K M N w), str := inferInstance } : LinOrd)) :
  y.1 = 0 → g'' K M N y.1 = K := by intro h ; simp only [g'', h]

lemma g''1 {K M N : LinOrd}
  (y : ({ carrier := Σₗ (w : ↑Three), (g'' K M N w), str := inferInstance } : LinOrd)) :
  y.1 = 1 → g'' K M N y.1 = M := by intro h ; simp only [g'', h]

lemma g''2 {K M N : LinOrd}
  (y : ({ carrier := Σₗ (w : ↑Three), (g'' K M N w), str := inferInstance } : LinOrd)) :
  y.1 = 2 → g'' K M N y.1 = N := by intro h ; simp only [g'', h]

lemma Two_g_0 {M N : LinOrd.{u}}
  {x : Two} :
  x = 0 → (g' M N x) = M := by
  intro h ; simp only [g', h]

lemma Two_g_1 {M N : LinOrd.{u}}
  {x : Two} :
  x = 1 → (g' M N x) = N := by
  intro h ; simp only [g', h]

-- def Two_iso_of_each_iso {L L' M M' : LinOrd.{u}} (fL : L ≃o L') (fM : M ≃o M'):
--   ({carrier := Σₗ (w : Two), g' L M w, str := inferInstance} : LinOrd)
--   ≃o ({carrier := Σₗ (w : Two), g' L' M' w, str := inferInstance} : LinOrd) :=
--   {
--     toFun := fun x =>
--       if h : x.1 = 0 then ⟨x.1, (@Two_g_0 L' M' _ h).symm ▸(fL ((@Two_g_0 L M _ h) ▸ x.2))⟩
--       else ⟨x.1, (@Two_g_1 L' M' x.1 (or_iff_not_imp_right.mp (Two_def x.1).symm h)).symm ▸
--                   (fM ((@Two_g_1 L M _ (or_iff_not_imp_right.mp (Two_def x.1).symm h) ▸ x.2)))⟩
--     invFun := fun x =>
--       if h : x.1 = 0 then ⟨x.1, (@Two_g_0 L M _ h).symm ▸ (fL.symm ((@Two_g_0 L' M' _ h) ▸ x.2))⟩
--       else ⟨x.1, (@Two_g_1 L M x.1 (or_iff_not_imp_right.mp (Two_def x.1).symm h)).symm ▸
--                   (fM.symm ((@Two_g_1 L' M' _ (or_iff_not_imp_right.mp (Two_def x.1).symm h) ▸ x.2)))⟩
--     left_inv := sorry
--     right_inv := sorry
--     map_rel_iff' := sorry
--   }

set_option maxHeartbeats 1000000
noncomputable def Two_iso_helper {L : LinOrd.{u}} (A B C : Set L)
  (h1 : A = B ∪ C) (h2 : ∀ c ∈ C, ∀ b ∈ B, b < c) :
  LinOrd.mk A ≃o ({ carrier := Σₗ (w : Two), (g' (LinOrd.mk B) (LinOrd.mk C) w),
                    str := Sigma.Lex.linearOrder } : LinOrd) := by
  use {
    toFun := fun x =>
      if h : x.1 ∈ B then ⟨0, ⟨x, h⟩⟩
      else ⟨1, ⟨x, or_iff_not_imp_right.mp (subset_of_eq h1 x.2).symm h⟩⟩
    invFun := fun x =>
      if h : x.1 = 0 then ⟨((Two_g_0 h) ▸ x.2).1,
                           (subset_of_eq h1.symm) (Or.inl ((Two_g_0 h) ▸ x.2).2)⟩
      else ⟨(Two_g_1 (or_iff_not_imp_right.mp (Two_def x.1).symm h) ▸ x.2).1,
            (subset_of_eq h1.symm)
            (Or.inr (Two_g_1 (or_iff_not_imp_right.mp (Two_def x.1).symm h) ▸ x.2).2)⟩
    left_inv := by
      intro x
      simp
      split_ifs with k1 k2 k3
      · have {α : Type*} {P1 P2 : α} : (if h : x.1 ∈ B then P1 else P2) = P1 := by
          exact (Ne.dite_eq_left_iff fun h a ↦ h k1).mpr k1
        sorry
      sorry
      sorry
      sorry
    right_inv := by
      intro x
      simp
      split_ifs with k1 k2 k3
      · simp
        apply Sigma.eq
        simp
        · sorry
        · simp [k1]
      sorry
      sorry
      sorry
  }
  intro x y
  simp
  sorry

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

#check Sigma.Lex

def Sigma_swap_alt_def {L : LinOrd} (i : L → LinOrd) :
  LinOrd_swap (dLexOrd L i) ≃o dLexOrd (LinOrd_swap L) (fun l => LinOrd_swap (i l)) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_rel_iff' := by
    intro a b
    simp
    constructor
    · intro h
      change (dLexOrd L i).str.le a b -- orderiso not correctly infering relations
      sorry
    sorry
    --   simp [Sigma.Lex.le_def] at h
    --   rcases h with h1 | h1
    --   · change L.str.lt b.1 a.1 at h1
    --     refine Sigma.Lex.le_def.mpr ?_
    --     left; exact h1
    --   · rcases h1 with ⟨h2, h3⟩
    --     change (f (Liso b).fst).str.le ((Liso b).snd) (h2 ▸ (Liso a).snd) at h3
    --     rw [Sigma.Lex.le_def]; right
    --     constructor
    --     · sorry
    --     · simp [h2]
    -- · intro h
    --   change L.str.le b a at h
    --   rw [<-OrderIso.le_iff_le Liso] at h
    --   sorry}
    --   have : @Sigma.Lex L _ (Function.swap LE.le) (fun w ↦ LE.le) a b := by
    --     sorry
    --   --#check @Sigma.lex_swap L _ L.str.swap.le (fun w => (i w).str.le) a b
    -- sorry



-- lemma ind_scat_of_rev_ind_scat {L : LinOrd.{u}} (h : Scattered_ind_prop.{u,u} L) :
--    Scattered_ind_prop.{u,u} {carrier := L.carrier , str := L.str.swap} := by
--   induction' h with M m hm WO hWO f f_scat L Liso IH
--   · apply Scattered_ind_prop.base
--     exact hm
--   · let map (w : ({ carrier := WO.carrier, str := WO.str.swap } : LinOrd)) : LinOrd :=
--       { carrier := (f w), str := (f w).str.swap }
--     let iso : ({ carrier := Σₗ (w : ↑WO), ↑(f w), str := Sigma.Lex.linearOrder.swap } : LinOrd.{u}) ≃o
--       ({ carrier := Σₗ (w : ({ carrier := WO.carrier, str := WO.str.swap } : LinOrd)), (map w),
--          str := Sigma.Lex.linearOrder} : LinOrd.{u}) :=
--       { toFun := fun x => x
--         invFun := fun x => x
--         left_inv := congrFun rfl
--         right_inv := congrFun rfl
--         map_rel_iff' := by
--           intro a b
--           simp
          -- constructor
          -- · intro h
          --   have : @Sigma.Lex WO _ (Function.swap LE.le) (fun w ↦ LE.le) a b := by
          --     sorry
          --   #check @Sigma.lex_swap WO _ WO.str.swap.le (fun w => (map w).str.le) a b
          -- sorry
--       }
--     sorry

-- lemma ind_scat_of_rev_ind_scat {L : LinOrd.{u}} (h : Scattered_ind_prop.{u,u} L) :
--   Scattered_ind_prop.{u,u} {carrier := L.carrier , str := L.str.swap} := by
--   induction' h with M m hm WO hWO f f_scat L Liso IH
--   · apply Scattered_ind_prop.base
--     exact hm
--   · let map (w : ({ carrier := WO.carrier, str := WO.str.swap } : LinOrd)) : LinOrd :=
--       { carrier := (f w), str := (f w).str.swap }
--     let iso : ({ carrier := ↑L, str := L.str.swap } : LinOrd.{u}) ≃o
--       ({ carrier := Σₗ (w : ({ carrier := WO.carrier, str := WO.str.swap } : LinOrd)), (map w),
--          str := Sigma.Lex.linearOrder} : LinOrd.{u}) :=
--       { toFun := fun x => Liso x
--         invFun := fun x => Liso.symm x
--         left_inv := by exact Liso.left_inv
--         right_inv := by exact Liso.right_inv
--         map_rel_iff' := by
--           intro a b
--           simp
--           simp [Sigma.Lex.le_def]
--           constructor
--           · intro h
          --   change L.str.le b a
          --   rw [<-OrderIso.le_iff_le Liso]
          --   rcases h with h1 | h1
          --   · change WO.str.lt (Liso b).fst (Liso a).fst at h1
          --     left; exact h1
          --   · rcases h1 with ⟨h2, h3⟩
          --     change (f (Liso b).fst).str.le ((Liso b).snd) (h2 ▸ (Liso a).snd) at h3
          --     rw [Sigma.Lex.le_def]; right
          --     constructor
          --     · sorry
          --     · simp [h2]
          -- · intro h
          --   change L.str.le b a at h
          --   rw [<-OrderIso.le_iff_le Liso] at h
          --   sorry}

    -- apply Scattered_ind_prop.lex_sum { carrier := WO.carrier, str := WO.str.swap } ?_ map IH _ iso
    -- · rcases hWO with WO | RWO
    --   · right; apply WO
    --   · left;
    --     apply RWO

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
    simp
    apply Sigma.ext_iff.mpr
    constructor
    · simp
      apply Eq.symm
      apply (choose_spec (partition x.2)).right _ x.2.2
    · simp
      have : HEq x.2.1 x.2 := by sorry
      apply HEq.trans _ this
      simp
      sorry -- should be trivial

  map_rel_iff' := by
    intro x y
    simp
    rw [Sigma.Lex.le_def]
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
        sorry
    · intro h
      sorry
