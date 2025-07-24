import Mathlib.Tactic
import Mathlib.Order.Category.LinOrd
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sigma.Lex
import Hausdorff.WellOrderedCofinalSubset
import Hausdorff.Scattered
import Hausdorff.Isomorphisms

universe u

/-- Hausdorff's recursive definition of scattered : HausdorffScattered is the smallest collection
    of LinOrds containing every singleton order that is closed under well-ordered and reverse
    well-ordered lexicographic sums -/
inductive HausdorffScattered : LinOrd.{u} → Prop
| base {L : LinOrd.{u}} (x : L.carrier) (h : {x} = @Set.univ L.carrier) : HausdorffScattered L
| lex_sum (I: LinOrd.{u})
  (hI : WellFounded I.str.lt ∨ WellFounded (I.str.swap).lt)
  (map: I.carrier → LinOrd)
  (hmap : ∀ i, HausdorffScattered (map i))
  (L : LinOrd.{u})
  (f : L ≃o dLexOrd I map) : HausdorffScattered L

/-- Empty LinOrds are HausdorffScatteredttered -/
lemma hausdorffScattered_of_isEmpty (L : LinOrd) (h : IsEmpty L) : HausdorffScattered L := by
  apply HausdorffScattered.lex_sum L (Or.inl (wellFounded_of_isEmpty L.str.lt)) (fun x => L)
  simp only [IsEmpty.forall_iff]
  have : IsEmpty (dLexOrd L (fun x => L)) := by
    apply IsEmpty.mk
    intro x
    rw [<- @IsEmpty.exists_iff _ h]
    use x.1
  use Equiv.equivOfIsEmpty L (dLexOrd L (fun x => L))
  simp

/-- Well founded LinOrds are HausdorffScatteredtered -/
lemma hausdorffScattered_of_wellFounded (L : LinOrd) (h : WellFounded L.str.lt) :
    HausdorffScattered L := by
  let f : L ≃o dLexOrd L (fun w => LinOrd.mk PUnit) := {
    toFun := fun x => ⟨x, PUnit.unit⟩
    invFun := fun ⟨a, b⟩ => a
    left_inv := by intro _ ; simp
    right_inv := by intro _ ; constructor
    map_rel_iff' := by simp [Sigma.Lex.le_def, <-le_iff_lt_or_eq]
    }
  exact HausdorffScattered.lex_sum L (Or.inl h) (fun x => LinOrd.mk PUnit)
    (fun x => by
      apply HausdorffScattered.base PUnit.unit
      exact Set.eq_univ_of_univ_subset fun a => congrFun rfl) L f

/-- Singleton orders are HausdorffScatteredtered -/
lemma hausdorffScattered_of_singleton {α : LinOrd} (x : α) :
    HausdorffScattered (LinOrd.mk ({x} : Set α)) :=
  hausdorffScattered_of_wellFounded _
    (@Finite.to_wellFoundedLT (LinOrd.mk ({x} : Set α)) (Set.finite_singleton x)).1

/-- Orders isomorphic to an HausdorffScatteredtered order are HausdorffScatteredtered -/
lemma hausdorffScattered_of_orderIso {L M : LinOrd.{u}} (f : M ≃o L) (h: HausdorffScattered M) :
    HausdorffScattered L := by
  rcases h with ⟨m, h'⟩ | ⟨I, hI, map, hmap, _, g⟩
  · apply HausdorffScattered.base (f m)
    rw [<- EquivLike.range_eq_univ f, <- Set.image_univ, <- h']
    exact (@Set.image_singleton _ _ f m).symm
  · apply HausdorffScattered.lex_sum I hI map hmap L (OrderIso.trans f.symm g)

/-- One scattered order ontop of another scattered order is scattered -/
lemma hausdorffScattered_of_two_dLexOrd (L M N : LinOrd.{u}) (h₁ : HausdorffScattered M)
    (h₂: HausdorffScattered N) (iso : L ≃o dLexOrd Two.L.{u} (two_map M N)) :
    HausdorffScattered L := by
  apply HausdorffScattered.lex_sum Two.L
    (Or.inl (@Finite.to_wellFoundedLT _ Two.instFinite).1) (two_map M N) ?_ L iso
  rintro (i | i) <;> simp only [two_map]
  · exact h₁
  · exact h₂

/-- A suborder of a HausdorffScattered order is HausdorffScatteredtered -/
lemma hausdorffScattered_of_suborder {L : LinOrd} (s : Set L) (h : HausdorffScattered L) :
    HausdorffScattered (LinOrd.mk s) := by
  induction' h with M m hm I hI map hmap N f IH
  · -- base case
    have s_subsingleton: s.Subsingleton := by
      apply Set.subsingleton_of_subset_singleton
      rw [hm]; exact Set.subset_univ s
    rcases Set.Subsingleton.eq_empty_or_singleton s_subsingleton with h | ⟨x, h⟩
    · apply hausdorffScattered_of_isEmpty _ (Set.isEmpty_coe_sort.mpr h)
    · apply @HausdorffScattered.base (LinOrd.mk s) ⟨x, by simp [h]⟩
      subst s
      exact Set.toFinset_eq_univ.mp rfl
  · -- inductive step
    let g (i : I) := LinOrd.mk {b | ⟨i, b⟩ ∈ f '' s}
    let iso : f '' s ≃o dLexOrd I g :=
      {
        toFun := fun ⟨⟨x₁, x₂⟩, x₃⟩ => ⟨x₁, ⟨x₂, x₃⟩⟩
        invFun := fun ⟨x₁, ⟨x₂, x₃⟩⟩ => ⟨⟨x₁, x₂⟩, x₃⟩
        left_inv := by intro ⟨⟨x₁, x₂⟩, x₃⟩; simp
        right_inv := by intro ⟨x₁, ⟨x₂, x₃⟩⟩; simp
        map_rel_iff' := by
          rintro ⟨⟨x, hx₀⟩, hx⟩ ⟨⟨y, hy₀⟩, hy⟩
          simp only [Equiv.coe_fn_mk, Sigma.Lex.le_def, Subtype.mk_le_mk]
          apply or_congr_right
          constructor <;> (rintro ⟨rfl, h⟩; use rfl, h)
      }
    apply hausdorffScattered_of_orderIso (OrderIso.trans iso.symm (OrderIso_restrict f s).symm)
    apply HausdorffScattered.lex_sum I hI g ?_ _ (by rfl)
    intro i; exact IH i {x | ⟨i, x⟩ ∈ f '' s}

/-- A subset of a suborder which is HausdorffScattered is HausdorffScattered-/
lemma hausdorffScattered_of_subset {L : LinOrd} (s : Set L) (h : HausdorffScattered (LinOrd.mk s))
    (t : Set L) (h₁ : t ⊆ s) : HausdorffScattered (LinOrd.mk t) :=
  @hausdorffScattered_of_orderIso _ (LinOrd.mk {x | x.1 ∈ t}) (linOrd_subtype_iso s t h₁)
    (hausdorffScattered_of_suborder _ h)

/-- Given that the subordering given by a property P is HausdorffScatteredtered,
    the subset of any other subordering given by P is also HausdorffScatteredtered -/
lemma hausdorffScattered_of_suborder' {L : LinOrd} (P : L → Prop) (T : L → Prop)
    (h : HausdorffScattered (LinOrd.mk {x | P x})) :
    HausdorffScattered (LinOrd.mk {x : {x // T x} | P x}) := by
  apply @hausdorffScattered_of_orderIso _ (LinOrd.mk {x | T x ∧ P x})
  · exact {
      toFun := fun x => ⟨⟨x.1, x.2.left⟩, x.2.right⟩
      invFun := fun x => ⟨x.1.1, And.intro x.1.2 x.2⟩
      left_inv := by intro _ ; simp
      right_inv := by intro _ ; simp
      map_rel_iff' := by simp
    }
  · apply hausdorffScattered_of_subset _ h
    simp

/-- The reversal of an HausdorffScatteredtered order is HausdorffScatteredtered -/
lemma hausdorffScattered_swap {L : LinOrd} (h : HausdorffScattered L) :
  HausdorffScattered (linOrd_swap L) := by
  induction' h with M m hm I hI map hmap L iso IH
  · exact @HausdorffScattered.base (linOrd_swap M) m hm
  · apply hausdorffScattered_of_orderIso
      (@OrderIso.symm L (linOrd_swap (dLexOrd I map))
        (linOrd_swap L).str.toLE (linOrd_swap (dLexOrd I map)).str.toLE
        (swap_iso_of_iso iso))
    let swap_map (w : linOrd_swap I) := linOrd_swap (map w)
    let swap_iso := Sigma_swap_alt_def map
    exact HausdorffScattered.lex_sum (linOrd_swap I) (Or.symm hI) swap_map IH _ swap_iso

/-- A relation describing that (x, y] (if x ≤ y) or (y, x] (if y < x) is HausdorffScattered -/
def hausdorffScattered_rel {L : LinOrd} (x y : L) : Prop :=
  HausdorffScattered (LinOrd.mk {a | (x < a ∧ a ≤ y) ∨ (y < a ∧ a ≤ x)})

/-- special case of the proof that scat_rel is transitive where the inputs are increasing -/
lemma aux_hausdorffScattered_rel_trans {L : LinOrd} {x y z : L} (h₁ : x ≤ y) (h₂ : y ≤ z)
    (scat_xy : hausdorffScattered_rel x y) (scat_yz : hausdorffScattered_rel y z) :
    hausdorffScattered_rel x z := by
  apply hausdorffScattered_of_two_dLexOrd _ _ _ scat_xy scat_yz
  apply Two_iso_helper
  · apply Set.eq_of_subset_of_subset
    · rintro w (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
      · rcases le_or_gt w y with hy | hy
        · left; left; constructor <;> order
        · right; left; constructor <;> order
      · by_contra; order
    · rintro w (⟨⟨hw₁, hw₂⟩ | ⟨hw₁, hw₂⟩⟩ | ⟨⟨hw₁, hw₂⟩ | ⟨hw₁, ha2⟩⟩)
      <;> (left; constructor <;> order)
  · intro c hc b hb
    rcases hb, hc with ⟨⟨hb1, hb2⟩ | ⟨hb1, hb2⟩, ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩⟩
    <;> order

/-- the hausdorffScattered_rel relation is symmetric -/
lemma hausdorffScattered_rel_symm {L : LinOrd} {x y : L} (h : hausdorffScattered_rel x y):
    hausdorffScattered_rel y x := by
  apply hausdorffScattered_of_orderIso ?_ h
  apply OrderIso.setCongr
  simp [or_comm]

/-- hausdorffScattered_rel is an equivalence relation -/
lemma hausdorffScattered_rel_equivalence {L : LinOrd}: Equivalence (@hausdorffScattered_rel L) where
  refl := by
    intro x
    apply hausdorffScattered_of_isEmpty
    apply Subtype.isEmpty_of_false
    simp
  symm := hausdorffScattered_rel_symm
  trans := by
    intro x y z scat_xy scat_yz
    rcases L.str.le_total x y, L.str.le_total y z with ⟨hxy | hxy, hyz | hyz⟩
    -- every case is either a subset or layered intervals
    · exact aux_hausdorffScattered_rel_trans hxy hyz scat_xy scat_yz
    · rcases (le_or_gt x z) with hxz | hz
      · apply hausdorffScattered_of_subset _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply hausdorffScattered_of_subset _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · rcases (le_or_gt x z) with hxz | hz
      · apply hausdorffScattered_of_subset _ scat_yz
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (left; constructor <;> order)
      · apply hausdorffScattered_of_subset _ scat_xy
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        <;> (right; constructor <;> order)
    · exact hausdorffScattered_rel_symm (aux_hausdorffScattered_rel_trans hyz hxy
        (hausdorffScattered_rel_symm scat_yz) (hausdorffScattered_rel_symm scat_xy))

/-- if hausdorffScattered_rel x y, then the LinOrd restricted to [x, y] is also HausdorffScatteredtered -/
lemma hausdorffScattered_closed_interval {L : LinOrd} (x y : L) (h : hausdorffScattered_rel x y):
    HausdorffScattered (LinOrd.mk {a | (x ≤ a ∧ a ≤ y) ∨ (y ≤ a ∧ a ≤ x)}) := by
  wlog hxy : x ≤ y
  · push_neg at hxy
    apply hausdorffScattered_of_orderIso _
      (this y x (Equivalence.symm hausdorffScattered_rel_equivalence h) (le_of_lt hxy))
    apply OrderIso.setCongr
    simp [or_comm]
  · apply hausdorffScattered_of_two_dLexOrd _ (LinOrd.mk ({x} : Set L))
      (LinOrd.mk {z | x < z ∧ z ≤ y})
      (hausdorffScattered_of_wellFounded _ wellFounded_lt)
    · apply hausdorffScattered_of_orderIso _ h
      apply OrderIso.setCongr
      ext z
      simp only [Set.mem_setOf_eq, or_iff_left_iff_imp]
      intro ⟨h₁, h₂⟩
      constructor <;> order
    · apply (Two_iso_helper _ {x} {z | x < z ∧ z ≤ y})
      · ext a
        simp only [Set.singleton_union]
        constructor
        · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
          <;>
            (apply or_iff_not_imp_left.mpr
             intro h
             constructor <;> order)
        · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
          <;> (left; constructor <;> order)
      · rintro c hc _ ⟨_, _⟩
        exact hc.left

/-- if (x, y] is HausdorffScatteredtered, so is [x, y) -/
lemma hausdorffScattered_interval_flip_bounds {L : LinOrd} (x y : L)
    (h : hausdorffScattered_rel x y) :
    HausdorffScattered (LinOrd.mk {a | (x ≤ a ∧ a < y) ∨ (y ≤ a ∧ a < x)}) := by
  apply hausdorffScattered_of_subset _ (hausdorffScattered_closed_interval x y h)
  rintro a (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · left; exact And.intro h₁ (le_of_lt h₂)
  · right; exact And.intro h₁ (le_of_lt h₂)

/-- any order which is not a NoMaxOrder has a maximum element-/
lemma max_of_noMaxOrder {L : LinOrd} (hm : ¬ NoMaxOrder L): ∃ a : L, ∀ b, b ≤ a := by
  by_contra! h
  exact hm {exists_gt := h}

--//////////////////////////////////////////////////////////////////////////////////////////////////////////
-- Hausdorff's theorem
--//////////////////////////////////////////////////////////////////////////////////////////////////////////

/-- Given a LinOrd and a subset I, map each element a of I to all the elements of the
    LinOrd less than a, but not less than any earlier element of I -/
def partition_mk {L : LinOrd} {I : Set L} (a : I) := {z : L | z ≤ a ∧ ∀ a' < a, a' < z}

/-- If the indexing set is WF cofinal, the partition_mk partitions the LinOrd -/
lemma partition_mk_of_cofinal {L : LinOrd} {cof : Set L}
    (hcof : IsCofinal cof ∧ cof.WellFoundedOn fun x1 x2 ↦ x1 < x2) (nomax : NoMaxOrder L) (z : L):
    ∃! (a : cof), z ∈ partition_mk a := by
  let final := {a : cof | z ≤ a}
  have final_nonempt : final.Nonempty := by
    rcases nomax.exists_gt z with ⟨z', hz'⟩
    rcases hcof.left z' with ⟨y, hy⟩
    use ⟨y, hy.left⟩
    exact le_of_lt (lt_of_lt_of_le hz' hy.right)
  rcases (@WellFounded.wellFounded_iff_has_min _ (· < ·)).mp hcof.right final final_nonempt
    with ⟨lb, ⟨hlb1, hlb2⟩⟩
  use lb
  constructor
  · constructor
    · exact hlb1
    · rintro a h
      by_contra! contra
      exact (hlb2 a contra) h
  · intro y ⟨h₁, h₂⟩
    apply eq_of_le_of_le
    · by_contra! contra
      apply not_lt_of_le hlb1
      exact h₂ lb contra
    · exact le_of_not_lt (hlb2 y h₁)

/-- Given a LinOrd and a WF cofinal subset, if the output of the partition_mk on that
    subset is always HausdorffScattered, then L is also HausdorffScattered -/
lemma hausdorffScattered_of_wellFounded_cofinal_parition (L : LinOrd) (cof : Set L)
    (hcof : IsCofinal cof ∧ cof.WellFoundedOn fun x1 x2 ↦ x1 < x2)
    (h : ∀ (w : LinOrd.mk cof), HausdorffScattered (LinOrd.mk (partition_mk w)))
    (nomax : NoMaxOrder L) : HausdorffScattered L := by
  let J (a : cof) := LinOrd.mk (partition_mk a)
  let iso : L ≃o dLexOrd (LinOrd.mk cof) J := by
    apply @iso_of_sigma_partition L (LinOrd.mk cof) partition_mk
      (partition_mk_of_cofinal hcof nomax)
    intro a b hab c hc d hd
    exact lt_of_le_of_lt hc.left (hd.right a hab)
  apply HausdorffScattered.lex_sum (LinOrd.mk cof) ?_ J (fun w ↦ h w) L iso
  left; exact hcof.right


/-- given a,b in a LinOrd, the set of x ∈ [a, b] such that a and x are
    related is HausdorffScattered -/
lemma aux_dense_quotient (L : LinOrd) (a b : L) :
    HausdorffScattered (LinOrd.mk {x | a ≤ x ∧ x ≤ b ∧ hausdorffScattered_rel a x}) := by
  let A := {x | a ≤ x ∧ x ≤ b ∧ hausdorffScattered_rel a x}
  rcases @exists_cofinal_wellFoundedOn_subset A _ with ⟨cof, hcof⟩
  rcases Classical.em (NoMaxOrder (LinOrd.mk A)) with nomax | max
  · apply hausdorffScattered_of_wellFounded_cofinal_parition _ cof hcof ?_ nomax
    intro w
    let h := hausdorffScattered_of_suborder' _ A
      (hausdorffScattered_closed_interval _ _ w.1.2.right.right)
    apply @hausdorffScattered_of_subset (LinOrd.mk A) _ h  {x : A | x ≤ ↑w ∧ ∀ a' < w, a' < x}
    intro x ⟨hx1, _⟩
    left; exact And.intro x.2.left hx1
  · rcases (max_of_noMaxOrder max) with ⟨m, hm⟩
    apply hausdorffScattered_of_subset _ (hausdorffScattered_closed_interval _ _ m.2.right.right)
    intro x ⟨hx1, hx2, hx3⟩
    repeat constructor
    · exact hx1
    · exact hm ⟨x, And.intro hx1 (And.intro hx2 hx3)⟩

/-- If a and b are related in the LinOrd L, they are also related from the
    perspective of the swapped version of L -/
lemma hausdorffScattered_rel_swap {L : LinOrd} (a b : L) :
  @hausdorffScattered_rel L a b → @hausdorffScattered_rel (linOrd_swap L) a b := by
  simp only [hausdorffScattered_rel]
  intro h
  let p := hausdorffScattered_swap (hausdorffScattered_interval_flip_bounds a b h)
  apply hausdorffScattered_of_orderIso _ p
  exact {
    toFun := fun x => ⟨x,
      by
      rw [Set.mem_setOf_eq, And.comm, Or.comm, And.comm]
      exact x.2⟩
    invFun := fun x => ⟨x,
      by
      rw [Set.mem_setOf_eq, And.comm, Or.comm, And.comm]
      exact x.2⟩
    left_inv := by intro _; simp
    right_inv := by intro _; simp
    map_rel_iff' := by trivial }

/-- The quotient of HausdorffScattered is dense -/
lemma hausdorffScattered_rel_dense_quot {L : LinOrd} {x y : L}
    (h : ¬ hausdorffScattered_rel x y) (hl : x < y) :
    ∃ z, x < z ∧ z ≤ y ∧ ¬ hausdorffScattered_rel x z ∧ ¬ hausdorffScattered_rel z y := by
  by_contra! contra ; apply h
  -- split the interval into elements related to a and elements related to b
  let X := { z | x < z ∧ z ≤ y ∧ hausdorffScattered_rel x z}
  let Y := { z | x < z ∧ z ≤ y ∧ hausdorffScattered_rel z y}
  -- show that A and B partition the interval
  have union_cover (z : L) (h₁ : x < z) (h₂ : z ≤ y): z ∈ X ∪ Y := by
    rcases Classical.em (z ∈ X) with h₀ | h₀
    · exact Or.inl h₀
    · simp only [Set.mem_setOf_eq, not_and, X] at h₀
      right; exact And.intro h₁ (And.intro h₂ (contra z h₁ h₂ (h₀ h₁ h₂)))
  have empty_inter : ¬ (X ∩ Y).Nonempty := by
    by_contra nonempty
    rcases nonempty with ⟨x, ⟨_, _, hX⟩, ⟨_, _, hY⟩⟩
    apply h
    apply hausdorffScattered_of_two_dLexOrd _ _ _ hX hY
    apply Two_iso_helper
    · apply Set.eq_of_subset_of_subset
      · rintro t ht
        rcases ht, (lt_or_le x t) with ⟨(⟨h₁, h₂⟩ | ⟨h₁, h₂⟩), h | h⟩
        · right; left; exact And.intro h h₂
        · left; left; exact And.intro h₁ h
        · left; right; exact And.intro h h₂
        · right; right; exact And.intro h₁ h
      · rintro t (⟨⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ | ⟨⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩)
        <;> (first | left; constructor <;> order)
    · rintro z (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) w (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      <;> order
  -- show that the interval must be HausdorffScattered by showing it is isomorphic to
  -- the LinOrd with B ontop of A
  apply hausdorffScattered_of_two_dLexOrd _ (LinOrd.mk X) (LinOrd.mk Y)
  · apply hausdorffScattered_of_subset _ (aux_dense_quotient L x y)
    intro x ⟨h₁, h₂, h₃⟩
    exact And.intro (le_of_lt h₁) (And.intro h₂ h₃)
  · -- this goal is essentially equivalent to the first one if we swap the order
    apply hausdorffScattered_of_subset { z | x ≤ z ∧ z ≤ y ∧ hausdorffScattered_rel z y}
    · apply @hausdorffScattered_swap
        (linOrd_swap (LinOrd.mk { z | x ≤ z ∧ z ≤ y ∧ hausdorffScattered_rel z y}))
      apply hausdorffScattered_of_orderIso _ (aux_dense_quotient (linOrd_swap L) y x)
      exact {
        toFun := fun ⟨x₁, hx₁, hx₂, hx₃⟩ =>
          ⟨x₁, And.intro hx₂ (And.intro hx₁
            (hausdorffScattered_rel_swap _ _ (hausdorffScattered_rel_symm hx₃)))⟩
        invFun := fun ⟨x₁, hx₁, hx₂, hx₃⟩ =>
          ⟨x₁, And.intro hx₂ (And.intro hx₁
            (hausdorffScattered_rel_swap _ _ (hausdorffScattered_rel_symm hx₃)))⟩
        left_inv := by rintro ⟨_, _, _, _⟩; simp
        right_inv := by rintro ⟨_, _, _, _⟩; simp
        map_rel_iff' := by rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩; trivial
      }
    · intro z ⟨h₁, h₂, h₃⟩
      exact And.intro (le_of_lt h₁) (And.intro h₂ h₃)
  · apply Two_iso_helper
    · ext z
      constructor
      · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
        · exact union_cover z h₁ h₂
        · order
      · rintro (⟨h₁, h₂, _⟩ | ⟨h₁, h₂, _⟩)
        <;> (left; exact And.intro h₁ h₂)
    · rintro z ⟨_, _, hz⟩ w ⟨_, _, hw⟩
      by_contra
      have : hausdorffScattered_rel x z := by
        apply hausdorffScattered_of_subset _ hw
        rintro x (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
        · left; constructor <;> order
        · right; constructor <;> order
      apply empty_inter
      use z
      split_ands <;> (first | order | exact this | exact hz)

/-- Given a LinOrd where all elements are related by hausdorffScattered_rel, any final segment
    of the LinOrd is HausdorffScatteredttered -/
lemma hausdorffScattered_of_final_segment_of_one_class (L : LinOrd) (x : L)
    (one_class : ∀ x y : L, hausdorffScattered_rel x y) :
    HausdorffScattered (LinOrd.mk {z // x < z}) := by
  rcases @exists_cofinal_wellFoundedOn_subset {z // z > x} _ with ⟨cof, hcof⟩
  rcases Classical.em (NoMaxOrder (LinOrd.mk {z // x < z})) with nomax | max
  · apply hausdorffScattered_of_wellFounded_cofinal_parition (LinOrd.mk {z // x < z}) cof hcof ?_ nomax
    intro w
    specialize one_class x w
    let p := hausdorffScattered_of_suborder'
      ((fun z => x < z ∧ z ≤ w ∨ w < z ∧ z ≤ x)) (fun z => x < z ) one_class
    apply @hausdorffScattered_of_subset (LinOrd.mk {z // x < z}) _ p
      {z | z ≤ w ∧ ∀ a' < w, a' < z}
    simp only [Subtype.forall, Set.setOf_subset_setOf]
    intro z h₁ h₂
    left; exact And.intro h₁ h₂.left
  · rcases isEmpty_or_nonempty (LinOrd.mk {z // x < z} ) with empt | nonempt
    · exact hausdorffScattered_of_isEmpty _ empt
    rcases (max_of_noMaxOrder max) with ⟨m, hm⟩
    apply hausdorffScattered_of_orderIso ?_ (one_class x m)
    apply OrderIso.setCongr {z | x < z ∧ z ≤ m ∨ m < z ∧ z ≤ x} {z | x < z}
    apply Set.Subset.antisymm
    · rintro y (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · exact h₁
      · by_contra
        apply not_lt_of_le h₂
        rcases nonempt with ⟨n⟩;
        exact lt_trans (lt_of_lt_of_le n.2 (hm n)) h₁
    · intro y h
      exact Or.inl (And.intro h (hm ⟨y, h⟩))

/-- The class of Scattered orders is the same as the class of HausdorffScattered orders-/
theorem hausdorff_scattered_orders (L : LinOrd): Scattered L ↔ HausdorffScattered L := by
  constructor
  · intro L_scat
    rcases Classical.em (Nonempty L) with nonempt | empt; swap
    · rw [not_nonempty_iff] at empt
      exact hausdorffScattered_of_isEmpty L empt
    rcases Classical.em (∀ x y : L, hausdorffScattered_rel x y) with one_class | mult_class
    · rcases Classical.exists_true_of_nonempty nonempt with ⟨x⟩
      have final_HS : HausdorffScattered (LinOrd.mk {x_1 // x < x_1}) := by
        exact hausdorffScattered_of_final_segment_of_one_class _ x one_class
      have initial_HS : HausdorffScattered (LinOrd.mk {x_1 // x_1 < x}) := by
        apply @hausdorffScattered_swap (linOrd_swap (LinOrd.mk { x_1 // x_1 < x }))
        apply @hausdorffScattered_of_orderIso _
          (LinOrd.mk {x_1 : linOrd_swap L | L.str.swap.lt x x_1 })
        apply @OrderIso.setCongr _ _ {x_1 : linOrd_swap L | L.str.swap.lt x x_1} _ rfl
        apply hausdorffScattered_of_final_segment_of_one_class (linOrd_swap L) x
        intro z₁ z₂
        exact hausdorffScattered_rel_swap _ _ (one_class z₁ z₂)

      let f : Three.L → Set L
        | Three.zero => {z | z < x}
        | Three.one => {x}
        | Three.two =>  {z | x < z}

      apply HausdorffScattered.lex_sum Three.L
        (Or.inl (@Finite.to_wellFoundedLT Three Three.instFinite).1)
        (fun i => LinOrd.mk (f i))
      · rintro ⟨i | i | i⟩
        · exact initial_HS
        · exact hausdorffScattered_of_singleton x
        · exact final_HS
      · apply (iso_of_sigma_partition f _ _)
        · intro z
          apply existsUnique_of_exists_of_unique
          · rcases lt_trichotomy z x  with h | h | h
            · use Three.zero; simp only [Set.mem_setOf_eq, h, f]
            · use Three.one; simp only [h, Set.mem_singleton_iff, f]
            · use Three.two; simp only [Set.mem_setOf_eq, h, f]
          · intro x₁ x₂ h₁ h₂
            cases x₁ <;>
              (cases x₂ <;>
                (simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, f] at *; try order))
        · intro i₁ i₂ hi x h₁ y h₂
          cases i₁ <;>
            (simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, f] at h₁ ; cases i₂ <;>
                (first | simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, f] at h₂; order
                       | by_contra; apply not_le_of_lt hi ; trivial))

    · let K : Setoid L := ⟨hausdorffScattered_rel, hausdorffScattered_rel_equivalence⟩
      let rep := @Quotient.out L K
      let rep_set := Set.range rep

      by_contra
      rw [Scattered, <-not_nonempty_iff] at L_scat
      apply L_scat
      simp only [not_forall] at mult_class

      have : Nontrivial rep_set := by
        rcases mult_class with ⟨x₁, x₂, h⟩
        use ⟨rep ⟦x₁⟧, by simp only [rep_set]; use ⟦x₁⟧⟩,
            ⟨rep ⟦x₂⟧, by simp only [rep_set]; use ⟦x₂⟧⟩
        by_contra! h₀; simp only [Subtype.mk.injEq, Quotient.out_inj, rep] at h₀
        exact h (Quotient.eq.mp h₀)

      have : DenselyOrdered rep_set := by
        constructor
        intro x y h
        have not_rel : ¬ hausdorffScattered_rel x.1 y := by
          rcases x.2, y.2 with ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩
          by_contra h₀
          apply ne_of_lt h
          apply SetCoe.ext
          rw [<- hx', <- hy'] at *
          rw [((@Quotient.out_equiv_out _ K).mp h₀)]

        rcases hausdorffScattered_rel_dense_quot not_rel h with ⟨z, h₁, h₂, h₃, h₄⟩
        let r : rep_set := ⟨(rep ⟦z⟧), by simp [rep_set]⟩
        use r
        by_contra! bounds
        rcases le_or_lt r x with h₀ | h₀
        · apply h₃
          apply hausdorffScattered_of_subset _ (Quotient.mk_out z)
          rintro w (⟨hw₁, hw₂⟩ | ⟨hw₁, hw₂⟩)
          · left; exact And.intro (lt_of_le_of_lt h₀ hw₁) hw₂
          · by_contra; exact not_lt_of_le hw₂ (lt_trans h₁ hw₁)
        · apply h₄
          apply hausdorffScattered_of_subset _ (Quotient.mk_out z)
          rintro w (⟨hw₁, hw₂⟩ | ⟨hw₁, hw₂⟩)
          · right; exact And.intro hw₁ (le_trans hw₂ (bounds h₀))
          · by_contra; exact not_lt_of_le hw₂ (lt_of_le_of_lt h₂ hw₁)

      rcases Order.embedding_from_countable_to_dense ℚ rep_set with ⟨f'⟩
      apply Nonempty.intro (OrderEmbedding_comp f' (Set.coeEmb rep_set))

-- RIGHT TO LEFT
  · intro L_scat_prop
    induction' L_scat_prop with N x singleton_N I hI map hmap L iso is_scat_f
    · -- singleton case
      by_contra h
      rw [Scattered, <-not_nonempty_iff, not_not] at h
      rcases h with ⟨f⟩
      apply Rat.zero_ne_one
      apply @f.inj' 0 1
      apply @Eq.trans _ (f 0) x (f 1) ?_ (Eq.symm ?_)
      <;>
        (change f _ ∈ ({x} : Set N)
         simp [singleton_N])
    · -- inductive case
      apply scatttered_of_iso_to_scattered L (dLexOrd I map) iso
      by_contra h
      rw [Scattered, <-not_nonempty_iff, not_not] at h
      rcases h with ⟨f⟩
      rcases Classical.em (Function.Injective (fun a => (f a).1)) with inj | ninj
      · have : Scattered I := by
          rcases hI with h₁ | h₁
          · exact scattered_of_wellFounded I h₁
          · exact scattered_of_rev_wellFounded I h₁
        apply not_nonempty_iff.mpr this
        exact Nonempty.intro {
          toFun := fun a => (f a).1
          inj' := inj
          map_rel_iff' := by
            intro a b;
            constructor
            · intro h
              apply (@f.map_rel_iff' a b).mp
              apply Sigma.Lex.le_def.mpr
              rcases le_iff_lt_or_eq.mp h with h₁ | h₁
              · left; exact h₁
              · right; use h₁
                cases inj h₁
                trivial
            · intro h
              rcases Sigma.Lex.le_def.mp ((@f.map_rel_iff' a b).mpr h) with h₁ | h₁
              · exact le_of_lt h₁
              · rcases h₁ with ⟨h₂, _⟩
                exact le_of_eq h₂ }
      · rw [Function.not_injective_iff] at ninj
        rcases ninj with ⟨a, b, h⟩
        wlog hab : a < b
        · apply this L I hI map hmap L iso is_scat_f f b a
            ((And.intro h.left.symm) h.right.symm)
            (lt_of_le_of_ne (le_of_not_lt hab) h.right.symm)
        let s := {c | a < c ∧ c < b}
        rcases OrderIso_Rat_to_interval a b hab with ⟨fsQ⟩

        let g' : (f '' s) ↪o (map (f a).1) :=
          embed_dLexOrd (f a).1 (f '' s)
            (by
              rintro x ⟨y, hy⟩
              rw [<-hy.right]
              rcases Sigma.Lex.le_def.mp (f.map_rel_iff'.mpr (le_of_lt hy.left.left))
                with h₁ | ⟨h₁, _⟩
              · by_contra
                apply not_lt_of_le (le_of_eq h.left.symm)
                rcases Sigma.Lex.le_def.mp (f.map_rel_iff'.mpr (le_of_lt hy.left.right))
                  with h₂ | ⟨h₂, _⟩
                · exact lt_trans h₁ h₂
                · exact lt_of_lt_of_eq h₁ h₂
              · exact h₁.symm)

        apply not_nonempty_iff.mpr (is_scat_f (f a).1)
        let f' := OrderEmbedding_restrict f s
        exact Nonempty.intro (OrderEmbedding_comp (OrderEmbedding_comp fsQ.toOrderEmbedding f') g')
