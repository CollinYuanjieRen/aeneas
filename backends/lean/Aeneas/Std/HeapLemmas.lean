module

public import Aeneas.Std.Heap
import all Aeneas.Std.Heap

public section

namespace Aeneas

/-- A partial commutative monoid: a total `∪`, meaningful on `Compatible` inputs. -/
class PartialCommMonoid (α : Type u) [EmptyCollection α] [Union α] where
  Compatible : α → α → Prop
  compatible_comm {a b : α} : Compatible a b → Compatible b a
  compatible_empty_left (a : α) : Compatible ∅ a
  compatible_assoc (a b c : α) :
    Compatible a b ∧ Compatible (a ∪ b) c ↔
      Compatible b c ∧ Compatible a (b ∪ c)
  union_assoc {a b c : α} :
    Compatible a b → Compatible (a ∪ b) c →
      a ∪ b ∪ c = a ∪ (b ∪ c)
  empty_union (a : α) : ∅ ∪ a = a
  union_empty (a : α) : a ∪ ∅ = a
  union_comm_of_compatible {a b : α} :
    Compatible a b → a ∪ b = b ∪ a

end Aeneas

namespace Aeneas.Std

namespace Loc

@[simp] theorem add_fst (l : Loc) (i : Nat) : (l.add i).1 = l.1 := rfl

@[simp] theorem add_snd (l : Loc) (i : Nat) : (l.add i).2 = l.2 + i := rfl

@[simp] theorem add_zero (l : Loc) : l.add 0 = l := rfl

theorem add_add (l : Loc) (i j : Nat) :
    (l.add i).add j = l.add (i + j) := by
  simp [Loc.add, Nat.add_assoc]

end Loc

namespace Heap

private instance : Coe Heap HeapImpl := ⟨Heap.impl⟩
private instance : Coe HeapImpl Heap := ⟨Heap.mk⟩

private theorem ext_impl {h₁ h₂ : Heap}
    (hEq : h₁.impl = h₂.impl) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hEq
  rfl

private theorem mem_union {address : Loc} {h₁ h₂ : Heap} :
    address ∈ h₁ ∪ h₂ ↔ address ∈ h₁ ∨ address ∈ h₂ :=
  Finmap.mem_union

private theorem lookup_union_left {address : Loc}
    {h₁ h₂ : Heap} (hMem : address ∈ h₁) :
    (h₁ ∪ h₂).lookup address = h₁.lookup address :=
  Finmap.lookup_union_left hMem

private theorem mem_of_lookup_eq_some {address : Loc} {h : Heap} {s : Slot}
    (hLookup : h.lookup address = some s) : address ∈ h :=
  Finmap.mem_of_lookup_eq_some hLookup

private theorem mem_insert {address insertedAddress : Loc}
    {s : Slot} {h : Heap} :
    address ∈ h.insert insertedAddress s ↔
      address = insertedAddress ∨ address ∈ h :=
  Finmap.mem_insert

private theorem insert_union {address : Loc}
    {s : Slot} {h₁ h₂ : Heap} :
    (h₁ ∪ h₂).insert address s =
      h₁.insert address s ∪ h₂ := by
  apply Heap.ext_impl
  exact Finmap.insert_union

private theorem union_assoc' (h₁ h₂ h₃ : Heap) :
    (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  apply Heap.ext_impl
  exact Finmap.union_assoc

@[simp]
theorem empty_union (h : Heap) : empty ∪ h = h := by
  apply Heap.ext_impl
  exact Finmap.empty_union

@[simp]
theorem union_empty (h : Heap) : h ∪ empty = h := by
  apply Heap.ext_impl
  exact Finmap.union_empty

instance instPartialCommMonoid : PartialCommMonoid Heap where
  Compatible := Heap.compatible
  compatible_comm hCompatible := by
    exact Finmap.Disjoint.symm _ _ hCompatible
  compatible_empty_left h := by
    exact Finmap.disjoint_empty h.impl
  compatible_assoc a b c := by
    change
      Finmap.Disjoint a.impl b.impl ∧
          Finmap.Disjoint (a.impl ∪ b.impl) c.impl ↔
        Finmap.Disjoint b.impl c.impl ∧
          Finmap.Disjoint a.impl (b.impl ∪ c.impl)
    rw [Finmap.disjoint_union_left, Finmap.disjoint_union_right]
    constructor
    · rintro ⟨hab, hac, hbc⟩
      exact ⟨hbc, hab, hac⟩
    · rintro ⟨hbc, hab, hac⟩
      exact ⟨hab, hac, hbc⟩
  union_assoc _ _ := by
    apply Heap.ext_impl
    exact Finmap.union_assoc
  empty_union _ := by
    apply Heap.ext_impl
    exact Finmap.empty_union
  union_empty _ := by
    apply Heap.ext_impl
    exact Finmap.union_empty
  union_comm_of_compatible hCompatible := by
    apply Heap.ext_impl
    exact Finmap.union_comm_of_disjoint hCompatible

theorem union_right_cancel {h₁ h₂ frame : Heap}
    (hCompatible₁ : PartialCommMonoid.Compatible h₁ frame)
    (hCompatible₂ : PartialCommMonoid.Compatible h₂ frame)
    (hEq : h₁ ∪ frame = h₂ ∪ frame) : h₁ = h₂ := by
  apply Heap.ext_impl
  exact (Finmap.union_cancel hCompatible₁ hCompatible₂).mp (congrArg Heap.impl hEq)

theorem mem_slot {l : Loc} {s : Slot} {address : Loc} :
    address ∈ slot l s ↔ address = l :=
  Finmap.mem_singleton _ _ _

theorem mem_cell {α : Type} {l : Loc} {content : Option α} {address : Loc} :
    address ∈ cell l content ↔ address = l :=
  mem_slot

theorem mem_endMarker {l address : Loc} : address ∈ endMarker l ↔ address = l :=
  mem_slot

private theorem lookup_slot (l : Loc) (s : Slot) : (slot l s).lookup l = some s := by
  simp [slot, Heap.lookup]

@[simp]
theorem not_contains_empty {α : Type} (l : Loc) :
    ¬ contains (∅ : Heap) α l := by
  change ¬ match Finmap.lookup l (∅ : HeapImpl) with
    | some (.live β _) => β = α
    | _ => False
  simp

@[simp] theorem cells_nil {α : Type} (l : Loc) :
    cells l ([] : List (Option α)) = empty := rfl

@[simp] theorem cells_cons {α : Type} (l : Loc) (content : Option α)
    (rest : List (Option α)) :
    cells l (content :: rest) = cell l content ∪ cells (l.add 1) rest :=
  rfl

@[simp] theorem cells_singleton {α : Type} (l : Loc) (content : Option α) :
    cells l [content] = cell l content := by
  rw [cells_cons, cells_nil, Heap.union_empty]

theorem mem_cells {α : Type} {l : Loc} {contents : List (Option α)} {address : Loc} :
    address ∈ cells l contents ↔
      ∃ i, i < contents.length ∧ address = l.add i := by
  induction contents generalizing l with
  | nil =>
      simp only [cells_nil, List.length_nil, Nat.not_lt_zero, false_and,
        exists_false, iff_false]
      intro hMem
      exact (Finmap.notMem_empty (a := address)) hMem
  | cons content rest ih =>
      have hShift : ∀ i : Nat, (l.add 1).add i = l.add (i + 1) := by
        intro i; rw [Loc.add_add, Nat.add_comm]
      rw [cells_cons, Heap.mem_union, mem_cell, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨i + 1, by simpa using hi, by rw [hShift]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, by simpa using hi, by rw [hShift]⟩

theorem cells_append {α : Type} (l : Loc) (xs ys : List (Option α)) :
    cells l (xs ++ ys) =
      cells l xs ∪ cells (l.add xs.length) ys := by
  induction xs generalizing l with
  | nil => simp
  | cons content rest ih =>
      have hShift : (l.add 1).add rest.length = l.add (rest.length + 1) := by
        rw [Loc.add_add, Nat.add_comm]
      rw [List.cons_append, cells_cons, cells_cons, ih, List.length_cons,
        hShift, Heap.union_assoc']

theorem compatible_cells_append {α : Type} (l : Loc) (xs ys : List (Option α)) :
    PartialCommMonoid.Compatible (cells l xs)
      (cells (l.add xs.length) ys) := by
  intro address hLeft hRight
  obtain ⟨i, hi, hL⟩ := mem_cells.mp hLeft
  obtain ⟨j, -, hR⟩ := mem_cells.mp hRight
  rw [Loc.add_add] at hR
  have hOffset : l.2 + i = l.2 + (xs.length + j) :=
    (congrArg Prod.snd hL).symm.trans (congrArg Prod.snd hR)
  omega

/-- A fresh allocation is aligned (see `freshBase`). -/
theorem dvd_freshBase (h : Heap) (align : Nat) : max align 1 ∣ freshBase h align :=
  Dvd.intro _ rfl

/-- The null allocation `0` is never allocated. -/
theorem freshBase_ne_zero (h : Heap) (align : Nat) : freshBase h align ≠ 0 := by
  unfold freshBase
  exact Nat.mul_ne_zero (by omega) (by omega)

theorem not_mem_freshBase {h : Heap} {align : Nat} {address : Loc}
    (hBase : address.1 = freshBase h align) : address ∉ h := by
  intro hMem
  have hMemKeys : address ∈ h.keys := Finmap.mem_keys.mpr hMem
  have hImage : freshBase h align ∈ h.keys.image Prod.fst :=
    Finset.mem_image.mpr ⟨_, hMemKeys, hBase⟩
  have hLe : freshBase h align ≤ (h.keys.image Prod.fst).sup id :=
    Finset.le_sup (f := id) hImage
  have hGe : 2 * ((h.keys.image Prod.fst).sup id + 1) + 1 ≤ freshBase h align :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hContra := Nat.le_trans hGe hLe
  generalize (h.keys.image Prod.fst).sup id = s at hContra
  omega

theorem compatible_freshLoc {α : Type} (h : Heap) (align : Nat) (contents : List (Option α))
    (last : Slot) :
    PartialCommMonoid.Compatible (allocation (freshLoc h align) contents last) h := by
  intro address hFresh hMem
  apply not_mem_freshBase (h := h) (align := align) _ hMem
  rcases Heap.mem_union.mp hFresh with hRange | hEnd
  · obtain ⟨i, -, rfl⟩ := mem_cells.mp hRange
    rfl
  · rw [mem_slot.mp hEnd]
    rfl

private theorem compatible_cells_end {α : Type} (l : Loc) (contents : List (Option α))
    (last : Slot) :
    PartialCommMonoid.Compatible (cells l contents) (slot (l.add contents.length) last) := by
  intro address hRange hEnd
  obtain ⟨i, hi, rfl⟩ := mem_cells.mp hRange
  have hOffset := congrArg Prod.snd (mem_slot.mp hEnd)
  simp only [Loc.add_snd] at hOffset
  omega

theorem sub_allocation {α : Type} (l : Loc) (contents : List (Option α)) (last : Slot) :
    Heap.Sub (cells l contents) (allocation l contents last) :=
  ⟨_, compatible_cells_end l contents last, rfl⟩

theorem compatible_allocation {α : Type} (l : Loc) (contents : List (Option α)) (last : Slot) :
    PartialCommMonoid.Compatible (cells l contents) (slot (l.add contents.length) last) :=
  compatible_cells_end l contents last

namespace Sub

@[refl]
theorem refl (h : Heap) : Heap.Sub h h :=
  ⟨∅,
    PartialCommMonoid.compatible_comm
      (PartialCommMonoid.compatible_empty_left h),
    (PartialCommMonoid.union_empty h).symm⟩

theorem trans {h₁ h₂ h₃ : Heap} (hSub₁₂ : Heap.Sub h₁ h₂)
    (hSub₂₃ : Heap.Sub h₂ h₃) : Heap.Sub h₁ h₃ := by
  obtain ⟨rest₁, hCompatible₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hCompatible₂, rfl⟩ := hSub₂₃
  have ⟨_, hCompatible⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ rest₁ rest₂).mp
      ⟨hCompatible₁, hCompatible₂⟩
  exact ⟨rest₁ ∪ rest₂, hCompatible,
    PartialCommMonoid.union_assoc hCompatible₁ hCompatible₂⟩

theorem of_empty (h : Heap) : Heap.Sub empty h :=
  ⟨h, PartialCommMonoid.compatible_empty_left h,
    (PartialCommMonoid.empty_union h).symm⟩

theorem union_left {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hCompatible, rfl⟩

theorem union_right {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₂ (h₁ ∪ h₂) :=
  ⟨h₁, PartialCommMonoid.compatible_comm hCompatible,
    PartialCommMonoid.union_comm_of_compatible hCompatible⟩

theorem split {h₁ h₂ h' : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub : Heap.Sub (h₁ ∪ h₂) h') :
    ∃ h₂', PartialCommMonoid.Compatible h₁ h₂' ∧
      h' = h₁ ∪ h₂' ∧ Heap.Sub h₂ h₂' := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hCompatible₂, hCompatible₁⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ rest).mp
      ⟨hCompatible, hCompatibleRest⟩
  exact ⟨h₂ ∪ rest, hCompatible₁,
    PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
    ⟨rest, hCompatible₂, rfl⟩⟩

theorem disjoint_of_sub {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    PartialCommMonoid.Compatible h frame := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have ⟨hFrame, _⟩ :=
    (PartialCommMonoid.compatible_assoc rest frame h).mp
      ⟨hRestFrame,
        PartialCommMonoid.compatible_comm hRestFrame'⟩
  exact PartialCommMonoid.compatible_comm hFrame

theorem union_mono_left {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    Heap.Sub (h ∪ frame) (h' ∪ frame) := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have hFrameRest := PartialCommMonoid.compatible_comm hRestFrame
  have hFrameRest' :
      PartialCommMonoid.Compatible h (frame ∪ rest) := by
    rw [← PartialCommMonoid.union_comm_of_compatible hRestFrame]
    exact hRestFrame'
  have ⟨hCompatibleFrame, hCompatibleCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h frame rest).mpr
      ⟨hFrameRest, hFrameRest'⟩
  refine ⟨rest, hCompatibleCombined, ?_⟩
  calc
    (h ∪ rest) ∪ frame = h ∪ (rest ∪ frame) :=
      PartialCommMonoid.union_assoc hCompatibleRest hCompatible
    _ = h ∪ (frame ∪ rest) := congrArg (h ∪ ·)
      (PartialCommMonoid.union_comm_of_compatible hRestFrame)
    _ = (h ∪ frame) ∪ rest :=
      (PartialCommMonoid.union_assoc
        hCompatibleFrame hCompatibleCombined).symm

theorem union_mono {A B h₁ h₂ : Heap}
    (hSub₁ : Heap.Sub A h₁) (hSub₂ : Heap.Sub B h₂)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub (A ∪ B) (h₁ ∪ h₂) := by
  have hAh₂ : PartialCommMonoid.Compatible A h₂ :=
    Heap.Sub.disjoint_of_sub hSub₁ hCompatible
  have hAB : PartialCommMonoid.Compatible A B :=
    PartialCommMonoid.compatible_comm
      (Heap.Sub.disjoint_of_sub hSub₂
        (PartialCommMonoid.compatible_comm hAh₂))
  have hStep₁ : Heap.Sub (B ∪ A) (h₂ ∪ A) :=
    Heap.Sub.union_mono_left hSub₂ (PartialCommMonoid.compatible_comm hAh₂)
  have hStep₂ : Heap.Sub (A ∪ B) (A ∪ h₂) := by
    rw [PartialCommMonoid.union_comm_of_compatible hAB,
      PartialCommMonoid.union_comm_of_compatible hAh₂]
    exact hStep₁
  exact hStep₂.trans (Heap.Sub.union_mono_left hSub₁ hCompatible)

end Sub

theorem mem_of_contains {α : Type} {h : Heap} {l : Loc}
    (hContains : contains h α l) : l ∈ h := by
  unfold contains at hContains
  split at hContains
  · rename_i hLookup
    exact Heap.mem_of_lookup_eq_some hLookup
  · contradiction

theorem disjoint_contains_false {α : Type} {h₁ h₂ : Heap} {l : Loc}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains₁ : contains h₁ α l)
    (hContains₂ : contains h₂ α l) : False :=
  hCompatible l (mem_of_contains hContains₁)
    (mem_of_contains hContains₂)

/-- A cell has a single type. -/
theorem contains_unique {α β : Type} {h : Heap} {l : Loc}
    (hα : contains h α l) (hβ : contains h β l) : α = β := by
  unfold contains at hα hβ
  split at hα <;> simp_all

theorem contains_union_left {α : Type} {h₁ h₂ : Heap} {l : Loc}
    (hContains : contains h₁ α l) : contains (h₁ ∪ h₂) α l := by
  have hMem : l ∈ h₁ := mem_of_contains hContains
  unfold contains at hContains ⊢
  rw [Heap.lookup_union_left hMem]
  exact hContains

/-- `read` only depends on the slot. -/
private theorem read_eq_of_lookup {α : Type} {h₁ h₂ : Heap} {l : Loc}
    (hLookup : h₁.lookup l = h₂.lookup l)
    (hContains₁ : contains h₁ α l) (hContains₂ : contains h₂ α l) :
    Heap.read l h₁ hContains₁ = Heap.read l h₂ hContains₂ := by
  unfold Heap.read
  split
  · rename_i β content hLookup₁
    split
    · rename_i β₂ content₂ hLookup₂
      have hEq : Slot.live β content = Slot.live β₂ content₂ :=
        Option.some.inj (hLookup₁.symm.trans (hLookup.trans hLookup₂))
      cases hEq
      rfl
    all_goals (rename_i hLookup₂; simp [contains, hLookup₂] at hContains₂)
  all_goals (rename_i hLookup₁; simp [contains, hLookup₁] at hContains₁)

theorem read_union_left {α : Type} {h₁ h₂ : Heap} {l : Loc}
    (hContains : contains h₁ α l) :
    Heap.read l (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.read l h₁ hContains :=
  read_eq_of_lookup (Heap.lookup_union_left (mem_of_contains hContains)) _ _

theorem update_union_left {α : Type} {h₁ h₂ : Heap}
    (l : Loc) (content : Option α) (hContains : contains h₁ α l) :
    Heap.update l content (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.update l content h₁ hContains ∪ h₂ := by
  exact Heap.insert_union

private theorem disjoint_insert_left {l : Loc} {s : Slot}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hMem : l ∈ h₁) :
    PartialCommMonoid.Compatible (h₁.insert l s) h₂ := by
  intro address hMem₁ hMem₂
  rcases Heap.mem_insert.mp hMem₁ with rfl | hMem₁
  · exact hCompatible _ hMem hMem₂
  · exact hCompatible address hMem₁ hMem₂

theorem disjoint_update_left {α : Type} {l : Loc} {content : Option α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ α l) :
    PartialCommMonoid.Compatible
      (Heap.update l content h₁ hContains) h₂ :=
  disjoint_insert_left hCompatible (mem_of_contains hContains)

theorem disjoint_free_left {α : Type} {l : Loc}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ α l) :
    PartialCommMonoid.Compatible (Heap.free l h₁ hContains) h₂ :=
  disjoint_insert_left hCompatible (mem_of_contains hContains)

theorem free_union_left {α : Type} {h₁ h₂ : Heap}
    (l : Loc) (_ : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ α l) :
    Heap.free l (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.free l h₁ hContains ∪ h₂ :=
  Heap.insert_union

/-- A freed slot keeps its address, so its allocation id is never handed out again. -/
theorem mem_free {α : Type} {l : Loc} {h : Heap} (hContains : contains h α l) :
    l ∈ Heap.free l h hContains :=
  Heap.mem_insert.mpr (Or.inl rfl)

/-- A dead slot cannot be read, written or freed. -/
theorem not_contains_of_dead {α : Type} {l : Loc} {h : Heap} (hDead : Heap.dead h l) :
    ¬ contains h α l := by
  simp [contains, Heap.lookup, show h.impl.lookup l = some .dead from hDead]

/-- A freed slot is dead: it cannot be read, written or freed again. -/
theorem not_contains_free {α β : Type} {l : Loc} {h : Heap} (hContains : contains h α l) :
    ¬ contains (Heap.free l h hContains) β l := by
  simp [contains, Heap.free, Heap.insert, Heap.lookup]

/-- Allocation leaves the slots already in the heap untouched. -/
theorem contains_freshHeap_of_mem {α β : Type} {h : Heap} {align : Nat} {contents : List (Option β)}
    {last : Slot} {l : Loc}
    (hMem : l ∈ h) : contains (freshHeap h align contents last) α l ↔ contains h α l := by
  have hNotMem : l ∉ allocation (freshLoc h align) contents last :=
    fun hFresh => compatible_freshLoc h align contents last l hFresh hMem
  unfold contains
  rw [show (freshHeap h align contents last).lookup l = h.lookup l from
    Finmap.lookup_union_right hNotMem]

/-- The end marker of an allocation is in the heap, so even an empty allocation reserves its id. -/
theorem mem_freshHeap_end {α : Type} (h : Heap) (align : Nat) (contents : List (Option α)) (last : Slot) :
    (freshLoc h align).add contents.length ∈ freshHeap h align contents last :=
  Heap.mem_union.mpr (Or.inl (Heap.mem_union.mpr (Or.inr (mem_slot.mpr rfl))))

/-- The end marker of an allocation is dead. -/
theorem not_contains_freshHeap_end {α β : Type} (h : Heap) (align : Nat) (contents : List (Option β))
    (last : Slot) (hLast : ∀ γ c, last ≠ .live γ c) :
    ¬ contains (freshHeap h align contents last) α ((freshLoc h align).add contents.length) := by
  have hNotRange :
      (freshLoc h align).add contents.length ∉ (cells (freshLoc h align) contents).impl := by
    intro hRange
    obtain ⟨i, hi, hEq⟩ := mem_cells.mp hRange
    have hOffset := congrArg Prod.snd hEq
    simp only [Loc.add_snd] at hOffset
    omega
  have hEnd : (freshLoc h align).add contents.length ∈
      (slot ((freshLoc h align).add contents.length) last).impl :=
    mem_slot.mpr rfl
  have hLookup : (freshHeap h align contents last).lookup ((freshLoc h align).add contents.length) =
      some last := by
    show Finmap.lookup _ (((cells (freshLoc h align) contents).impl ∪
      (slot ((freshLoc h align).add contents.length) last).impl) ∪ h.impl) = _
    rw [Finmap.lookup_union_left (Finmap.mem_union.mpr (Or.inr hEnd)),
      Finmap.lookup_union_right hNotRange]
    simp [slot]
  unfold contains
  rw [hLookup]
  cases last with
  | live γ c => exact absurd rfl (hLast γ c)
  | dead | boxEnd => simp

theorem disjoint_cell {α : Type} {l l' : Loc} {content₁ content₂ : Option α}
    (hNe : l ≠ l') :
    PartialCommMonoid.Compatible
      (cell l content₁) (cell l' content₂) := by
  intro address hMem₁ hMem₂
  exact hNe ((mem_cell.mp hMem₁).symm.trans (mem_cell.mp hMem₂))

theorem contains_cell {α : Type} (l : Loc) (content : Option α) :
    contains (cell l content) α l := by
  simp [contains, cell, slot, Heap.lookup]

theorem read_cell {α : Type} (l : Loc) (content : Option α)
    (hContains : contains (cell l content) α l) :
    Heap.read l (cell l content) hContains = content := by
  unfold Heap.read
  split
  · rename_i β stored hLookup
    rw [show cell l content = slot l (.live α content) from rfl, lookup_slot] at hLookup
    cases hLookup
    rfl
  all_goals (rename_i hLookup; rw [show cell l content = slot l (.live α content) from rfl,
    lookup_slot] at hLookup; cases hLookup)

theorem update_cell {α : Type} (l : Loc)
    (oldContent newContent : Option α)
    (hContains : contains (cell l oldContent) α l) :
    Heap.update l newContent (cell l oldContent) hContains =
      cell l newContent := by
  apply Heap.ext_impl
  simp [Heap.update, cell, slot, Heap.insert]

theorem Sub.contains {α : Type} {A h : Heap} {l : Loc} (hSub : Heap.Sub A h)
    (hContains : contains A α l) : contains h α l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact contains_union_left hContains

theorem contains_cells {α : Type} {l : Loc} {contents : List (Option α)} {i : Nat}
    (hIndex : i < contents.length) : contains (cells l contents) α (l.add i) := by
  induction contents generalizing l i with
  | nil => simp at hIndex
  | cons content rest ih =>
    rw [cells_cons]
    cases i with
    | zero => exact contains_union_left (contains_cell l content)
    | succ j =>
      have hCompatible :
          PartialCommMonoid.Compatible (cell l content) (cells (l.add 1) rest) := by
        simpa using compatible_cells_append l [content] rest
      rw [PartialCommMonoid.union_comm_of_compatible hCompatible,
        show l.add (j + 1) = (l.add 1).add j by rw [Loc.add_add, Nat.add_comm]]
      exact contains_union_left (ih (by simpa using hIndex))

theorem read_of_sub {α : Type} {l : Loc} {content : Option α} {h : Heap}
    (hSub : Heap.Sub (cell l content) h)
    (hContains : contains h α l) : Heap.read l h hContains = content := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hContainsCell := contains_cell l content
  rw [show hContains = contains_union_left hContainsCell from
      Subsingleton.elim _ _,
    read_union_left hContainsCell, read_cell]

theorem dead_union_left {h₁ h₂ : Heap} {l : Loc} (hDead : Heap.dead h₁ l) :
    Heap.dead (h₁ ∪ h₂) l :=
  (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hDead)).trans hDead

theorem Sub.dead {h : Heap} {l : Loc} (hSub : Heap.Sub (endMarker l) h) : Heap.dead h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact dead_union_left (by simp [Heap.dead, endMarker, slot])

theorem Sub.isBoxEnd {h : Heap} {l : Loc} (hSub : Heap.Sub (boxEnd l) h) : Heap.isBoxEnd h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some
    (show (boxEnd l).impl.lookup l = some .boxEnd by simp [boxEnd, slot]))).trans
    (by simp [boxEnd, slot])

theorem disjoint_revive_left {α : Type} {l : Loc} {content : Option α} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hDead : Heap.dead h₁ l) :
    PartialCommMonoid.Compatible (Heap.revive l content h₁ hDead) h₂ :=
  disjoint_insert_left hCompatible (Finmap.mem_of_lookup_eq_some hDead)

theorem revive_union_left {α : Type} {h₁ h₂ : Heap} (l : Loc) (content : Option α)
    (hDead : Heap.dead h₁ l) :
    Heap.revive l content (h₁ ∪ h₂) (dead_union_left hDead) =
      Heap.revive l content h₁ hDead ∪ h₂ :=
  Heap.insert_union

/-- Freeing a slot one owns leaves one owning it dead. -/
theorem Sub.free {α : Type} {l : Loc} {content : Option α} {h : Heap}
    (hSub : Heap.Sub (cell l content) h) (hContains : Heap.contains h α l) :
    Heap.Sub (endMarker l) (Heap.free l h hContains) := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  refine ⟨rest, fun a hMem => hCompatible a (mem_cell.mpr (mem_endMarker.mp hMem)), ?_⟩
  show (cell l content ∪ rest).insert l .dead = _
  rw [Heap.insert_union]
  congr 1
  apply Heap.ext_impl
  simp [Heap.insert, cell, endMarker, slot]

/-- Reviving a dead slot one owns leaves one owning it live. -/
theorem Sub.revive {α : Type} {l : Loc} {h : Heap} (content : Option α)
    (hSub : Heap.Sub (endMarker l) h) (hDead : Heap.dead h l) :
    Heap.Sub (cell l content) (Heap.revive l content h hDead) := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  refine ⟨rest, fun a hMem => hCompatible a (mem_endMarker.mpr (mem_cell.mp hMem)), ?_⟩
  show (endMarker l ∪ rest).insert l (.live α content) = _
  rw [Heap.insert_union]
  congr 1
  apply Heap.ext_impl
  simp [Heap.insert, cell, endMarker, slot]

/-- A slot which is not a live cell can not be read, written or freed. -/
theorem Sub.not_contains {α : Type} {h : Heap} {l : Loc} {s : Slot} (hSub : Heap.Sub (slot l s) h)
    (hs : ∀ β c, s ≠ .live β c) : ¬ Heap.contains h α l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  have hLookup : (slot l s ∪ rest).lookup l = some s :=
    (Heap.lookup_union_left (mem_slot.mpr rfl)).trans (lookup_slot l s)
  unfold Heap.contains
  rw [hLookup]
  cases s with
  | live β c => exact absurd rfl (hs β c)
  | dead | boxEnd => simp

/-- A dead slot is not the end marker of a box. -/
theorem Sub.not_isBoxEnd {h : Heap} {l : Loc} (hSub : Heap.Sub (endMarker l) h) :
    ¬ Heap.isBoxEnd h l := by
  have hDead : Heap.dead h l := Sub.dead hSub
  unfold Heap.dead at hDead
  unfold Heap.isBoxEnd
  rw [hDead]
  simp

end Heap

end Aeneas.Std
