module
import Aeneas.Std.HeapLemmas

/-! Freed slots and end markers are dead, and their allocation ids are never reused. -/

namespace Aeneas.Std.HeapTests

open Heap

/-- The first free of a fresh slot is allowed; a second one is not, since its guard fails. -/
example (value : Nat) :
    ∃ hContains : contains (freshHeap ∅ [some value] .boxEnd) Nat (freshLoc ∅),
      ¬ contains (free (freshLoc ∅) (freshHeap ∅ [some value] .boxEnd) hContains) Nat
        (freshLoc ∅) :=
  ⟨contains_union_left (contains_union_left (by
    rw [cells_singleton]; exact contains_cell _ (some value))), not_contains_free _⟩

/-- Allocating after a free gets a new id, and the freed slot stays dead. -/
example {α : Type} (h : Heap) (l : Loc) (hContains : contains h α l) (value : Option α) :
    (freshLoc (free l h hContains)).1 ≠ l.1 ∧
      ¬ contains (freshHeap (free l h hContains) [value] .dead) α l :=
  ⟨fun hEq => not_mem_freshBase hEq.symm (mem_free hContains),
    fun hLive => not_contains_free hContains
      ((contains_freshHeap_of_mem (mem_free hContains)).mp hLive)⟩

/-- An empty allocation reserves its id, and its pointer stays dead after the next allocation. -/
example {α β : Type} (h : Heap) (value : Option β) :
    (freshLoc (freshHeap h ([] : List (Option α)) .dead)).1 ≠ (freshLoc h).1 ∧
      ¬ contains (freshHeap (freshHeap h ([] : List (Option α)) .dead) [value] .dead) β
        (freshLoc h) :=
  ⟨fun hEq => not_mem_freshBase hEq.symm (mem_freshHeap_end h ([] : List (Option α)) .dead),
    fun hLive => not_contains_freshHeap_end h ([] : List (Option α)) .dead (by simp)
      ((contains_freshHeap_of_mem (mem_freshHeap_end _ _ _)).mp hLive)⟩

end Aeneas.Std.HeapTests
