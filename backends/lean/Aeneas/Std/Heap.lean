module

public import Mathlib.Data.Finmap

/-! Block-based heap: finite map from (allocation id, offset) to slots. A slot is a typed cell,
initialized (`some value`) or not (`none`), or a dead slot. Supports interior pointers, stored
pointers, uninitialized memory, provenance by allocation id. Freed slots and the end marker of each
allocation stay in the map as dead slots, so allocation ids are never reused. The end marker of a
box allocation is a distinguished dead slot, which is what makes freeing check that it frees a
whole box. Not supported: byte-level representation/type punning, pointer-integer casts,
higher-order store, permissions. -/

public section

namespace Aeneas.Std

abbrev AllocId := Nat

abbrev Loc := AllocId × Nat

/-- A heap slot. Dead slots (`dead`, `boxEnd`) are never readable, but keep their allocation id
reserved. -/
inductive Slot : Type 1 where
  /-- A cell holding a value of type `α`, or uninitialized (`none`). -/
  | live (α : Type) (content : Option α)
  /-- A freed slot, a slot moved out by a borrow, or the end marker of an allocation which is not
  a box. -/
  | dead
  /-- The end marker of a box allocation (its single cell is at offset `0`). -/
  | boxEnd

abbrev HeapImpl := Finmap fun _ : Loc => Slot

structure Heap where
  private mk ::
  private impl : HeapImpl

@[expose]
def Loc.add (l : Loc) (i : Nat) : Loc := (l.1, l.2 + i)

namespace Heap

private def lookup (h : Heap) (address : Loc) : Option Slot :=
  h.impl.lookup address

private def insert (h : Heap) (address : Loc) (slot : Slot) : Heap :=
  ⟨h.impl.insert address slot⟩

private def keys (h : Heap) :=
  h.impl.keys

def empty : Heap := ⟨∅⟩

instance instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

def union (h₁ h₂ : Heap) : Heap := ⟨h₁.impl ∪ h₂.impl⟩

instance instUnion : Union Heap := ⟨Heap.union⟩

def mem (address : Loc) (h : Heap) : Prop :=
  address ∈ h.impl

instance instMembership : Membership Loc Heap :=
  ⟨fun h address => Heap.mem address h⟩

def compatible (h₁ h₂ : Heap) : Prop :=
  Finmap.Disjoint h₁.impl h₂.impl

/-- The single slot `slot` at `l`. -/
def slot (l : Loc) (s : Slot) : Heap := ⟨Finmap.singleton l s⟩

/-- A live cell at `l` of type `α`, uninitialized if `content = none`. -/
@[expose] def cell {α : Type} (l : Loc) (content : Option α) : Heap := slot l (.live α content)

/-- A dead slot at `l`. -/
@[expose] def endMarker (l : Loc) : Heap := slot l .dead

/-- The end marker of a box allocation at `l`. -/
@[expose] def boxEnd (l : Loc) : Heap := slot l .boxEnd

/-- The definedness guard of operations on `l`: `h` holds a live cell of type `α` at `l`,
initialized or not. -/
def contains (h : Heap) (α : Type) (l : Loc) : Prop :=
  match h.lookup l with
  | some (.live β _) => β = α
  | _ => False

@[expose]
def cells {α : Type} (l : Loc) : List (Option α) → Heap
  | [] => empty
  | content :: rest => cell l content ∪ cells (l.add 1) rest

/-- `contents` stored from `l` on, followed by the end marker `last`: it reserves the allocation
id even when `contents` is empty. -/
@[expose] def allocation {α : Type} (l : Loc) (contents : List (Option α)) (last : Slot) : Heap :=
  cells l contents ∪ slot (l.add contents.length) last

/-- The next allocation identifier, past every one in the heap: allocation is deterministic. Since
freed slots and end markers stay in the heap as dead slots, an identifier is never handed out
twice. -/
def freshBase (h : Heap) : AllocId :=
  (h.keys.image Prod.fst).sup id + 1

@[expose] def freshLoc (h : Heap) : Loc := (freshBase h, 0)

@[expose] def freshHeap {α : Type} (h : Heap) (contents : List (Option α)) (last : Slot) : Heap :=
  allocation (freshLoc h) contents last ∪ h

/-- `h'` is `h` extended with cells that `h` does not own. -/
@[expose] def Sub (h h' : Heap) : Prop :=
  ∃ rest, Heap.compatible h rest ∧ h' = h ∪ rest

/-- The content of the live cell at `l`: `none` if it is uninitialized. -/
def read {α : Type} (l : Loc) (h : Heap)
    (hContains : contains h α l) : Option α :=
  match hlookup : h.lookup l with
  | some (.live β content) => by
      have htype : β = α := by
        simpa [contains, hlookup] using hContains
      exact htype ▸ content
  | some .dead | some .boxEnd | none => by simp [contains, hlookup] at hContains

/-- Writes `content` to the live cell at `l`, initialized or not. -/
def update {α : Type} (l : Loc) (content : Option α) (h : Heap)
    (_ : contains h α l) : Heap :=
  h.insert l (.live α content)

/-- Kills the slot at `l`: it stays in the heap as a dead slot. -/
def free {α : Type} (l : Loc) (h : Heap)
    (_ : contains h α l) : Heap :=
  h.insert l .dead

/-- The slot at `l` is dead: freed, killed, or the end marker of an allocation which is not a
box. -/
def dead (h : Heap) (l : Loc) : Prop :=
  h.impl.lookup l = some .dead

/-- The slot at `l` is the end marker of a box allocation. -/
def isBoxEnd (h : Heap) (l : Loc) : Prop :=
  h.impl.lookup l = some .boxEnd

/-- Brings the dead slot at `l` back to life, holding `content`. -/
def revive {α : Type} (l : Loc) (content : Option α) (h : Heap)
    (_ : dead h l) : Heap :=
  h.insert l (.live α content)

end Heap

end Aeneas.Std
