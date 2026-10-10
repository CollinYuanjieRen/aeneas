module
public import Aeneas.Std.Delab
public import Aeneas.Std.Heap
public import Aeneas.SepLogic.IProp
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.SliceDef
public import Aeneas.Data.List.List
public import Aeneas.Std.WP
public import Aeneas.Std.Primitives
public import Aeneas.SepLogic.Lemmas
public import Aeneas.SepLogic.Delab
public import Aeneas.SepLogic.Tactic.IFrame
public import Aeneas.SepLogic.Tactic.IIntro
public import Aeneas.SepLogic.Tactic.IRewrite
public import Aeneas.SepLogic.Tactic.ISimp
public import Aeneas.Tactic.Step.Init
@[expose] public section

open Aeneas SepLogic

namespace Aeneas.Std

/-! ### START Trusted definitions

Every executable definition below models a Rust function (see its `rust_fun` pattern), with the
signature Aeneas gives that function: `Box<T>` is `T`, and a `&mut T` argument is returned updated
next to the result. The exceptions are the heap primitives behind them (`RawPtr.allocate`,
`RawPtr.materialize`, `RawPtr.take`, `RawPtr.revive`, their range versions, `RawPtr.null`,
`RawPtr.LiveBox`, `Result.require`), `RawPtr.eq` and `RawPtr.ne`, which model `==` and `!=` on raw
pointers, and `RawPtr.cast_scalar`, the `as` cast between raw pointers, which always fails.

The heap is typed: a pointer `*mut T` reads and writes cells of type `Pointee.Cell T`, which is
`T` itself except for `MaybeUninit<U>`, whose cells are the (possibly uninitialized) cells of `U`.
Every access checks the type of the cell, so that casting a pointer (`<*mut T>::cast`) is safe: an
access at a type which does not match the cell fails. The extraction only accepts the casts which
add or remove `MaybeUninit` wrappers, since several Rust types share the same Lean type (`Box<T>`
and `&T` are `T`). -/

inductive Mutability where
| Mut | Const

/-- A Rust raw pointer: an allocation identifier and an offset into it. `T` is a phantom
    parameter, universe-polymorphic like the other type parameters (only the heap cells a
    pointer reads or writes need to live in `Type`). -/
structure RawPtr (T : Type _) (M : Mutability) where
  base : AllocId
  offset : Nat
  deriving Inhabited, DecidableEq

abbrev MutRawPtr (T : Type _) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type _) := RawPtr T .Const

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab RawPtr]
meta def delabRawPtr : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``RawPtr 2)
  let name ← match e.appArg! with
    | .const ``Mutability.Mut _ => pure ``MutRawPtr
    | .const ``Mutability.Const _ => pure ``ConstRawPtr
    | _ => failure
  let t ← withNaryArg 0 delab
  `($(mkIdent (← unresolveNameGlobal name)) $t)

/-- How the values of type `T` are stored in the heap: a value is a cell of type `Cell`, which
may be uninitialized (`none`). `ofCell` gives back the value stored in a cell, if any: reading an
uninitialized cell fails unless `T` can represent uninitialized memory (`MaybeUninit`).

The cells of `T` must have the memory representation of `T` (this is what makes pointer casts
between types with the same cells meaningful).

Limitation: the instance is resolved where a definition is elaborated, so generic code (with a
type parameter `T`) always uses `Pointee.default`, whose cells have type `T`. Instantiated with
`T := MaybeUninit U`, such code accesses cells of type `MaybeUninit U`, while the concrete
functions on `MaybeUninit U` (and the slices, boxes and pointers created from them) use cells of
type `U`: the accesses of the generic code to those cells always fail (this is sound, but such
programs can not be verified). -/
class Pointee (T : Type) where
  Cell : Type
  toCell : T → Option Cell
  ofCell : Option Cell → Option T
  ofCell_toCell (value : T) : ofCell (toCell value) = some value

/-- By default, the cells of `T` hold initialized values of type `T`. -/
instance (priority := low) Pointee.default {T : Type} : Pointee T where
  Cell := T
  toCell := some
  ofCell := id
  ofCell_toCell _ := rfl

@[simp] theorem Pointee.toCell_default {T : Type} (value : T) :
    @Pointee.toCell T Pointee.default value = some value := rfl

@[simp] theorem Pointee.ofCell_default {T : Type} (content : Option T) :
    @Pointee.ofCell T Pointee.default content = content := rfl

namespace RawPtr

def addr (q : RawPtr T M) : Loc := (q.base, q.offset)

/-- `q` moved `i` slots forward, for specifications. Programs use `add`. -/
def shift (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.base, q.offset + i⟩

def retype (q : RawPtr T M) : RawPtr U M' :=
  ⟨q.base, q.offset⟩

/-- `q` owns a cell holding `content` (uninitialized if `content = none`). -/
def pointsToCell {T : Type} [Pointee T] (q : RawPtr T M) (content : Option (Pointee.Cell T)) :
    IProp :=
  owns (Heap.cell q.addr content)

/-- `q` owns the `contents.length` cells from `q` on. -/
def pointsToCells {T : Type} [Pointee T] (q : RawPtr T M)
    (contents : List (Option (Pointee.Cell T))) : IProp :=
  owns (Heap.cells q.addr contents)

def pointsTo {T : Type} [Pointee T] (q : RawPtr T M) (value : T) : IProp :=
  q.pointsToCell (Pointee.toCell value)

/-- `q` owns the `values.length` slots from `q` on. -/
def pointsToRange {T : Type} [Pointee T] (q : RawPtr T M) (values : List T) : IProp :=
  q.pointsToCells (values.map Pointee.toCell)

/-- `q` owns the `n` dead slots from `q` on (killed by `take`, to be brought back by `revive`). -/
def pointsToDead (q : RawPtr T M) : Nat → IProp
  | 0 => emp
  | n + 1 => owns (Heap.endMarker q.addr) ∗ pointsToDead (q.shift 1) n

/-- `q` points to the cell of a box allocation: `Box::from_raw` can free it. -/
def boxed (q : RawPtr T M) : IProp :=
  owns (Heap.boxEnd (q.addr.add 1))

end RawPtr

instance instPointsToRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

instance instPointsToRangeRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsToRange (RawPtr T M) T := ⟨RawPtr.pointsToRange⟩

end Aeneas.Std

namespace Aeneas

scoped notation:50 q:50 " ↦† " n:50 => Std.RawPtr.pointsToDead q n
scoped notation:50 q:50 " ↦? " content:50 => Std.RawPtr.pointsToCell q content
scoped notation:50 q:50 " ↦*? " contents:50 => Std.RawPtr.pointsToCells q contents

end Aeneas

namespace Aeneas.Std

open Aeneas

/-- Not a Rust function: stores `values` in fresh slots, followed by the end marker `last`. -/
def RawPtr.allocate {T : Type} [Pointee T] (last : Slot) (values : List T) :
    Result (RawPtr T M) :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (⟨(Heap.freshLoc h).1, (Heap.freshLoc h).2⟩,
      Heap.freshHeap h (values.map Pointee.toCell) last)

/-- Not a Rust function: stores `values` in fresh slots, which can not be freed. -/
def RawPtr.materialize {T : Type} [Pointee T] (values : List T) : Result (RawPtr T M) :=
  RawPtr.allocate .dead values

/-- `add` stays in bounds. -/
def RawPtr.InBounds (q : RawPtr T M) (count : Nat) (h : Heap) : Prop :=
  ∀ i < count, ∃ α, Heap.contains h α (q.addr.add i)

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::add"]
def RawPtr.add (q : RawPtr T M) (count : Usize) : Result (RawPtr T M) :=
  Result.guardedModify (fun h => q.InBounds count.val h) fun h _ => (q.shift count.val, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::add"] RawPtr.add

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast_const" -canFail -lift]
def RawPtr.cast_const (q : MutRawPtr T) : ConstRawPtr T :=
  q.retype

/-- Changes the pointee type: the accesses through the new pointer check that the cells have the
type of the new pointee (see `Pointee`). -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast" -canFail -lift]
def RawPtr.cast {T : Type _} {M : Mutability} (U : Type _) (q : RawPtr T M) : RawPtr U M :=
  q.retype

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::cast" -canFail -lift] RawPtr.cast

namespace RawPtr

/-- `q` points to a live cell of the type of its pointee, holding a value of the pointee. -/
structure Readable {T : Type} [Pointee T] (q : RawPtr T M) (h : Heap) : Prop where
  contains : Heap.contains h (Pointee.Cell T) q.addr
  valid : (Pointee.ofCell (Heap.read q.addr h contains)).isSome

/-- The value `q` points to. -/
def get {T : Type} [Pointee T] (q : RawPtr T M) (h : Heap) (hReadable : q.Readable h) : T :=
  (Pointee.ofCell (Heap.read q.addr h hReadable.contains)).get hReadable.valid

@[rust_fun "core::ptr::const_ptr::{*const @T}::read"]
def read {T : Type} [Pointee T] (q : RawPtr T M) : Result T :=
  Result.guardedModify (fun h => q.Readable h) fun h hReadable => (q.get h hReadable, h)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read

end RawPtr

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write {T : Type} [Pointee T] (q : MutRawPtr T) (value : T) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h (Pointee.Cell T) q.addr) fun h hContains =>
    ((), Heap.update q.addr (Pointee.toCell value) h hContains)

attribute [rust_fun "core::ptr::write"] MutRawPtr.write

@[rust_fun "alloc::boxed::{Box<@T>}::into_raw"]
def alloc.boxed.Box.into_raw {T : Type} [Pointee T] (b : T) : Result (MutRawPtr T) :=
  RawPtr.allocate .boxEnd [b]

/-- Not a Rust function: moves the value out and kills its slot. -/
def RawPtr.take {T : Type} [Pointee T] (q : RawPtr T M) : Result T :=
  Result.guardedModify (fun h => q.Readable h) fun h hReadable =>
    (q.get h hReadable, Heap.free q.addr h hReadable.contains)

/-- Not a Rust function: brings the dead slot of `q` back to life, holding `value`. -/
def RawPtr.revive {T : Type} [Pointee T] (q : RawPtr T M) (value : T) : Result Unit :=
  Result.guardedModify (fun h => Heap.dead h q.addr) fun h hDead =>
    ((), Heap.revive q.addr (Pointee.toCell value) h hDead)

/-- Not a Rust function: `take` on the `n` slots from `q` on. -/
def RawPtr.takeRange {T : Type} [Pointee T] (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.take
    let values ← (q.shift 1).takeRange n
    .ok (value :: values)

/-- Not a Rust function: `revive` on the `values.length` slots from `q` on. -/
def RawPtr.reviveRange {T : Type} [Pointee T] (q : RawPtr T M) : List T → Result Unit
  | [] => .ok ()
  | value :: values => do
    q.revive value
    (q.shift 1).reviveRange values

/-- Not a Rust function: fails unless `p` holds (`p` need not be decidable). -/
def Result.require (p : Prop) : Result Unit :=
  Result.guardedModify (fun _ => p) fun h _ => ((), h)

/-- Moves the value out and frees its slot. `p` must point to the cell of a box allocation (see
`Box::into_raw`): the next slot is the end marker of a box, which only box allocations have (at
offset `1`). This rejects double frees, frees of pointers which do not come from a box, and frees
of interior pointers. -/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw {T : Type} [Pointee T] (p : MutRawPtr T) : Result T :=
  Result.guardedModify (fun h => p.Readable h ∧ Heap.isBoxEnd h (p.addr.add 1)) fun h hPre =>
    (p.get h hPre.1, Heap.free p.addr h hPre.1.contains)

/-- Not a Rust function: end of the borrow given to `from_mut`; moves the value, with the writes
made through the pointer, out of the slot and kills it. -/
def core.ptr.end_from_mut {T : Type} [Pointee T] (p : MutRawPtr T) : Result T :=
  p.take

/-- The pointer points to a fresh slot holding `r`; the back computation runs when the borrow
ends (`statefulLifetimes`). -/
@[rust_fun "core::ptr::from_mut" (statefulLifetimes := [0])]
def core.ptr.from_mut {T : Type} [Pointee T] (r : T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.materialize [r]) fun p => .ok (p, core.ptr.end_from_mut p)

/-- `&mut *p`: the value is moved out of its slot, which is killed so that the other accesses to
it fail while the borrow is live, and the slot is brought back to life, holding the final value
of the borrow, when the borrow ends (`statefulLifetimes`). The extraction translates the borrows
of places behind raw pointers (`&mut (*p).f`) to this function. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::as_mut_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) :
    Result (T × (T → Result Unit)) :=
  Aeneas.Std.bind p.take fun value => .ok (value, p.revive)

/-- `&*p`: like `as_mut_unchecked`, the value is moved out while the borrow is live, so that
writing through another pointer fails (this is conservative: reading through another pointer
also fails), and brought back unchanged when the borrow ends. -/
@[rust_fun "core::ptr::const_ptr::{*const @T}::as_ref_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_ref_unchecked {T : Type} [Pointee T] (p : RawPtr T M) : Result (T × Result Unit) :=
  Aeneas.Std.bind p.take fun value => .ok (value, p.revive value)

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::as_ref_unchecked" (statefulLifetimes := [0])]
  RawPtr.as_ref_unchecked

/-- Not a Rust function: the null pointer. The allocation `0` is never allocated (see
`Heap.freshBase`): the pointers to it can not be dereferenced. -/
def RawPtr.null : RawPtr T M := ⟨0, 0⟩

@[rust_fun "core::ptr::null" -canFail -lift]
def core.ptr.null (T : Type _) : ConstRawPtr T := RawPtr.null

@[rust_fun "core::ptr::null_mut" -canFail -lift]
def core.ptr.null_mut (T : Type _) : MutRawPtr T := RawPtr.null

/-- Not a Rust function: `q` points to the live cell of a box allocation (see `Box::into_raw`). -/
def RawPtr.LiveBox {T : Type} [Pointee T] (q : RawPtr T M) (h : Heap) : Prop :=
  Heap.contains h (Pointee.Cell T) q.addr ∧ Heap.isBoxEnd h (q.addr.add 1)

/-- Not a Rust class: `nonZero T = true` if the Rust type modelled by `T` is known not to be
zero-sized. Different slots of the same allocation, or live allocations, then have different
addresses. By default (in particular in generic code, and for `MaybeUninit<()>`, whose Lean model
has two values but which is zero-sized) the type may be zero-sized. The extraction derives the
instances of the structures from their fields (see `RawPtr.eq`); adding an instance is an
assumption. -/
class NonZeroSized (T : Type) where
  nonZero : Bool

instance (priority := low) NonZeroSized.default : NonZeroSized T := ⟨false⟩
instance : NonZeroSized (UScalar ty) := ⟨true⟩
instance : NonZeroSized (IScalar ty) := ⟨true⟩
instance : NonZeroSized Bool := ⟨true⟩
instance : NonZeroSized Char := ⟨true⟩
instance : NonZeroSized (RawPtr T M) := ⟨true⟩
instance [NonZeroSized T] : NonZeroSized (Option T) := ⟨NonZeroSized.nonZero T⟩

/-- Pointer comparison (`==` on raw pointers, `NonNull`). The model does not know the addresses:
two pointers are equal if they are the same. Otherwise they are different if they point to
different slots of the same allocation, or to two live box allocations (live allocations do not
overlap), and the pointee is not zero-sized (`NonZeroSized`). In the other cases the comparison
fails: in particular, the pointers obtained from borrows (`from_mut`, `as_ptr`, `NonNull::from`...)
point to fresh copies of the borrowed values, whose actual addresses are those of the borrowed
values, and freed allocations may share their addresses with new ones. -/
def RawPtr.eq {T : Type} [Pointee T] [NonZeroSized T] (p q : RawPtr T M) : Result Bool :=
  if p.addr = q.addr then .ok true
  else Result.guardedModify
    (fun h => NonZeroSized.nonZero T ∧ (p.base = q.base ∨ p.LiveBox h ∧ q.LiveBox h))
    fun h _ => (false, h)

/-- `!=` on pointers (see `RawPtr.eq`). -/
def RawPtr.ne {T : Type} [Pointee T] [NonZeroSized T] (p q : RawPtr T M) : Result Bool :=
  Aeneas.Std.bind (p.eq q) fun b => .ok (!b)

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

-- TODO: the typed heap cannot read a cell at another scalar type, so casts are not modelled
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability) [IsScalar T] [IsScalar T']
    (_ : RawPtr T M) : Result (RawPtr T' M') :=
  .fail .undef

/-! ### END Trusted definitions -/

namespace RawPtr

def contains {T : Type} [Pointee T] (h : Heap) (q : RawPtr T M) : Prop :=
  Heap.contains h (Pointee.Cell T) q.addr

end RawPtr

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

open WP

namespace RawPtr

@[simp] theorem base_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).base = q.base := rfl

@[simp] theorem offset_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).offset = q.offset + i := rfl

@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q := rfl

@[simp] theorem cast_const_eq_retype (q : MutRawPtr T) : q.cast_const = q.retype := rfl

@[simp] theorem cast_eq_retype (q : RawPtr T M) : (q.cast U : RawPtr U M) = q.retype := rfl

@[simp] theorem base_retype (q : RawPtr T M) : (q.retype : RawPtr U M').base = q.base := rfl

@[simp] theorem offset_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').offset = q.offset := rfl

@[simp] theorem addr_retype (q : RawPtr T M) : (q.retype : RawPtr U M').addr = q.addr := rfl

@[simp] theorem retype_retype (q : RawPtr T M) :
    ((q.retype : RawPtr U M').retype : RawPtr V M'') = q.retype := rfl

@[simp] theorem retype_self (q : RawPtr T M) : (q.retype : RawPtr T M) = q := rfl

theorem shift_retype (q : RawPtr T M) (i : Nat) :
    ((q.retype : RawPtr U M').shift i) = (q.shift i).retype := rfl

theorem addr_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).addr = q.addr.add i := rfl

theorem shift_shift (q : RawPtr T M) (i j : Nat) :
    (q.shift i).shift j = q.shift (i + j) := by
  simp [shift, Nat.add_assoc]

end RawPtr

section PointsTo

variable {T : Type} [Pointee T] {M : Mutability}

theorem RawPtr.pointsTo_eq (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦? Pointee.toCell value) := rfl

theorem RawPtr.pointsToRange_eq (q : RawPtr T M) (values : List T) :
    (q ↦* values) = (q ↦*? values.map Pointee.toCell) := rfl

theorem RawPtr.pointsToCell_eq_cell (q : RawPtr T M) (content : Option (Pointee.Cell T)) :
    (q ↦? content) = owns (Heap.cell q.addr content) := rfl

theorem RawPtr.pointsToCells_eq_cells (q : RawPtr T M)
    (contents : List (Option (Pointee.Cell T))) :
    (q ↦*? contents) = owns (Heap.cells q.addr contents) := rfl

theorem RawPtr.pointsToCell_eq_cells (q : RawPtr T M) (content : Option (Pointee.Cell T)) :
    (q ↦? content) = (q ↦*? [content]) := by
  rw [RawPtr.pointsToCell_eq_cell, RawPtr.pointsToCells_eq_cells, Heap.cells_singleton]

theorem RawPtr.pointsTo_eq_range (q : RawPtr T M) (value : T) :
    (q ↦ value) = (q ↦* [value]) :=
  RawPtr.pointsToCell_eq_cells q _

@[simp] theorem RawPtr.pointsTo_retype (q : RawPtr T M) (value : T) :
    ((q.retype : RawPtr T M') ↦ value) = (q ↦ value) := rfl

@[simp] theorem RawPtr.pointsToRange_retype (q : RawPtr T M) (values : List T) :
    ((q.retype : RawPtr T M') ↦* values) = (q ↦* values) := rfl

@[simp] theorem RawPtr.pointsToCell_retype (q : RawPtr T M) (content : Option (Pointee.Cell T)) :
    ((q.retype : RawPtr T M') ↦? content) = (q ↦? content) := rfl

@[simp] theorem RawPtr.pointsToCells_retype (q : RawPtr T M)
    (contents : List (Option (Pointee.Cell T))) :
    ((q.retype : RawPtr T M') ↦*? contents) = (q ↦*? contents) := rfl

namespace RawPtr

theorem pointsToCells_append (q : RawPtr T M) (xs ys : List (Option (Pointee.Cell T))) :
    (q ↦*? (xs ++ ys)) = iprop(q ↦*? xs ∗ (q.shift xs.length) ↦*? ys) := by
  rw [pointsToCells_eq_cells, pointsToCells_eq_cells, pointsToCells_eq_cells, addr_shift,
    Heap.cells_append q.addr xs ys]
  exact owns_union _ _ (Heap.compatible_cells_append q.addr xs ys)

theorem pointsToCells_split (q : RawPtr T M) (contents : List (Option (Pointee.Cell T)))
    (i : Nat) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗ (q.shift (contents.take i).length) ↦*? contents.drop i) := by
  conv_lhs => rw [← List.take_append_drop i contents]
  exact pointsToCells_append q (contents.take i) (contents.drop i)

theorem pointsToCells_eq_take_get_drop {q : RawPtr T M}
    {contents : List (Option (Pointee.Cell T))} {i : Nat} (hIndex : i < contents.length) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗
        ((q.shift i) ↦? contents[i] ∗ (q.shift (i + 1)) ↦*? contents.drop (i + 1))) := by
  have hTake : (contents.take i).length = i := by simp; omega
  have hSplit := pointsToCells_split q contents i
  rw [hTake] at hSplit
  rw [hSplit, List.drop_eq_getElem_cons hIndex,
    show contents[i] :: contents.drop (i + 1)
      = [contents[i]] ++ contents.drop (i + 1) from rfl,
    pointsToCells_append (q.shift i) [contents[i]] (contents.drop (i + 1)),
    ← pointsToCell_eq_cells]
  rfl

theorem pointsToCells_cons (q : RawPtr T M) (content : Option (Pointee.Cell T))
    (rest : List (Option (Pointee.Cell T))) :
    (q ↦*? (content :: rest)) = iprop(q ↦? content ∗ (q.shift 1) ↦*? rest) := by
  rw [show (content :: rest) = [content] ++ rest from rfl,
    pointsToCells_append q [content] rest, ← pointsToCell_eq_cells]
  rfl

@[simp] theorem pointsToCells_nil (q : RawPtr T M) :
    (q ↦*? ([] : List (Option (Pointee.Cell T)))) = emp :=
  entails_antisymm (fun _ _ => trivial) (fun h _ => Heap.Sub.of_empty h)

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    (q ↦* (xs ++ ys)) = iprop(q ↦* xs ∗ (q.shift xs.length) ↦* ys) := by
  rw [pointsToRange_eq, List.map_append, pointsToCells_append, List.length_map]
  rfl

theorem pointsToRange_split (q : RawPtr T M) (values : List T) (i : Nat) :
    (q ↦* values) =
      iprop(q ↦* values.take i ∗ (q.shift (values.take i).length) ↦* values.drop i) := by
  conv_lhs => rw [← List.take_append_drop i values]
  exact pointsToRange_append q (values.take i) (values.drop i)

theorem pointsToRange_eq_take_get_drop {q : RawPtr T M} {values : List T} {i : Nat}
    (hIndex : i < values.length) :
    (q ↦* values) =
      iprop(q ↦* values.take i ∗
        ((q.shift i) ↦ values[i] ∗ (q.shift (i + 1)) ↦* values.drop (i + 1))) := by
  rw [pointsToRange_eq, pointsToCells_eq_take_get_drop (by simpa using hIndex)]
  simp only [← List.map_take, ← List.map_drop, List.getElem_map]
  rfl

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.shift 1) ↦* rest) := by
  rw [pointsToRange_eq, List.map_cons, pointsToCells_cons]
  rfl

@[simp] theorem pointsToRange_nil (q : RawPtr T M) :
    (q ↦* ([] : List T)) = emp :=
  pointsToCells_nil q

end RawPtr

end PointsTo

namespace RawPtr

@[simp] theorem pointsToDead_zero (q : RawPtr T M) : (q ↦† 0) = emp := rfl

theorem pointsToDead_one (q : RawPtr T M) : (q ↦† 1) = owns (Heap.endMarker q.addr) :=
  sep_emp_r_eq _

theorem pointsToDead_succ (q : RawPtr T M) (n : Nat) :
    (q ↦† (n + 1)) = iprop(q ↦† 1 ∗ (q.shift 1) ↦† n) := by
  rw [pointsToDead_one]
  rfl

@[simp] theorem pointsToDead_retype (q : RawPtr T M) (n : Nat) :
    ((q.retype : RawPtr U M') ↦† n) = (q ↦† n) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [pointsToDead_succ, pointsToDead_succ q, shift_retype, ih]
    rfl

@[simp] theorem boxed_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').boxed = q.boxed := rfl

end RawPtr

section

variable {T : Type} [Pointee T] {M : Mutability}

theorem RawPtr.pointsToCell_exclusive (q : RawPtr T M) (content₁ content₂ : Option (Pointee.Cell T)) :
    q ↦? content₁ ∗ q ↦? content₂ ⊢ ⌜False⌝ :=
  owns_cell_exclusive q.addr content₁ content₂

theorem RawPtr.pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ :=
  RawPtr.pointsToCell_exclusive q _ _

namespace RawPtr

@[simp]
theorem not_contains_empty (q : RawPtr T M) :
    ¬ RawPtr.contains (∅ : Heap) q :=
  Heap.not_contains_empty q.addr

theorem contains_of_pointsToCell {q : RawPtr T M} {content : Option (Pointee.Cell T)} {h : Heap}
    (hPointsTo : (q ↦? content) h) : RawPtr.contains h q :=
  Heap.Sub.contains hPointsTo (Heap.contains_cell q.addr content)

theorem contains_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : RawPtr.contains h q :=
  contains_of_pointsToCell hPointsTo

theorem addr_injective {q r : RawPtr T M} (hEq : q.addr = r.addr) : q = r := by
  cases q
  cases r
  have hBase := congrArg Prod.fst hEq
  have hOffset := congrArg Prod.snd hEq
  simp only [RawPtr.addr] at hBase hOffset
  simp_all

theorem get_eq {q : RawPtr T M} {h : Heap} {value : T} (hReadable : q.Readable h)
    (hValue : Pointee.ofCell (Heap.read q.addr h hReadable.contains) = some value) :
    q.get h hReadable = value :=
  Option.some.inj ((Option.some_get _).trans hValue)

theorem readable_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) : q.Readable h :=
  have hContains := contains_of_pointsTo hPointsTo
  ⟨hContains, by rw [Heap.read_of_sub hPointsTo hContains, Pointee.ofCell_toCell]; rfl⟩

theorem get_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) (hReadable : q.Readable h) : q.get h hReadable = value :=
  get_eq hReadable (by rw [Heap.read_of_sub hPointsTo, Pointee.ofCell_toCell])

end RawPtr

theorem RawPtr.allocate.spec (last : Slot) (values : List T) :
    ⦃ emp ⦄ RawPtr.allocate (M := M) last values
      ⦃ p => p ↦* values ∗ owns (Heap.slot (p.addr.add values.length) last) ⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.allocation (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell) last)
        (h ∪ frame) :=
    Heap.compatible_freshLoc _ _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.allocation (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell) last) h
        frame).mpr ⟨hCompatible, hFresh⟩
  refine ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm, ?_⟩
  have hSep : iprop(owns (Heap.cells (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell)) ∗
      owns (Heap.slot ((Heap.freshLoc (h ∪ frame)).add (values.map Pointee.toCell).length) last))
      (Heap.allocation (Heap.freshLoc (h ∪ frame)) (values.map Pointee.toCell) last) := by
    rw [← owns_union _ _ (Heap.compatible_allocation _ _ _)]
    exact Heap.Sub.refl _
  rw [List.length_map] at hSep
  exact IProp.up_closed _ hSep (Heap.Sub.union_left hFreshH)

@[step]
theorem RawPtr.materialize.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.materialize (M := M) values
      ⦃ p => p ↦* values⦄ :=
  WP.ispec_mono (RawPtr.allocate.spec .dead values) (by iframe) (by iframe)

@[step]
theorem alloc.boxed.Box.into_raw.spec (value : T) :
    ⦃ emp ⦄ alloc.boxed.Box.into_raw value ⦃ q => q ↦ value ∗ q.boxed ⦄ := by
  unfold alloc.boxed.Box.into_raw
  have hSpec := RawPtr.allocate.spec (M := .Mut) .boxEnd [value]
  simp only [← RawPtr.pointsTo_eq_range, List.length_singleton] at hSpec
  exact hSpec

namespace RawPtr

@[step]
theorem read.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ q ↦ value⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hPointsToFrame : (q ↦ value) (h ∪ frame) :=
    (q ↦ value).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  have hReadable : q.Readable (h ∪ frame) :=
    readable_of_pointsTo hPointsToFrame
  refine ⟨hReadable, h, hCompatible, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr ⟨get_of_pointsTo hPointsToFrame hReadable, hPointsTo⟩

end RawPtr

theorem MutRawPtr.write.spec_cell (q : MutRawPtr T) (content : Option (Pointee.Cell T))
    (newValue : T) :
    ⦃ q ↦? content ⦄ q.write newValue ⦃ q ↦ newValue⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hPointsTo
  have hContainsSlot := Heap.contains_cell q.addr content
  have hContains : Heap.contains (Heap.cell q.addr content ∪ rest) (Pointee.Cell T) q.addr :=
    Heap.contains_union_left hContainsSlot
  refine ⟨Heap.contains_union_left hContains,
    Heap.update q.addr (Pointee.toCell newValue) _ hContains,
    Heap.disjoint_update_left hCompatible hContains, ?_, ?_⟩
  · simpa only [show Heap.contains_union_left hContains =
        Heap.contains_union_left (h₂ := frame) hContains from rfl] using
      Heap.update_union_left q.addr (Pointee.toCell newValue) hContains
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.cell q.addr (Pointee.toCell newValue)) rest := by
      have hUpdated := Heap.disjoint_update_left (content := Pointee.toCell newValue)
        hCompatibleRest hContainsSlot
      rwa [Heap.update_cell] at hUpdated
    rw [show hContains = Heap.contains_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.update_union_left q.addr _ hContainsSlot,
      Heap.update_cell]
    exact Heap.Sub.union_left hCompatibleNew

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃ q ↦ newValue⦄ :=
  MutRawPtr.write.spec_cell q _ newValue

namespace RawPtr

theorem take.spec_cell (q : RawPtr T M) (content : Option (Pointee.Cell T)) (value : T)
    (hValue : Pointee.ofCell content = some value) :
    ⦃ q ↦? content ⦄ q.take ⦃ result => ⌜result = value⌝ ∗ q ↦† 1⦄ := by
  rw [pointsToDead_one]
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : Heap.contains h (Pointee.Cell T) q.addr := contains_of_pointsToCell hPointsTo
  have hPointsToFrame : (q ↦? content) (h ∪ frame) :=
    (q ↦? content).up_closed hPointsTo (Heap.Sub.union_left hCompatible)
  have hRead : Heap.read q.addr (h ∪ frame) (Heap.contains_union_left hContains) = content :=
    Heap.read_of_sub hPointsToFrame _
  have hReadable : q.Readable (h ∪ frame) :=
    ⟨Heap.contains_union_left hContains, by rw [hRead, hValue]; rfl⟩
  refine ⟨hReadable, Heap.free q.addr h hContains,
    Heap.disjoint_free_left hCompatible hContains, ?_, ?_⟩
  · simpa only [show hReadable.contains =
        Heap.contains_union_left (h₂ := frame) hContains from rfl] using
      Heap.free_union_left q.addr hCompatible hContains
  · exact (sep_pure_l _ _ _).mpr
      ⟨get_eq hReadable (by rw [hRead, hValue]), Heap.Sub.free hPointsTo hContains⟩

@[step]
theorem take.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.take ⦃ result => ⌜result = value⌝ ∗ q ↦† 1⦄ :=
  take.spec_cell q _ value (Pointee.ofCell_toCell value)

@[step]
theorem revive.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦† 1 ⦄ q.revive value ⦃ q ↦ value⦄ := by
  rw [pointsToDead_one]
  apply ispec_guardedModify
  intro h hDead frame hCompatible
  have hDeadH : Heap.dead h q.addr := Heap.Sub.dead hDead
  exact ⟨Heap.dead_union_left hDeadH, Heap.revive q.addr (Pointee.toCell value) h hDeadH,
    Heap.disjoint_revive_left hCompatible hDeadH, Heap.revive_union_left _ _ hDeadH,
    Heap.Sub.revive _ hDead hDeadH⟩

@[step]
theorem takeRange.spec (q : RawPtr T M) (values : List T) :
    ⦃ q ↦* values ⦄ q.takeRange values.length
      ⦃ result => ⌜result = values⌝ ∗ q ↦† values.length⦄ := by
  induction values generalizing q with
  | nil => simp [takeRange]
  | cons value values ih =>
    rw [pointsToRange_cons, List.length_cons, pointsToDead_succ, takeRange]
    apply WP.ispec_bind (take.spec q value)
    · iframe
    · intro v
      apply WP.ispec_bind (ih (q.shift 1))
      · iframe
      · intro vs
        apply (WP.ispec_ok _).2
        iframe

@[step]
theorem reviveRange.spec (q : RawPtr T M) (values : List T) :
    ⦃ q ↦† values.length ⦄ q.reviveRange values ⦃ q ↦* values⦄ := by
  induction values generalizing q with
  | nil => simp [reviveRange]
  | cons value values ih =>
    rw [pointsToRange_cons, List.length_cons, pointsToDead_succ, reviveRange]
    apply WP.ispec_bind (revive.spec q value)
    · iframe
    · intro _
      apply WP.ispec_mono (ih (q.shift 1)) <;> iframe

/-- `reviveRange.spec` with the number of dead slots given separately. -/
theorem reviveRange.spec_len (q : RawPtr T M) (values : List T) (n : Nat)
    (h : values.length = n) :
    ⦃ q ↦† n ⦄ q.reviveRange values ⦃ q ↦* values⦄ := by
  subst h
  exact reviveRange.spec q values

end RawPtr

@[step]
theorem Result.require.spec {p : Prop} (hp : p) : ⦃ emp ⦄ Result.require p ⦃ emp⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  exact ⟨hp, h, hCompatible, rfl, trivial⟩

/-- `from_raw` frees the cell: it is left dead, so that it can not be freed or used again. -/
theorem alloc.boxed.Box.from_raw.spec_freed {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ∗ q.boxed ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝ ∗ (q ↦† 1 ∗ q.boxed)⦄ := by
  rw [RawPtr.pointsToDead_one]
  apply ispec_guardedModify
  rintro _ ⟨h, hBox, hCompatibleBox, rfl, hPointsTo, hBoxed⟩ frame hCompatible
  have hContains : Heap.contains h (Pointee.Cell T) q.addr := RawPtr.contains_of_pointsTo hPointsTo
  have hSub : Heap.Sub h (h ∪ hBox ∪ frame) :=
    (Heap.Sub.union_left hCompatibleBox).trans (Heap.Sub.union_left hCompatible)
  have hPointsToFrame : (q ↦ value) (h ∪ hBox ∪ frame) := (q ↦ value).up_closed hPointsTo hSub
  have hReadable := RawPtr.readable_of_pointsTo hPointsToFrame
  have hBoxEnd : Heap.isBoxEnd (h ∪ hBox ∪ frame) (q.addr.add 1) :=
    Heap.Sub.isBoxEnd ((show Heap.Sub (Heap.boxEnd (q.addr.add 1)) hBox from hBoxed).trans
      ((Heap.Sub.union_right hCompatibleBox).trans (Heap.Sub.union_left hCompatible)))
  have hOwned : Heap.contains (h ∪ hBox) (Pointee.Cell T) q.addr := Heap.contains_union_left hContains
  refine ⟨⟨hReadable, hBoxEnd⟩, Heap.free q.addr (h ∪ hBox) hOwned,
    Heap.disjoint_free_left hCompatible hOwned, ?_, ?_⟩
  · simpa only [show hReadable.contains =
        Heap.contains_union_left (h₂ := frame) hOwned from rfl] using
      Heap.free_union_left q.addr hCompatible hOwned
  · rw [show hOwned = Heap.contains_union_left hContains from rfl,
      Heap.free_union_left q.addr hCompatibleBox hContains]
    exact (sep_pure_l _ _ _).mpr ⟨RawPtr.get_of_pointsTo hPointsToFrame hReadable,
      ⟨_, hBox, Heap.disjoint_free_left hCompatibleBox hContains, rfl,
        Heap.Sub.free hPointsTo hContains, hBoxed⟩⟩

@[step]
theorem alloc.boxed.Box.from_raw.spec {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ∗ q.boxed ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝⦄ :=
  WP.ispec_mono (alloc.boxed.Box.from_raw.spec_freed q) (by iframe) (by iframe)

@[step]
theorem core.ptr.from_mut.spec (value : T) :
    ⦃ emp ⦄ core.ptr.from_mut value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_mut q⌝ ∗ q ↦ value⦄ := by
  unfold core.ptr.from_mut
  apply WP.ispec_bind (RawPtr.materialize.spec (M := .Mut) [value])
  · iframe
  · intro q
    apply (ispec_ok _).2
    rw [← RawPtr.pointsTo_eq_range]
    iframe

@[step]
theorem core.ptr.end_from_mut.spec (q : MutRawPtr T) (value : T) :
    ⦃ q ↦ value ⦄ core.ptr.end_from_mut q ⦃ result => ⌜result = value⌝⦄ :=
  WP.ispec_mono (RawPtr.take.spec q value) (by iframe) (by iframe)

@[step]
theorem RawPtr.as_mut_unchecked.spec (q : MutRawPtr T) (value : T) :
    ⦃ q ↦ value ⦄ q.as_mut_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.revive⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_mut_unchecked
  apply WP.ispec_bind (RawPtr.take.spec q value)
  · iframe
  · intro v
    apply (ispec_ok _).2
    iframe

@[step]
theorem RawPtr.as_ref_unchecked.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.as_ref_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.revive value⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_ref_unchecked
  apply WP.ispec_bind (RawPtr.take.spec q value)
  · iframe
  · intro v
    apply (ispec_ok _).2
    iframe

theorem RawPtr.eq.spec_self [NonZeroSized T] (q : RawPtr T M) :
    ⦃ emp ⦄ q.eq q ⦃ b => ⌜b = true⌝⦄ := by
  rw [RawPtr.eq, if_pos rfl]
  apply (ispec_ok _).2
  iframe

/-- Two different pointers into the same allocation are different. -/
theorem RawPtr.eq.spec_same_alloc [NonZeroSized T] (hNZ : NonZeroSized.nonZero T)
    {p q : RawPtr T M} (hNe : p ≠ q) (hBase : p.base = q.base) : ⦃ emp ⦄ p.eq q ⦃ b => ⌜b = false⌝⦄ := by
  rw [RawPtr.eq, if_neg fun h => hNe (RawPtr.addr_injective h)]
  apply ispec_guardedModify
  intro h hEmp frame hCompatible
  exact ⟨⟨hNZ, .inl hBase⟩, h, hCompatible, rfl, (pure_holds h).mpr rfl⟩

/-- Two pointers to different live box allocations are different. -/
theorem RawPtr.eq.spec_boxes [NonZeroSized T] (hNZ : NonZeroSized.nonZero T)
    {p q : RawPtr T M} (hNe : p ≠ q)
    (v w : T) :
    ⦃ p ↦ v ∗ p.boxed ∗ q ↦ w ∗ q.boxed ⦄ p.eq q
      ⦃ b => ⌜b = false⌝ ∗ (p ↦ v ∗ p.boxed ∗ q ↦ w ∗ q.boxed)⦄ := by
  rw [RawPtr.eq, if_neg fun h => hNe (RawPtr.addr_injective h)]
  apply ispec_guardedModify
  intro h hPre frame hCompatible
  have hSub : Heap.Sub h (h ∪ frame) := Heap.Sub.union_left hCompatible
  obtain ⟨h₁, h₂, hCompatible₁₂, rfl, hP, h₂₃⟩ := hPre
  obtain ⟨h₂, h₃, hCompatible₂₃, rfl, hPBoxed, h₃₄⟩ := h₂₃
  obtain ⟨h₃, h₄, hCompatible₃₄, rfl, hQ, hQBoxed⟩ := h₃₄
  have hSub₁ : Heap.Sub h₁ (h₁ ∪ (h₂ ∪ (h₃ ∪ h₄))) := Heap.Sub.union_left hCompatible₁₂
  have hSub₂ : Heap.Sub h₂ (h₁ ∪ (h₂ ∪ (h₃ ∪ h₄))) :=
    (Heap.Sub.union_left hCompatible₂₃).trans (Heap.Sub.union_right hCompatible₁₂)
  have hSub₃ : Heap.Sub h₃ (h₁ ∪ (h₂ ∪ (h₃ ∪ h₄))) :=
    ((Heap.Sub.union_left hCompatible₃₄).trans (Heap.Sub.union_right hCompatible₂₃)).trans
      (Heap.Sub.union_right hCompatible₁₂)
  have hSub₄ : Heap.Sub h₄ (h₁ ∪ (h₂ ∪ (h₃ ∪ h₄))) :=
    ((Heap.Sub.union_right hCompatible₃₄).trans (Heap.Sub.union_right hCompatible₂₃)).trans
      (Heap.Sub.union_right hCompatible₁₂)
  refine ⟨⟨hNZ, .inr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩, _, hCompatible, rfl, ?_⟩
  · exact RawPtr.contains_of_pointsTo ((p ↦ v).up_closed hP (hSub₁.trans hSub))
  · exact Heap.Sub.isBoxEnd ((show Heap.Sub (Heap.boxEnd (p.addr.add 1)) h₂ from hPBoxed).trans
      (hSub₂.trans hSub))
  · exact RawPtr.contains_of_pointsTo ((q ↦ w).up_closed hQ (hSub₃.trans hSub))
  · exact Heap.Sub.isBoxEnd ((show Heap.Sub (Heap.boxEnd (q.addr.add 1)) h₄ from hQBoxed).trans
      (hSub₄.trans hSub))
  · exact (sep_pure_l _ _ _).mpr
      ⟨rfl, ⟨h₁, _, hCompatible₁₂, rfl, hP, ⟨h₂, _, hCompatible₂₃, rfl, hPBoxed,
        ⟨h₃, h₄, hCompatible₃₄, rfl, hQ, hQBoxed⟩⟩⟩⟩

/-- Comparing a pointer to a borrow view (whose allocation ends with a dead slot, see
`core.ptr.from_mut.spec_view`) with a pointer into another allocation fails. -/
theorem RawPtr.eq.fails_view [NonZeroSized T] {p q : RawPtr T M} (hBase : p.base ≠ q.base) :
    ifails ((p.shift 1) ↦† 1) (p.eq q) := by
  rw [RawPtr.eq, if_neg fun h => hBase (congrArg Prod.fst h)]
  rw [RawPtr.pointsToDead_one]
  apply ifails_guardedModify
  intro h hDead h' hSub hPre
  rcases hPre.2 with hEq | ⟨⟨_, hBox⟩, _⟩
  · exact hBase hEq
  · exact Heap.Sub.not_isBoxEnd (hDead.trans hSub) hBox

/-- Comparing two pointers to different slots of a type which may be zero-sized fails. -/
theorem RawPtr.eq.fails_zero_sized [NonZeroSized T] (hZ : NonZeroSized.nonZero T = false)
    {p q : RawPtr T M} (v w : T) : ifails (p ↦ v ∗ q ↦ w) (p.eq q) := by
  by_cases hA : p.addr = q.addr
  · refine ifails_mono (P' := ⌜False⌝ ∗ emp) ?_ (ifails_ipure False.elim)
    rw [sep_emp_r_eq]
    rw [RawPtr.addr_injective hA]
    exact owns_cell_exclusive q.addr _ _
  · rw [RawPtr.eq, if_neg hA]
    apply ifails_guardedModify
    intro _ _ _ _ hPre
    exact absurd hPre.1 (by simp [hZ])

namespace RawPtr

theorem take_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set,
    if_neg (show ¬ i = n by omega)]

theorem drop_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set,
    if_neg (show ¬ i = i + 1 + n by omega)]

theorem read.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ (q.shift i).read
      ⦃ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read.spec (q.shift i) values[i]) <;> iframe

theorem read.spec_frame (q : RawPtr T M) (value : T) (H : IProp) :
    ⦃ q ↦ value ∗ H ⦄ q.read
      ⦃ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ := by
  apply WP.ispec_mono (read.spec q value) <;> iframe

/-- `add` stays in bounds of the range of cells `q` owns. -/
theorem add.spec_cells (q : RawPtr T M) (contents : List (Option (Pointee.Cell T)))
    (count : Usize) (hCount : count.val ≤ contents.length) :
    ⦃ q ↦*? contents ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦*? contents⦄ := by
  apply ispec_guardedModify
  intro h hRange frame hCompatible
  refine ⟨fun i hi => ⟨Pointee.Cell T, ?_⟩, h, hCompatible, rfl,
    (sep_pure_l _ _ h).mpr ⟨rfl, hRange⟩⟩
  exact Heap.Sub.contains ((show Heap.Sub (Heap.cells q.addr contents) h from hRange).trans
    (Heap.Sub.union_left hCompatible)) (Heap.contains_cells (by omega))

@[step]
theorem add.spec (q : RawPtr T M) (values : List T) (count : Usize)
    (hCount : count.val ≤ values.length) :
    ⦃ q ↦* values ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦* values⦄ :=
  add.spec_cells q _ count (by simpa using hCount)

end RawPtr

theorem MutRawPtr.write.spec_range (q : MutRawPtr T) (values : List T)
    (i : Nat) (value : T) (hIndex : i < values.length) :
    ⦃ q ↦* values ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦* values.set i value⦄ := by
  rw [RawPtr.pointsToRange_eq_take_get_drop hIndex,
    RawPtr.pointsToRange_eq_take_get_drop
      (show i < (values.set i value).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set, List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec (q.shift i) values[i] value) <;> iframe

/-- `write.spec_range` on a range of cells, some of which may be uninitialized. -/
theorem MutRawPtr.write.spec_cells (q : MutRawPtr T) (contents : List (Option (Pointee.Cell T)))
    (i : Nat) (value : T) (hIndex : i < contents.length) :
    ⦃ q ↦*? contents ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦*? contents.set i (Pointee.toCell value)⦄ := by
  rw [RawPtr.pointsToCells_eq_take_get_drop hIndex,
    RawPtr.pointsToCells_eq_take_get_drop
      (show i < (contents.set i (Pointee.toCell value)).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set, List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec_cell (q.shift i) contents[i] value) <;> iframe

theorem MutRawPtr.write.spec_head (q : MutRawPtr T) (values : List T) (value : T)
    (h : 0 < values.length) :
    ⦃ q ↦* values ⦄ q.write value ⦃ q ↦* values.set 0 value⦄ := by
  simpa using MutRawPtr.write.spec_range q values 0 value h

/-! ### Undefined behaviors rejected by the model -/

namespace RawPtr

/-- Reading a cell which holds no value of the pointee (it is uninitialized) fails. -/
theorem read.fails_cell (q : RawPtr T M) (content : Option (Pointee.Cell T))
    (hNone : Pointee.ofCell content = none) :
    ifails (q ↦? content) q.read := by
  apply ifails_guardedModify
  intro h hPointsTo h' hSub hReadable
  have hValid := hReadable.valid
  rw [Heap.read_of_sub ((show Heap.Sub (Heap.cell q.addr content) h from hPointsTo).trans hSub),
    hNone] at hValid
  exact Bool.false_ne_true hValid

/-- Reading uninitialized memory fails. -/
theorem read.fails_uninit (q : RawPtr T M) (hNone : Pointee.ofCell (none : Option (Pointee.Cell T)) = none) :
    ifails (q ↦? none) q.read :=
  read.fails_cell q none hNone

/-- Reading a dead slot (freed, or moved out by a borrow) fails. -/
theorem read.fails_dead (q : RawPtr T M) : ifails (q ↦† 1) q.read := by
  rw [pointsToDead_one]
  apply ifails_guardedModify
  intro h hDead h' hSub hReadable
  exact Heap.not_contains_of_dead (Heap.Sub.dead (hDead.trans hSub)) hReadable.contains

/-- Moving a value out of a cell which holds no value of the pointee fails. -/
theorem take.fails_cell (q : RawPtr T M) (content : Option (Pointee.Cell T))
    (hNone : Pointee.ofCell content = none) :
    ifails (q ↦? content) q.take := by
  apply ifails_guardedModify
  intro h hPointsTo h' hSub hReadable
  have hValid := hReadable.valid
  rw [Heap.read_of_sub ((show Heap.Sub (Heap.cell q.addr content) h from hPointsTo).trans hSub),
    hNone] at hValid
  exact Bool.false_ne_true hValid

/-- Moving a value out of a dead slot (freed, or moved out by a borrow) fails. -/
theorem take.fails_dead (q : RawPtr T M) : ifails (q ↦† 1) q.take := by
  rw [pointsToDead_one]
  apply ifails_guardedModify
  intro h hDead h' hSub hReadable
  exact Heap.not_contains_of_dead (Heap.Sub.dead (hDead.trans hSub)) hReadable.contains

/-- Borrowing a value which is already borrowed mutably (its slot is dead) fails. -/
theorem as_mut_unchecked.fails_dead (q : MutRawPtr T) : ifails (q ↦† 1) q.as_mut_unchecked :=
  ifails_bind_left (take.fails_dead q)

/-- Borrowing a value which is already borrowed (its slot is dead) fails. -/
theorem as_ref_unchecked.fails_dead (q : RawPtr T M) : ifails (q ↦† 1) q.as_ref_unchecked :=
  ifails_bind_left (take.fails_dead q)

end RawPtr

/-- Double free, or use of a pointer freed by `Box::from_raw`: freeing a dead slot fails. -/
theorem alloc.boxed.Box.from_raw.fails_dead (q : MutRawPtr T) :
    ifails (q ↦† 1) (alloc.boxed.Box.from_raw q) := by
  rw [RawPtr.pointsToDead_one]
  apply ifails_guardedModify
  intro h hDead h' hSub hPre
  exact Heap.not_contains_of_dead (Heap.Sub.dead (hDead.trans hSub)) hPre.1.contains

/-- Freeing a pointer which does not come from a box fails: the next slot is the dead end marker
of a borrow view (`as_mut_ptr`, `from_mut`, ...), not the end marker of a box. -/
theorem alloc.boxed.Box.from_raw.fails_view (q : MutRawPtr T) :
    ifails ((q.shift 1) ↦† 1) (alloc.boxed.Box.from_raw q) := by
  rw [RawPtr.pointsToDead_one]
  apply ifails_guardedModify
  intro h hDead h' hSub hPre
  exact Heap.Sub.not_isBoxEnd (hDead.trans hSub) hPre.2

/-- Freeing a pointer past the cell of a box (an interior pointer) fails: it points to the end
marker of the box. -/
theorem alloc.boxed.Box.from_raw.fails_past_box (q : MutRawPtr T) :
    ifails q.boxed (alloc.boxed.Box.from_raw (q.shift 1)) := by
  apply ifails_guardedModify
  intro h hBoxed h' hSub hPre
  exact Heap.Sub.not_contains (s := .boxEnd) (hBoxed.trans hSub) (by simp) hPre.1.contains

theorem core.ptr.from_mut.spec_view (value : T) :
    ⦃ emp ⦄ core.ptr.from_mut value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_mut q⌝ ∗ q ↦ value ∗ (q.shift 1) ↦† 1⦄ := by
  unfold core.ptr.from_mut RawPtr.materialize
  apply WP.ispec_bind (RawPtr.allocate.spec (M := .Mut) .dead [value])
  · iframe
  · intro q
    apply (ispec_ok _).2
    rw [← RawPtr.pointsTo_eq_range, show owns (Heap.slot (q.addr.add [value].length) .dead) =
      ((q.shift 1) ↦† 1) from (RawPtr.pointsToDead_one (q.shift 1)).symm]
    iframe

end

end Aeneas.Std
