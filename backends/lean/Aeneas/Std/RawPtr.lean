module
public import Aeneas.Std.Delab
public import Aeneas.Std.Heap
public import Aeneas.SepLogic.IProp
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.SliceDef
public import Aeneas.Std.Array.Array
public import Aeneas.Data.BitVec
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
next to the result. The exceptions are the heap primitives behind them (`HeapOp`,
`RawPtr.allocate`, `RawPtr.materialize`, `RawPtr.take`, `RawPtr.revive`, their range versions,
`RawPtr.null`, `RawPtr.LiveBox`, `Result.require`, `Pointee.decode`), and `RawPtr.eq` and
`RawPtr.ne`, which model `==` and `!=` on raw pointers.

The heap is a map from locations (an allocation and an offset) to cells. A pointer `*mut T` reads
and writes the `Pointee.size T` cells of type `Pointee.Cell T` from its location on, and decodes
them with `Pointee.ofCells` (see `Pointee`). There are two kinds of cells:
- byte cells (`U8`), for the types which have a fixed, total byte representation (integers,
  `bool`, arrays of them, `MaybeUninit` of them): the cells of a value are its bytes, so that
  reading memory at another such type (after a pointer cast, `read_unaligned`, a transmute...)
  decodes the same bytes differently, as in Rust (little-endian, 64-bit layouts);
- typed cells (`TypedCell T`), one per value, for the other types (in particular pointers, whose
  bytes we do not model): accessing them at another type `U` fails if `TypedCell T ≠ TypedCell U`
  (when the two types have the same cardinality, this inequality can not be proved, and neither
  can the success of the access).

Every access checks the type of the cells (so that casting a pointer is safe: `<*mut T>::cast` and
`as` casts only change the type of the pointer), that the pointer is not null, and, if it requires
it, the alignment of the pointer (`RawPtr.Aligned`). Pointer arithmetic is only allowed over the
cells of the pointee (`RawPtr.InBounds`). The extraction only accepts the casts and transmutes
between types which do not mention `Box`, references, or `repr(packed)`/`repr(align)` types
(several Rust types share the same Lean type: `Box<T>` and `&T` are `T`, and a tuple structure with
one field is its field). -/

inductive Mutability where
| Mut | Const

/-- A Rust raw pointer: an allocation identifier and an offset (in cells) into it. `T` is a
    phantom parameter, universe-polymorphic like the other type parameters (only the heap cells a
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

/-- The cell holding a value of a type without byte representation. -/
structure TypedCell (T : Type) where
  val : T

/-- How the values of `T` are stored in the heap: a value is `size` cells of type `Cell`, each of
which may be uninitialized (`none`). `ofCells` decodes the cells found in the heap, if they hold a
value of `T`: for instance, reading uninitialized memory fails unless `T` can represent it
(`MaybeUninit`).

An instance is an assumption about the memory representation of the Rust type modelled by `T`:
the byte instances (`Cell = U8`) must give the bytes of the values and the Rust `size` and
`align`ment (a power of two), and the Rust type must not be zero-sized if `nonZero` is `true`.
Typed instances (`Pointee.typed`, `Cell = TypedCell T`, one cell per value, alignment `1`) are
always safe: their cells can only be accessed at the type `T` (or at arrays and `MaybeUninit` of
`T`, whose cells are those of `T`). The laws needed by the proofs are in `Pointee.Lawful`.

Generic code takes the instances of its type parameters as arguments (`[Pointee T]` binders,
added by the extraction to the stateful functions). The definitions which are elaborated without
the instance of a type parameter (e.g., the implementations of a trait for a generic type) use
`Pointee.default`, whose cells are typed: they can not access the cells of byte types. -/
class Pointee (T : Type) where
  Cell : Type
  size : Nat
  align : Nat
  nonZero : Bool
  toCells : T → List (Option Cell)
  ofCells : List (Option Cell) → Option T

/-- One typed cell per value: the cells can not be read at another type. `nonZero` tells whether
the Rust type is known not to be zero-sized (see `RawPtr.eq`). -/
def Pointee.typed (T : Type) (nonZero : Bool) : Pointee T where
  Cell := TypedCell T
  size := 1
  align := 1
  nonZero := nonZero
  toCells value := [some ⟨value⟩]
  ofCells
    | [some cell] => some cell.val
    | _ => none

/-- By default, a value is stored in a typed cell, and the type may be zero-sized. -/
instance (priority := low) Pointee.default {T : Type} : Pointee T := Pointee.typed T false

/-- The byte cells of a type: `encode` gives the bytes of a value, and `decode` the value whose
bytes are given (if any). -/
def Pointee.bytes (T : Type) (size align : Nat) (encode : T → List U8)
    (decode : List U8 → Option T) : Pointee T where
  Cell := U8
  size := size
  align := align
  nonZero := size != 0
  toCells value := (encode value).map some
  ofCells cells := cells.mapM id >>= decode

/-- Little-endian bytes of `numBits` bits. -/
def Pointee.decodeLE (numBits : Nat) (bytes : List U8) : Option (BitVec numBits) :=
  if h : 8 * bytes.length = numBits then
    some ((BitVec.fromLEBytes (bytes.map U8.bv)).cast (by simpa using h))
  else none

instance UScalar.instPointee (ty : UScalarTy) : Pointee (UScalar ty) :=
  Pointee.bytes (UScalar ty) (ty.numBits / 8) (ty.numBits / 8)
    (fun x => x.bv.toLEBytes.map UScalar.mk)
    (fun bytes => (Pointee.decodeLE ty.numBits bytes).map UScalar.mk)

instance IScalar.instPointee (ty : IScalarTy) : Pointee (IScalar ty) :=
  Pointee.bytes (IScalar ty) (ty.numBits / 8) (ty.numBits / 8)
    (fun x => x.bv.toLEBytes.map UScalar.mk)
    (fun bytes => (Pointee.decodeLE ty.numBits bytes).map IScalar.mk)

/-- A `bool` is a byte, `0` or `1`: reading another byte as a `bool` fails. -/
instance Bool.instPointee : Pointee Bool :=
  Pointee.bytes Bool 1 1 (fun b => [if b then 1#u8 else 0#u8])
    (fun
      | [byte] => if byte.val = 0 then some false else if byte.val = 1 then some true else none
      | _ => none)

/-- The values decoded from consecutive runs of `size T` cells. -/
def Pointee.ofCellsList (T : Type) [Pointee T] :
    Nat → List (Option (Pointee.Cell T)) → Option (List T)
  | 0, _ => some []
  | n + 1, cells => do
    let value ← Pointee.ofCells (cells.take (Pointee.size T))
    let values ← Pointee.ofCellsList T n (cells.drop (Pointee.size T))
    some (value :: values)

/-- The cells of an array are the cells of its elements. -/
instance Array.instPointee {T : Type} [Pointee T] {n : Usize} : Pointee (Array T n) where
  Cell := Pointee.Cell T
  size := n.val * Pointee.size T
  align := Pointee.align T
  nonZero := n.val != 0 && Pointee.nonZero T
  toCells a := a.val.flatMap Pointee.toCells
  ofCells cells := do
    let values ← Pointee.ofCellsList T n.val cells
    if h : values.length = n.val then some (Array.from values h) else none

instance Option.instPointee {T : Type} [Pointee T] : Pointee (Option T) :=
  Pointee.typed (Option T) (Pointee.nonZero T)

instance RawPtr.instPointee {T : Type _} {M : Mutability} : Pointee (RawPtr T M) :=
  Pointee.typed (RawPtr T M) true

instance Char.instPointee : Pointee Char := Pointee.typed Char true

/-- The cells of a value, or `size` uninitialized cells. -/
def Pointee.optCells {T : Type} [Pointee T] : Option T → List (Option (Pointee.Cell T))
  | some value => Pointee.toCells value
  | none => List.replicate (Pointee.size T) none

/-- Not a Rust function: decodes cells, failing if they do not hold a value. -/
def Pointee.decode {T : Type} [Pointee T] (cells : List (Option (Pointee.Cell T))) : Result T :=
  match Pointee.ofCells cells with
  | some value => .ok value
  | none => .fail .undef

/-- Not a Rust function: fails unless `p` holds (`p` need not be decidable). -/
def Result.require (p : Prop) : Result Unit :=
  Result.guardedModify (fun _ => p) fun h _ => ((), h)

namespace HeapOp

/-- The content of the live cell of type `α` at `l`. -/
def read (α : Type) (l : Loc) : Result (Option α) :=
  Result.guardedModify (fun h => Heap.contains h α l) fun h hContains =>
    (Heap.read l h hContains, h)

def reads (α : Type) (l : Loc) : Nat → Result (List (Option α))
  | 0 => .ok []
  | n + 1 => do
    let content ← read α l
    let contents ← reads α (l.add 1) n
    .ok (content :: contents)

/-- Overwrites the live cell of type `α` at `l`. -/
def write {α : Type} (l : Loc) (content : Option α) : Result Unit :=
  Result.guardedModify (fun h => Heap.contains h α l) fun h hContains =>
    ((), Heap.update l content h hContains)

def writes {α : Type} (l : Loc) : List (Option α) → Result Unit
  | [] => .ok ()
  | content :: contents => do
    write l content
    writes (l.add 1) contents

/-- Moves the content of the live cell of type `α` at `l` out, and kills the cell. -/
def kill (α : Type) (l : Loc) : Result (Option α) :=
  Result.guardedModify (fun h => Heap.contains h α l) fun h hContains =>
    (Heap.read l h hContains, Heap.free l h hContains)

def kills (α : Type) (l : Loc) : Nat → Result (List (Option α))
  | 0 => .ok []
  | n + 1 => do
    let content ← kill α l
    let contents ← kills α (l.add 1) n
    .ok (content :: contents)

/-- Brings the dead cell at `l` back to life, holding `content`. -/
def revive {α : Type} (l : Loc) (content : Option α) : Result Unit :=
  Result.guardedModify (fun h => Heap.dead h l) fun h hDead =>
    ((), Heap.revive l content h hDead)

def revives {α : Type} (l : Loc) : List (Option α) → Result Unit
  | [] => .ok ()
  | content :: contents => do
    revive l content
    revives (l.add 1) contents

/-- The `n` cells from `l` on are live cells of type `α`. -/
def Live (α : Type) (h : Heap) (l : Loc) (n : Nat) : Prop :=
  ∀ i < n, Heap.contains h α (l.add i)

end HeapOp

namespace RawPtr

def addr (q : RawPtr T M) : Loc := (q.base, q.offset)

def retype (q : RawPtr T M) : RawPtr U M' :=
  ⟨q.base, q.offset⟩

/-- `q` moved `i` cells forward. -/
def shiftCells (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.base, q.offset + i⟩

/-- `q` moved `i` values forward, for specifications. Programs use `add`. -/
def shift {T : Type} [Pointee T] (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  q.shiftCells (i * Pointee.size T)

/-- `q` is not null, for an access to `n` cells. Rust requires it for every access, even one which
touches no byte (zero-sized values, zero values). An access to cells checks that they are live,
and the allocation `0` is never allocated (`Heap.freshBase`): we only need to check it when no cell
is accessed. This is conservative: `NonNull::dangling()` (allocation `0`) can not be used to
access zero-sized values. -/
def NotNull (q : RawPtr T M) (n : Nat) : Prop := n = 0 → q.base ≠ 0

/-- `q` is aligned for `T` (and not null, see `NotNull`). The identifier of an allocation is an
odd multiple of the alignment Rust guarantees for it (`Heap.freshBase`), and its cells are bytes or
typed cells (whose alignment is `1`, see `Pointee`): the address of `q` is a multiple of `align T`
if both the identifier and the offset are. This is conservative: an allocation may be more aligned
than its type requires. -/
def Aligned {T : Type} [Pointee T] (q : RawPtr T M) : Prop :=
  Pointee.align T ∣ q.base ∧ Pointee.align T ∣ q.offset ∧ q.NotNull (Pointee.size T)

/-- The cells of the `n` values from `q` on are live cells of the type of the cells of `T` (`add`
stays in bounds). Pointer arithmetic counts cells, which are bytes for the byte types, and values
for the typed ones: it is only allowed over the cells of the pointee, so that `size T` cells are
`size_of::<T>()` bytes or one value. -/
def InBounds {T : Type} [Pointee T] (q : RawPtr T M) (n : Nat) (h : Heap) : Prop :=
  HeapOp.Live (Pointee.Cell T) h q.addr (n * Pointee.size T)

end RawPtr

/-- Not a Rust function: stores `values` in fresh cells, followed by the end marker `last`. The
allocation is aligned for `T`. -/
def RawPtr.allocate {T : Type} [Pointee T] (last : Slot) (values : List T) :
    Result (RawPtr T M) :=
  Result.guardedModify (fun _ => True) fun h _ =>
    (⟨(Heap.freshLoc h (Pointee.align T)).1, 0⟩,
      Heap.freshHeap h (Pointee.align T) (values.flatMap Pointee.toCells) last)

/-- Not a Rust function: stores `values` in fresh cells, which can not be freed. -/
def RawPtr.materialize {T : Type} [Pointee T] (values : List T) : Result (RawPtr T M) :=
  RawPtr.allocate .dead values

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::add"]
def RawPtr.add {T : Type} [Pointee T] (q : RawPtr T M) (count : Usize) : Result (RawPtr T M) :=
  Result.guardedModify (fun h => q.InBounds count.val h) fun h _ => (q.shift count.val, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::add"] RawPtr.add

/-- `offset` by a signed number of values: the cells between the pointer and the result must be
live cells of the pointee (in particular, the result stays in the allocation). -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::offset"]
def RawPtr.offsetBy {T : Type} [Pointee T] (q : RawPtr T M) (count : Isize) :
    Result (RawPtr T M) :=
  let target : Int := q.offset + count.val * Pointee.size T
  Result.guardedModify
    (fun h => 0 ≤ target ∧ HeapOp.Live (Pointee.Cell T) h (q.base, min q.offset target.toNat)
      (target - q.offset).natAbs)
    fun h _ => (⟨q.base, target.toNat⟩, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::offset"] RawPtr.offsetBy

/-- The distance between two pointers, in values: they must point into the same allocation, the
cells between them must be live cells of the pointee, the distance must be a multiple of the size
of `T`, which must not be zero-sized. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::offset_from"]
def RawPtr.offset_from {T : Type} [Pointee T] (p : RawPtr T M) (origin : RawPtr T M') :
    Result Isize :=
  let distance : Int := ((p.offset : Int) - origin.offset) / Pointee.size T
  Result.guardedModify
    (fun h => p.base = origin.base ∧ Pointee.nonZero T ∧ Pointee.size T ≠ 0 ∧
      (Pointee.size T : Int) ∣ ((p.offset : Int) - origin.offset) ∧
      HeapOp.Live (Pointee.Cell T) h (p.base, min p.offset origin.offset)
        ((p.offset : Int) - origin.offset).natAbs ∧
      -2 ^ (IScalarTy.Isize.numBits - 1) ≤ distance ∧ distance < 2 ^ (IScalarTy.Isize.numBits - 1))
    fun h hPre => (IScalar.ofIntCore distance ⟨hPre.2.2.2.2.2.1, hPre.2.2.2.2.2.2⟩, h)

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::offset_from"] RawPtr.offset_from

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast_const" -canFail -lift]
def RawPtr.cast_const (q : MutRawPtr T) : ConstRawPtr T :=
  q.retype

/-- Changes the pointee type: the accesses through the new pointer check that the cells have the
type of the cells of the new pointee, and decode them (see `Pointee`). -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::cast" -canFail -lift]
def RawPtr.cast {T : Type _} {M : Mutability} (U : Type _) (q : RawPtr T M) : RawPtr U M :=
  q.retype

attribute [rust_fun "core::ptr::const_ptr::{*const @T}::cast" -canFail -lift] RawPtr.cast

namespace RawPtr

/-- Reads the value `q` points to, which need not be aligned. -/
@[rust_fun "core::ptr::const_ptr::{*const @T}::read_unaligned"]
def read_unaligned {T : Type} [Pointee T] (q : RawPtr T M) : Result T := do
  Result.require (q.NotNull (Pointee.size T))
  let cells ← HeapOp.reads (Pointee.Cell T) q.addr (Pointee.size T)
  Pointee.decode cells

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read_unaligned"] read_unaligned
attribute [rust_fun "core::ptr::read_unaligned"] read_unaligned

@[rust_fun "core::ptr::const_ptr::{*const @T}::read"]
def read {T : Type} [Pointee T] (q : RawPtr T M) : Result T := do
  Result.require q.Aligned
  q.read_unaligned

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read"] read
attribute [rust_fun "core::ptr::read"] read
attribute [rust_fun "core::ptr::const_ptr::{*const @T}::read_volatile"] read
attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::read_volatile"] read
attribute [rust_fun "core::ptr::read_volatile"] read

end RawPtr

/-- Writes a value, which need not be aligned. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write_unaligned"]
def MutRawPtr.write_unaligned {T : Type} [Pointee T] (q : MutRawPtr T) (value : T) :
    Result Unit := do
  Result.require (q.NotNull (Pointee.size T))
  HeapOp.writes q.addr (Pointee.toCells value)

attribute [rust_fun "core::ptr::write_unaligned"] MutRawPtr.write_unaligned

@[rust_fun "core::ptr::mut_ptr::{*mut @T}::write"]
def MutRawPtr.write {T : Type} [Pointee T] (q : MutRawPtr T) (value : T) : Result Unit := do
  Result.require q.Aligned
  q.write_unaligned value

attribute [rust_fun "core::ptr::write"] MutRawPtr.write
attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::write_volatile"] MutRawPtr.write
attribute [rust_fun "core::ptr::write_volatile"] MutRawPtr.write

/-- Copies the cells of `count` values, initialized or not (`memmove`). -/
@[rust_fun "core::ptr::copy"]
def core.ptr.copy {T : Type} [Pointee T] (src : ConstRawPtr T) (dst : MutRawPtr T)
    (count : Usize) : Result Unit := do
  Result.require (src.Aligned ∧ dst.Aligned ∧ src.NotNull (count.val * Pointee.size T) ∧
    dst.NotNull (count.val * Pointee.size T))
  let cells ← HeapOp.reads (Pointee.Cell T) src.addr (count.val * Pointee.size T)
  HeapOp.writes dst.addr cells

/-- `copy`, on ranges which must not overlap. -/
@[rust_fun "core::ptr::copy_nonoverlapping"]
def core.ptr.copy_nonoverlapping {T : Type} [Pointee T] (src : ConstRawPtr T)
    (dst : MutRawPtr T) (count : Usize) : Result Unit := do
  let n := count.val * Pointee.size T
  Result.require (src.base ≠ dst.base ∨ src.offset + n ≤ dst.offset ∨ dst.offset + n ≤ src.offset)
  core.ptr.copy src dst count

/-- Sets the bytes of `count` values to `value`: the cells must be bytes. -/
@[rust_fun "core::ptr::write_bytes"]
def core.ptr.write_bytes {T : Type} [Pointee T] (dst : MutRawPtr T) (value : U8)
    (count : Usize) : Result Unit := do
  Result.require (Pointee.Cell T = U8 ∧ dst.Aligned ∧ dst.NotNull (count.val * Pointee.size T))
  HeapOp.writes dst.addr (List.replicate (count.val * Pointee.size T) (some value))

attribute [rust_fun "core::ptr::mut_ptr::{*mut @T}::write_bytes"] core.ptr.write_bytes

/-- Reinterprets the cells of a value at another type: the cells must have the same type and
number, and hold a value of the target type. -/
@[rust_fun "core::intrinsics::transmute"]
def core.mem.transmute {A : Type} (B : Type) [Pointee A] [Pointee B] (x : A) : Result B :=
  Aeneas.Std.bind
    (Result.guardedModify (fun _ => Pointee.Cell A = Pointee.Cell B ∧ Pointee.size A = Pointee.size B)
      fun h hEq => (cast (congrArg (fun α => List (Option α)) hEq.1) (Pointee.toCells x), h))
    Pointee.decode

/-- Runs the destructor of the value (a no-op in the model: drops are not modelled): the value
must be valid, and its cells are left uninitialized. -/
@[rust_fun "core::ptr::drop_in_place"]
def core.ptr.drop_in_place {T : Type} [Pointee T] (p : MutRawPtr T) : Result Unit :=
  Aeneas.Std.bind p.read fun _ => HeapOp.writes p.addr (Pointee.optCells (none : Option T))

@[rust_fun "alloc::boxed::{Box<@T>}::into_raw"]
def alloc.boxed.Box.into_raw {T : Type} [Pointee T] (b : T) : Result (MutRawPtr T) :=
  RawPtr.allocate .boxEnd [b]

/-- Not a Rust function: moves the value out and kills its cells. -/
def RawPtr.take {T : Type} [Pointee T] (q : RawPtr T M) : Result T := do
  let cells ← HeapOp.kills (Pointee.Cell T) q.addr (Pointee.size T)
  Pointee.decode cells

/-- Not a Rust function: brings the dead cells of `q` back to life, holding `value`. -/
def RawPtr.revive {T : Type} [Pointee T] (q : RawPtr T M) (value : T) : Result Unit :=
  HeapOp.revives q.addr (Pointee.toCells value)

/-- Not a Rust function: `take` on the `n` values from `q` on. -/
def RawPtr.takeRange {T : Type} [Pointee T] (q : RawPtr T M) : Nat → Result (List T)
  | 0 => .ok []
  | n + 1 => do
    let value ← q.take
    let values ← (q.shift 1).takeRange n
    .ok (value :: values)

/-- Not a Rust function: `revive` on the `values.length` values from `q` on. -/
def RawPtr.reviveRange {T : Type} [Pointee T] (q : RawPtr T M) : List T → Result Unit
  | [] => .ok ()
  | value :: values => do
    q.revive value
    (q.shift 1).reviveRange values

/-- Moves the value out and frees its cells. `p` must point to the cells of a box allocation
(see `Box::into_raw`): they are followed by the end marker of a box, which only box allocations
have. This rejects double frees, frees of pointers which do not come from a box, and frees of
interior pointers. -/
@[rust_fun "alloc::boxed::{Box<@T>}::from_raw"]
def alloc.boxed.Box.from_raw {T : Type} [Pointee T] (p : MutRawPtr T) : Result T := do
  Result.guardedModify (fun h => Heap.isBoxEnd h (p.addr.add (Pointee.size T))) fun h _ => ((), h)
  p.take

/-- Not a Rust function: end of the borrow given to `from_mut`; moves the value, with the writes
made through the pointer, out of the cells and kills them. -/
def core.ptr.end_from_mut {T : Type} [Pointee T] (p : MutRawPtr T) : Result T :=
  p.take

/-- The pointer points to fresh cells holding `r`; the back computation runs when the borrow
ends (`statefulLifetimes`). -/
@[rust_fun "core::ptr::from_mut" (statefulLifetimes := [0])]
def core.ptr.from_mut {T : Type} [Pointee T] (r : T) : Result (MutRawPtr T × Result T) :=
  Aeneas.Std.bind (RawPtr.materialize [r]) fun p => .ok (p, core.ptr.end_from_mut p)

/-- Not a Rust function: end of the shared borrow given to `from_ref`: the cells must still hold
the value (writing through a const pointer cast to mut is UB), and are killed. -/
def core.ptr.end_from_ref {T : Type} [Pointee T] (r : T) (p : ConstRawPtr T) : Result Unit := do
  let value ← p.take
  Result.require (value = r)

/-- The pointer points to fresh cells holding `r` (`&raw const place`, `ptr::addr_of!`). -/
@[rust_fun "core::ptr::from_ref" (statefulLifetimes := [0])]
def core.ptr.from_ref {T : Type} [Pointee T] (r : T) : Result (ConstRawPtr T × Result Unit) :=
  Aeneas.Std.bind (RawPtr.materialize [r]) fun p => .ok (p, core.ptr.end_from_ref r p)

/-- `&mut *p`: the value is moved out of its cells, which are killed so that the other accesses to
them fail while the borrow is live, and brought back to life, holding the final value of the
borrow, when the borrow ends (`statefulLifetimes`). The pointer must be aligned. The extraction
translates the borrows of places behind raw pointers (`&mut (*p).f`) to this function. -/
@[rust_fun "core::ptr::mut_ptr::{*mut @T}::as_mut_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_mut_unchecked {T : Type} [Pointee T] (p : MutRawPtr T) :
    Result (T × (T → Result Unit)) :=
  Aeneas.Std.bind (Result.require p.Aligned) fun _ =>
  Aeneas.Std.bind p.take fun value => .ok (value, p.revive)

/-- `&*p`: like `as_mut_unchecked`, the value is moved out while the borrow is live, so that
writing through another pointer fails (this is conservative: reading through another pointer
also fails), and brought back unchanged when the borrow ends. -/
@[rust_fun "core::ptr::const_ptr::{*const @T}::as_ref_unchecked" (statefulLifetimes := [0])]
def RawPtr.as_ref_unchecked {T : Type} [Pointee T] (p : RawPtr T M) :
    Result (T × Result Unit) :=
  Aeneas.Std.bind (Result.require p.Aligned) fun _ =>
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

/-- Not a Rust function: `q` points to the live cells of a box allocation (see `Box::into_raw`),
of a type which is not zero-sized. -/
def RawPtr.LiveBox {T : Type} [Pointee T] (q : RawPtr T M) (h : Heap) : Prop :=
  Pointee.size T ≠ 0 ∧ Heap.contains h (Pointee.Cell T) q.addr ∧
    Heap.isBoxEnd h (q.addr.add (Pointee.size T))

/-- Pointer comparison (`==` on raw pointers, `NonNull`). The model does not know the addresses:
two pointers are equal if they are the same. Otherwise they are different if they point to
different cells of the same allocation, all the cells between them being live cells of the pointee
(so that the cells are bytes, or values of `T`, and not, e.g., values of a zero-sized type
reached through a cast), or to two live box allocations (live allocations do not overlap), and the
pointee is not zero-sized (`Pointee.nonZero`). In the other cases the comparison fails: in
particular, the pointers obtained from borrows (`from_mut`, `as_ptr`, ...) point to fresh copies of
the borrowed values, whose actual addresses are those of the borrowed values, and freed
allocations may share their addresses with new ones. -/
def RawPtr.eq {T : Type} [Pointee T] (p q : RawPtr T M) : Result Bool :=
  if p.addr = q.addr then .ok true
  else Result.guardedModify
    (fun h => Pointee.nonZero T ∧
      (p.base = q.base ∧ HeapOp.Live (Pointee.Cell T) h (p.base, min p.offset q.offset)
          ((p.offset : Int) - q.offset).natAbs ∨
        p.LiveBox h ∧ q.LiveBox h))
    fun h _ => (false, h)

/-- `!=` on pointers (see `RawPtr.eq`). -/
def RawPtr.ne {T : Type} [Pointee T] (p q : RawPtr T M) : Result Bool :=
  Aeneas.Std.bind (p.eq q) fun b => .ok (!b)

/-! ### END Trusted definitions -/

/-! ### Laws of the instances -/

/-- The laws of a `Pointee` instance used by the proofs (they are not needed by the model). -/
class Pointee.Lawful (T : Type) [Pointee T] : Prop where
  length_toCells (value : T) : (Pointee.toCells value).length = Pointee.size T
  ofCells_toCells (value : T) : Pointee.ofCells (Pointee.toCells value) = some value
  align_pos : 0 < Pointee.align T
  align_dvd_size : Pointee.align T ∣ Pointee.size T

/-- Uninitialized cells hold no value of `T` (see `MaybeUninit`). -/
class Pointee.UninitInvalid (T : Type) [Pointee T] : Prop where
  ofCells_uninit : Pointee.ofCells (List.replicate (Pointee.size T) none : List (Option (Pointee.Cell T))) = none

namespace Pointee

theorem typed.lawful (T : Type) (nonZero : Bool) : @Lawful T (typed T nonZero) :=
  @Lawful.mk T (typed T nonZero) (fun _ => rfl) (fun _ => rfl) Nat.one_pos (Nat.dvd_refl 1)

instance typed.instLawful {T : Type} {nonZero : Bool} : @Lawful T (typed T nonZero) :=
  typed.lawful T nonZero

instance default.instLawful {T : Type} : @Lawful T Pointee.default := typed.lawful T false

instance typed.instUninitInvalid {T : Type} {nonZero : Bool} : @UninitInvalid T (typed T nonZero) :=
  @UninitInvalid.mk T (typed T nonZero) rfl

instance default.instUninitInvalid {T : Type} : @UninitInvalid T Pointee.default :=
  typed.instUninitInvalid

instance Option.instLawful {T : Type} [Pointee T] : Lawful (Option T) := typed.lawful _ _
instance RawPtr.instLawful {T : Type} {M : Mutability} : Lawful (RawPtr T M) := typed.lawful _ _
instance Char.instLawful : Lawful Char := typed.lawful _ _
instance Option.instUninitInvalid {T : Type} [Pointee T] : UninitInvalid (Option T) :=
  typed.instUninitInvalid
instance RawPtr.instUninitInvalid {T : Type} {M : Mutability} : UninitInvalid (RawPtr T M) :=
  typed.instUninitInvalid

@[simp] theorem size_typed (T : Type) (nonZero : Bool) : @size T (typed T nonZero) = 1 := rfl
@[simp] theorem align_typed (T : Type) (nonZero : Bool) : @align T (typed T nonZero) = 1 := rfl
@[simp] theorem nonZero_typed (T : Type) (nonZero : Bool) :
    @Pointee.nonZero T (typed T nonZero) = nonZero := rfl
@[simp] theorem toCells_typed (T : Type) (nonZero : Bool) (value : T) :
    @toCells T (typed T nonZero) value = [some ⟨value⟩] := rfl
@[simp] theorem size_default (T : Type) : @size T Pointee.default = 1 := rfl
@[simp] theorem align_default (T : Type) : @align T Pointee.default = 1 := rfl
@[simp] theorem nonZero_default (T : Type) : @Pointee.nonZero T Pointee.default = false := rfl
@[simp] theorem toCells_default (T : Type) (value : T) :
    @toCells T Pointee.default value = [some ⟨value⟩] := rfl

theorem _root_.List.mapM_id_map_some {α : Type} (xs : List α) :
    (xs.map some).mapM id = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

theorem bytes.lawful (T : Type) (size align : Nat) (encode : T → List U8)
    (decode : List U8 → Option T) (length_encode : ∀ value, (encode value).length = size)
    (decode_encode : ∀ value, decode (encode value) = some value) (align_pos : 0 < align)
    (align_dvd_size : align ∣ size) : @Lawful T (bytes T size align encode decode) :=
  @Lawful.mk T (bytes T size align encode decode)
    (fun value => by
      show ((encode value).map some).length = size
      simp [length_encode])
    (fun value => by
      show ((encode value).map some).mapM id >>= decode = some value
      rw [List.mapM_id_map_some]
      exact decode_encode value)
    align_pos align_dvd_size

theorem bytes.uninitInvalid (T : Type) (size align : Nat) (encode : T → List U8)
    (decode : List U8 → Option T) (hSize : size ≠ 0) :
    @UninitInvalid T (bytes T size align encode decode) :=
  @UninitInvalid.mk T (bytes T size align encode decode) (by
    obtain ⟨n, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
    show (List.replicate (n + 1) (none : Option U8)).mapM id >>= decode = none
    simp [List.replicate_succ, List.mapM_cons])

theorem _root_.Aeneas.Std.UScalarTy.numBits_mod_eight (ty : UScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [UScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

theorem _root_.Aeneas.Std.IScalarTy.numBits_mod_eight (ty : IScalarTy) : ty.numBits % 8 = 0 := by
  cases ty <;> simp only [IScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

theorem _root_.Aeneas.Std.UScalarTy.numBits_div_eight_pos (ty : UScalarTy) : 0 < ty.numBits / 8 := by
  cases ty <;> simp only [UScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

theorem _root_.Aeneas.Std.IScalarTy.numBits_div_eight_pos (ty : IScalarTy) : 0 < ty.numBits / 8 := by
  cases ty <;> simp only [IScalarTy.numBits] <;> rcases System.Platform.numBits_eq with h | h <;>
    simp [h]

theorem decodeLE_toLEBytes {n : Nat} (hn : n % 8 = 0) (b : BitVec n) :
    decodeLE n (b.toLEBytes.map UScalar.mk) = some b := by
  have hLen : 8 * (b.toLEBytes.map (UScalar.mk (ty := .U8))).length = n := by
    rw [List.length_map, BitVec.toLEBytes_length]; omega
  unfold decodeLE
  rw [dif_pos hLen]
  have hMap : (b.toLEBytes.map (UScalar.mk (ty := .U8))).map U8.bv = b.toLEBytes := by
    rw [List.map_map]; exact List.map_id _
  have key : ∀ l, l = b.toLEBytes → (BitVec.fromLEBytes l).toNat = b.toNat := by
    rintro l rfl
    rw [BitVec.fromLEBytes_toLEBytes hn, BitVec.toNat_cast]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast]
  exact key _ hMap

instance UScalar.instLawful (ty : UScalarTy) : Lawful (UScalar ty) :=
  bytes.lawful _ _ _ _ _
    (fun x => by rw [List.length_map, BitVec.toLEBytes_length]; have := ty.numBits_mod_eight; omega)
    (fun x => by simp only [decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some])
    ty.numBits_div_eight_pos (Nat.dvd_refl _)

instance IScalar.instLawful (ty : IScalarTy) : Lawful (IScalar ty) :=
  bytes.lawful _ _ _ _ _
    (fun x => by rw [List.length_map, BitVec.toLEBytes_length]; have := ty.numBits_mod_eight; omega)
    (fun x => by simp only [decodeLE_toLEBytes ty.numBits_mod_eight, Option.map_some])
    ty.numBits_div_eight_pos (Nat.dvd_refl _)

instance Bool.instLawful : Lawful Bool :=
  bytes.lawful _ _ _ _ _ (fun _ => rfl) (fun b => by cases b <;> rfl) Nat.one_pos (Nat.dvd_refl 1)

instance UScalar.instUninitInvalid (ty : UScalarTy) : UninitInvalid (UScalar ty) :=
  bytes.uninitInvalid _ _ _ _ _ (Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos)

instance IScalar.instUninitInvalid (ty : IScalarTy) : UninitInvalid (IScalar ty) :=
  bytes.uninitInvalid _ _ _ _ _ (Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos)

instance Bool.instUninitInvalid : UninitInvalid Bool := bytes.uninitInvalid _ _ _ _ _ (by decide)

@[simp] theorem size_uscalar (ty : UScalarTy) : size (UScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem align_uscalar (ty : UScalarTy) : align (UScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem size_iscalar (ty : IScalarTy) : size (IScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem align_iscalar (ty : IScalarTy) : align (IScalar ty) = ty.numBits / 8 := rfl
@[simp] theorem size_bool : size Bool = 1 := rfl
@[simp] theorem align_bool : align Bool = 1 := rfl
@[simp] theorem nonZero_uscalar (ty : UScalarTy) : Pointee.nonZero (UScalar ty) = true := by
  show (ty.numBits / 8 != 0) = true
  simp [Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos]
@[simp] theorem nonZero_iscalar (ty : IScalarTy) : Pointee.nonZero (IScalar ty) = true := by
  show (ty.numBits / 8 != 0) = true
  simp [Nat.pos_iff_ne_zero.mp ty.numBits_div_eight_pos]
@[simp] theorem nonZero_bool : Pointee.nonZero Bool = true := rfl
@[simp] theorem toCells_uscalar {ty : UScalarTy} (x : UScalar ty) :
    toCells x = (x.bv.toLEBytes.map (UScalar.mk (ty := .U8))).map some := rfl
@[simp] theorem toCells_u8 (x : U8) : toCells x = [some x] := by
  simp only [toCells_uscalar]
  have h : x.bv.toLEBytes = [x.bv] := by
    unfold BitVec.toLEBytes
    simp only [UScalarTy.U8_numBits_eq, gt_iff_lt, Nat.ofNat_pos, ↓reduceIte, Nat.sub_self]
    unfold BitVec.toLEBytes
    simp
  rw [h]
  rfl

theorem length_flatMap_toCells {T : Type} [Pointee T] [Lawful T] (values : List T) :
    (values.flatMap toCells).length = values.length * size T := by
  induction values with
  | nil => simp
  | cons value values ih =>
    simp [List.flatMap_cons, Lawful.length_toCells, ih, Nat.succ_mul, Nat.add_comm]

theorem length_optCells {T : Type} [Pointee T] [Lawful T] (content : Option T) :
    (optCells content).length = size T := by
  cases content <;> simp [optCells, Lawful.length_toCells]

theorem length_flatMap_optCells {T : Type} [Pointee T] [Lawful T] (contents : List (Option T)) :
    (contents.flatMap optCells).length = contents.length * size T := by
  induction contents with
  | nil => simp
  | cons content contents ih =>
    simp [List.flatMap_cons, length_optCells, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem optCells_some {T : Type} [Pointee T] (value : T) :
    optCells (some value) = toCells value := rfl

@[simp] theorem optCells_none {T : Type} [Pointee T] :
    optCells (none : Option T) = List.replicate (size T) none := rfl

theorem flatMap_optCells_map_some {T : Type} [Pointee T] (values : List T) :
    (values.map some).flatMap optCells = values.flatMap toCells := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.flatMap_cons, ih]

theorem ofCellsList_flatMap {T : Type} [Pointee T] [Lawful T] (values : List T)
    (rest : List (Option (Cell T))) :
    ofCellsList T values.length (values.flatMap toCells ++ rest) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.length_cons, ofCellsList, List.flatMap_cons, List.append_assoc]
    rw [List.take_left' (Lawful.length_toCells value), List.drop_left' (Lawful.length_toCells value),
      Lawful.ofCells_toCells, ih]
    rfl

instance Array.instLawful {T : Type} [Pointee T] [Lawful T] {n : Usize} : Lawful (Array T n) where
  length_toCells a := by
    simp only [Pointee.toCells, Pointee.size, length_flatMap_toCells, Array.property]
  ofCells_toCells a := by
    have h := ofCellsList_flatMap a.val []
    rw [List.append_nil, Array.property] at h
    simp only [Pointee.toCells, Pointee.ofCells, h, Option.bind_eq_bind, Option.bind_some,
      Array.property, dite_true, Array.val_from]
  align_pos := (Lawful.align_pos : 0 < align T)
  align_dvd_size := Dvd.dvd.mul_left (Lawful.align_dvd_size : align T ∣ size T) _

@[simp] theorem size_array (T : Type) [Pointee T] (n : Usize) :
    size (Array T n) = n.val * size T := rfl
@[simp] theorem align_array (T : Type) [Pointee T] (n : Usize) :
    align (Array T n) = align T := rfl

end Pointee

/-! ### Cells -/

open WP

namespace HeapOp

variable {α : Type}

/-- Owning the cells `contents` from `l` on. Irreducible, so that unifying assertions does not
unfold the heap. -/
@[irreducible] def cellsAt {α : Type} (l : Loc) (contents : List (Option α)) : IProp :=
  owns (Heap.cells l contents)

/-- Owning `n` dead cells from `l` on. -/
def deadAt (l : Loc) : Nat → IProp
  | 0 => emp
  | n + 1 => owns (Heap.endMarker l) ∗ deadAt (l.add 1) n

theorem cellsAt_eq {α : Type} (l : Loc) (contents : List (Option α)) :
    cellsAt l contents = owns (Heap.cells l contents) := by
  unfold cellsAt; rfl

@[simp] theorem cellsAt_nil {α : Type} (l : Loc) : cellsAt l ([] : List (Option α)) = emp := by
  rw [cellsAt_eq]
  exact entails_antisymm (fun _ _ => trivial) (fun h _ => Heap.Sub.of_empty h)

theorem cellsAt_append {α : Type} (l : Loc) (xs ys : List (Option α)) :
    cellsAt l (xs ++ ys) = iprop(cellsAt l xs ∗ cellsAt (l.add xs.length) ys) := by
  rw [cellsAt_eq, cellsAt_eq, cellsAt_eq, Heap.cells_append l xs ys]
  exact owns_union _ _ (Heap.compatible_cells_append l xs ys)

theorem cellsAt_cons {α : Type} (l : Loc) (content : Option α) (rest : List (Option α)) :
    cellsAt l (content :: rest) = iprop(owns (Heap.cell l content) ∗ cellsAt (l.add 1) rest) := by
  rw [show content :: rest = [content] ++ rest from rfl, cellsAt_append, cellsAt_eq l [content]]
  simp

@[simp] theorem deadAt_zero (l : Loc) : deadAt l 0 = emp := rfl

theorem deadAt_succ (l : Loc) (n : Nat) :
    deadAt l (n + 1) = iprop(owns (Heap.endMarker l) ∗ deadAt (l.add 1) n) := rfl

theorem deadAt_add (l : Loc) (m n : Nat) :
    deadAt l (m + n) = iprop(deadAt l m ∗ deadAt (l.add m) n) := by
  induction m generalizing l with
  | zero => simp [sep_emp_l_eq]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, deadAt_succ, ih, deadAt_succ, sep_assoc_eq,
      Loc.add_add, Nat.add_comm 1 m]

theorem contains_of_cellsAt {α : Type} {l : Loc} {contents : List (Option α)} {h : Heap}
    (hCells : cellsAt l contents h) {i : Nat} (hi : i < contents.length) :
    Heap.contains h α (l.add i) := by
  rw [cellsAt_eq] at hCells
  exact Heap.Sub.contains hCells (Heap.contains_cells hi)

theorem live_of_cellsAt {α : Type} {l : Loc} {contents : List (Option α)} {h : Heap}
    (hCells : cellsAt l contents h) {n : Nat} (hn : n ≤ contents.length) : Live α h l n :=
  fun _ hi => contains_of_cellsAt hCells (by omega)

theorem read.spec (l : Loc) (content : Option α) :
    ⦃ owns (Heap.cell l content) ⦄ read α l
      ⦃ result => ⌜result = content⌝ ∗ owns (Heap.cell l content) ⦄ := by
  apply ispec_guardedModify
  intro h hCell frame hCompatible
  have hSub : Heap.Sub (Heap.cell l content) (h ∪ frame) :=
    (show Heap.Sub (Heap.cell l content) h from hCell).trans (Heap.Sub.union_left hCompatible)
  have hContains : Heap.contains (h ∪ frame) α l := Heap.Sub.contains hSub (Heap.contains_cell l content)
  exact ⟨hContains, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨Heap.read_of_sub hSub _, hCell⟩⟩

theorem write.spec (l : Loc) (content newContent : Option α) :
    ⦃ owns (Heap.cell l content) ⦄ write l newContent ⦃ owns (Heap.cell l newContent) ⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hPointsTo
  have hContainsSlot := Heap.contains_cell l content
  have hContains : Heap.contains (Heap.cell l content ∪ rest) α l :=
    Heap.contains_union_left hContainsSlot
  refine ⟨Heap.contains_union_left hContains,
    Heap.update l newContent _ hContains,
    Heap.disjoint_update_left hCompatible hContains, ?_, ?_⟩
  · simpa only [show Heap.contains_union_left hContains =
        Heap.contains_union_left (h₂ := frame) hContains from rfl] using
      Heap.update_union_left l newContent hContains
  · have hCompatibleNew :
        PartialCommMonoid.Compatible (Heap.cell l newContent) rest := by
      have hUpdated := Heap.disjoint_update_left (content := newContent)
        hCompatibleRest hContainsSlot
      rwa [Heap.update_cell] at hUpdated
    rw [show hContains = Heap.contains_union_left hContainsSlot from
      Subsingleton.elim _ _, Heap.update_union_left l _ hContainsSlot,
      Heap.update_cell]
    exact Heap.Sub.union_left hCompatibleNew

theorem kill.spec (l : Loc) (content : Option α) :
    ⦃ owns (Heap.cell l content) ⦄ kill α l
      ⦃ result => ⌜result = content⌝ ∗ owns (Heap.endMarker l) ⦄ := by
  apply ispec_guardedModify
  intro h hPointsTo frame hCompatible
  have hContains : Heap.contains h α l :=
    Heap.Sub.contains hPointsTo (Heap.contains_cell l content)
  have hSub : Heap.Sub (Heap.cell l content) (h ∪ frame) :=
    (show Heap.Sub (Heap.cell l content) h from hPointsTo).trans (Heap.Sub.union_left hCompatible)
  refine ⟨Heap.contains_union_left hContains, Heap.free l h hContains,
    Heap.disjoint_free_left hCompatible hContains, ?_, ?_⟩
  · exact Heap.free_union_left l hCompatible hContains
  · exact (sep_pure_l _ _ _).mpr ⟨Heap.read_of_sub hSub _, Heap.Sub.free hPointsTo hContains⟩

theorem revive.spec (l : Loc) (content : Option α) :
    ⦃ owns (Heap.endMarker l) ⦄ revive l content ⦃ owns (Heap.cell l content) ⦄ := by
  apply ispec_guardedModify
  intro h hDead frame hCompatible
  have hDeadH : Heap.dead h l := Heap.Sub.dead hDead
  exact ⟨Heap.dead_union_left hDeadH, Heap.revive l content h hDeadH,
    Heap.disjoint_revive_left hCompatible hDeadH, Heap.revive_union_left _ _ hDeadH,
    Heap.Sub.revive _ hDead hDeadH⟩

theorem reads.spec (l : Loc) (contents : List (Option α)) :
    ⦃ cellsAt l contents ⦄ reads α l contents.length
      ⦃ result => ⌜result = contents⌝ ∗ cellsAt l contents ⦄ := by
  induction contents generalizing l with
  | nil => simp [reads]
  | cons content contents ih =>
    rw [cellsAt_cons, List.length_cons, reads]
    apply ispec_bind (read.spec l content)
    · iframe
    · intro c
      iintro
      apply ispec_bind (ih (l.add 1))
      · iframe
      · intro cs
        iintro
        apply (ispec_ok _).2
        subst_vars
        iframe

theorem writes.spec (l : Loc) (contents newContents : List (Option α))
    (hLen : newContents.length = contents.length) :
    ⦃ cellsAt l contents ⦄ writes l newContents ⦃ cellsAt l newContents ⦄ := by
  induction contents generalizing l newContents with
  | nil =>
    have : newContents = [] := List.length_eq_zero_iff.mp (by simpa using hLen)
    subst this
    simp [writes]
  | cons content contents ih =>
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_length_pos (l := newContents) (by simp [hLen])
    rw [cellsAt_cons, cellsAt_cons, writes]
    apply ispec_bind (write.spec l content c)
    · iframe
    · intro _
      apply ispec_mono (ih (l.add 1) cs (by simpa using hLen)) <;> iframe

theorem kills.spec (l : Loc) (contents : List (Option α)) :
    ⦃ cellsAt l contents ⦄ kills α l contents.length
      ⦃ result => ⌜result = contents⌝ ∗ deadAt l contents.length ⦄ := by
  induction contents generalizing l with
  | nil => simp [kills]
  | cons content contents ih =>
    rw [cellsAt_cons, List.length_cons, kills, deadAt_succ]
    apply ispec_bind (kill.spec l content)
    · iframe
    · intro c
      iintro
      apply ispec_bind (ih (l.add 1))
      · iframe
      · intro cs
        iintro
        apply (ispec_ok _).2
        subst_vars
        iframe

theorem revives.spec (l : Loc) (contents : List (Option α)) :
    ⦃ deadAt l contents.length ⦄ revives l contents ⦃ cellsAt l contents ⦄ := by
  induction contents generalizing l with
  | nil => simp [revives]
  | cons content contents ih =>
    rw [cellsAt_cons, List.length_cons, revives, deadAt_succ]
    apply ispec_bind (revive.spec l content)
    · iframe
    · intro _
      apply ispec_mono (ih (l.add 1)) <;> iframe

theorem read.fails_dead (α : Type) (l : Loc) : ifails (owns (Heap.endMarker l)) (read α l) := by
  apply ifails_guardedModify
  intro h hDead h' hSub hContains
  exact Heap.not_contains_of_dead (Heap.Sub.dead (hDead.trans hSub)) hContains

theorem kill.fails_dead (α : Type) (l : Loc) : ifails (owns (Heap.endMarker l)) (kill α l) := by
  apply ifails_guardedModify
  intro h hDead h' hSub hContains
  exact Heap.not_contains_of_dead (Heap.Sub.dead (hDead.trans hSub)) hContains

theorem write.fails_dead {α : Type} (l : Loc) (content : Option α) :
    ifails (owns (Heap.endMarker l)) (write l content) := by
  apply ifails_guardedModify
  intro h hDead h' hSub hContains
  exact Heap.not_contains_of_dead (Heap.Sub.dead (hDead.trans hSub)) hContains

/-- Reading `n > 0` cells starting with a dead one fails. -/
theorem reads.fails_dead (α : Type) (l : Loc) (n : Nat) (hn : 0 < n) :
    ifails (owns (Heap.endMarker l)) (reads α l n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [reads]
  exact ifails_bind_left (read.fails_dead α l)

theorem kills.fails_dead (α : Type) (l : Loc) (n : Nat) (hn : 0 < n) :
    ifails (owns (Heap.endMarker l)) (kills α l n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [kills]
  exact ifails_bind_left (kill.fails_dead α l)

theorem writes.fails_dead {α : Type} (l : Loc) (contents : List (Option α))
    (hn : 0 < contents.length) : ifails (owns (Heap.endMarker l)) (writes l contents) := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_length_pos hn
  rw [writes]
  exact ifails_bind_left (write.fails_dead l c)

end HeapOp

/-! ### Pointers -/

namespace RawPtr

variable {T : Type} [Pointee T] {M : Mutability}

/-- `q` owns the cells `cells` (of the type of the cells of `T`). -/
def pointsToCells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) : IProp :=
  HeapOp.cellsAt q.addr cells

def pointsTo (q : RawPtr T M) (value : T) : IProp :=
  q.pointsToCells (Pointee.toCells value)

/-- `q` owns the `values.length` values from `q` on. -/
def pointsToRange (q : RawPtr T M) (values : List T) : IProp :=
  q.pointsToCells (values.flatMap Pointee.toCells)

/-- `q` owns the cells of a value, or uninitialized cells (`none`). -/
def pointsToOpt (q : RawPtr T M) (content : Option T) : IProp :=
  q.pointsToCells (Pointee.optCells content)

/-- `pointsToOpt` on the `contents.length` values from `q` on. -/
def pointsToOpts (q : RawPtr T M) (contents : List (Option T)) : IProp :=
  q.pointsToCells (contents.flatMap Pointee.optCells)

/-- `q` owns the dead cells of `n` values from `q` on (killed by `take`, to be brought back by
`revive`). -/
def pointsToDead (q : RawPtr T M) (n : Nat) : IProp :=
  HeapOp.deadAt q.addr (n * Pointee.size T)

/-- `q` points to the cells of a box allocation: `Box::from_raw` can free it. -/
def boxed (q : RawPtr T M) : IProp :=
  owns (Heap.boxEnd (q.addr.add (Pointee.size T)))

end RawPtr

instance instPointsToRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsTo (RawPtr T M) T := ⟨RawPtr.pointsTo⟩

instance instPointsToRangeRawPtr {T : Type} [Pointee T] {M : Mutability} :
    PointsToRange (RawPtr T M) T := ⟨RawPtr.pointsToRange⟩

end Aeneas.Std

namespace Aeneas

scoped notation:50 q:50 " ↦† " n:50 => Std.RawPtr.pointsToDead q n
scoped notation:50 q:50 " ↦# " cells:50 => Std.RawPtr.pointsToCells q cells
scoped notation:50 q:50 " ↦? " content:50 => Std.RawPtr.pointsToOpt q content
scoped notation:50 q:50 " ↦*? " contents:50 => Std.RawPtr.pointsToOpts q contents

end Aeneas

namespace Aeneas.Std

open Aeneas WP

namespace RawPtr

@[simp] theorem base_shiftCells (q : RawPtr T M) (i : Nat) : (q.shiftCells i).base = q.base := rfl
@[simp] theorem offset_shiftCells (q : RawPtr T M) (i : Nat) :
    (q.shiftCells i).offset = q.offset + i := rfl
@[simp] theorem shiftCells_zero (q : RawPtr T M) : q.shiftCells 0 = q := rfl
theorem addr_shiftCells (q : RawPtr T M) (i : Nat) : (q.shiftCells i).addr = q.addr.add i := rfl
theorem shiftCells_shiftCells (q : RawPtr T M) (i j : Nat) :
    (q.shiftCells i).shiftCells j = q.shiftCells (i + j) := by
  simp [shiftCells, Nat.add_assoc]

section

variable {T : Type} [Pointee T] {M : Mutability}

@[simp] theorem base_shift (q : RawPtr T M) (i : Nat) : (q.shift i).base = q.base := rfl
@[simp] theorem offset_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).offset = q.offset + i * Pointee.size T := rfl
@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q := by simp [shift]
theorem addr_shift (q : RawPtr T M) (i : Nat) :
    (q.shift i).addr = q.addr.add (i * Pointee.size T) := rfl
theorem shift_shift (q : RawPtr T M) (i j : Nat) : (q.shift i).shift j = q.shift (i + j) := by
  simp [shift, shiftCells, Nat.add_assoc, Nat.add_mul]

theorem shift_eq_shiftCells (q : RawPtr T M) (i : Nat) :
    q.shift i = q.shiftCells (i * Pointee.size T) := rfl

end

@[simp] theorem cast_const_eq_retype (q : MutRawPtr T) : q.cast_const = q.retype := rfl
@[simp] theorem cast_eq_retype (q : RawPtr T M) : (q.cast U : RawPtr U M) = q.retype := rfl
@[simp] theorem base_retype (q : RawPtr T M) : (q.retype : RawPtr U M').base = q.base := rfl
@[simp] theorem offset_retype (q : RawPtr T M) :
    (q.retype : RawPtr U M').offset = q.offset := rfl
@[simp] theorem addr_retype (q : RawPtr T M) : (q.retype : RawPtr U M').addr = q.addr := rfl
@[simp] theorem retype_retype (q : RawPtr T M) :
    ((q.retype : RawPtr U M').retype : RawPtr V M'') = q.retype := rfl
@[simp] theorem retype_self (q : RawPtr T M) : (q.retype : RawPtr T M) = q := rfl
theorem shiftCells_retype (q : RawPtr T M) (i : Nat) :
    ((q.retype : RawPtr U M').shiftCells i) = (q.shiftCells i).retype := rfl

theorem addr_injective {q r : RawPtr T M} (hEq : q.addr = r.addr) : q = r := by
  cases q
  cases r
  have hBase := congrArg Prod.fst hEq
  have hOffset := congrArg Prod.snd hEq
  simp only [RawPtr.addr] at hBase hOffset
  simp_all

end RawPtr

section PointsTo

variable {T : Type} [Pointee T] {M : Mutability}

namespace RawPtr

theorem pointsTo_eq (q : RawPtr T M) (value : T) : (q ↦ value) = (q ↦# Pointee.toCells value) := rfl

theorem pointsToRange_eq_cells (q : RawPtr T M) (values : List T) :
    (q ↦* values) = (q ↦# values.flatMap Pointee.toCells) := rfl

theorem pointsToOpt_eq (q : RawPtr T M) (content : Option T) :
    (q ↦? content) = (q ↦# Pointee.optCells content) := rfl

theorem pointsToOpts_eq (q : RawPtr T M) (contents : List (Option T)) :
    (q ↦*? contents) = (q ↦# contents.flatMap Pointee.optCells) := rfl

@[simp] theorem pointsToOpt_some (q : RawPtr T M) (value : T) : (q ↦? some value) = (q ↦ value) :=
  rfl

theorem pointsToRange_eq (q : RawPtr T M) (values : List T) :
    (q ↦* values) = (q ↦*? values.map some) := by
  rw [pointsToOpts_eq, Pointee.flatMap_optCells_map_some]
  rfl

theorem pointsToCells_eq_cellsAt (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) :
    (q ↦# cells) = HeapOp.cellsAt q.addr cells := rfl

@[simp] theorem pointsTo_retype (q : RawPtr T M) (value : T) :
    ((q.retype : RawPtr T M') ↦ value) = (q ↦ value) := rfl
@[simp] theorem pointsToRange_retype (q : RawPtr T M) (values : List T) :
    ((q.retype : RawPtr T M') ↦* values) = (q ↦* values) := rfl
@[simp] theorem pointsToOpt_retype (q : RawPtr T M) (content : Option T) :
    ((q.retype : RawPtr T M') ↦? content) = (q ↦? content) := rfl
@[simp] theorem pointsToOpts_retype (q : RawPtr T M) (contents : List (Option T)) :
    ((q.retype : RawPtr T M') ↦*? contents) = (q ↦*? contents) := rfl
@[simp] theorem pointsToCells_retype (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) :
    ((q.retype : RawPtr T M') ↦# cells) = (q ↦# cells) := rfl
@[simp] theorem pointsToDead_retype (q : RawPtr T M) (n : Nat) :
    ((q.retype : RawPtr T M') ↦† n) = (q ↦† n) := rfl
@[simp] theorem boxed_retype (q : RawPtr T M) :
    (q.retype : RawPtr T M').boxed = q.boxed := rfl

@[simp] theorem pointsToCells_nil (q : RawPtr T M) :
    (q ↦# ([] : List (Option (Pointee.Cell T)))) = emp := HeapOp.cellsAt_nil _

theorem pointsToCells_append (q : RawPtr T M) (xs ys : List (Option (Pointee.Cell T))) :
    (q ↦# (xs ++ ys)) = iprop(q ↦# xs ∗ (q.shiftCells xs.length) ↦# ys) :=
  HeapOp.cellsAt_append _ _ _

@[simp] theorem pointsToRange_nil (q : RawPtr T M) : (q ↦* ([] : List T)) = emp :=
  pointsToCells_nil q

@[simp] theorem pointsToOpts_nil (q : RawPtr T M) : (q ↦*? ([] : List (Option T))) = emp :=
  pointsToCells_nil q

variable [Pointee.Lawful T]

theorem pointsToRange_append (q : RawPtr T M) (xs ys : List T) :
    (q ↦* (xs ++ ys)) = iprop(q ↦* xs ∗ (q.shift xs.length) ↦* ys) := by
  rw [pointsToRange_eq_cells, List.flatMap_append, pointsToCells_append,
    Pointee.length_flatMap_toCells]
  rfl

theorem pointsToRange_cons (q : RawPtr T M) (value : T) (rest : List T) :
    (q ↦* (value :: rest)) = iprop(q ↦ value ∗ (q.shift 1) ↦* rest) := by
  rw [pointsToRange_eq_cells, List.flatMap_cons, pointsToCells_append,
    Pointee.Lawful.length_toCells, shift_eq_shiftCells, Nat.one_mul]
  rfl

theorem pointsTo_eq_range (q : RawPtr T M) (value : T) : (q ↦ value) = (q ↦* [value]) := by
  rw [pointsToRange_cons, pointsToRange_nil, sep_emp_r_eq]

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
  have hTake : (values.take i).length = i := by simp; omega
  rw [pointsToRange_split q values i, hTake, List.drop_eq_getElem_cons hIndex,
    pointsToRange_cons, shift_shift]

theorem pointsToOpts_append (q : RawPtr T M) (xs ys : List (Option T)) :
    (q ↦*? (xs ++ ys)) = iprop(q ↦*? xs ∗ (q.shift xs.length) ↦*? ys) := by
  rw [pointsToOpts_eq, List.flatMap_append, pointsToCells_append,
    Pointee.length_flatMap_optCells]
  rfl

theorem pointsToOpts_cons (q : RawPtr T M) (content : Option T) (rest : List (Option T)) :
    (q ↦*? (content :: rest)) = iprop(q ↦? content ∗ (q.shift 1) ↦*? rest) := by
  rw [pointsToOpts_eq, List.flatMap_cons, pointsToCells_append, Pointee.length_optCells,
    shift_eq_shiftCells, Nat.one_mul]
  rfl

theorem pointsToOpts_split (q : RawPtr T M) (contents : List (Option T)) (i : Nat) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗ (q.shift (contents.take i).length) ↦*? contents.drop i) := by
  conv_lhs => rw [← List.take_append_drop i contents]
  exact pointsToOpts_append q (contents.take i) (contents.drop i)

theorem pointsToOpts_eq_take_get_drop {q : RawPtr T M} {contents : List (Option T)} {i : Nat}
    (hIndex : i < contents.length) :
    (q ↦*? contents) =
      iprop(q ↦*? contents.take i ∗
        ((q.shift i) ↦? contents[i] ∗ (q.shift (i + 1)) ↦*? contents.drop (i + 1))) := by
  have hTake : (contents.take i).length = i := by simp; omega
  rw [pointsToOpts_split q contents i, hTake, List.drop_eq_getElem_cons hIndex,
    pointsToOpts_cons, shift_shift]

end RawPtr

end PointsTo

namespace RawPtr

variable {T : Type} [Pointee T] {M : Mutability}

@[simp] theorem pointsToDead_zero (q : RawPtr T M) : (q ↦† 0) = emp := by
  simp [pointsToDead]

theorem pointsToDead_add (q : RawPtr T M) (m n : Nat) :
    (q ↦† (m + n)) = iprop(q ↦† m ∗ (q.shift m) ↦† n) := by
  rw [pointsToDead, Nat.add_mul, HeapOp.deadAt_add]
  rfl

theorem pointsToDead_succ (q : RawPtr T M) (n : Nat) :
    (q ↦† (n + 1)) = iprop(q ↦† 1 ∗ (q.shift 1) ↦† n) := by
  rw [Nat.add_comm, pointsToDead_add]

theorem pointsToDead_one (q : RawPtr T M) :
    (q ↦† 1) = HeapOp.deadAt q.addr (Pointee.size T) := by
  simp [pointsToDead]

/-! #### Alignment -/

@[simp] theorem notNull_iff (q : RawPtr T M) (n : Nat) : q.NotNull n ↔ (n = 0 → q.base ≠ 0) :=
  Iff.rfl

/-- An access to some cells need not check the pointer (see `NotNull`). -/
theorem notNull_of_pos {q : RawPtr T M} {n : Nat} (h : 0 < n) : q.NotNull n :=
  fun h0 => absurd h0 (by omega)

@[simp] theorem aligned_iff (q : RawPtr T M) :
    q.Aligned ↔ Pointee.align T ∣ q.base ∧ Pointee.align T ∣ q.offset ∧
      (Pointee.size T = 0 → q.base ≠ 0) := Iff.rfl

theorem Aligned.notNull {q : RawPtr T M} (hAligned : q.Aligned) : q.NotNull (Pointee.size T) :=
  hAligned.2.2

theorem Aligned.shift [Pointee.Lawful T] {q : RawPtr T M} (hAligned : q.Aligned) (i : Nat) :
    (q.shift i).Aligned :=
  ⟨hAligned.1, Nat.dvd_add hAligned.2.1 (Dvd.dvd.mul_left Pointee.Lawful.align_dvd_size _),
    hAligned.2.2⟩

theorem Aligned.retype {q : RawPtr T M} (hAligned : q.Aligned) :
    (q.retype : RawPtr T M').Aligned := hAligned

theorem aligned_of_align_one {q : RawPtr T M} (h : Pointee.align T = 1)
    (hNotNull : q.NotNull (Pointee.size T)) : q.Aligned := by
  simp_all

theorem not_aligned_null (hSize : Pointee.size T = 0) : ¬ (RawPtr.null : RawPtr T M).Aligned := by
  simp [RawPtr.null, hSize]

end RawPtr

end Aeneas.Std

namespace Aeneas.Std

open Aeneas WP

/-! ### Specifications -/

@[step]
theorem Result.require.spec {p : Prop} (hp : p) : ⦃ emp ⦄ Result.require p ⦃ emp⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  exact ⟨hp, h, hCompatible, rfl, trivial⟩

theorem Result.require.fails {p : Prop} (hp : ¬ p) {P : IPre} : ifails P (Result.require p) := by
  apply ifails_guardedModify
  intro _ _ _ _ h
  exact hp h

theorem ifails_require_bind {β : Type u} {p : Prop} {k : Unit → Result β} {P : IPre}
    (hk : ifails P (k ())) : ifails P (Aeneas.Std.bind (Result.require p) k) :=
  ifails_bind_check hk

theorem RawPtr.take_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).take i = values.take i := by
  apply List.ext_getElem (by simp)
  intro n h₁ _
  have hn : n < i := by simp at h₁; omega
  simp only [List.getElem_take, List.getElem_set, if_neg (show ¬ i = n by omega)]

theorem RawPtr.drop_set (values : List α) (i : Nat) (value : α) :
    (values.set i value).drop (i + 1) = values.drop (i + 1) := by
  apply List.ext_getElem (by simp)
  intro n _ _
  simp only [List.getElem_drop, List.getElem_set, if_neg (show ¬ i = i + 1 + n by omega)]

section Specs

variable {T : Type} [Pointee T] [Pointee.Lawful T] {M : Mutability}

omit [Pointee.Lawful T] in
theorem Pointee.decode.spec {cells : List (Option (Pointee.Cell T))} {value : T}
    (hValue : Pointee.ofCells cells = some value) {P : IPre} :
    ⦃ P ⦄ Pointee.decode cells ⦃ r => ⌜r = value⌝ ∗ P ⦄ := by
  simp only [Pointee.decode, hValue]
  apply (ispec_ok _).2
  iframe

omit [Pointee.Lawful T] in
theorem Pointee.decode.fails {cells : List (Option (Pointee.Cell T))}
    (hNone : Pointee.ofCells cells = none) {P : IPre} : ifails P (Pointee.decode cells) := by
  simp only [Pointee.decode, hNone]
  exact ifails_fail _

theorem Heap.aligned_freshBase (h : Heap) : Pointee.align T ∣ Heap.freshBase h (Pointee.align T) := by
  have h := Heap.dvd_freshBase h (Pointee.align T)
  rwa [Nat.max_eq_left (Pointee.Lawful.align_pos (T := T))] at h

/-- The fresh allocation is aligned, and the pointer points to its start. -/
theorem RawPtr.allocate.spec_offset (last : Slot) (values : List T) :
    ⦃ emp ⦄ RawPtr.allocate (M := M) last values
      ⦃ p => ⌜p.Aligned ∧ p.offset = 0⌝ ∗ p ↦* values ∗
        owns (Heap.slot (p.addr.add (values.length * Pointee.size T)) last) ⦄ := by
  apply ispec_guardedModify
  intro h _ frame hCompatible
  have hFresh :
      PartialCommMonoid.Compatible
        (Heap.allocation (Heap.freshLoc (h ∪ frame) (Pointee.align T))
          (values.flatMap Pointee.toCells) last)
        (h ∪ frame) :=
    Heap.compatible_freshLoc _ _ _ _
  obtain ⟨hFreshH, hFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Heap.allocation (Heap.freshLoc (h ∪ frame) (Pointee.align T))
        (values.flatMap Pointee.toCells) last) h frame).mpr ⟨hCompatible, hFresh⟩
  refine ⟨trivial, _, hFreshFrame,
    (PartialCommMonoid.union_assoc hFreshH hFreshFrame).symm, ?_⟩
  have hSep : iprop(owns (Heap.cells (Heap.freshLoc (h ∪ frame) (Pointee.align T))
        (values.flatMap Pointee.toCells)) ∗
      owns (Heap.slot ((Heap.freshLoc (h ∪ frame) (Pointee.align T)).add
        (values.flatMap Pointee.toCells).length) last))
      (Heap.allocation (Heap.freshLoc (h ∪ frame) (Pointee.align T))
        (values.flatMap Pointee.toCells) last) := by
    rw [← owns_union _ _ (Heap.compatible_allocation _ _ _)]
    exact Heap.Sub.refl _
  rw [Pointee.length_flatMap_toCells, ← HeapOp.cellsAt_eq] at hSep
  refine (sep_pure_l _ _ _).mpr
    ⟨⟨⟨Heap.aligned_freshBase _, Nat.dvd_zero _, fun _ => Heap.freshBase_ne_zero _ _⟩, rfl⟩, ?_⟩
  exact IProp.up_closed _ hSep (Heap.Sub.union_left hFreshH)

theorem RawPtr.allocate.spec (last : Slot) (values : List T) :
    ⦃ emp ⦄ RawPtr.allocate (M := M) last values
      ⦃ p => ⌜p.Aligned⌝ ∗ p ↦* values ∗
        owns (Heap.slot (p.addr.add (values.length * Pointee.size T)) last) ⦄ :=
  WP.ispec_mono (RawPtr.allocate.spec_offset last values) (by iframe) (by iframe)

theorem RawPtr.materialize.spec_offset (values : List T) :
    ⦃ emp ⦄ RawPtr.materialize (M := M) values ⦃ p => ⌜p.Aligned ∧ p.offset = 0⌝ ∗ p ↦* values⦄ :=
  WP.ispec_mono (RawPtr.allocate.spec_offset .dead values) (by iframe) (by iframe)

@[step]
theorem RawPtr.materialize.spec (values : List T) :
    ⦃ emp ⦄ RawPtr.materialize (M := M) values ⦃ p => ⌜p.Aligned⌝ ∗ p ↦* values⦄ :=
  WP.ispec_mono (RawPtr.allocate.spec .dead values) (by iframe) (by iframe)

@[step]
theorem alloc.boxed.Box.into_raw.spec (value : T) :
    ⦃ emp ⦄ alloc.boxed.Box.into_raw value ⦃ q => ⌜q.Aligned⌝ ∗ q ↦ value ∗ q.boxed ⦄ := by
  unfold alloc.boxed.Box.into_raw
  have hSpec := RawPtr.allocate.spec (M := .Mut) .boxEnd [value]
  simp only [← RawPtr.pointsTo_eq_range, List.length_singleton, Nat.one_mul] at hSpec
  exact hSpec

namespace RawPtr

theorem read_unaligned.spec_raw (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (value : T) (hLen : cells.length = Pointee.size T)
    (hValue : Pointee.ofCells cells = some value) (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦# cells ⦄ q.read_unaligned ⦃ r => ⌜r = value⌝ ∗ q ↦# cells ⦄ := by
  unfold RawPtr.read_unaligned
  apply ispec_bind (Result.require.spec hNotNull)
  · iframe
  · intro _
    rw [← hLen]
    apply ispec_bind (HeapOp.reads.spec q.addr cells)
    · iframe
    · intro cs
      iintro
      subst_vars
      apply WP.ispec_mono (Pointee.decode.spec hValue (P := emp)) <;> iframe

@[step]
theorem read_unaligned.spec (q : RawPtr T M) (value : T) (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦ value ⦄ q.read_unaligned ⦃ r => ⌜r = value⌝ ∗ q ↦ value ⦄ :=
  read_unaligned.spec_raw q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value) hNotNull

theorem read.spec_raw (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (value : T) (hLen : cells.length = Pointee.size T)
    (hValue : Pointee.ofCells cells = some value) (hAlign : q.Aligned) :
    ⦃ q ↦# cells ⦄ q.read ⦃ r => ⌜r = value⌝ ∗ q ↦# cells ⦄ := by
  unfold RawPtr.read
  apply ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_mono (read_unaligned.spec_raw q cells value hLen hValue hAlign.notNull) <;>
      iframe

@[step]
theorem read.spec (q : RawPtr T M) (value : T) (hAlign : q.Aligned) :
    ⦃ q ↦ value ⦄ q.read ⦃ r => ⌜r = value⌝ ∗ q ↦ value ⦄ :=
  read.spec_raw q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value) hAlign

theorem read.spec_frame (q : RawPtr T M) (value : T) (H : IProp)
    (hAlign : q.Aligned) :
    ⦃ q ↦ value ∗ H ⦄ q.read ⦃ result => ⌜result = value⌝ ∗ (q ↦ value ∗ H)⦄ := by
  apply WP.ispec_mono (read.spec q value hAlign) <;> iframe

theorem read.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) (hAlign : q.Aligned) :
    ⦃ q ↦* values ⦄ (q.shift i).read
      ⦃ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read.spec (q.shift i) values[i] (hAlign.shift i)) <;> iframe

theorem read_unaligned.spec_range (q : RawPtr T M) (values : List T) (i : Nat)
    (hIndex : i < values.length) (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦* values ⦄ (q.shift i).read_unaligned
      ⦃ result => ⌜result = values[i]⌝ ∗ q ↦* values⦄ := by
  rw [pointsToRange_eq_take_get_drop hIndex]
  apply WP.ispec_mono (read_unaligned.spec (q.shift i) values[i] hNotNull) <;> iframe

end RawPtr

theorem MutRawPtr.write_unaligned.spec_raw (q : MutRawPtr T)
    (cells : List (Option (Pointee.Cell T))) (value : T) (hLen : cells.length = Pointee.size T)
    (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦# cells ⦄ q.write_unaligned value ⦃ q ↦ value ⦄ := by
  unfold MutRawPtr.write_unaligned
  apply ispec_bind (Result.require.spec hNotNull)
  · iframe
  · intro _
    apply WP.ispec_mono (HeapOp.writes.spec q.addr cells (Pointee.toCells value)
      (by rw [Pointee.Lawful.length_toCells, hLen])) <;> iframe

@[step]
theorem MutRawPtr.write_unaligned.spec (q : MutRawPtr T) (oldValue newValue : T)
    (hNotNull : q.NotNull (Pointee.size T)) :
    ⦃ q ↦ oldValue ⦄ q.write_unaligned newValue ⦃ q ↦ newValue ⦄ :=
  write_unaligned.spec_raw q _ newValue (Pointee.Lawful.length_toCells oldValue) hNotNull

theorem MutRawPtr.write.spec_raw (q : MutRawPtr T) (cells : List (Option (Pointee.Cell T)))
    (value : T) (hLen : cells.length = Pointee.size T) (hAlign : q.Aligned) :
    ⦃ q ↦# cells ⦄ q.write value ⦃ q ↦ value ⦄ := by
  unfold MutRawPtr.write
  apply ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_mono (write_unaligned.spec_raw q cells value hLen hAlign.notNull) <;> iframe

/-- Writing over a value or uninitialized memory. -/
theorem MutRawPtr.write.spec_opt (q : MutRawPtr T) (content : Option T) (value : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦? content ⦄ q.write value ⦃ q ↦ value ⦄ :=
  write.spec_raw q _ value (Pointee.length_optCells content) hAlign

@[step]
theorem MutRawPtr.write.spec (q : MutRawPtr T) (oldValue newValue : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ oldValue ⦄ q.write newValue ⦃ q ↦ newValue ⦄ :=
  write.spec_raw q _ newValue (Pointee.Lawful.length_toCells oldValue) hAlign

theorem MutRawPtr.write.spec_range (q : MutRawPtr T) (values : List T)
    (i : Nat) (value : T) (hIndex : i < values.length)
    (hAlign : q.Aligned) :
    ⦃ q ↦* values ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦* values.set i value⦄ := by
  rw [RawPtr.pointsToRange_eq_take_get_drop hIndex,
    RawPtr.pointsToRange_eq_take_get_drop
      (show i < (values.set i value).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set,
    List.getElem_set_self]
  apply WP.ispec_mono (MutRawPtr.write.spec (q.shift i) values[i] value (hAlign.shift i)) <;> iframe

/-- `write.spec_range` on a range of values, some of which may be uninitialized. -/
theorem MutRawPtr.write.spec_cells (q : MutRawPtr T) (contents : List (Option T))
    (i : Nat) (value : T) (hIndex : i < contents.length)
    (hAlign : q.Aligned) :
    ⦃ q ↦*? contents ⦄ MutRawPtr.write (q.shift i) value
      ⦃ q ↦*? contents.set i (some value)⦄ := by
  rw [RawPtr.pointsToOpts_eq_take_get_drop hIndex,
    RawPtr.pointsToOpts_eq_take_get_drop
      (show i < (contents.set i (some value)).length by simpa using hIndex),
    RawPtr.take_set, RawPtr.drop_set,
    List.getElem_set_self, RawPtr.pointsToOpt_some]
  apply WP.ispec_mono (MutRawPtr.write.spec_opt (q.shift i) contents[i] value (hAlign.shift i)) <;>
    iframe

theorem MutRawPtr.write.spec_head (q : MutRawPtr T) (values : List T) (value : T)
    (h : 0 < values.length) (hAlign : q.Aligned) :
    ⦃ q ↦* values ⦄ q.write value ⦃ q ↦* values.set 0 value⦄ := by
  simpa using MutRawPtr.write.spec_range q values 0 value h hAlign

namespace RawPtr

theorem take.spec_raw (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) (value : T)
    (hLen : cells.length = Pointee.size T) (hValue : Pointee.ofCells cells = some value) :
    ⦃ q ↦# cells ⦄ q.take ⦃ result => ⌜result = value⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.take
  rw [pointsToDead_one, ← hLen]
  apply ispec_bind (HeapOp.kills.spec q.addr cells)
  · iframe
  · intro cs
    iintro
    subst_vars
    apply WP.ispec_mono (Pointee.decode.spec hValue (P := emp)) <;> iframe

@[step]
theorem take.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦ value ⦄ q.take ⦃ result => ⌜result = value⌝ ∗ q ↦† 1⦄ :=
  take.spec_raw q _ value (Pointee.Lawful.length_toCells value)
    (Pointee.Lawful.ofCells_toCells value)

@[step]
theorem revive.spec (q : RawPtr T M) (value : T) :
    ⦃ q ↦† 1 ⦄ q.revive value ⦃ q ↦ value⦄ := by
  unfold RawPtr.revive
  rw [pointsToDead_one, ← Pointee.Lawful.length_toCells value]
  exact HeapOp.revives.spec q.addr _

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

/-- `reviveRange.spec` with the number of dead values given separately. -/
theorem reviveRange.spec_len (q : RawPtr T M) (values : List T) (n : Nat)
    (h : values.length = n) :
    ⦃ q ↦† n ⦄ q.reviveRange values ⦃ q ↦* values⦄ := by
  subst h
  exact reviveRange.spec q values

end RawPtr

/-- The end marker of a box is still there. -/
private theorem boxEnd_check.spec (q : MutRawPtr T) :
    ⦃ q.boxed ⦄
      Result.guardedModify (fun h => Heap.isBoxEnd h (q.addr.add (Pointee.size T)))
        (fun h _ => ((), h))
      ⦃ _ => q.boxed ⦄ := by
  apply ispec_guardedModify
  intro h hBoxed frame hCompatible
  exact ⟨Heap.Sub.isBoxEnd ((show Heap.Sub (Heap.boxEnd _) h from hBoxed).trans
    (Heap.Sub.union_left hCompatible)), h, hCompatible, rfl, hBoxed⟩

/-- `from_raw` frees the cells: they are left dead, so that they can not be freed or used again. -/
theorem alloc.boxed.Box.from_raw.spec_freed {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ∗ q.boxed ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝ ∗ (q ↦† 1 ∗ q.boxed)⦄ := by
  unfold alloc.boxed.Box.from_raw
  apply WP.ispec_bind (boxEnd_check.spec q)
  · iframe
  · intro _
    apply WP.ispec_mono (RawPtr.take.spec q value) <;> iframe

@[step]
theorem alloc.boxed.Box.from_raw.spec {value : T} (q : MutRawPtr T) :
    ⦃ q ↦ value ∗ q.boxed ⦄ alloc.boxed.Box.from_raw q
      ⦃ result => ⌜result = value⌝⦄ :=
  WP.ispec_mono (alloc.boxed.Box.from_raw.spec_freed q) (by iframe) (by iframe)

@[step]
theorem core.ptr.from_mut.spec (value : T) :
    ⦃ emp ⦄ core.ptr.from_mut value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_mut q⌝ ∗ ⌜q.Aligned⌝ ∗ q ↦ value⦄ := by
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
theorem core.ptr.from_ref.spec (value : T) :
    ⦃ emp ⦄ core.ptr.from_ref value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_ref value q⌝ ∗ ⌜q.Aligned⌝ ∗ q ↦ value⦄ := by
  unfold core.ptr.from_ref
  apply WP.ispec_bind (RawPtr.materialize.spec (M := .Const) [value])
  · iframe
  · intro q
    apply (ispec_ok _).2
    rw [← RawPtr.pointsTo_eq_range]
    iframe

@[step]
theorem core.ptr.end_from_ref.spec (q : ConstRawPtr T) (value : T) :
    ⦃ q ↦ value ⦄ core.ptr.end_from_ref value q ⦃ emp ⦄ := by
  unfold core.ptr.end_from_ref
  apply WP.ispec_bind (RawPtr.take.spec q value)
  · iframe
  · intro v
    iintro
    apply WP.ispec_mono (Result.require.spec (by assumption)) <;> iframe

@[step]
theorem RawPtr.as_mut_unchecked.spec (q : MutRawPtr T) (value : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ value ⦄ q.as_mut_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.revive⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_mut_unchecked
  apply WP.ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_bind (RawPtr.take.spec q value)
    · iframe
    · intro v
      apply (ispec_ok _).2
      iframe

@[step]
theorem RawPtr.as_ref_unchecked.spec (q : RawPtr T M) (value : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ value ⦄ q.as_ref_unchecked
      ⦃ (result, back) => ⌜result = value ∧ back = q.revive value⌝ ∗ q ↦† 1⦄ := by
  unfold RawPtr.as_ref_unchecked
  apply WP.ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    apply WP.ispec_bind (RawPtr.take.spec q value)
    · iframe
    · intro v
      apply (ispec_ok _).2
      iframe

namespace RawPtr

theorem pointsTo_exclusive (q : RawPtr T M) (value₁ value₂ : T) (hSize : Pointee.size T ≠ 0) :
    q ↦ value₁ ∗ q ↦ value₂ ⊢ ⌜False⌝ := by
  rintro h ⟨h₁, h₂, hCompatible, -, hP₁, hP₂⟩
  have hLen := fun v : T => Pointee.Lawful.length_toCells v
  exact Heap.disjoint_contains_false hCompatible
    (HeapOp.contains_of_cellsAt (i := 0) hP₁ (by rw [hLen]; omega))
    (HeapOp.contains_of_cellsAt (i := 0) hP₂ (by rw [hLen]; omega))

theorem contains_of_pointsTo {q : RawPtr T M} {value : T} {h : Heap}
    (hPointsTo : (q ↦ value) h) (hSize : Pointee.size T ≠ 0) :
    Heap.contains h (Pointee.Cell T) q.addr :=
  HeapOp.contains_of_cellsAt (i := 0) hPointsTo (by rw [Pointee.Lawful.length_toCells]; omega)

end RawPtr

theorem RawPtr.eq.spec_self (q : RawPtr T M) :
    ⦃ emp ⦄ q.eq q ⦃ b => ⌜b = true⌝⦄ := by
  rw [RawPtr.eq, if_pos rfl]
  apply (ispec_ok _).2
  iframe

/-- Two different pointers into the same range of values are different. -/
theorem RawPtr.eq.spec_same_alloc (q : RawPtr T M) (values : List T) (i j : Nat)
    (hi : i ≤ values.length) (hj : j ≤ values.length) (hij : i ≠ j)
    (hNZ : Pointee.nonZero T) (hSize : Pointee.size T ≠ 0) :
    ⦃ q ↦* values ⦄ (q.shift i).eq (q.shift j) ⦃ b => ⌜b = false⌝ ∗ q ↦* values ⦄ := by
  have hOff : i * Pointee.size T ≠ j * Pointee.size T := fun h =>
    hij (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hSize) h)
  rw [RawPtr.eq, if_neg fun h => hOff (by
    have := congrArg Prod.snd h
    simp only [addr_shift, Loc.add] at this
    omega)]
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  have hLen := Pointee.length_flatMap_toCells (T := T) values
  have hLive := (q ↦* values).up_closed hCells (Heap.Sub.union_left hCompatible)
  refine ⟨⟨hNZ, .inl ⟨rfl, ?_⟩⟩, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨rfl, hCells⟩⟩
  intro k hk
  have ha : i * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hi
  have hb : j * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hj
  simp only [offset_shift, base_shift] at hk ⊢
  clear hOff
  generalize i * Pointee.size T = a at *
  generalize j * Pointee.size T = b at *
  have hk' : min a b + k < (values.flatMap Pointee.toCells).length := by rw [hLen]; omega
  convert HeapOp.contains_of_cellsAt hLive hk' using 1
  simp only [RawPtr.addr, Loc.add, Prod.mk.injEq, true_and]
  omega

/-- Two pointers to different live box allocations are different. -/
theorem RawPtr.eq.spec_boxes (hNZ : Pointee.nonZero T) (hSize : Pointee.size T ≠ 0)
    {p q : RawPtr T M} (hNe : p ≠ q) (v w : T) :
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
  refine ⟨⟨hNZ, .inr ⟨⟨hSize, ?_, ?_⟩, ⟨hSize, ?_, ?_⟩⟩⟩, _, hCompatible, rfl, ?_⟩
  · exact RawPtr.contains_of_pointsTo ((p ↦ v).up_closed hP (hSub₁.trans hSub)) hSize
  · exact Heap.Sub.isBoxEnd ((show Heap.Sub (Heap.boxEnd _) h₂ from hPBoxed).trans
      (hSub₂.trans hSub))
  · exact RawPtr.contains_of_pointsTo ((q ↦ w).up_closed hQ (hSub₃.trans hSub)) hSize
  · exact Heap.Sub.isBoxEnd ((show Heap.Sub (Heap.boxEnd _) h₄ from hQBoxed).trans
      (hSub₄.trans hSub))
  · exact (sep_pure_l _ _ _).mpr
      ⟨rfl, ⟨h₁, _, hCompatible₁₂, rfl, hP, ⟨h₂, _, hCompatible₂₃, rfl, hPBoxed,
        ⟨h₃, h₄, hCompatible₃₄, rfl, hQ, hQBoxed⟩⟩⟩⟩

/-- Comparing a pointer to a borrow view (whose allocation ends with a dead slot, see
`core.ptr.from_mut.spec_view`) with a pointer into another allocation fails. -/
theorem RawPtr.eq.fails_view {p q : RawPtr T M} (hBase : p.base ≠ q.base) :
    ifails (owns (Heap.endMarker (p.addr.add (Pointee.size T)))) (p.eq q) := by
  rw [RawPtr.eq, if_neg fun h => hBase (congrArg Prod.fst h)]
  apply ifails_guardedModify
  intro h hDead h' hSub hPre
  rcases hPre.2 with hEq | ⟨⟨_, _, hBox⟩, _⟩
  · exact hBase hEq.1
  · exact Heap.Sub.not_isBoxEnd (hDead.trans hSub) hBox

/-- Comparing two pointers to different cells of a type which may be zero-sized fails. -/
theorem RawPtr.eq.fails_zero_sized (hZ : Pointee.nonZero T = false) (hSize : Pointee.size T ≠ 0)
    {p q : RawPtr T M} (v w : T) : ifails (p ↦ v ∗ q ↦ w) (p.eq q) := by
  by_cases hA : p.addr = q.addr
  · refine ifails_mono (P' := ⌜False⌝ ∗ emp) ?_ (ifails_ipure False.elim)
    rw [sep_emp_r_eq]
    rw [RawPtr.addr_injective hA]
    exact RawPtr.pointsTo_exclusive q v w hSize
  · rw [RawPtr.eq, if_neg hA]
    apply ifails_guardedModify
    intro _ _ _ _ hPre
    exact absurd hPre.1 (by simp [hZ])

namespace RawPtr

/-- `add` stays in bounds of the cells `q` owns. -/
theorem add.spec_raw (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (count : Usize) (hCount : count.val * Pointee.size T ≤ cells.length) :
    ⦃ q ↦# cells ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦# cells⦄ := by
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  refine ⟨HeapOp.live_of_cellsAt ((q ↦# cells).up_closed hCells (Heap.Sub.union_left hCompatible))
    hCount, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨rfl, hCells⟩⟩

@[step]
theorem add.spec (q : RawPtr T M) (values : List T) (count : Usize)
    (hCount : count.val ≤ values.length) :
    ⦃ q ↦* values ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦* values⦄ :=
  add.spec_raw q _ count (by rw [Pointee.length_flatMap_toCells]; exact Nat.mul_le_mul_right _ hCount)

/-- `add` on a range of values, some of which may be uninitialized. -/
theorem add.spec_cells (q : RawPtr T M) (contents : List (Option T)) (count : Usize)
    (hCount : count.val ≤ contents.length) :
    ⦃ q ↦*? contents ⦄ q.add count
      ⦃ result => ⌜result = q.shift count.val⌝ ∗ q ↦*? contents⦄ :=
  add.spec_raw q _ count
    (by rw [Pointee.length_flatMap_optCells]; exact Nat.mul_le_mul_right _ hCount)

/-- `offset` from the `k`-th cell of a range of cells, staying in the range. -/
theorem offset.spec_raw (q : RawPtr T M) (cells : List (Option (Pointee.Cell T))) (k : Nat)
    (count : Isize) (hk : k ≤ cells.length)
    (hTarget : 0 ≤ (k : Int) + count.val * Pointee.size T)
    (hEnd : (k : Int) + count.val * Pointee.size T ≤ cells.length) :
    ⦃ q ↦# cells ⦄ (q.shiftCells k).offsetBy count
      ⦃ result => ⌜result = q.shiftCells ((k : Int) + count.val * Pointee.size T).toNat⌝ ∗
        q ↦# cells⦄ := by
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  have hLive := (q ↦# cells).up_closed hCells (Heap.Sub.union_left hCompatible)
  refine ⟨⟨by simp only [offset_shiftCells]; omega, ?_⟩, h, hCompatible, rfl,
    (sep_pure_l _ _ h).mpr ⟨?_, hCells⟩⟩
  · intro i hi
    have hc := HeapOp.contains_of_cellsAt (i := min (q.offset + k)
      (((q.offset + k : Nat) : Int) + count.val * Pointee.size T).toNat - q.offset + i) hLive (by
        simp only [offset_shiftCells] at hi
        omega)
    convert hc using 1
    simp only [RawPtr.addr, Loc.add, offset_shiftCells, base_shiftCells, Prod.mk.injEq, true_and]
    omega
  · simp only [RawPtr.shiftCells, offset_shiftCells]
    congr 1
    omega

/-- `offset` on a range of values, staying in the range. -/
theorem offset.spec (q : RawPtr T M) (values : List T) (i : Nat) (count : Isize)
    (hi : i ≤ values.length) (hTarget : 0 ≤ (i : Int) + count.val)
    (hEnd : (i : Int) + count.val ≤ values.length) :
    ⦃ q ↦* values ⦄ (q.shift i).offsetBy count
      ⦃ result => ⌜result = q.shift ((i : Int) + count.val).toNat⌝ ∗ q ↦* values⦄ := by
  have hLen := Pointee.length_flatMap_toCells (T := T) values
  have hPtr : q.shiftCells (((i * Pointee.size T : Nat) : Int) + count.val * Pointee.size T).toNat =
      q.shift ((i : Int) + count.val).toNat := by
    simp only [RawPtr.shift, RawPtr.shiftCells]
    congr 1
    have : ((i * Pointee.size T : Nat) : Int) + count.val * Pointee.size T =
        (((i : Int) + count.val).toNat * Pointee.size T : Nat) := by
      push_cast; rw [Int.toNat_of_nonneg hTarget, Int.add_mul]
    rw [this, Int.toNat_natCast]
  have hSpec := offset.spec_raw q _ (i * Pointee.size T) count
    (by rw [hLen]; exact Nat.mul_le_mul_right _ hi)
    (by push_cast; rw [← Int.add_mul]; exact Int.mul_nonneg hTarget (Int.natCast_nonneg _))
    (by rw [hLen]; push_cast; rw [← Int.add_mul]; exact Int.mul_le_mul_of_nonneg_right hEnd (Int.natCast_nonneg _))
  rw [hPtr] at hSpec
  exact hSpec

/-- The distance between two pointers into a range of values. -/
theorem offset_from.spec (q : RawPtr T M) (values : List T) (i j : Nat)
    (hi : i ≤ values.length) (hj : j ≤ values.length) (hNZ : Pointee.nonZero T)
    (hSize : Pointee.size T ≠ 0)
    (hBound : -2 ^ (IScalarTy.Isize.numBits - 1) ≤ (i : Int) - j ∧
      (i : Int) - j < 2 ^ (IScalarTy.Isize.numBits - 1)) :
    ⦃ q ↦* values ⦄ (q.shift i).offset_from ((q.shift j).retype : RawPtr T M')
      ⦃ result => ⌜result.val = (i : Int) - j⌝ ∗ q ↦* values⦄ := by
  have hLen := Pointee.length_flatMap_toCells (T := T) values
  have hDist : (((q.shift i).offset : Int) - ((q.shift j).retype : RawPtr T M').offset) =
      ((i : Int) - j) * Pointee.size T := by
    simp only [offset_shift, offset_retype]; push_cast; rw [Int.sub_mul]; omega
  have hDiv : ((((q.shift i).offset : Int) - ((q.shift j).retype : RawPtr T M').offset) /
      Pointee.size T) = (i : Int) - j := by
    rw [hDist, Int.mul_ediv_cancel _ (by exact_mod_cast hSize)]
  unfold RawPtr.offset_from
  apply ispec_guardedModify
  intro h hCells frame hCompatible
  have hLive := (q ↦* values).up_closed hCells (Heap.Sub.union_left hCompatible)
  refine ⟨⟨rfl, hNZ, hSize, ⟨(i : Int) - j, by rw [hDist, Int.mul_comm]⟩, ?_, by rw [hDiv]; exact hBound.1,
    by rw [hDiv]; exact hBound.2⟩, h, hCompatible, rfl, (sep_pure_l _ _ h).mpr ⟨?_, hCells⟩⟩
  · intro k hk
    have ha : i * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hi
    have hb : j * Pointee.size T ≤ values.length * Pointee.size T := Nat.mul_le_mul_right _ hj
    simp only [offset_shift, base_shift, offset_retype] at hk ⊢
    clear hDist hDiv
    generalize i * Pointee.size T = a at *
    generalize j * Pointee.size T = b at *
    have hk' : min a b + k < (values.flatMap Pointee.toCells).length := by rw [hLen]; omega
    convert HeapOp.contains_of_cellsAt hLive hk' using 1
    simp only [RawPtr.addr, Loc.add, Prod.mk.injEq, true_and]
    omega
  · simp only [IScalar.ofInt_val_eq]
    exact hDiv

end RawPtr

/-! #### Copies -/

/-- Copy between two separate ranges of cells. -/
theorem core.ptr.copy.spec_raw (src : ConstRawPtr T) (dst : MutRawPtr T)
    (srcCells dstCells : List (Option (Pointee.Cell T))) (count : Usize)
    (hSrc : srcCells.length = count.val * Pointee.size T)
    (hDst : dstCells.length = count.val * Pointee.size T)
    (hAlign : src.Aligned ∧ dst.Aligned ∧ src.NotNull (count.val * Pointee.size T) ∧
      dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦# srcCells ∗ dst ↦# dstCells ⦄ core.ptr.copy src dst count
      ⦃ src ↦# srcCells ∗ dst ↦# srcCells ⦄ := by
  unfold core.ptr.copy
  apply WP.ispec_bind (Result.require.spec hAlign)
  · iframe
  · intro _
    rw [← hSrc]
    apply WP.ispec_bind (HeapOp.reads.spec src.addr srcCells)
    · iframe
    · intro cs
      iintro
      subst_vars
      apply WP.ispec_mono (HeapOp.writes.spec dst.addr dstCells cs (by rw [hSrc, hDst]))
      · iframe
      · iframe

@[step]
theorem core.ptr.copy.spec (src : ConstRawPtr T) (dst : MutRawPtr T) (srcValues dstValues : List T)
    (count : Usize) (hSrc : srcValues.length = count.val) (hDst : dstValues.length = count.val)
    (hAlignSrc : src.Aligned) (hAlignDst : dst.Aligned)
    (hNotNullSrc : src.NotNull (count.val * Pointee.size T))
    (hNotNullDst : dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦* srcValues ∗ dst ↦* dstValues ⦄ core.ptr.copy src dst count
      ⦃ src ↦* srcValues ∗ dst ↦* srcValues ⦄ :=
  core.ptr.copy.spec_raw src dst _ _ count
    (by rw [Pointee.length_flatMap_toCells, hSrc]) (by rw [Pointee.length_flatMap_toCells, hDst])
    ⟨hAlignSrc, hAlignDst, hNotNullSrc, hNotNullDst⟩

/-- Two ranges of cells owned separately do not overlap. -/
theorem RawPtr.disjoint_of_sep {src : ConstRawPtr T} {dst : MutRawPtr T}
    {srcCells dstCells : List (Option (Pointee.Cell T))} {h : Heap}
    (hSep : (src ↦# srcCells ∗ dst ↦# dstCells) h) (n : Nat)
    (hSrc : n ≤ srcCells.length) (hDst : n ≤ dstCells.length) :
    src.base ≠ dst.base ∨ src.offset + n ≤ dst.offset ∨ dst.offset + n ≤ src.offset := by
  by_contra hOverlap
  simp only [not_or, not_not, Nat.not_le] at hOverlap
  obtain ⟨hBase, h₁, h₂⟩ := hOverlap
  obtain ⟨hs, hd, hCompatible, -, hS, hD⟩ := hSep
  by_cases hle : src.offset ≤ dst.offset
  · have hcs := HeapOp.contains_of_cellsAt (i := dst.offset - src.offset) hS (by omega)
    have hcd := HeapOp.contains_of_cellsAt (i := 0) hD (by omega)
    refine Heap.disjoint_contains_false hCompatible hcs ?_
    convert hcd using 1
    simp only [RawPtr.addr, Loc.add, hBase, Prod.mk.injEq, true_and]
    omega
  · have hcs := HeapOp.contains_of_cellsAt (i := 0) hS (by omega)
    have hcd := HeapOp.contains_of_cellsAt (i := src.offset - dst.offset) hD (by omega)
    refine Heap.disjoint_contains_false hCompatible hcs ?_
    convert hcd using 1
    simp only [RawPtr.addr, Loc.add, hBase, Prod.mk.injEq, true_and]
    omega

theorem core.ptr.copy_nonoverlapping.spec_raw (src : ConstRawPtr T) (dst : MutRawPtr T)
    (srcCells dstCells : List (Option (Pointee.Cell T))) (count : Usize)
    (hSrc : srcCells.length = count.val * Pointee.size T)
    (hDst : dstCells.length = count.val * Pointee.size T)
    (hAlign : src.Aligned ∧ dst.Aligned ∧ src.NotNull (count.val * Pointee.size T) ∧
      dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦# srcCells ∗ dst ↦# dstCells ⦄ core.ptr.copy_nonoverlapping src dst count
      ⦃ src ↦# srcCells ∗ dst ↦# srcCells ⦄ := by
  unfold core.ptr.copy_nonoverlapping
  apply WP.ispec_bind (Pm := iprop(src ↦# srcCells ∗ dst ↦# dstCells)) (F := emp)
    (Qm := fun _ => iprop(src ↦# srcCells ∗ dst ↦# dstCells))
  · apply ispec_guardedModify
    intro h hSep frame hCompatible
    exact ⟨RawPtr.disjoint_of_sep hSep _ (by omega) (by omega), h, hCompatible, rfl, hSep⟩
  · iframe
  · intro _
    apply WP.ispec_mono (core.ptr.copy.spec_raw src dst srcCells dstCells count hSrc hDst hAlign)
      <;> iframe

@[step]
theorem core.ptr.copy_nonoverlapping.spec (src : ConstRawPtr T) (dst : MutRawPtr T)
    (srcValues dstValues : List T) (count : Usize) (hSrc : srcValues.length = count.val)
    (hDst : dstValues.length = count.val)
    (hAlignSrc : src.Aligned) (hAlignDst : dst.Aligned)
    (hNotNullSrc : src.NotNull (count.val * Pointee.size T))
    (hNotNullDst : dst.NotNull (count.val * Pointee.size T)) :
    ⦃ src ↦* srcValues ∗ dst ↦* dstValues ⦄ core.ptr.copy_nonoverlapping src dst count
      ⦃ src ↦* srcValues ∗ dst ↦* srcValues ⦄ :=
  core.ptr.copy_nonoverlapping.spec_raw src dst _ _ count
    (by rw [Pointee.length_flatMap_toCells, hSrc]) (by rw [Pointee.length_flatMap_toCells, hDst])
    ⟨hAlignSrc, hAlignDst, hNotNullSrc, hNotNullDst⟩

/-- `write_bytes` on byte cells. -/
theorem core.ptr.write_bytes.spec (dst : MutRawPtr T) (cells : List (Option U8)) (value : U8)
    (count : Usize) (hLen : cells.length = count.val * Pointee.size T)
    (hByte : Pointee.Cell T = U8) (hAlign : dst.Aligned)
    (hNotNull : dst.NotNull (count.val * Pointee.size T)) :
    ⦃ HeapOp.cellsAt dst.addr cells ⦄ core.ptr.write_bytes dst value count
      ⦃ HeapOp.cellsAt dst.addr (List.replicate (count.val * Pointee.size T) (some value)) ⦄ := by
  unfold core.ptr.write_bytes
  apply WP.ispec_bind (Result.require.spec ⟨hByte, hAlign, hNotNull⟩)
  · iframe
  · intro _
    apply WP.ispec_mono (HeapOp.writes.spec dst.addr cells _ (by simp [hLen])) <;> iframe

/-- A transmute decodes the cells of the value at the target type. -/
theorem core.mem.transmute.spec {A B : Type} [Pointee A] [Pointee B] (x : A)
    (hCell : Pointee.Cell A = Pointee.Cell B) (hSize : Pointee.size A = Pointee.size B)
    (value : B)
    (hValue : Pointee.ofCells (cast (congrArg (fun α => List (Option α)) hCell)
      (Pointee.toCells x)) = some value) :
    ⦃ emp ⦄ core.mem.transmute B x ⦃ r => ⌜r = value⌝ ⦄ := by
  unfold core.mem.transmute
  apply WP.ispec_bind (Pm := emp) (F := emp)
    (Qm := fun cs => ⌜cs = cast (congrArg (fun α => List (Option α)) hCell) (Pointee.toCells x)⌝)
  · apply ispec_guardedModify
    intro h _ frame hCompatible
    exact ⟨⟨hCell, hSize⟩, h, hCompatible, rfl, rfl⟩
  · iframe
  · intro cs
    iintro
    subst_vars
    apply WP.ispec_mono (Pointee.decode.spec hValue (P := emp)) <;> iframe

@[step]
theorem core.ptr.drop_in_place.spec (p : MutRawPtr T) (value : T)
    (hAlign : p.Aligned) :
    ⦃ p ↦ value ⦄ core.ptr.drop_in_place p ⦃ p ↦? none ⦄ := by
  unfold core.ptr.drop_in_place
  apply WP.ispec_bind (RawPtr.read.spec p value hAlign)
  · iframe
  · intro _
    apply WP.ispec_mono (HeapOp.writes.spec p.addr (Pointee.toCells value) _
      (by rw [Pointee.length_optCells, Pointee.Lawful.length_toCells])) <;> iframe

/-! ### Undefined behaviors rejected by the model -/

namespace RawPtr

theorem read.fails_misaligned (q : RawPtr T M) (hNot : ¬ q.Aligned) {P : IPre} :
    ifails P q.read :=
  ifails_bind_left (Result.require.fails hNot)

theorem write.fails_misaligned (q : MutRawPtr T) (value : T) (hNot : ¬ q.Aligned) {P : IPre} :
    ifails P (MutRawPtr.write q value) :=
  ifails_bind_left (Result.require.fails hNot)

/-- Accessing a zero-sized value through the null pointer fails (when some cells are accessed,
the access fails since the allocation `0` is never allocated). -/
theorem read_unaligned.fails_null (q : RawPtr T M) (hNull : q.base = 0)
    (hSize : Pointee.size T = 0) {P : IPre} : ifails P q.read_unaligned :=
  ifails_bind_left (Result.require.fails (by simp [hNull, hSize]))

theorem write_unaligned.fails_null (q : MutRawPtr T) (value : T) (hNull : q.base = 0)
    (hSize : Pointee.size T = 0) {P : IPre} : ifails P (MutRawPtr.write_unaligned q value) :=
  ifails_bind_left (Result.require.fails (by simp [hNull, hSize]))

/-- Pointer arithmetic over cells which are not cells of the pointee fails: it would count cells
of another size (e.g. bytes for a pointer to a typed value). -/
theorem add.fails_cells {α : Type} (q : RawPtr T M) (cells : List (Option α)) (count : Usize)
    (hNe : α ≠ Pointee.Cell T) (hLen : 0 < cells.length)
    (hCount : 0 < count.val * Pointee.size T) :
    ifails (HeapOp.cellsAt q.addr cells) (q.add count) := by
  apply ifails_guardedModify
  intro h hCells h' hSub hPre
  exact hNe (Heap.contains_unique
    (HeapOp.contains_of_cellsAt (i := 0) (IProp.up_closed _ hCells hSub) hLen) (hPre 0 hCount))

/-- `offset_from` over cells which are not cells of the pointee fails. -/
theorem offset_from.fails_cells {α : Type} (p : RawPtr T M) (origin : RawPtr T M')
    (cells : List (Option α)) (hNe : α ≠ Pointee.Cell T) (hLen : 0 < cells.length)
    (hDist : p.offset ≠ origin.offset) :
    ifails (HeapOp.cellsAt (p.base, min p.offset origin.offset) cells) (p.offset_from origin) := by
  apply ifails_guardedModify
  intro h hCells h' hSub hPre
  exact hNe (Heap.contains_unique
    (HeapOp.contains_of_cellsAt (i := 0) (IProp.up_closed _ hCells hSub) hLen)
    (hPre.2.2.2.2.1 0 (by omega)))

/-- `write_bytes` fails unless the cells of the pointee are bytes, and the pointer is aligned (and
not null, even if no byte is written). -/
theorem _root_.Aeneas.Std.core.ptr.write_bytes.fails (dst : MutRawPtr T) (value : U8)
    (count : Usize)
    (hNot : ¬ (Pointee.Cell T = U8 ∧ dst.Aligned ∧ dst.NotNull (count.val * Pointee.size T)))
    {P : IPre} :
    ifails P (core.ptr.write_bytes dst value count) :=
  ifails_bind_left (Result.require.fails hNot)

/-- Reading cells which hold no value of the pointee (uninitialized cells, invalid bytes...)
fails. -/
theorem read_unaligned.fails_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (hLen : cells.length = Pointee.size T) (hNone : Pointee.ofCells cells = none) :
    ifails (q ↦# cells) q.read_unaligned := by
  unfold RawPtr.read_unaligned
  apply ifails_require_bind
  rw [← hLen]
  exact ifails_bind (HeapOp.reads.spec q.addr cells) fun cs =>
    ifails_ipure fun h => by subst h; exact Pointee.decode.fails hNone

theorem read.fails_cells (q : RawPtr T M) (cells : List (Option (Pointee.Cell T)))
    (hLen : cells.length = Pointee.size T) (hNone : Pointee.ofCells cells = none) :
    ifails (q ↦# cells) q.read :=
  ifails_require_bind (read_unaligned.fails_cells q cells hLen hNone)

/-- Reading uninitialized memory fails. -/
theorem read.fails_uninit [Pointee.UninitInvalid T] (q : RawPtr T M) : ifails (q ↦? none) q.read :=
  read.fails_cells q _ (by simp) Pointee.UninitInvalid.ofCells_uninit

/-- Reading a dead cell (freed, or moved out by a borrow) fails. -/
theorem read.fails_dead (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) : ifails (q ↦† 1) q.read := by
  obtain ⟨n, hn⟩ : ∃ n, Pointee.size T = n + 1 := ⟨Pointee.size T - 1, by omega⟩
  rw [pointsToDead_one, hn, HeapOp.deadAt_succ]
  apply ifails_require_bind
  unfold RawPtr.read_unaligned
  apply ifails_require_bind
  rw [hn]
  exact ifails_bind_left (ifails_mono (sep_elim_right _ _) (HeapOp.reads.fails_dead _ _ _ (by omega)))

/-- Moving a value out of a dead cell (freed, or moved out by a borrow) fails. -/
theorem take.fails_dead (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) : ifails (q ↦† 1) q.take := by
  obtain ⟨n, hn⟩ : ∃ n, Pointee.size T = n + 1 := ⟨Pointee.size T - 1, by omega⟩
  rw [pointsToDead_one, hn, HeapOp.deadAt_succ]
  unfold RawPtr.take
  rw [hn]
  exact ifails_bind_left (ifails_mono (sep_elim_right _ _) (HeapOp.kills.fails_dead _ _ _ (by omega)))

/-- Borrowing a value which is already borrowed mutably (its cells are dead) fails. -/
theorem as_mut_unchecked.fails_dead (q : MutRawPtr T) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) q.as_mut_unchecked :=
  ifails_require_bind (ifails_bind_left (take.fails_dead q hSize))

/-- Borrowing a value which is already borrowed (its cells are dead) fails. -/
theorem as_ref_unchecked.fails_dead (q : RawPtr T M) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) q.as_ref_unchecked :=
  ifails_require_bind (ifails_bind_left (take.fails_dead q hSize))

end RawPtr

/-- Double free, or use of a pointer freed by `Box::from_raw`: freeing dead cells fails. -/
theorem alloc.boxed.Box.from_raw.fails_dead (q : MutRawPtr T) (hSize : Pointee.size T ≠ 0) :
    ifails (q ↦† 1) (alloc.boxed.Box.from_raw q) :=
  ifails_bind_check (RawPtr.take.fails_dead q hSize)

/-- Freeing a pointer which does not come from a box fails: its cells are followed by the dead end
marker of a borrow view (`as_mut_ptr`, `from_mut`, ...), not the end marker of a box. -/
theorem alloc.boxed.Box.from_raw.fails_view (q : MutRawPtr T) :
    ifails (owns (Heap.endMarker (q.addr.add (Pointee.size T)))) (alloc.boxed.Box.from_raw q) := by
  apply ifails_bind_left
  apply ifails_guardedModify
  intro h hDead h' hSub hPre
  exact Heap.Sub.not_isBoxEnd (hDead.trans hSub) hPre

/-- Freeing a pointer past the cells of a box (an interior pointer) fails: it points to the end
marker of the box. -/
theorem alloc.boxed.Box.from_raw.fails_past_box (q : MutRawPtr T) (hSize : Pointee.size T ≠ 0) :
    ifails q.boxed (alloc.boxed.Box.from_raw (q.shift 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, Pointee.size T = n + 1 := ⟨Pointee.size T - 1, by omega⟩
  apply ifails_bind_check
  unfold RawPtr.take
  rw [hn, HeapOp.kills]
  apply ifails_bind_left
  apply ifails_bind_left
  apply ifails_guardedModify
  intro h hBoxed h' hSub hPre
  have hAddr : (RawPtr.shift q 1).addr = q.addr.add (Pointee.size T) := by
    simp [RawPtr.addr_shift]
  rw [hAddr] at hPre
  exact Heap.Sub.not_contains (α := Pointee.Cell T) (s := .boxEnd) (hBoxed.trans hSub) (by simp) hPre

theorem core.ptr.from_mut.spec_view (value : T) :
    ⦃ emp ⦄ core.ptr.from_mut value
      ⦃ (q, back) => ⌜back = core.ptr.end_from_mut q⌝ ∗ q ↦ value ∗
        owns (Heap.endMarker (q.addr.add (Pointee.size T)))⦄ := by
  unfold core.ptr.from_mut RawPtr.materialize
  apply WP.ispec_bind (RawPtr.allocate.spec (M := .Mut) .dead [value])
  · iframe
  · intro q
    apply (ispec_ok _).2
    simp only [← RawPtr.pointsTo_eq_range, List.length_singleton, Nat.one_mul]
    iframe

end Specs

end Aeneas.Std
