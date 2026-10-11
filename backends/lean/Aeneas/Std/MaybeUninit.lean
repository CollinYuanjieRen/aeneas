module
public import Aeneas.Std.RawPtr
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Alloc
@[expose] public section

/-! # `core::mem::MaybeUninit`

A `MaybeUninit<T>` is either uninitialized or holds a value of `T`. In the heap, it is stored in a
cell of `T`, uninitialized if the value is (`Pointee` instance): a pointer to a `MaybeUninit<T>`
can be cast to a pointer to `T` (and back), and reading uninitialized memory at type `T` fails.

Limitation: generic code instantiated with `MaybeUninit<U>` uses the default `Pointee` instance
(cells of type `MaybeUninit U`), so its accesses to the cells of `MaybeUninit<U>` values always
fail (see `Pointee`). `MaybeUninit<MaybeUninit<U>>` is stored in cells of `MaybeUninit U`. -/

open Aeneas SepLogic

namespace Aeneas.Std

open Result WP

/-! ### START Trusted definitions -/

@[rust_type "core::mem::maybe_uninit::MaybeUninit" (body := .opaque)]
inductive MaybeUninit (T : Type u) where
  | uninit
  | init (value : T)

def MaybeUninit.toOption {T : Type u} : MaybeUninit T → Option T
  | .uninit => none
  | .init value => some value

def MaybeUninit.ofOption {T : Type u} : Option T → MaybeUninit T
  | none => .uninit
  | some value => .init value

/-- Decodes the cells of a `MaybeUninit<T>`: a value of `T`, or uninitialized cells. -/
def MaybeUninit.ofCells {T : Type} [Pointee T] (cells : List (Option (Pointee.Cell T))) :
    Option (MaybeUninit T) :=
  match Pointee.ofCells (T := T) cells with
  | some value => some (.init value)
  | none => if cells.all Option.isNone then some .uninit else none

/-- The cells of a `MaybeUninit<T>` are the cells of `T`, uninitialized if the value is. -/
instance MaybeUninit.instPointee {T : Type} [Pointee T] : Pointee (MaybeUninit T) where
  Cell := Pointee.Cell T
  size := Pointee.size T
  align := Pointee.align T
  nonZero := Pointee.nonZero T
  toCells m := Pointee.optCells m.toOption
  ofCells := MaybeUninit.ofCells

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::uninit"]
def core.mem.maybe_uninit.MaybeUninit.uninit (T : Type u) : Result (MaybeUninit T) :=
  ok .uninit

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::new"]
def core.mem.maybe_uninit.MaybeUninit.new {T : Type u} (value : T) : Result (MaybeUninit T) :=
  ok (.init value)

/-- Initializes the value; the returned mutable borrow gives access to it. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::write"]
def core.mem.maybe_uninit.MaybeUninit.write {T : Type u} (_ : MaybeUninit T) (value : T) :
    Result (T × (T → MaybeUninit T)) :=
  ok (value, .init)

/-- Fails if the value is uninitialized. -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::assume_init"]
def core.mem.maybe_uninit.MaybeUninit.assume_init {T : Type u} : MaybeUninit T → Result T
  | .uninit => fail .undef
  | .init value => ok value

/-- Not a Rust function: end of the shared borrow of `as_ptr`: the cell must still hold the
value (writing through a const pointer cast to mut is UB), and is killed. -/
def core.mem.maybe_uninit.MaybeUninit.end_as_ptr {T : Type} [Pointee T] (m : MaybeUninit T)
    (p : ConstRawPtr T) : Result Unit := do
  let value ← (p.retype : ConstRawPtr (MaybeUninit T)).take
  Result.require (value = m)

/-- Not a Rust function: end of the mutable borrow of `as_mut_ptr`: the cell is killed and its
content, initialized or not, is the new value. -/
def core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr {T : Type} [Pointee T] (p : MutRawPtr T) :
    Result (MaybeUninit T) :=
  (p.retype : MutRawPtr (MaybeUninit T)).take

/-- The pointer points to a fresh cell holding the value, uninitialized if the value is; the back
computation runs when the borrow ends (`statefulLifetimes`). -/
@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_ptr"
  (statefulLifetimes := [0])]
def core.mem.maybe_uninit.MaybeUninit.as_ptr {T : Type} [Pointee T] (m : MaybeUninit T) :
    Result (ConstRawPtr T × Result Unit) :=
  Aeneas.Std.bind (RawPtr.materialize [m] : Result (ConstRawPtr (MaybeUninit T))) fun p =>
    .ok (p.retype, core.mem.maybe_uninit.MaybeUninit.end_as_ptr m p.retype)

@[rust_fun "core::mem::maybe_uninit::{core::mem::maybe_uninit::MaybeUninit<@T>}::as_mut_ptr"
  (statefulLifetimes := [0])]
def core.mem.maybe_uninit.MaybeUninit.as_mut_ptr {T : Type} [Pointee T] (m : MaybeUninit T) :
    Result (MutRawPtr T × Result (MaybeUninit T)) :=
  Aeneas.Std.bind (RawPtr.materialize [m] : Result (MutRawPtr (MaybeUninit T))) fun p =>
    .ok (p.retype, core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr p.retype)

@[rust_fun "core::mem::maybe_uninit::{core::clone::Clone<core::mem::maybe_uninit::MaybeUninit<@T>>}::clone"]
def core.mem.maybe_uninit.CloneMaybeUninit.clone {T : Type u} (_ : core.marker.Copy T)
    (m : MaybeUninit T) : Result (MaybeUninit T) :=
  ok m

@[reducible, rust_trait_impl "core::clone::Clone<core::mem::maybe_uninit::MaybeUninit<@T>>"]
def core.clone.CloneMaybeUninit {T : Type u} (copyInst : core.marker.Copy T) :
    core.clone.Clone (MaybeUninit T) := {
  clone := core.mem.maybe_uninit.CloneMaybeUninit.clone copyInst
}

@[reducible, rust_trait_impl "core::marker::Copy<core::mem::maybe_uninit::MaybeUninit<@T>>"]
def core.marker.CopyMaybeUninit {T : Type u} (copyInst : core.marker.Copy T) :
    core.marker.Copy (MaybeUninit T) := {
  cloneInst := core.clone.CloneMaybeUninit copyInst
}

/-- `Box::new_uninit`: a box is its content. -/
@[rust_fun "alloc::boxed::{Box<@T>}::new_uninit"]
def alloc.boxed.Box.new_uninit (T : Type u) : Result (MaybeUninit T) :=
  ok .uninit

@[rust_fun "alloc::boxed::{Box<core::mem::maybe_uninit::MaybeUninit<@T>>}::assume_init"
  (keepParams := [true, false])]
def alloc.boxed.BoxMaybeUninit.assume_init {T : Type u} (b : MaybeUninit T) : Result T :=
  core.mem.maybe_uninit.MaybeUninit.assume_init b

/-! ### END Trusted definitions -/

namespace MaybeUninit

@[simp] theorem toOption_uninit {T : Type u} : (uninit : MaybeUninit T).toOption = none := rfl
@[simp] theorem toOption_init {T : Type u} (v : T) : (init v).toOption = some v := rfl
@[simp] theorem ofOption_none {T : Type u} : ofOption (none : Option T) = uninit := rfl
@[simp] theorem ofOption_some {T : Type u} (v : T) : ofOption (some v) = init v := rfl
@[simp] theorem toOption_ofOption {T : Type u} (o : Option T) : (ofOption o).toOption = o := by
  cases o <;> rfl
@[simp] theorem ofOption_toOption {T : Type u} (m : MaybeUninit T) : ofOption m.toOption = m := by
  cases m <;> rfl

end MaybeUninit

instance MaybeUninit.instLawful {T : Type} [Pointee T] [Pointee.Lawful T] [Pointee.UninitInvalid T] :
    Pointee.Lawful (MaybeUninit T) where
  length_toCells m := Pointee.length_optCells m.toOption
  ofCells_toCells m := by
    cases m with
    | uninit =>
      show MaybeUninit.ofCells (List.replicate (Pointee.size T) none) = some .uninit
      unfold MaybeUninit.ofCells
      rw [Pointee.UninitInvalid.ofCells_uninit]
      simp
    | init v =>
      show MaybeUninit.ofCells (Pointee.toCells v) = _
      unfold MaybeUninit.ofCells
      rw [Pointee.Lawful.ofCells_toCells]
  align_pos := (Pointee.Lawful.align_pos : 0 < Pointee.align T)
  align_dvd_size := (Pointee.Lawful.align_dvd_size : Pointee.align T ∣ Pointee.size T)

namespace MaybeUninit

@[simp] theorem toCells_eq {T : Type} [Pointee T] (m : MaybeUninit T) :
    Pointee.toCells m = Pointee.optCells m.toOption := rfl

@[simp] theorem size_eq {T : Type} [Pointee T] : Pointee.size (MaybeUninit T) = Pointee.size T := rfl

@[simp] theorem align_eq {T : Type} [Pointee T] : Pointee.align (MaybeUninit T) = Pointee.align T :=
  rfl

theorem ofCells_optCells {T : Type} [Pointee T] [Pointee.Lawful T] [Pointee.UninitInvalid T]
    (content : Option T) :
    (Pointee.ofCells (Pointee.optCells (T := T) content) : Option (MaybeUninit T)) =
      some (ofOption content) := by
  have h := Pointee.Lawful.ofCells_toCells (ofOption content)
  rwa [toCells_eq, toOption_ofOption] at h

end MaybeUninit

section

variable {T : Type} [Pointee T] {M : Mutability}

/-- A pointer to `MaybeUninit<T>` owns cells of `T`. -/
theorem MaybeUninit.pointsTo_eq (q : RawPtr (MaybeUninit T) M) (m : MaybeUninit T) :
    (q ↦ m) = ((q.retype : RawPtr T M) ↦? m.toOption) := rfl

theorem MaybeUninit.pointsToRange_eq (q : RawPtr (MaybeUninit T) M) (ms : List (MaybeUninit T)) :
    (q ↦* ms) = ((q.cast T) ↦*? ms.map MaybeUninit.toOption) := by
  rw [RawPtr.pointsToOpts_eq, List.flatMap_map]
  rfl

@[simp] theorem MaybeUninit.pointsToCells_retype (q : RawPtr (MaybeUninit T) M)
    (cells : List (Option (Pointee.Cell T))) :
    ((q.retype : RawPtr T M') ↦# cells) = (q ↦# cells) := rfl

@[simp] theorem MaybeUninit.pointsToCells_retype' (q : RawPtr T M)
    (cells : List (Option (Pointee.Cell T))) :
    ((q.retype : RawPtr (MaybeUninit T) M') ↦# cells) = (q ↦# cells) := rfl

@[simp] theorem MaybeUninit.aligned_retype (q : RawPtr (MaybeUninit T) M) :
    (q.retype : RawPtr T M').Aligned ↔ q.Aligned := Iff.rfl

@[simp] theorem MaybeUninit.aligned_retype' (q : RawPtr T M) :
    (q.retype : RawPtr (MaybeUninit T) M').Aligned ↔ q.Aligned := Iff.rfl

@[simp] theorem MaybeUninit.shift_cast (q : RawPtr (MaybeUninit T) M) (i : Nat) :
    (q.cast T).shift i = (q.shift i).cast T := rfl

variable [Pointee.Lawful T]

/-- A buffer of `MaybeUninit<T>` whose first cells are initialized with `vs`. -/
theorem MaybeUninit.pointsToRange_init (q : RawPtr (MaybeUninit T) M) (vs : List T)
    (ms : List (MaybeUninit T)) :
    (q ↦* (vs.map .init ++ ms)) =
      iprop((q.cast T) ↦* vs ∗ ((q.cast T).shift vs.length) ↦*? ms.map MaybeUninit.toOption) := by
  rw [MaybeUninit.pointsToRange_eq, List.map_append, List.map_map,
    show MaybeUninit.toOption ∘ MaybeUninit.init = (some : T → Option T) from rfl,
    RawPtr.pointsToOpts_append, List.length_map, ← RawPtr.pointsToRange_eq]

/-- `add` on a pointer to `MaybeUninit<T>` cast to a pointer to `T`. -/
theorem MaybeUninit.add_cast.spec (q : RawPtr (MaybeUninit T) M) (ms : List (MaybeUninit T))
    (count : Usize) (h : count.val ≤ ms.length) :
    ⦃ q ↦* ms ⦄ (q.cast T).add count
      ⦃ r => ⌜r = (q.cast T).shift count.val⌝ ∗ q ↦* ms ⦄ := by
  rw [MaybeUninit.pointsToRange_eq]
  exact RawPtr.add.spec_cells (q.retype : RawPtr T M) (ms.map MaybeUninit.toOption) count (by simpa)

/-- Writing through a pointer to `MaybeUninit<T>` cast to a pointer to `T` initializes it. -/
@[step]
theorem MaybeUninit.write_cast.spec (q : MutRawPtr (MaybeUninit T)) (m : MaybeUninit T) (v : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ m ⦄ MutRawPtr.write (q.cast T) v ⦃ q ↦ MaybeUninit.init v ⦄ :=
  MutRawPtr.write.spec_opt (q.retype : MutRawPtr T) m.toOption v hAlign

theorem MaybeUninit.write_cast.spec_range (q : MutRawPtr (MaybeUninit T))
    (ms : List (MaybeUninit T)) (i : Nat) (v : T) (hIndex : i < ms.length)
    (hAlign : q.Aligned) :
    ⦃ q ↦* ms ⦄ MutRawPtr.write ((q.cast T).shift i) v ⦃ q ↦* ms.set i (.init v) ⦄ := by
  rw [MaybeUninit.pointsToRange_eq, MaybeUninit.pointsToRange_eq, List.map_set]
  exact MutRawPtr.write.spec_cells (q.retype : MutRawPtr T) _ i v (by simpa using hIndex) hAlign

/-- Reading through a pointer to `MaybeUninit<T>` cast to a pointer to `T`. -/
@[step]
theorem MaybeUninit.read_cast.spec (q : RawPtr (MaybeUninit T) M) (v : T)
    (hAlign : q.Aligned) :
    ⦃ q ↦ MaybeUninit.init v ⦄ RawPtr.read (q.cast T)
      ⦃ r => ⌜r = v⌝ ∗ q ↦ MaybeUninit.init v ⦄ :=
  RawPtr.read.spec (q.retype : RawPtr T M) v hAlign

/-- Reading uninitialized memory through a pointer to `MaybeUninit<T>` cast to a pointer to `T`
fails. -/
theorem MaybeUninit.read_cast.fails [Pointee.UninitInvalid T] (q : RawPtr (MaybeUninit T) M) :
    ifails (q ↦ MaybeUninit.uninit) (RawPtr.read (q.cast T)) :=
  RawPtr.read.fails_uninit (q.retype : RawPtr T M)

end

section

variable {T : Type}

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.uninit.spec :
    core.mem.maybe_uninit.MaybeUninit.uninit T ⦃ m => m = .uninit ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.uninit]

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.new.spec (value : T) :
    core.mem.maybe_uninit.MaybeUninit.new value ⦃ m => m = .init value ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.new]

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.write.spec (m : MaybeUninit T) (value : T) :
    core.mem.maybe_uninit.MaybeUninit.write m value
      ⦃ v back => v = value ∧ back = .init ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.write]

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.assume_init.spec (value : T) :
    core.mem.maybe_uninit.MaybeUninit.assume_init (.init value) ⦃ v => v = value ⦄ := by
  simp [core.mem.maybe_uninit.MaybeUninit.assume_init]

@[step]
theorem alloc.boxed.Box.new_uninit.spec :
    alloc.boxed.Box.new_uninit T ⦃ m => m = .uninit ⦄ := by
  simp [alloc.boxed.Box.new_uninit]

@[step]
theorem alloc.boxed.BoxMaybeUninit.assume_init.spec (value : T) :
    alloc.boxed.BoxMaybeUninit.assume_init (.init value) ⦃ v => v = value ⦄ := by
  simp [alloc.boxed.BoxMaybeUninit.assume_init, core.mem.maybe_uninit.MaybeUninit.assume_init]

/-- `assume_init` on an uninitialized value fails. -/
theorem core.mem.maybe_uninit.MaybeUninit.assume_init.fails_uninit {P : IPre} :
    ifails P (core.mem.maybe_uninit.MaybeUninit.assume_init (.uninit : MaybeUninit T)) :=
  ifails_fail _

end

section

variable {T : Type} [Pointee T] [Pointee.Lawful T] [Pointee.UninitInvalid T]

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.as_mut_ptr.spec (m : MaybeUninit T) :
    ⦃ emp ⦄ core.mem.maybe_uninit.MaybeUninit.as_mut_ptr m
      ⦃ (p, back) => ⌜back = core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr p⌝ ∗ ⌜p.Aligned⌝ ∗
        p ↦? m.toOption ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.as_mut_ptr
  apply WP.ispec_bind (RawPtr.materialize.spec (M := .Mut) [m])
  · iframe
  · intro p
    apply (ispec_ok _).2
    rw [← RawPtr.pointsTo_eq_range, MaybeUninit.pointsTo_eq]
    iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr.spec (p : MutRawPtr T)
    (content : Option T) :
    ⦃ p ↦? content ⦄ core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr p
      ⦃ m => ⌜m = MaybeUninit.ofOption content⌝ ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.end_as_mut_ptr
  apply WP.ispec_mono (RawPtr.take.spec_raw (p.retype : MutRawPtr (MaybeUninit T))
    (Pointee.optCells (T := T) content) (MaybeUninit.ofOption content) (Pointee.length_optCells content)
    (MaybeUninit.ofCells_optCells content)) <;> iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.as_ptr.spec (m : MaybeUninit T) :
    ⦃ emp ⦄ core.mem.maybe_uninit.MaybeUninit.as_ptr m
      ⦃ (p, back) => ⌜back = core.mem.maybe_uninit.MaybeUninit.end_as_ptr m p⌝ ∗ ⌜p.Aligned⌝ ∗
        p ↦? m.toOption ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.as_ptr
  apply WP.ispec_bind (RawPtr.materialize.spec (M := .Const) [m])
  · iframe
  · intro p
    apply (ispec_ok _).2
    rw [← RawPtr.pointsTo_eq_range, MaybeUninit.pointsTo_eq]
    iframe

@[step]
theorem core.mem.maybe_uninit.MaybeUninit.end_as_ptr.spec (m : MaybeUninit T)
    (p : ConstRawPtr T) :
    ⦃ p ↦? m.toOption ⦄ core.mem.maybe_uninit.MaybeUninit.end_as_ptr m p ⦃ emp ⦄ := by
  unfold core.mem.maybe_uninit.MaybeUninit.end_as_ptr
  apply WP.ispec_bind (RawPtr.take.spec (p.retype : ConstRawPtr (MaybeUninit T)) m)
  · iframe
  · intro v
    iintro
    apply WP.ispec_mono (Result.require.spec (by assumption)) <;> iframe

end

end Aeneas.Std
