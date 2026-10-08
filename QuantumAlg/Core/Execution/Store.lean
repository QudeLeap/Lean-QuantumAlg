/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ClassicalOp
public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Algorithm.ClassicalOp.Finite
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Classical cells of the instruction interpreter

The cells contain only finite classical values. Quantum entries contribute
presence markers: their complete joint state is held separately by
`ExecutionState`, including all copies and correlations. Reading or writing a
classical result cannot inspect, replace, or discard a quantum state.

Every access follows the existing context-indexed storage reference. The
read-after-write law is used by Z measurement to store the observed value and
by later conditional instructions to read that same value.
-/

namespace QuantumAlg.Execution

private def CellValue {kind : ProblemKind} : RuntimeEntry kind → Type
  | .storage _key _role shape => CShape.Value shape
  | .borrowedLayout _key _layout => Unit
  | .suppliedLayout _key _layout => Unit
  | .ownedLayout _key _layout => Unit
  | .ownedCopies _key _bank => Unit

private def Cells {kind : ProblemKind} : List (RuntimeEntry kind) → Type
  | [] => Unit
  | head :: tail => CellValue head × Cells tail

private noncomputable instance cellFintype {kind : ProblemKind}
    (entry : RuntimeEntry kind) : Fintype (CellValue entry) := by
  cases entry <;> dsimp [CellValue] <;> infer_instance

@[instance_reducible]
private noncomputable def cellsFintype {kind : ProblemKind} :
    (entries : List (RuntimeEntry kind)) → Fintype (Cells entries)
  | [] => inferInstanceAs (Fintype Unit)
  | head :: tail =>
      letI := cellsFintype tail
      inferInstanceAs (Fintype (CellValue head × Cells tail))

namespace Cells

private def ofValues {kind : ProblemKind} : (entries : List (RuntimeEntry kind)) →
    (∀ entry, entry ∈ entries → CellValue entry) → Cells entries
  | [], _values => ()
  | head :: tail, values =>
      (values head (.head _), ofValues tail (fun entry present =>
        values entry (.tail head present)))

private def read {kind : ProblemKind} {target : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} (cells : Cells entries)
    (slot : RuntimeEntrySlot target entries) : CellValue target :=
  match slot with
  | .here => cells.1
  | .there next => read cells.2 next

private theorem read_ofValues {kind : ProblemKind} {target : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)}
    (values : ∀ entry, entry ∈ entries → CellValue entry)
    (slot : RuntimeEntrySlot target entries) :
    read (ofValues entries values) slot = values target slot.toMem := by
  induction slot with
  | here => rfl
  | there next ih => exact ih (fun entry present => values entry (.tail _ present))

private def write {kind : ProblemKind} {target : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} (cells : Cells entries)
    (slot : RuntimeEntrySlot target entries) (value : CellValue target) : Cells entries :=
  match slot with
  | .here => (value, cells.2)
  | .there next => (cells.1, write cells.2 next value)

private theorem read_write_same {kind : ProblemKind} {target : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} (cells : Cells entries)
    (slot : RuntimeEntrySlot target entries) (value : CellValue target) :
    read (write cells slot value) slot = value := by
  induction slot with
  | here => rfl
  | there next ih => exact ih cells.2

private theorem read_write_other {kind : ProblemKind}
    {written observed : RuntimeEntry kind} {entries : List (RuntimeEntry kind)}
    (cells : Cells entries) (output : RuntimeEntrySlot written entries)
    (input : RuntimeEntrySlot observed entries) (value : CellValue written)
    (different : written.key ≠ observed.key) :
    read (write cells output value) input = read cells input := by
  induction output with
  | here =>
      cases input with
      | here => exact False.elim (different rfl)
      | there next => rfl
  | there next ih =>
      cases input with
      | here => rfl
      | there observed => exact ih cells.2 observed

end Cells

/-- Finite classical values indexed by the exact live context. This
store contains no quantum vectors or independently sampled copy states. -/
-- Declaration-scoped exception: the pinned structureInType linter reconstructs
-- a public projection name for the private data field and fails to find it.
-- The field contains actual classical values, so this carrier belongs in Type.
@[nolint structureInType]
public structure Store {kind : ProblemKind} (ctx : RuntimeCtx kind) where
  private mk ::
  /-- Exactly the context-indexed classical cells and quantum presence markers. -/
  private cells : Cells ctx.entries

@[instance_reducible]
private noncomputable def finiteStore {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    Fintype (Store ctx) := by
  letI := cellsFintype ctx.entries
  exact Fintype.ofEquiv (Cells ctx.entries)
    { toFun := Store.mk
      invFun := Store.cells
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[no_expose]
public noncomputable instance storeFintype {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    Fintype (Store ctx) := finiteStore ctx

namespace Store

private def initializedCell {kind : ProblemKind} {entries : List (RuntimeEntry kind)}
    (values : ∀ key role shape,
      RuntimeEntry.storage key role shape ∈ entries → CShape.Value shape) :
    (entry : RuntimeEntry kind) → entry ∈ entries → CellValue entry
  | .storage key role shape, present => values key role shape present
  | .borrowedLayout _key _layout, _present => ()
  | .suppliedLayout _key _layout, _present => ()
  | .ownedLayout _key _layout, _present => ()
  | .ownedCopies _key _bank, _present => ()

/-- Initialize the existing classical cells with values of their exact stored shapes.
Quantum entries receive only their automatic presence markers; this does not allocate
storage or initialize a quantum state. -/
public def ofValues {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (values : ∀ key role shape,
      RuntimeEntry.storage key role shape ∈ ctx.entries → CShape.Value shape) : Store ctx :=
  ⟨Cells.ofValues ctx.entries (initializedCell values)⟩

/-- The empty context has one empty classical store. -/
public def empty {kind : ProblemKind} : Store (RuntimeCtx.empty : RuntimeCtx kind) := ⟨()⟩

/-- Read a typed reference from the actual classical cells. -/
public def read {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (store : Store ctx) : CInputRef ctx shape → CShape.Value shape
  | .storage ref => Cells.read store.cells ref.slot
  | .product first second => .product (read store first) (read store second)
  | .fixedVector entries => .fixedVector fun index => read store (entries index)
  | .first input => (read store input).first
  | .second input => (read store input).second
  | .vectorGet input index => (read store input).get index
  | .bitsGet input index => (read store input).bitGet index
  | .wordBitGet input index => (read store input).wordBitGet index

/-- Every live classical reference reads precisely its supplied initial value. -/
public theorem read_ofValues {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (values : ∀ key role shape,
      RuntimeEntry.storage key role shape ∈ ctx.entries → CShape.Value shape)
    (ref : CStorageRef ctx shape) :
    (ofValues ctx values).read (.storage ref) = values ref.key ref.role shape ref.present :=
  Cells.read_ofValues (initializedCell values) ref.slot

/-- Update only the writable cell named by the typed output reference. -/
public def write {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (store : Store ctx) (output : CWriteRef ctx shape) (value : CShape.Value shape) : Store ctx :=
  ⟨Cells.write store.cells output.toCStorageRef.slot value⟩

/-- A later read of the written reference obtains exactly the value stored. -/
public theorem read_write_same {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (store : Store ctx) (output : CWriteRef ctx shape) (value : CShape.Value shape) :
    (store.write output value).read (.storage output.toCStorageRef) = value :=
  Cells.read_write_same store.cells output.toCStorageRef.slot value

/-- Writing a measured or computed result leaves every differently named
classical cell unchanged, even when its stored shape is different. -/
public theorem read_write_other {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {writtenShape observedShape : CShape} (store : Store ctx)
    (output : CWriteRef ctx writtenShape) (input : CStorageRef ctx observedShape)
    (value : CShape.Value writtenShape) (different : output.key ≠ input.key) :
    (store.write output value).read (.storage input) = store.read (.storage input) :=
  Cells.read_write_other store.cells output.toCStorageRef.slot input.slot value different

/-- Execute one atomic classical instruction by reading and writing its actual references. -/
public def applyOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {input output : CShape}
    (store : Store ctx) (op : ClassicalOp input output ctx ctx) : Store ctx :=
  store.write op.outputRef (op.eval (store.read op.inputRef))

/-- The output cell contains precisely the result computed from the pre-step store. -/
public theorem read_applyOp_output {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {input output : CShape} (store : Store ctx) (op : ClassicalOp input output ctx ctx) :
    (store.applyOp op).read (.storage op.outputRef.toCStorageRef) =
      op.eval (store.read op.inputRef) :=
  read_write_same store op.outputRef _

/-- Allocate the exact classical workspace head with its canonical initial encoding. -/
public def pushWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Store (ctx.addWorkspace key shape fresh) :=
  ⟨(CShape.initialValue shape, store.cells)⟩

/-- Release the exact workspace head; all older cells and quantum presence markers remain. -/
public def popWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addWorkspace key shape fresh)) : Store ctx :=
  ⟨store.cells.2⟩

/-- Allocate a retained classical result cell initialized according to its declared shape. -/
public def pushRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Store (ctx.addRetained key shape fresh) :=
  ⟨(CShape.initialValue shape, store.cells)⟩

/-- Preparing physical systems adds only their presence marker to the classical store.
The quantum state itself is extended by the preparation interpreter. -/
public def pushOwnedLayout {ctx : RuntimeCtx .quantum} (store : Store ctx)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    Store (ctx.addOwnedLayout key layout fresh disjoint) :=
  ⟨((), store.cells)⟩

private theorem popWorkspace_pushWorkspace_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    popWorkspace key shape fresh (store.pushWorkspace key shape fresh) = store := rfl

/-- An untouched workspace allocation releases back to the identical classical store. -/
public theorem popWorkspace_pushWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    popWorkspace key shape fresh (store.pushWorkspace key shape fresh) = store :=
  popWorkspace_pushWorkspace_eq store key shape fresh

private theorem read_pushRetained_head_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (store.pushRetained key shape fresh).read
      (.storage (CStorageRef.retainedHead ctx key shape fresh)) = CShape.initialValue shape := rfl

/-- A freshly allocated retained cell contains the shape's initial encoding. -/
public theorem read_pushRetained_head {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (store.pushRetained key shape fresh).read
      (.storage (CStorageRef.retainedHead ctx key shape fresh)) = CShape.initialValue shape :=
  read_pushRetained_head_eq store key shape fresh

/-- Allocating retained storage preserves every previously readable classical value. -/
public theorem read_pushRetained_underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {observed : CShape} (input : CInputRef ctx observed) :
    (store.pushRetained key shape fresh).read (input.underRetained key shape fresh) =
      store.read input := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

end Store

end QuantumAlg.Execution
