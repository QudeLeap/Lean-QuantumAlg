/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.PNat.Defs

/-!
# Kind-indexed accounting coordinates

This module fixes the closed type-level vocabulary used by the event and
live-space ledgers.  It deliberately contains no ledger order, model
conversion, capacity magnitude, or peak-space calculation.

Classical machine operations are represented by closed constructors.  In
particular there is no string-labelled `named` operation escape hatch.  Gate,
preparation, measurement, and opaque-subroutine names remain declaration
labels: their accounting role is fixed by the surrounding `Event`
constructor.
-/

section

namespace QuantumAlg

/-- Whether an accounting object belongs to a classical or quantum problem. -/
public inductive ProblemKind where
  | classical
  | quantum
deriving DecidableEq

namespace Resource

/-- A stable qualified name for one declared gate capability. -/
public structure GateLabel where
  /-- Declaration family or namespace. -/
  family : String
  /-- Name within the declaration family. -/
  name : String
  /-- Structural dimensions or other natural-number declaration parameters. -/
  parameters : List Nat := []
  /-- Finite control-register dimensions decorating this gate occurrence.

  Gate control is structural metadata of the gate coordinate.  Opaque
  subroutine control is deliberately absent from `SubroutineLabel`; it has a
  separate, quantum-only normalization boundary. -/
  controlDimensions : List Nat := []
deriving DecidableEq

/-- A stable qualified name for one declared state-preparation capability. -/
public structure PreparationLabel where
  /-- Declaration family or namespace. -/
  family : String
  /-- Name within the declaration family. -/
  name : String
  /-- Structural dimensions or other natural-number declaration parameters. -/
  parameters : List Nat := []
deriving DecidableEq

/-- A stable qualified name for one declared measurement capability. -/
public structure MeasurementLabel where
  /-- Declaration family or namespace. -/
  family : String
  /-- Name within the declaration family. -/
  name : String
  /-- Structural dimensions or other natural-number declaration parameters. -/
  parameters : List Nat := []
deriving DecidableEq

/-- A stable base coordinate for one declared opaque subroutine.

Controlled quantum coordinates are intentionally not encoded here.  A
classical subroutine therefore cannot acquire quantum control data through
this base label.
-/
public structure SubroutineLabel where
  /-- Declaration family or namespace. -/
  family : String
  /-- Base capability name. -/
  name : String
  /-- Widths/dimensions that distinguish members of the declared family. -/
  parameters : List Nat := []
deriving DecidableEq

/-- One quantum use of a declared opaque subroutine.

The base declaration is shared with an uncontrolled classical use, while the
finite control-register dimensions distinguish independently budgeted quantum
capabilities.  Dimensions are stored from the innermost control layer to the
outermost one.
-/
public structure QuantumSubroutineLabel where
  /-- The declared opaque capability before quantum control is applied. -/
  base : SubroutineLabel
  /-- Control-register dimensions, ordered from inner to outer. -/
  controlDimensions : List Nat := []
deriving DecidableEq

namespace SubroutineLabel

/-- Regard one base subroutine declaration as its uncontrolled quantum
capability. -/
def quantum (label : SubroutineLabel) : QuantumSubroutineLabel :=
  { base := label }

@[simp] theorem quantum_base (label : SubroutineLabel) :
    label.quantum.base = label :=
  rfl

@[simp] theorem quantum_controlDimensions (label : SubroutineLabel) :
    label.quantum.controlDimensions = [] :=
  rfl

end SubroutineLabel

/-- Closed bit-level machine operations. -/
public inductive BitOpcode where
  | copy
  | not
  | and
  | or
  | xor
  | select
deriving DecidableEq

/-- Closed unary fixed-width word operations. -/
public inductive WordUnaryOpcode where
  | copy
  | complement
  | increment
  | decrement
  | shiftLeft
  | shiftRight
deriving DecidableEq

/-- Closed binary fixed-width word operations. -/
public inductive WordBinaryOpcode where
  | add
  | sub
  | mulLow
  | quotient
  | remainder
  | bitAnd
  | bitOr
  | bitXor
  | equal
  | lessThan
deriving DecidableEq

/-- Closed representation-only operations on raw canonical-residue encodings. -/
public inductive ResidueEncodingOpcode where
  /-- Read the raw residue encoding as an equal-width unsigned word. -/
  | unpack
  /-- Store an equal-width unsigned word as a raw residue encoding. -/
  | pack
deriving DecidableEq

/-- Closed structural operations on nominal classical encodings.

Every constructor records the dimensions fixed by its typed machine
instruction.  These labels describe representation work only; they do not
assign signed, modulus, unit, or option-validity semantics. -/
public inductive NominalEncodingOpcode where
  /-- Materialize ordered binary finite-register values as a bit string. -/
  | packFiniteBits (count : Nat)
  /-- Materialize two adjacent values as one writable product encoding. -/
  | packProduct (leftWidth rightWidth : Nat)
  /-- Store a word unchanged in the distinct bounded-signed representation. -/
  | packBoundedSignedWord (width : Nat)
  /-- Materialize a tag and fixed payload as one optional encoding. -/
  | packOption (payloadWidth : Nat)
  /-- Expose an optional encoding as one tag and fixed payload. -/
  | unpackOption (payloadWidth : Nat)
  /-- Erase the nominal unit-residue wrapper without changing its raw word. -/
  | unpackUnitResidue (width : Nat)
  /-- Expose raw point storage as one tag and two coordinate words. -/
  | unpackEllipticCurvePoint (width : Nat)
  /-- Materialize raw point storage from one tag and two coordinate words. -/
  | packEllipticCurvePoint (width : Nat)
deriving DecidableEq

/-- Closed operations on fixed-length vectors of fixed-width words. -/
public inductive VectorOpcode where
  | read
  | write
  | swap
  | rowXor
  | rowSwap
  | pivotSearch
deriving DecidableEq

/-- Closed operations on canonical residues. -/
public inductive ResidueOpcode where
  | reduce
  | add
  | sub
  | neg
  | double
  | mul
  | square
  | inverseCheck
  | divideCheck
deriving DecidableEq

/-- Closed operations on canonical elliptic-curve point encodings. -/
public inductive PointOpcode where
  | decode
  | neg
  | add
  | sub
  | double
deriving DecidableEq

/-- Closed recovery and decoding machine operations. -/
public inductive RecoveryOpcode where
  | terminalDecode
  | gcdStep
  | xgcdStep
  | continuedFractionStep
  | candidateValidate
  | retainCandidate
deriving DecidableEq

/-- Closed, dimension-indexed labels for classical execution events.

Every constructor fixes the accounting category and its structural width
parameters.  The indexed `ClassicalOp` syntax selects the exact input/output
`CShape` and corresponding event together; an event label is not a detached
semantic instruction or a caller-supplied shape claim.
-/
public inductive ClassicalOpLabel where
  | randomBits (width : Nat)
  | bit (opcode : BitOpcode)
  | wordUnary (opcode : WordUnaryOpcode) (width : Nat)
  | wordBinary (opcode : WordBinaryOpcode) (width : Nat)
  | wordResize (sourceWidth targetWidth : Nat)
  | addCarry (width : Nat)
  | subBorrow (width : Nat)
  | mulFull (leftWidth rightWidth : Nat)
  | divRem (numeratorWidth divisorWidth : Nat)
  | vector (opcode : VectorOpcode) (length elementWidth : Nat)
  | residueEncoding (opcode : ResidueEncodingOpcode) (width : Nat)
  | nominalEncoding (opcode : NominalEncodingOpcode)
  | residue (opcode : ResidueOpcode) (modulusWidth : Nat)
  | point (opcode : PointOpcode) (fieldWidth : Nat)
  | recovery (opcode : RecoveryOpcode) (width : Nat)
deriving DecidableEq

/-- Closed event coordinates admitted by a problem kind.

Both kinds admit classical work and declared classical subroutines.  Only the
quantum kind admits gates, preparations, measurements, and opaque quantum
subroutines.  Live storage is intentionally absent.
-/
public inductive Event : ProblemKind → Type where
  | classicalOperation {kind : ProblemKind} (label : ClassicalOpLabel) : Event kind
  | classicalSubroutine {kind : ProblemKind} (label : SubroutineLabel) : Event kind
  | gate (label : GateLabel) : Event .quantum
  | preparation (label : PreparationLabel) : Event .quantum
  | measurement (label : MeasurementLabel) : Event .quantum
  | quantumSubroutine (label : QuantumSubroutineLabel) : Event .quantum
deriving DecidableEq

namespace Event

/-- Embed a classical coordinate in the quantum event family without
relabeling or aggregation. -/
def liftClassical : Event .classical → Event .quantum
  | .classicalOperation label => .classicalOperation label
  | .classicalSubroutine label => .classicalSubroutine label

@[simp] theorem liftClassical_classicalOperation (label : ClassicalOpLabel) :
    liftClassical (.classicalOperation label : Event .classical) =
      (.classicalOperation label : Event .quantum) :=
  rfl

@[simp] theorem liftClassical_classicalSubroutine (label : SubroutineLabel) :
    liftClassical (.classicalSubroutine label : Event .classical) =
      (.classicalSubroutine label : Event .quantum) :=
  rfl

/-- The structural classical-event embedding never identifies coordinates. -/
theorem liftClassical_injective : Function.Injective liftClassical := by
  intro left right equality
  cases left <;> cases right <;> simp_all

end Event
end Resource

/-- Native live-space coordinates admitted by a problem kind. Quantum systems
are counted separately at each positive dimension; dimension two counts qubits.
Physical placement is carried by layouts rather than by a second count axis. -/
public inductive SpaceAxis : ProblemKind → Type where
  | classicalBits {kind : ProblemKind} : SpaceAxis kind
  | quantumSystems (dimension : ℕ+) : SpaceAxis .quantum
deriving DecidableEq

namespace SpaceAxis

/-- Embed the sole classical space coordinate into quantum space. -/
def liftClassical : SpaceAxis .classical → SpaceAxis .quantum
  | .classicalBits => .classicalBits

@[simp] theorem liftClassical_classicalBits :
    liftClassical .classicalBits = (.classicalBits : SpaceAxis .quantum) :=
  rfl

/-- The structural classical-space embedding is injective. -/
theorem liftClassical_injective : Function.Injective liftClassical := by
  intro left right
  cases left
  cases right
  intro
  rfl

end SpaceAxis

namespace AccountingKindFixtures

/-- Positive fixture: classical operation axes are classical events. -/
example : Resource.Event .classical :=
  .classicalOperation (.addCarry 32)

/-- Positive fixture: the same classical coordinate embeds structurally. -/
example : Resource.Event .quantum :=
  Resource.Event.liftClassical (.classicalOperation (.addCarry 32))

/-- Positive fixture: gate axes are available to quantum accounting. -/
example : Resource.Event .quantum :=
  .gate { family := "builtin", name := "cnot" }

/-- Positive fixture: qubits and qutrits have separate native coordinates. -/
example : SpaceAxis .quantum × SpaceAxis .quantum :=
  (.quantumSystems 2, .quantumSystems 3)

/-- Different system dimensions cannot share one space coordinate. -/
example : SpaceAxis.quantumSystems 2 ≠ SpaceAxis.quantumSystems 3 := by
  decide

/-- Positive fixture: event coordinates retain decidable equality. -/
example (kind : ProblemKind) : DecidableEq (Resource.Event kind) :=
  inferInstance

/-- Positive fixture: space coordinates retain decidable equality. -/
example (kind : ProblemKind) : DecidableEq (SpaceAxis kind) :=
  inferInstance

/-!
The following compile-time fixtures pin the negative construction boundary.
They are checked by Lean itself rather than by a source-text convention.
-/

/--
error: Type mismatch
  Resource.Event.gate { family := "builtin", name := "cnot" }
has type
  Resource.Event ProblemKind.quantum
but is expected to have type
  Resource.Event ProblemKind.classical
-/
#guard_msgs in
example : Resource.Event .classical :=
  .gate { family := "builtin", name := "cnot" }

/--
error: Type mismatch
  Resource.Event.preparation { family := "builtin", name := "zero" }
has type
  Resource.Event ProblemKind.quantum
but is expected to have type
  Resource.Event ProblemKind.classical
-/
#guard_msgs in
example : Resource.Event .classical :=
  .preparation { family := "builtin", name := "zero" }

/--
error: Type mismatch
  Resource.Event.measurement { family := "builtin", name := "computational" }
has type
  Resource.Event ProblemKind.quantum
but is expected to have type
  Resource.Event ProblemKind.classical
-/
#guard_msgs in
example : Resource.Event .classical :=
  .measurement { family := "builtin", name := "computational" }

/--
error: Type mismatch
  Resource.Event.quantumSubroutine { family := "oracle", name := "member" }.quantum
has type
  Resource.Event ProblemKind.quantum
but is expected to have type
  Resource.Event ProblemKind.classical
-/
#guard_msgs in
example : Resource.Event .classical :=
  .quantumSubroutine
    ({ family := "oracle", name := "member" } : Resource.SubroutineLabel).quantum

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example : SpaceAxis .classical := .quantumSystems 3

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check SpaceAxis.depth

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check Resource.Event.depth

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check Resource.ClassicalOpLabel.named

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check Resource.Event.qSystem

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check Resource.Event.cSystem

end AccountingKindFixtures

end QuantumAlg

end
