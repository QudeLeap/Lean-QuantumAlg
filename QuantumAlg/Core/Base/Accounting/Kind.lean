/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.PNat.Defs

/-!
# Computation kinds and classical and storage coordinates

These types classify mathematical state and storage without selecting quantum
operations. Classical opcodes are closed typed machine operations. Quantum gate
and query coordinates are supplied separately by an execution model.
-/

namespace QuantumAlg

/-- Whether an accounting object belongs to a classical or quantum problem. -/
public inductive ProblemKind where
  | classical
  | quantum
deriving DecidableEq

namespace Resource

/-- A stable base coordinate for one declared opaque subroutine.

This coordinate describes a classical call. Quantum oracle capabilities have
an independent typed declaration.
-/
public structure SubroutineLabel where
  /-- Declaration family or namespace. -/
  family : String
  /-- Base capability name. -/
  name : String
  /-- Widths/dimensions that distinguish members of the declared family. -/
  parameters : List Nat := []
deriving DecidableEq

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

end QuantumAlg
