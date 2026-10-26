/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Constant
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Readout

/-!
# Paid native preparation of the terminal region length

Actual public X loading is followed by the actual inverse placed TTK
adder on the complete original prefix. Both length choices use the same
complete runtime other metadata, padded by the actual retained conjunction.
The physical zero-padding premise is discharged separately from semantics.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private lemma constantStep_key (width : Nat) (field : Field) (state : Data width) :
    boundaryValue field (constantStep width field state).1 = boundaryValue field state.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := constantStep_original width field state (boundaryBit width field ⟨index, within⟩)
  simpa only [sourceBit_get, boundaryBit_get] using actual

private lemma constantStep_sourceValue (width : Nat) (field : Field) (state : Data width) :
    sourceValue width field (constantStep width field state) = sourceValue width field state := by
  rw [sourceValue, constantStep_conjunction, constantStep_key]
  rfl

/-- One paid public load then one actual native inverse adder on the existing full prefix. -/
def prepareProgram (width : Nat) (field : Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (constantProgram width field).seq (placement width field).subtractProgram

/-- Complete finite action of the same two actual native components. -/
def prepareStep (width : Nat) (field : Field) (state : Data width) : Data width :=
  (placement width field).subtractStep (constantStep width field state)

/-- Coherent semantics cover every original source label and the whole arbitrary input pool. -/
lemma prepareProgram_realizes (width : Nat) (field : Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (prepareProgram width field) environment
      (prepareStep width field) := by
  have first := constantProgram_realizes width field environment
  have second := (placement width field).subtractProgram_realizes environment
  have complete := UnitaryCircuit.Realizes.seq first second
  exact complete

/-- The actual prefix equation includes arbitrary input data and the original real padding. -/
lemma prepareStep_prefix (width : Nat) (field : Field) (state : Data width) :
    (prepareStep width field state).2.2.1 =
      (state.2.2.1 ^^^ constant width field) - sourceValue width field state := by
  rw [prepareStep, subtractStep_prefix, constantStep_prefix, constantStep_sourceValue]

/-- Every original physical source bit survives the complete paid preparation. -/
lemma prepareStep_original (width : Nat) (field : Field) (state : Data width)
    (observed : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width observed).get (prepareStep width field state) =
      (sourceBit width observed).get state := by
  rw [prepareStep, subtractStep_original, constantStep_original]

/-- The conjunction stays at its actual input value before becoming the next borrow output. -/
lemma prepareStep_conjunction (width : Nat) (field : Field) (state : Data width) :
    (prepareStep width field state).2.2.2 = state.2.2.2 := by
  rw [prepareStep, subtractStep_conjunction, constantStep_conjunction]

/-- The first-one address remains unchanged throughout the actual length preparation. -/
lemma prepareStep_address (width : Nat) (field : Field) (state : Data width) :
    (prepareStep width field state).2.1 = state.2.1 := by
  rw [prepareStep, subtractStep_address, constantStep_address]

/-- Actual clean prefix and conjunction identify the result with the padded complete boundary. -/
lemma prepareStep_prefix_clean (width : Nat) (field : Field) (state : Data width)
    (prefixZero : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (conjunctionZero : state.2.2.2 = false) :
    (prepareStep width field state).2.2.1 =
      constant width field - BitVec.cons false (boundaryValue field state.1) := by
  rw [prepareStep_prefix, prefixZero, BitVec.zero_xor, sourceValue, conjunctionZero]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary
