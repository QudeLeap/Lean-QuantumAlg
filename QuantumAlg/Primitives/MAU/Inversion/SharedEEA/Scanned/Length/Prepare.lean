/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Height
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Commutation

/-!
# Complete native aligned first-one and clipping preparation

The actual chronological sequence aligns the original source word,
encodes its first position into the existing address, then prepares the
real clipped-difference controls and value. Its all-label mathematical
action is exactly its actual native program, before clean-pool readout.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Actual first-one tree, using the supplied complete existing address and prefix widths. -/
def program (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (LengthAlignment.program width field first).seq
    ((LengthEncoder.program width field first (LengthEncoder.height width)
      (LengthEncoder.height_capacity width capacity) (LengthEncoder.height_fits width)).seq
      (LengthClip.prepareProgram width field))

/-- Complete physical finite action in precisely the same native execution order. -/
def step (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) : Data width :=
  LengthClip.prepareStep width field
    (GateSpec.stepList ((LengthEncoder.frame width field first).encoderGates
      (LengthEncoder.height width) (LengthEncoder.height_capacity width capacity)
      (LengthEncoder.height_fits width))
      (GateSpec.stepList (LengthAlignment.gates width field first) state))

/-- Actual complete preparation is coherent on every original state, pool and external reference. -/
lemma program_realizes (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width field first capacity) environment
      (step width field first capacity) := by
  have alignment := LengthAlignment.program_realizes width field first environment
  have encoder := LengthEncoder.program_realizes width field first (LengthEncoder.height width)
    (LengthEncoder.height_capacity width capacity) (LengthEncoder.height_fits width) environment
  have clipping := LengthClip.prepareProgram_realizes width field environment
  have tail := UnitaryCircuit.Realizes.seq encoder clipping
  have complete := UnitaryCircuit.Realizes.seq alignment tail
  exact complete

/-- A finite output XOR can pass the whole actual preparation, including every dirty temporary. -/
lemma step_output_comm (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    step width field first capacity
        (Word.xorConstantStep (LengthCopy.target width field) mask state) =
      Word.xorConstantStep (LengthCopy.target width field) mask
        (step width field first capacity state) := by
  unfold step
  rw [LengthAlignment.gates_output_comm, LengthEncoder.gates_output_comm,
    LengthClip.prepareStep_output_comm]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare
