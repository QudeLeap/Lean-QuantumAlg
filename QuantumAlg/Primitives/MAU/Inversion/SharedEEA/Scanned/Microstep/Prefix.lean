/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ZeroShiftControl
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-! # Actual original shift and phase blocks retaining the complete scanned pool -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

open EncodedBit

/-- The original physical shift/counter primitive occupies the actual original source prefix. -/
def shiftProgram (width : Nat) (selected : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (GuardedShift.program width selected)

/-- Both source shift directions keep the complete arbitrary resident pool. -/
lemma shiftProgram_realizes (width : Nat) (selected : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (shiftProgram width selected) environment
      (fun state => (GuardedShift.step selected state.1, state.2)) :=
  (GuardedShift.program_realizes (environment := environment) width selected).onBinaryPrefix

/-- Original ordered phase-update gates execute beside the same physical pool. -/
def controlProgram (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (NativeControl.program width enough)

/-- Complete original phase-update action retains all actual pool values. -/
lemma controlProgram_realizes (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (controlProgram width enough) environment
      (fun state => (NativeControl.step state.1, state.2)) :=
  (NativeControl.program_realizes (environment := environment) width enough).onBinaryPrefix

/-- Original zero-shift phase complements remain actual native gates on their original systems. -/
def zeroProgram (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (ZeroShiftControl.program width enough)

/-- Complete actual zero-shift action retains every original pool coordinate. -/
lemma zeroProgram_realizes (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (zeroProgram width enough) environment
      (fun state => (ZeroShiftControl.step state.1, state.2)) :=
  (ZeroShiftControl.program_realizes (environment := environment) width enough).onBinaryPrefix

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep
