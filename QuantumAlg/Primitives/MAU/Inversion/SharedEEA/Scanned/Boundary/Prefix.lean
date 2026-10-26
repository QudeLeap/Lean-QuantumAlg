/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Natural
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-! # Actual original boundary predicate and parity gates beside the complete pool -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TerminalBoundary

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The original microstep's width premise internally supplies the full nontruncated sentinel. -/
lemma sentinel_fits (width : Nat) (enough : 2 ≤ width.size) :
    width + 3 < 2 ^ ScanMetadata.addressWidth width := by
  apply LengthBoundary.sentinel_fits
  by_contra small
  have smallCases : width = 0 ∨ width = 1 := by omega
  rcases smallCases with rfl | rfl <;> norm_num at enough

/-- No stronger caller restriction is added to the complete original boundary entry point. -/
lemma capacity (width : Nat) (enough : 2 ≤ width.size) :
    width + 3 ≤ 2 ^ ScanMetadata.addressWidth width :=
  (sentinel_fits width enough).le

private def predicateSourceProgram (width : Nat) (enough : 2 ≤ width.size) (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (SharedEEA.encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty
    (if inverse then (BoundaryPredicate.gates width enough).reverse
      else BoundaryPredicate.gates width enough)

private lemma predicateSourceProgram_realizes (width : Nat) (enough : 2 ≤ width.size)
    (inverse : Bool) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (SharedEEA.encoding width)
      (predicateSourceProgram width enough inverse) environment
      (fun state => NativePredicate.xorControl (BoundaryPredicate.condition state) state) := by
  cases inverse
  · exact GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
      (BoundaryPredicate.gates_step width enough) environment
  · exact GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
      (BoundaryPredicate.reverse_step width enough) environment

/-- Actual original predicate or its literal reversed native list on the existing prefix. -/
def predicateProgram (width : Nat) (enough : 2 ≤ width.size) (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width
    (predicateSourceProgram width enough inverse)

/-- Both native directions retain the same entire arbitrary pool and all original predicate work. -/
lemma predicateProgram_realizes (width : Nat) (enough : 2 ≤ width.size) (inverse : Bool)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (predicateProgram width enough inverse) environment
      (fun state =>
        (NativePredicate.xorControl (BoundaryPredicate.condition state.1) state.1, state.2)) :=
  (predicateSourceProgram_realizes width enough inverse environment).onBinaryPrefix

private def paritySourceProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (SharedEEA.encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty
    (SharedEEA.BoundaryExchange.parityGates width)

private lemma paritySourceProgram_realizes (width : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (SharedEEA.encoding width) (paritySourceProgram width) environment
      SharedEEA.BoundaryExchange.parityStep :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (SharedEEA.BoundaryExchange.parityGates_step width) environment

/-- The original paid Ctrl-to-Iter CNOT acts on its real systems while the same pool stays live. -/
def parityProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (poolEncoding width).width (paritySourceProgram width)

/-- Complete original parity action retains every source field besides the selected Iter toggle. -/
lemma parityProgram_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (parityProgram width) environment
      (fun state => (SharedEEA.BoundaryExchange.parityStep state.1, state.2)) :=
  (paritySourceProgram_realizes width environment).onBinaryPrefix

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TerminalBoundary
