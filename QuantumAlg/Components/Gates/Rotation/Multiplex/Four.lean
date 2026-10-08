/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Rotation.Multiplex.Placement

/-!
# Four selected rotations from native two-qubit controls

Two selectors choose four specified angles. Recursing through average and
difference angles uses four one-qubit rotations and six CNOTs, with no source
query or additional work wire.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex.Four
noncomputable section

/-- Two original selectors followed by the original rotation target. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 3 := (QuantumSignature.qubits 3).canonicalPlacement.layout

/-- The outer selector toggles only the phase target and preserves the inner selector. -/
def outerCnot (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout :=
  Gate.cnotAt layout oracles 0 2 (by decide) rfl rfl

/-- Actual recursive multiplexing, with selector zero outermost in the angle subscripts. -/
def circuit (oracles : OracleModel) (a00 a01 a10 a11 : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let average := Multiplex.circuitAt (width := 3) 1 2 (by decide) oracles
    ((a00 + a10) / 2) ((a01 + a11) / 2)
  let difference := Multiplex.circuitAt (width := 3) 1 2 (by decide) oracles
    ((a00 - a10) / 2) ((a01 - a11) / 2)
  ((average.seq (outerCnot oracles)).seq difference).seq (outerCnot oracles)

/-- Four actual rotations and six actual CNOTs retain their complete execution order. -/
theorem fourRotation_eventTrace (oracles : OracleModel) (a00 a01 a10 a11 : ℝ) :
    (circuit oracles a00 a01 a10 a11).eventTrace =
      [.gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .cnot,
        .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .cnot] := by
  simp only [circuit, UnitaryCircuit.seq_eventTrace, Multiplex.circuitAt_eventTrace]
  rfl

/-- All ten native occurrences lie on the same target dependency chain. -/
theorem fourRotation_depth (oracles : OracleModel) (a00 a01 a10 a11 : ℝ) :
    (circuit oracles a00 a01 a10 a11).evaluatedEventDepth (fun _ => 1) = 10 := by
  simp only [circuit, UnitaryCircuit.evaluatedEventDepth_seq, Multiplex.circuitAt_depth]
  rfl

end
end QuantumAlg.Gate.Rotation.Multiplex.Four
