/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Signature

import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Hadamard.Operator
import all QuantumAlg.Components.Gates.PhaseOperator

/-!
# One- and two-qubit native word for Toffoli

The middle phase word evaluates the three-bit parity identity using seven
quarter-turn phases and six CNOTs. Two actual target Hadamards surround it.
All three original wires are retained and no work ancilla is introduced.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

/-- Two original control wires followed by the original target. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 3 := (QuantumSignature.qubits 3).canonicalPlacement.layout

private def phase (oracles : OracleModel) (target : Fin 3) (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  Gate.singleQubitAt layout oracles (phaseGateOp angle) target rfl

private def cnot (oracles : OracleModel) (control target : Fin 3) (distinct : control ≠ target) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  Gate.cnotAt layout oracles control target distinct rfl rfl

/-- The native parity-phase word preserves all three computational coordinates. -/
def phaseWord (oracles : OracleModel) (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let initial := ((phase oracles 0 angle).seq (phase oracles 1 angle)).seq
    (phase oracles 2 angle)
  let pair := ((cnot oracles 0 1 (by decide)).seq (phase oracles 1 (-angle))).seq
    (cnot oracles 0 1 (by decide))
  let tail := ((((((cnot oracles 0 2 (by decide)).seq (phase oracles 2 (-angle))).seq
    (cnot oracles 1 2 (by decide))).seq (phase oracles 2 angle)).seq
    (cnot oracles 0 2 (by decide))).seq (phase oracles 2 (-angle))).seq
    (cnot oracles 1 2 (by decide))
  (initial.seq pair).seq tail

/-- The full fifteen-gate word acts on the original two controls and target. -/
def circuit (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let hadamard := Gate.singleQubitAt layout oracles Gate.HOp (2 : Fin 3) rfl
  (hadamard.seq (phaseWord oracles (Real.pi / 4))).seq hadamard

/-- The complete executed trace has nine single-qubit operations and six CNOTs. -/
theorem toffoliExpansion_eventTrace (oracles : OracleModel) :
    (circuit oracles).eventTrace =
      [.gate .singleQubit, .gate .singleQubit, .gate .singleQubit, .gate .singleQubit,
        .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .cnot, .gate .singleQubit,
        .gate .cnot, .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot,
        .gate .singleQubit] := rfl

/-- Every occurrence of the serial expansion is charged to its dependency depth. -/
theorem toffoliExpansion_depth (oracles : OracleModel) :
    (circuit oracles).evaluatedEventDepth (fun _ => 1) = 15 := rfl

end
end QuantumAlg.Gate.Toffoli
