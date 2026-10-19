/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.ControlledPhase.Physical
import all QuantumAlg.Components.Gates.ControlledPhase.Physical
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
public import QuantumAlg.Components.Gates.ControlledPhase.Coordinates
import all QuantumAlg.Components.Gates.ControlledPhase.Coordinates
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Diagonal
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Diagonal
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Native controlled phase with the original qubit-register target

The exact target is the existing addressed operator on big-endian integer
labels. Reindexing only translates that fixed label convention to the physical
layout basis. The implementation contains the complete native five-gate word.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

/-- The original ordered register of the supplied number of physical qubits. -/
@[expose, implicit_reducible]
public def qubitLayout (width : Nat) : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

/-- Execute the full native word at two distinct positions of the original qubit register. -/
public def qubitCircuit (oracles : OracleModel) {width : Nat}
    (control target : Fin width) (distinct : control ≠ target) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles (qubitLayout width) :=
  circuitAt (qubitLayout width) control target distinct rfl rfl oracles angle

/-- The native implementation realizes the unchanged addressed target on every register state. -/
public lemma controlledPhase_qubitCircuit_matrix (oracles : OracleModel) {width : Nat}
    (control target : Fin width) (distinct : control ≠ target) (angle : Real) (environment :
      oracles.Interpretation) :
    ((qubitCircuit oracles control target distinct angle).matrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm
        (qftControlledPhaseOperator control target angle) := by
  rw [qubitCircuit, controlledPhase_circuitAt_matrix]
  apply Subtype.ext
  have localDiagonal : (operator angle : HilbertOperator layout.register) =
      Matrix.diagonal (fun (basis : Fin 2 → Fin 2) =>
        if finTwoEquiv (basis 0) && finTwoEquiv (basis 1) then
          Complex.exp ((angle : Complex) * Complex.I) else 1) :=
    qftControlledPhaseOperator_coordinates (width := 2) 0 1 angle
  refine (UnitaryCircuit.operatorAt_diagonal layout (qubitLayout width)
    (positions control target distinct)
    (dimensions (qubitLayout width) control target distinct rfl rfl)
    (operator angle) _ localDiagonal).trans ?_
  rw [qftControlledPhaseOperator_coordinates]
  apply congrArg Matrix.diagonal
  funext basis
  have first :
      UnitaryCircuit.selectedInput layout (qubitLayout width) (positions control target distinct)
        (dimensions (qubitLayout width) control target distinct rfl rfl) basis (0 : Fin 2) =
          basis control := by
    apply Fin.ext
    rfl
  have second :
      UnitaryCircuit.selectedInput layout (qubitLayout width) (positions control target distinct)
        (dimensions (qubitLayout width) control target distinct rfl rfl) basis (1 : Fin 2) =
          basis target := by
    apply Fin.ext
    rfl
  rw [first, second]

/-- The original register realization retains all five native occurrences. -/
public lemma controlledPhase_qubitCircuit_events (oracles : OracleModel) {width : Nat}
    (control target : Fin width) (distinct : control ≠ target) (angle : Real) :
    (qubitCircuit oracles control target distinct angle).eventTrace =
      [.gate .singleQubit, .gate .singleQubit, .gate .cnot, .gate .singleQubit, .gate .cnot] := by
  exact controlledPhase_circuitAt_events (qubitLayout width) control target distinct rfl rfl
    oracles angle

end

end QuantumAlg.Gate.ControlledPhase
