/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.Event
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Default native gates at physical positions

The default algorithm language has Toffoli, CNOT and an arbitrary one-qubit
unitary. These constructors select actual ambient wires in argument order.
Each selected wire must be a qubit, and control and target positions must be
distinct. All unselected systems, including non-qubit systems, are spectators.
The oracle declaration is retained independently and grants no extra gates.
-/

namespace QuantumAlg.Gate

noncomputable section

variable {count : Nat} (layout : QuantumLayout count)

/-- Place the actual one-qubit operator on one dimension-two ambient system. -/
@[expose]
public def singleQubitApplication (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (layout.wire target).dimension = 2) :
    GateModel.Application AlgorithmGate.model layout :=
  GateModel.Application.ofPositions AlgorithmGate.model (.singleQubit operator) layout
    ⟨fun _ => target, fun _ _ _ => Subsingleton.elim (α := Fin 1) _ _⟩ (fun _ => qubit)

/-- Place CNOT with its control first and its distinct target second. -/
@[expose]
public def cnotApplication (control target : Fin count) (distinct : control ≠ target)
    (controlQubit : (layout.wire control).dimension = 2)
    (targetQubit : (layout.wire target).dimension = 2) :
    GateModel.Application AlgorithmGate.model layout :=
  GateModel.Application.ofPositions AlgorithmGate.model .cnot layout
    { toFun := ![control, target]
      inj' := by
        intro left right same
        fin_cases left <;> fin_cases right <;> simp_all }
    (by intro index; fin_cases index <;> assumption)

/-- Place Toffoli on its two controls and target, preserving that argument order. -/
@[expose]
public def toffoliApplication (controlA controlB target : Fin count)
    (controlsDistinct : controlA ≠ controlB)
    (firstDistinct : controlA ≠ target) (secondDistinct : controlB ≠ target)
    (firstQubit : (layout.wire controlA).dimension = 2)
    (secondQubit : (layout.wire controlB).dimension = 2)
    (targetQubit : (layout.wire target).dimension = 2) :
    GateModel.Application AlgorithmGate.model layout :=
  GateModel.Application.ofPositions AlgorithmGate.model .toffoli layout
    { toFun := ![controlA, controlB, target]
      inj' := by
        intro left right same
        fin_cases left <;> fin_cases right <;> simp_all }
    (by intro index; fin_cases index <;> assumption)

/-- Execute one actual one-qubit gate in the default algorithm model. -/
public def singleQubitAt (oracles : OracleModel) (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (layout.wire target).dimension = 2) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  .native (singleQubitApplication layout operator target qubit)

/-- Execute one CNOT on the supplied physical control and target. -/
public def cnotAt (oracles : OracleModel) (control target : Fin count)
    (distinct : control ≠ target)
    (controlQubit : (layout.wire control).dimension = 2)
    (targetQubit : (layout.wire target).dimension = 2) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  .native (cnotApplication layout control target distinct controlQubit targetQubit)

/-- Execute one Toffoli on three supplied, distinct physical qubits. -/
public def toffoliAt (oracles : OracleModel) (controlA controlB target : Fin count)
    (controlsDistinct : controlA ≠ controlB)
    (firstDistinct : controlA ≠ target) (secondDistinct : controlB ≠ target)
    (firstQubit : (layout.wire controlA).dimension = 2)
    (secondQubit : (layout.wire controlB).dimension = 2)
    (targetQubit : (layout.wire target).dimension = 2) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  .native (toffoliApplication layout controlA controlB target
    controlsDistinct firstDistinct secondDistinct firstQubit secondQubit targetQubit)

/-- Every supplied one-qubit operator contributes exactly one native one-qubit event. -/
@[simp] public lemma singleQubitAt_eventCost
    (oracles : OracleModel) (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (layout.wire target).dimension = 2) :
    (singleQubitAt layout oracles operator target qubit).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rfl

/-- A placed CNOT contributes exactly its own default-model coordinate. -/
@[simp] public lemma cnotAt_eventCost (oracles : OracleModel)
    (control target : Fin count) (distinct : control ≠ target)
    (controlQubit : (layout.wire control).dimension = 2)
    (targetQubit : (layout.wire target).dimension = 2) :
    (cnotAt layout oracles control target distinct controlQubit targetQubit).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) := by
  rfl

/-- A placed Toffoli contributes exactly its own default-model coordinate. -/
@[simp] public lemma toffoliAt_eventCost (oracles : OracleModel)
    (controlA controlB target : Fin count) (controlsDistinct : controlA ≠ controlB)
    (firstDistinct : controlA ≠ target) (secondDistinct : controlB ≠ target)
    (firstQubit : (layout.wire controlA).dimension = 2)
    (secondQubit : (layout.wire controlB).dimension = 2)
    (targetQubit : (layout.wire target).dimension = 2) :
    (toffoliAt layout oracles controlA controlB target controlsDistinct firstDistinct
      secondDistinct firstQubit secondQubit targetQubit).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) := by
  rfl

end

end QuantumAlg.Gate
