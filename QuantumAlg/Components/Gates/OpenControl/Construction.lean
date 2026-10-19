/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.Hadamard.Layer.Layout
public import QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Components.Gates.Rotation.Operator
public import QuantumAlg.Core.Base.UnitaryCircuit.Layout
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement
public import QuantumAlg.Core.Base.UnitaryCircuit.Tensor
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor

/-!
# Native open-control words

These two-qubit words implement a leading control active on zero.  Their
construction contains only default one-qubit gates and CNOTs.  The first and
last pairs of one-qubit gates are actual disjoint parallel layers; macro names
are descriptive and retain the complete native construction.
-/

namespace QuantumAlg.Gate.OpenControl

noncomputable section

/-- The original control and target qubits, in that physical order. -/
public abbrev layout : QuantumLayout 2 := Gate.HadamardLayer.layout 2

/-- Two arbitrary one-qubit gates on the control and target in one dependency layer. -/
def parallelPair (oracles : OracleModel)
    (controlOp targetOp : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  ((Gate.singleQubitAt (Gate.HadamardLayer.layout 1) oracles controlOp 0 rfl).tensor
    (Gate.singleQubitAt (Gate.HadamardLayer.lastLayout 1) oracles targetOp 0
      (Gate.HadamardLayer.hadamardLayer_last_dimension 1))
    (Gate.HadamardLayer.hadamardLayer_layout_disjoint 1)).castLayout
      (Gate.HadamardLayer.hadamardLayer_layout_append 1)

/-- One arbitrary one-qubit gate on the target. -/
def targetGate (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  Gate.singleQubitAt layout oracles operator 1 rfl

/-- One arbitrary one-qubit gate on the control. -/
def controlGate (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  Gate.singleQubitAt layout oracles operator 0 rfl

/-- The canonical CNOT from the leading control to the trailing target. -/
def cnot (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  .native (GateModel.Application.canonical AlgorithmGate.model .cnot)

private lemma parallelPair_unit_depth (oracles : OracleModel)
    (controlOp targetOp : UnitaryOperator (Qubits 1)) :
    (parallelPair oracles controlOp targetOp).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [parallelPair, UnitaryCircuit.castLayout_evaluatedEventDepth,
    UnitaryCircuit.tensor_native_evaluatedEventDepth]
  rfl

private lemma targetGate_unit_depth (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    (targetGate oracles operator).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

private lemma controlGate_unit_depth (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) :
    (controlGate oracles operator).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

private lemma cnot_unit_depth (oracles : OracleModel) :
    (cnot oracles).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

/-- Active-on-zero `R_Y(angle)` with four one-qubit gates and two CNOTs. -/
public def rotY (oracles : OracleModel) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let body := parallelPair oracles Gate.XOp (rotYOp (angle / 2))
  let body := body.seq (cnot oracles)
  let body := body.seq (targetGate oracles (rotYOp (-(angle / 2))))
  let body := body.seq (cnot oracles)
  .macroCall "zero-controlled-ry" (body.seq (controlGate oracles Gate.XOp))

/-- Exchange the local control and target positions without inserting a swap
gate.  Placement rewrites the physical positions of every native occurrence
in the supplied word. -/
public def swappedPosition : Fin 2 ↪ Fin 2 where
  toFun := ![1, 0]
  inj' := by
    intro left right same
    fin_cases left <;> fin_cases right <;> simp_all

/-- Both positions of the reversed local placement retain qubit dimension. -/
public lemma swappedDimensions : ∀ index,
    (layout.wire index).dimension = (layout.wire (swappedPosition index)).dimension :=
  fun index => by fin_cases index <;> rfl

/-- The same native open-controlled rotation with its target on the leading
physical wire and its zero-control on the trailing physical wire. -/
public def rotYRight (oracles : OracleModel) (angle : Real) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  UnitaryCircuit.placeAt layout layout swappedPosition
    swappedDimensions (rotY oracles angle)

/-- Active-on-zero Hadamard with four one-qubit gates and one CNOT. -/
public def hadamard (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  let body := parallelPair oracles Gate.XOp (rotYOp (Real.pi / 4))
  let body := body.seq (cnot oracles)
  .macroCall "zero-controlled-hadamard"
    (body.seq (parallelPair oracles Gate.XOp (rotYOp (-(Real.pi / 4)))))

/-- The rotation word retains every actual native event. -/
public lemma rotY_eventCost (oracles : OracleModel) (angle : Real) :
    (rotY oracles angle).eventCost =
      4 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) +
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) := by
  simp [rotY, parallelPair, targetGate, controlGate, cnot,
    UnitaryCircuit.castLayout_eventCost, UnitaryCircuit.tensor_native_eventCost,
    show (4 : Nat) = 2 + 1 + 1 from rfl, show (2 : Nat) = 1 + 1 from rfl,
    two_nsmul]
  abel

/-- The rotation word has five actual dependency layers. -/
public lemma rotY_unit_depth (oracles : OracleModel) (angle : Real) :
    (rotY oracles angle).evaluatedEventDepth (fun _ => 1) = 5 := by
  simp [rotY, parallelPair_unit_depth, targetGate_unit_depth,
    controlGate_unit_depth, cnot_unit_depth]

/-- Reorienting the rotation changes no native event multiplicity. -/
public lemma rotYRight_eventCost (oracles : OracleModel) (angle : Real) :
    (rotYRight oracles angle).eventCost =
      4 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) +
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) := by
  rw [rotYRight, UnitaryCircuit.placeAt_eventCost, rotY_eventCost]

/-- Reorienting the rotation changes no native dependency depth. -/
public lemma rotYRight_unit_depth (oracles : OracleModel) (angle : Real) :
    (rotYRight oracles angle).evaluatedEventDepth (fun _ => 1) = 5 := by
  rw [rotYRight, UnitaryCircuit.placeAt_evaluatedEventDepth, rotY_unit_depth]

/-- The Hadamard word retains every actual native event. -/
public lemma hadamard_eventCost (oracles : OracleModel) :
    (hadamard oracles).eventCost =
      4 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) +
      ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) := by
  simp [hadamard, parallelPair, cnot, UnitaryCircuit.castLayout_eventCost,
    UnitaryCircuit.tensor_native_eventCost, show (4 : Nat) = 2 + 2 from rfl]
  abel

/-- The Hadamard word has three actual dependency layers. -/
public lemma hadamard_unit_depth (oracles : OracleModel) :
    (hadamard oracles).evaluatedEventDepth (fun _ => 1) = 3 := by
  simp [hadamard, parallelPair_unit_depth, cnot_unit_depth]

end

end QuantumAlg.Gate.OpenControl
