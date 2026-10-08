/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Hadamard.Layer.Layout
public import QuantumAlg.Components.Gates.Construction
public import QuantumAlg.Components.Gates.Operator
public import QuantumAlg.Core.Base.UnitaryCircuit.Tensor
public import QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Actual parallel native Hadamard layers

There is exactly one native one-qubit Hadamard instruction on each system.
Disjoint physical tensor construction retains parallel depth one for every
nonempty layer and depth zero for the empty layer [dW19, qcnotes.tex:1005-1006].
-/

namespace QuantumAlg.Gate.HadamardLayer

noncomputable section

/-- One actual native Hadamard on each canonical qubit, all executed in parallel. -/
public def circuit (oracles : OracleModel) :
    (width : Nat) → UnitaryCircuit AlgorithmGate.model oracles (layout width)
  | 0 => UnitaryCircuit.identity AlgorithmGate.model oracles (layout 0)
  | width + 1 =>
      ((circuit oracles width).tensor
        (Gate.singleQubitAt (lastLayout width) oracles Gate.HOp 0
          (hadamardLayer_last_dimension width))
        (hadamardLayer_layout_disjoint width)).castLayout (hadamardLayer_layout_append width)

/-- The native ledger contains exactly one single-qubit instruction per actual system. -/
public theorem hadamardLayer_circuit_eventCost (oracles : OracleModel) (width : Nat) :
    (circuit oracles width).eventCost = width •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [circuit, UnitaryCircuit.castLayout_eventCost,
        UnitaryCircuit.tensor_native_eventCost, ih, Gate.singleQubitAt_eventCost,
        add_nsmul, one_nsmul]

/-- Empty layers have no dependency; all nonempty disjoint layers have depth one. -/
public theorem hadamardLayer_circuit_unit_depth (oracles : OracleModel) (width : Nat) :
    (circuit oracles width).evaluatedEventDepth (fun _ => 1) =
      if width = 0 then 0 else 1 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [circuit, UnitaryCircuit.castLayout_evaluatedEventDepth,
        UnitaryCircuit.tensor_native_evaluatedEventDepth]
      change max ((circuit oracles width).evaluatedEventDepth (fun _ => 1)) 1 = 1
      rw [ih]
      split <;> rfl

end

end QuantumAlg.Gate.HadamardLayer
