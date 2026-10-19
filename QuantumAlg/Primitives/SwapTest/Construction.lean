/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled.Register.Semantics
public import QuantumAlg.Components.Gates.Swap.Controlled.Register.Resources
public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Primitives.SwapTest.Basic
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Components.Gates.Swap.Controlled.Register.Semantics
import all QuantumAlg.Components.Gates.Swap.Controlled.Register.Resources
import all QuantumAlg.Components.Gates.Swap.Controlled.Register
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# The SWAP test from actual Hadamards, CNOTs and Toffolis

The original control drives two CNOTs and one Toffoli for each pair of supplied
word positions. Both boundary Hadamards are actual native one-qubit operations.
No auxiliary quantum word is used [BCWdW01, main.tex:287-329].
-/

namespace QuantumAlg.SwapTest

noncomputable section

private def boundary (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (Gate.ControlledRegisterSwap.layout width) :=
  Gate.singleQubitAt (Gate.ControlledRegisterSwap.layout width) .empty Gate.HOp
    (0 : Fin (1 + (width + width))) rfl

/-- The complete native word acts on the original control and both full input words. -/
def sourceCircuit (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (Gate.ControlledRegisterSwap.layout width) :=
  ((boundary width).seq (Gate.ControlledRegisterSwap.circuit .empty width)).seq (boundary width)

/-- The full exact operator equals the independently specified mathematical SWAP test. -/
lemma sourceCircuit_matrix (width : Nat) (actual : OracleModel.empty.Interpretation) :
    (sourceCircuit width).binaryMatrix actual = swapTest width := by
  rw [sourceCircuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    Gate.ControlledRegisterSwap.controlledRegisterSwap_binaryMatrix]
  have matrix : (boundary width).binaryMatrix actual =
      Gate.HOp.tensor (1 : UnitaryOperator (Qubits (width + width))) :=
    Gate.singleQubitAt_first_binaryMatrix .empty (width + width) Gate.HOp actual
  rw [matrix]
  rfl

/-- Every original pair contributes exactly two CNOTs and one Toffoli. -/
lemma sourceCircuit_eventCost (width : Nat) :
    (sourceCircuit width).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) 2 +
        (ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .cnot) (2 * width) +
          ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .toffoli) width) := by
  rw [sourceCircuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    Gate.ControlledRegisterSwap.controlledRegisterSwap_eventCost]
  change (ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) + _) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) =
      (ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit)) + _
  ac_rfl

/-- The common control orders every native layer, including both boundary Hadamards. -/
lemma sourceCircuit_depth (width : Nat) :
    (sourceCircuit width).evaluatedEventDepth (fun _ => 1) = 3 * width + 2 := by
  rw [sourceCircuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq,
    Gate.ControlledRegisterSwap.controlledRegisterSwap_unit_depth]
  change (1 + 3 * width) + 1 = _
  omega

end

end QuantumAlg.SwapTest
