/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Complete native event budget for one reusable-bank round

The independent native pool contains the compiled arithmetic and QFT member,
one Z event for each measured exponent bit, the real finite-bit packing
instruction, the bank reset's dimension-two correction envelope and the fixed
seed's literal X reload. Classically choosing a member preserves its native
controlled gate labels. The reset envelope lists both possible corrections;
only one correction is executed per reset wire.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

private theorem seq_pool_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (first second : Circuit ctx ctx) (path : (Circuit.seq first second).Path)
    (firstBudget secondBudget : ResourcePool kind)
    (firstBound : first.resourcePool path.1 ≤ firstBudget)
    (secondBound : second.resourcePool path.2 ≤ secondBudget) :
    (Circuit.seq first second).resourcePool path ≤ firstBudget + secondBudget :=
  (ResourcePool.ofList_append (first.eventTrace path.1) (second.eventTrace path.2)).le.trans
    (add_le_add firstBound secondBound)

/-- Independent measurement, conversion, correction alternatives and literal seed-X budget. -/
def eventEnvelope (m ell width N : Nat) : ResourcePool .quantum :=
  compiledCircuitEventEnvelope m ell width N +
    (resultBits m ell width • ResourcePool.singleton (Circuit.zEvent 2) +
      (ResourcePool.singleton (.classicalOperation
        (.nominalEncoding (.packFiniteBits (resultBits m ell width)))) +
        (ZReset.Bank.envelope (totalQubits (registerParameters m ell width)) +
          reloadXCount m ell width N • ResourcePool.singleton (.gate (.builtin "x")))))

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

include sameWires in
private theorem systemCount_eq :
    ctx.systemCount = totalQubits (registerParameters m ell width) :=
  ctx.physicalIdx_length.symm.trans
    ((congrArg List.length
      (RuntimePlacement.shortDLP_runtimePlacement_physicalIdx m ell width sameWires)).trans
      (by simp only [List.length_range]))

private theorem selected_pool_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (path : (selected m ell width sameWires parameter N generator target).Path) :
    (selected m ell width sameWires parameter N generator target).resourcePool path ≤
      compiledCircuitEventEnvelope m ell width N :=
  (UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (RuntimePlacement.memberProgram m ell width sameWires N
      (generator path.1) (target path.1))).le.trans
    (compiledCircuit_eventCost_le m ell width N (generator path.1) (target path.1))

private theorem measured_pool
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (readouts m ell width sameWires cells)).Path) :
    (Circuit.measurementSequence (readouts m ell width sameWires cells)).resourcePool path =
      resultBits m ell width • ResourcePool.singleton (Circuit.zEvent 2) :=
  (Circuit.measurementSequence_qubit_resourcePool (readouts m ell width sameWires cells)
    (shortDLP_runtimeReadouts_qubits m ell width sameWires cells) path).trans
    (congrArg (fun count => count • ResourcePool.singleton (Circuit.zEvent 2))
      (shortDLP_runtimeReadouts_length m ell width sameWires cells))

private theorem packing_pool
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (Circuit.classical (packing m ell width cells result)).Path) :
    (Circuit.classical (packing m ell width cells result)).resourcePool path =
      ResourcePool.singleton (.classicalOperation
        (.nominalEncoding (.packFiniteBits (resultBits m ell width)))) :=
  congrArg ResourcePool.ofList
    (ClassicalOp.eventTrace_packFiniteBits (resultBits m ell width) ctx _ result)

private theorem resetReload_pool_le (N : Nat)
    (path : (resetReload m ell width sameWires N).Path) :
    (resetReload m ell width sameWires N).resourcePool path ≤
      ZReset.Bank.envelope (totalQubits (registerParameters m ell width)) +
        reloadXCount m ell width N • ResourcePool.singleton (.gate (.builtin "x")) := by
  apply seq_pool_le
    (ZReset.BankScope.code
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires))
    (.unitary (RuntimePlacement.reloadProgram m ell width sameWires N)
      (RuntimePlacement.shortDLP_runtimeReload_physicalIdx m ell width sameWires N)) path
  · exact (ZReset.BankScope.zResetBankScope_resourcePool_le
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) path.1).trans_eq
      (congrArg ZReset.Bank.envelope (systemCount_eq m ell width sameWires))
  · exact ((UnitaryCircuit.ofList_eventTrace_eq_eventCost
      (RuntimePlacement.reloadProgram m ell width sameWires N)).trans
      (shortDLP_reload_eventCost m ell width N)).le

/-- Every actual round path satisfies the complete independent native-coordinate budget. -/
theorem shortDLP_runtimeRound_resourcePool_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    (code m ell width sameWires parameter N generator target cells result).resourcePool path ≤
      eventEnvelope m ell width N :=
  seq_pool_le _ _ path _ _
    (selected_pool_le m ell width sameWires parameter N generator target path.1)
    (seq_pool_le _ _ path.2 _ _
      (measured_pool m ell width sameWires cells path.2.1).le
      (seq_pool_le _ _ path.2.2 _ _
        (packing_pool m ell width cells result path.2.2.1).le
        (resetReload_pool_le m ell width sameWires N path.2.2.2)))

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
