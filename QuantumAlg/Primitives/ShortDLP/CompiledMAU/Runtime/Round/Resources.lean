/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Bounds
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Complete native event budget for one reusable-bank round

The independent native pool contains the compiled arithmetic and QFT member,
one Z event for each measured exponent bit, the real finite-bit packing
instruction, the bank reset's dimension-two correction envelope and the fixed
seed's literal X reload. Classically choosing a member preserves its native
gate coordinates. Each reset wire reserves one measurement and at
most one X; its zero-outcome correction executes no gate.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

private lemma seq_pool_le {execution : ExecutionModel} {ctx : RuntimeCtx execution.kind}
    (first second : Circuit execution ctx ctx) (path : (Circuit.seq first second).Path)
    (firstBudget secondBudget : ResourcePool execution)
    (firstBound : first.resourcePool path.1 ≤ firstBudget)
    (secondBound : second.resourcePool path.2 ≤ secondBudget) :
    (Circuit.seq first second).resourcePool path ≤ firstBudget + secondBudget :=
  (ResourcePool.ofList_append (first.eventTrace path.1) (second.eventTrace path.2)).le.trans
    (add_le_add firstBound secondBound)

/-- Independent measurement, conversion, reset and literal seed-X budget. -/
def eventEnvelope (m ell width N : Nat) : ResourcePool model :=
  compiledCircuitEventEnvelopeInClassicalContext m ell width N BitWord.model .empty +
    (resultBits m ell width • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) +
      (ResourcePool.singleton (model := model)
          (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.nominalEncoding (.packFiniteBits (resultBits m ell width))))) +
        (ZReset.Bank.envelope (oracles := .empty)
            (totalQubits (registerParameters m ell width)) BitWord.model +
          reloadXCount m ell width N •
            ResourcePool.singleton (model := model) (.gate .singleQubit))))

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

include sameWires in
/-- The reused physical bank has exactly the complete compiled member's system count. -/
lemma shortDLP_runtimeRound_systemCount :
    ctx.systemCount = totalQubits (registerParameters m ell width) :=
  ctx.physicalIdx_length.symm.trans
    ((congrArg List.length
      (RuntimePlacement.shortDLP_runtimePlacement_physicalIdx m ell width sameWires)).trans
      (by simp only [List.length_range]))

private lemma selected_pool_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (path : (selected m ell width sameWires parameter N generator target).Path) :
    (selected m ell width sameWires parameter N generator target).resourcePool path ≤
      compiledCircuitEventEnvelopeInClassicalContext m ell width N BitWord.model .empty := by
  rcases path with ⟨value, _⟩
  change ResourcePool.ofList
    ((RuntimePlacement.memberProgram m ell width sameWires N
      (generator value) (target value)).eventTrace BitWord.model .empty) ≤ _
  rw [RuntimePlacement.shortDLP_runtimeMember_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model .empty]
  exact compiledCircuit_eventCost_le_classical_context m ell width N
    (generator value) (target value) BitWord.model .empty

private lemma measured_pool
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).Path) :
    (Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).resourcePool path =
      resultBits m ell width • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) :=
  (Circuit.measurementSequence_qubit_resourcePool (readouts m ell width sameWires cells)
    (shortDLP_runtimeReadouts_qubits m ell width sameWires cells) path).trans
    (congrArg (fun count => count •
      ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)))
      (shortDLP_runtimeReadouts_length m ell width sameWires cells))

private lemma packing_pool
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (BitWord.instruction (execution := model) (packing m ell width cells result)).Path) :
    Circuit.resourcePool
      (BitWord.instruction (execution := model) (packing m ell width cells result)) path =
      ResourcePool.singleton (model := model) (.classicalOperation
        (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packFiniteBits (resultBits m ell width))))) :=
  congrArg ResourcePool.ofList
    (BitWord.bitWord_instruction_eventTrace (execution := model)
      (packing m ell width cells result) path)

private lemma resetReload_pool_le (N : Nat)
    (path : (resetReload m ell width sameWires N).Path) :
    (resetReload m ell width sameWires N).resourcePool path ≤
      ZReset.Bank.envelope (oracles := .empty)
          (totalQubits (registerParameters m ell width)) BitWord.model +
        reloadXCount m ell width N •
          ResourcePool.singleton (model := model) (.gate .singleQubit) := by
  apply seq_pool_le
    (ZReset.BankParallel.code
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) BitWord.model)
    (.unitary (RuntimePlacement.reloadProgram m ell width sameWires N)) path
  · exact (ZReset.BankParallel.code_eventEnvelope_le (services := .empty)
      (operations := BitWord.model)
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) path.1).trans_eq
      (congrArg (fun count => ZReset.Bank.envelope (oracles := .empty) count BitWord.model)
        (shortDLP_runtimeRound_systemCount m ell width sameWires))
  · change ResourcePool.ofList
      ((RuntimePlacement.reloadProgram m ell width sameWires N).eventTrace
        BitWord.model .empty) ≤ _
    rw [RuntimePlacement.shortDLP_runtimeReload_eventTrace,
      UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model .empty,
      shortDLP_reload_eventCost_classical_context]

/-- Every actual round path satisfies the complete independent native-coordinate budget. -/
lemma shortDLP_runtimeRound_resourcePool_le {shape : CShape} (parameter : CInputRef ctx shape)
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
