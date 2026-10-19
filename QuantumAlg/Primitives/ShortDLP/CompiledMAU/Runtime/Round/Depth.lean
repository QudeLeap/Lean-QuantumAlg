/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Resources
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Bounds
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Depth

/-!
# Sequential depth of the actual reusable-bank round

The independent unit-duration bound includes the chosen compiled member,
each original Z measurement, the actual packing instruction, every reset
measurement and correction, and the fixed literal X reload. The original
bank remains resident, and classical selection preserves every native instruction.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

/-- Independent serial-stage bound including every operation between consecutive rounds. -/
def unitDepthBound (m ell width N : Nat) : Nat :=
  compiledCircuitEventUnitDepth m ell width N +
    (resultBits m ell width +
      (1 + (2 * totalQubits (registerParameters m ell width) + reloadXCount m ell width N)))

/-- Independent complete quantum time with one simultaneous reset correction layer. -/
def quantumTimeBound (m ell width N : Nat) : Nat :=
  compiledCircuitEventUnitDepth m ell width N +
    ((if totalQubits (registerParameters m ell width) = 0 then 0 else 1) +
      reloadXCount m ell width N)

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

private lemma selected_depth_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (path : (selected m ell width sameWires parameter N generator target).Path) :
    (selected m ell width sameWires parameter N generator target).depth (fun _ => 1) path ≤
      compiledCircuitEventUnitDepth m ell width N := by
  rcases path with ⟨value, _⟩
  change DepthExpr.depthEval (fun _ => 1)
    ((compiledCircuit m ell width N (generator value) (target value)).eventDepth
      BitWord.model .empty) ≤ _
  exact compiledCircuit_eventUnitDepth_classical_context_le m ell width N
    (generator value) (target value) BitWord.model .empty

private lemma measured_depth
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).Path) :
    (Circuit.measurementSequence (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).depth (fun _ => 1) path =
      resultBits m ell width :=
  (Circuit.measurementSequence_unitDepth (readouts m ell width sameWires cells) path).trans
    (shortDLP_runtimeReadouts_length m ell width sameWires cells)

private lemma resetReload_depth_le (N : Nat)
    (path : (resetReload m ell width sameWires N).Path) :
    (resetReload m ell width sameWires N).depth (fun _ => 1) path ≤
      2 * totalQubits (registerParameters m ell width) + reloadXCount m ell width N := by
  change (ZReset.BankParallel.code
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires)
      BitWord.model).depth (fun _ => 1) path.1 +
    DepthExpr.depthEval (fun _ => 1)
      ((RuntimePlacement.reloadProgram m ell width sameWires N).eventDepth
        BitWord.model .empty) ≤ _
  apply Nat.add_le_add
  · exact (ZReset.BankParallel.code_unitDepth_le (services := .empty)
      (operations := BitWord.model)
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires)
      path.1).trans_eq
        (congrArg (2 * ·) (shortDLP_runtimeRound_systemCount m ell width sameWires))
  · change DepthExpr.depthEval (fun _ => 1)
      ((CompiledMAU.reloadProgram m ell width N).eventDepth BitWord.model .empty) ≤ _
    exact (UnitaryCircuit.unitaryCircuit_unit_depth_classical_context
      (CompiledMAU.reloadProgram m ell width N) BitWord.model .empty).le.trans
      (shortDLP_reload_unitDepth m ell width N).le

/-- Every actual path respects the complete depth bound including reset and seed reload. -/
lemma shortDLP_runtimeRound_unitDepth_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    (code m ell width sameWires parameter N generator target cells result).depth
      (fun _ => 1) path ≤ unitDepthBound m ell width N :=
  Nat.add_le_add
    (selected_depth_le m ell width sameWires parameter N generator target path.1)
    (Nat.add_le_add (measured_depth m ell width sameWires cells path.2.1).le
      (Nat.add_le_add (Nat.le_refl 1)
        (resetReload_depth_le m ell width sameWires N path.2.2.2)))

/-- The simultaneous reset contributes at most one quantum layer before the literal seed reload. -/
lemma shortDLP_runtimeResetReload_quantumTime_le (N : Nat)
    (path : (resetReload m ell width sameWires N).Path) :
    (resetReload m ell width sameWires N).quantumTime path ≤
      (if totalQubits (registerParameters m ell width) = 0 then 0 else 1) +
        reloadXCount m ell width N := by
  change (ZReset.BankParallel.code
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires)
      BitWord.model).quantumTime path.1 +
    (Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := .empty)
      (RuntimePlacement.reloadProgram m ell width sameWires N)).quantumTime path.2 ≤ _
  apply Nat.add_le_add
  · simpa only [shortDLP_runtimeRound_systemCount m ell width sameWires] using
      ZReset.BankParallel.code_quantumTime_le_layer (services := .empty)
        (operations := BitWord.model)
        (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) path.1
  · refine (Circuit.quantumTime_le_unitDepth _ path.2).trans ?_
    change DepthExpr.depthEval (fun _ => 1)
      ((CompiledMAU.reloadProgram m ell width N).eventDepth BitWord.model .empty) ≤ _
    exact (UnitaryCircuit.unitaryCircuit_unit_depth_classical_context
      (CompiledMAU.reloadProgram m ell width N) BitWord.model .empty).le.trans
      (shortDLP_reload_unitDepth m ell width N).le

/-- Complete actual round time excludes classical processing and charges the real reset layer. -/
lemma shortDLP_runtimeRound_quantumTime_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    (code m ell width sameWires parameter N generator target cells result).quantumTime path ≤
      quantumTimeBound m ell width N := by
  have measured :
      (Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).quantumTime path.2.1 = 0 := by
    simp [Circuit.quantumTime, Circuit.measurementSequence_depth, Circuit.zEvent]
  have packed :
      (BitWord.instruction (execution := model) (packing m ell width cells result)).quantumTime
          path.2.2.1 = 0 :=
    Circuit.quantumTime_classical _ _
  change (selected m ell width sameWires parameter N generator target).quantumTime path.1 +
      ((Circuit.measurementSequence (allowAllocation := true) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells)).quantumTime path.2.1 +
      ((BitWord.instruction (execution := model) (packing m ell width cells result)).quantumTime
          path.2.2.1 +
        (resetReload m ell width sameWires N).quantumTime path.2.2.2)) ≤ _
  rw [measured, packed, zero_add, zero_add]
  exact Nat.add_le_add
    ((Circuit.quantumTime_le_unitDepth _ path.1).trans
      (selected_depth_le m ell width sameWires parameter N generator target path.1))
    (shortDLP_runtimeResetReload_quantumTime_le m ell width sameWires N path.2.2.2)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
