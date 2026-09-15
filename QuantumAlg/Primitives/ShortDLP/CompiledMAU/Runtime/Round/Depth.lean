/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Depth

/-!
# Sequential depth of the actual reusable-bank round

The independent unit-duration bound includes the chosen compiled member,
each original Z measurement, the actual packing instruction, every reset
measurement and correction, and the fixed literal X reload. No preparation
is repeated, and classical dispatch does not remove a native gate control.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

/-- Independent serial-stage bound including every operation between consecutive rounds. -/
def unitDepthBound (m ell width N : Nat) : Nat :=
  compiledCircuitEventUnitDepth m ell width N +
    (resultBits m ell width +
      (1 + (2 * totalQubits (registerParameters m ell width) + reloadXCount m ell width N)))

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

private theorem selected_depth_le {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (path : (selected m ell width sameWires parameter N generator target).Path) :
    (selected m ell width sameWires parameter N generator target).depth (fun _ => 1) path ≤
      compiledCircuitEventUnitDepth m ell width N :=
  compiledCircuit_eventUnitDepth_le m ell width N (generator path.1) (target path.1)

private theorem measured_depth
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (readouts m ell width sameWires cells)).Path) :
    (Circuit.measurementSequence (readouts m ell width sameWires cells)).depth (fun _ => 1) path =
      resultBits m ell width :=
  (Circuit.measurementSequence_unitDepth (readouts m ell width sameWires cells) path).trans
    (shortDLP_runtimeReadouts_length m ell width sameWires cells)

private theorem resetReload_depth (N : Nat)
    (path : (resetReload m ell width sameWires N).Path) :
    (resetReload m ell width sameWires N).depth (fun _ => 1) path =
      2 * totalQubits (registerParameters m ell width) + reloadXCount m ell width N :=
  congrArg₂ Nat.add
    ((ZReset.BankScope.zResetBankScope_unitDepth
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) path.1).trans
      (congrArg (2 * ·) (systemCount_eq m ell width sameWires)))
    (shortDLP_reload_unitDepth m ell width N)

/-- Every actual path respects the complete depth bound including reset and seed reload. -/
theorem shortDLP_runtimeRound_unitDepth_le {shape : CShape} (parameter : CInputRef ctx shape)
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
        (resetReload_depth m ell width sameWires N path.2.2.2).le))

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
