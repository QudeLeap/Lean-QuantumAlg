/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Components.Gates.ControlledPhase.Physical
import all QuantumAlg.Components.Gates.ControlledPhase.QubitRegister
import all QuantumAlg.Components.Gates.Swap.Physical
import all QuantumAlg.Components.Gates.Swap.QubitRegister
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import Mathlib.Data.Nat.Choose.Basic

/-!
# Dependency depth of the recursive native QFT word

The serial construction retains every native layer within controlled phases
and swaps. Placing the recursively executed tail preserves its full depth.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

variable (oracles : OracleModel)

private theorem phaseStep_depth (n : Nat) (offset : Fin n) :
    (phaseStep oracles n offset).evaluatedEventDepth (fun _ => 1) = 5 := by
  unfold phaseStep QFTPrimitive.circuit Gate.ControlledPhase.qubitCircuit
  exact Gate.ControlledPhase.controlledPhase_circuitAt_unit_depth _ _ _ _ _ _ _ _

private theorem phasePrefix_depth (n count : Nat) (bounded : count ≤ n) :
    (phasePrefix oracles n count bounded).evaluatedEventDepth (fun _ => 1) = 5 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.evaluatedEventDepth_seq, ih, phaseStep_depth]
      omega

private theorem tailLayer_depth (n : Nat)
    (body : UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout n)) :
    (tailLayer oracles n body).evaluatedEventDepth (fun _ => 1) =
      body.evaluatedEventDepth (fun _ => 1) := by
  unfold tailLayer
  change DepthExpr.depthEval (fun _ => 1) (UnitaryCircuit.placeAt _ _ _ _ body).eventDepth = _
  rw [UnitaryCircuit.placeAt_eventDepth]
  rfl

private theorem noSwap_depth (n : Nat) :
    (noSwap oracles n).evaluatedEventDepth (fun _ => 1) = n + 5 * n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [noSwap, UnitaryCircuit.evaluatedEventDepth_seq,
        UnitaryCircuit.evaluatedEventDepth_seq, phaseLayer, phasePrefix_depth,
        tailLayer_depth, ih]
      have leading : (leadingHadamard oracles n).evaluatedEventDepth (fun _ => 1) = 1 := by rfl
      rw [leading]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      change 1 + (5 * n + (n + 5 * n.choose 2)) = (n + 1) + 5 * (n + n.choose 2)
      omega

private theorem swapStep_depth (n : Nat) (index : Fin (n / 2)) :
    (swapStep oracles n index).evaluatedEventDepth (fun _ => 1) = 3 := by
  unfold swapStep QFTPrimitive.circuit Gate.Swap.qubitCircuit
  exact Gate.Swap.swap_circuitAt_unit_depth _ _ _ _ _ _ _

private theorem reversePrefix_depth (n count : Nat) (bounded : count ≤ n / 2) :
    (reversePrefix oracles n count bounded).evaluatedEventDepth (fun _ => 1) = 3 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [reversePrefix, UnitaryCircuit.evaluatedEventDepth_seq, ih, swapStep_depth]
      omega

/-- The complete serial native word retains all layers inside its phase and SWAP expansions. -/
public theorem qftNative_circuit_unit_depth (n : Nat) :
    (circuit oracles n).evaluatedEventDepth (fun _ => 1) =
      n + 5 * n.choose 2 + 3 * (n / 2) := by
  rw [circuit, UnitaryCircuit.evaluatedEventDepth_seq, noSwap_depth,
    bitReverse, reversePrefix_depth]

end

end QuantumAlg.QuantumFourierTransform.Native
