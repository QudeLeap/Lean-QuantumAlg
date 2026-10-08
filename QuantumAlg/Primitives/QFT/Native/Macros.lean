/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Components.Gates.ControlledPhase.Physical
import all QuantumAlg.Components.Gates.ControlledPhase.QubitRegister
import all QuantumAlg.Components.Gates.Swap
import all QuantumAlg.Components.Gates.Swap.Physical
import all QuantumAlg.Components.Gates.Swap.QubitRegister
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import Mathlib.Data.Nat.Choose.Basic

/-!
# Original QFT macro counts on the same native word

The Hadamard, controlled-phase and SWAP counts describe retained subroutine
occurrences. Every occurrence still contains its complete native expansion.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

variable (oracles : OracleModel) (name : String)

private theorem phaseStep_macro (n : Nat) (offset : Fin n) :
    (phaseStep oracles n offset).macroCount name =
      if "controlled-phase" = name then 1 else 0 := by
  unfold phaseStep QFTPrimitive.circuit Gate.ControlledPhase.qubitCircuit
    Gate.ControlledPhase.circuitAt
  dsimp only
  refine (UnitaryCircuit.placeAt_macroCount Gate.ControlledPhase.layout
    (Gate.ControlledPhase.qubitLayout (n + 1)) _ _
    (Gate.ControlledPhase.circuit oracles (phaseAngle offset.val)) name).trans ?_
  change List.count name ["controlled-phase"] = _
  simp only [List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]

private theorem phasePrefix_macro (n count : Nat) (bounded : count ≤ n) :
    (phasePrefix oracles n count bounded).macroCount name =
      count * (if "controlled-phase" = name then 1 else 0) := by
  induction count with
  | zero =>
      change 0 = _
      simp
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.macroCount_seq, ih, phaseStep_macro]
      ring

private theorem noSwap_macro (n : Nat) :
    (noSwap oracles n).macroCount name =
      n * (if "hadamard" = name then 1 else 0) +
        n.choose 2 * (if "controlled-phase" = name then 1 else 0) := by
  induction n with
  | zero =>
      change 0 = _
      simp
  | succ n ih =>
      rw [noSwap, UnitaryCircuit.macroCount_seq, UnitaryCircuit.macroCount_seq,
        phaseLayer, phasePrefix_macro, tailLayer, UnitaryCircuit.placeAt_macroCount, ih]
      have leading : (leadingHadamard oracles n).macroCount name =
          if "hadamard" = name then 1 else 0 := by
        change List.count name ["hadamard"] = _
        simp only [List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]
      rw [leading]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      ring

private theorem swapStep_macro (n : Nat) (index : Fin (n / 2)) :
    (swapStep oracles n index).macroCount name = if "swap" = name then 1 else 0 := by
  unfold swapStep QFTPrimitive.circuit Gate.Swap.qubitCircuit Gate.Swap.circuitAt
  dsimp only
  refine (UnitaryCircuit.placeAt_macroCount Gate.Swap.layout (Gate.Swap.qubitLayout n)
    _ _ (Gate.Swap.circuit oracles) name).trans ?_
  change List.count name ["swap"] = _
  simp only [List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]

private theorem reversePrefix_macro (n count : Nat) (bounded : count ≤ n / 2) :
    (reversePrefix oracles n count bounded).macroCount name =
      count * (if "swap" = name then 1 else 0) := by
  induction count with
  | zero =>
      change 0 = _
      simp
  | succ count ih =>
      rw [reversePrefix, UnitaryCircuit.macroCount_seq, ih, swapStep_macro]
      ring

/-- The source-level macro counts are observations of the same fully expanded native QFT word. -/
public theorem qftNative_circuit_macro_count (n : Nat) :
    (circuit oracles n).macroCount name =
      n * (if "hadamard" = name then 1 else 0) +
        n.choose 2 * (if "controlled-phase" = name then 1 else 0) +
          (n / 2) * (if "swap" = name then 1 else 0) := by
  rw [circuit, UnitaryCircuit.macroCount_seq, noSwap_macro, bitReverse, reversePrefix_macro]

end

end QuantumAlg.QuantumFourierTransform.Native
