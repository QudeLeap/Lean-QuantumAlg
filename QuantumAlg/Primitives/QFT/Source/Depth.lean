/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Source
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

Each native Hadamard, controlled phase and SWAP occupies one source layer.
Placing the recursively executed tail preserves its full dependency depth.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

variable (oracles : OracleModel)
variable (duration : Resource.Event (.quantum FourierGate.model oracles) → Nat)

private lemma phaseStep_depth (n : Nat) (offset : Fin n) :
    (phaseStep oracles n offset).evaluatedEventDepth duration =
      duration (.gate .controlledPhase) := by rfl

private lemma phasePrefix_depth (n count : Nat) (bounded : count ≤ n) :
    (phasePrefix oracles n count bounded).evaluatedEventDepth duration =
      duration (.gate .controlledPhase) * count := by
  induction count with
  | zero => simp [phasePrefix]
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.evaluatedEventDepth_seq, ih, phaseStep_depth]
      ring

private lemma tailLayer_depth (n : Nat)
    (body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout n)) :
    (tailLayer oracles n body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  unfold tailLayer
  change DepthExpr.depthEval duration (UnitaryCircuit.placeAt _ _ _ _ body).eventDepth = _
  rw [UnitaryCircuit.placeAt_eventDepth]
  rfl

private lemma noSwap_depth (n : Nat) :
    (noSwap oracles n).evaluatedEventDepth duration = n * duration (.gate .hadamard) +
      n.choose 2 * duration (.gate .controlledPhase) := by
  induction n with
  | zero => simp [noSwap]
  | succ n ih =>
      rw [noSwap, UnitaryCircuit.evaluatedEventDepth_seq,
        UnitaryCircuit.evaluatedEventDepth_seq, phaseLayer, phasePrefix_depth,
        tailLayer_depth, ih]
      have leading : (leadingHadamard oracles n).evaluatedEventDepth duration =
          duration (.gate .hadamard) := by rfl
      rw [leading]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      ring

/-- Every duration assignment observes the same sequential QFT and disjoint final reversal. -/
public lemma qftSource_circuit_depth (n : Nat) :
    (circuit oracles n).evaluatedEventDepth duration =
      n * duration (.gate .hadamard) +
        n.choose 2 * duration (.gate .controlledPhase) +
          (if n / 2 = 0 then 0 else duration (.gate .swap)) := by
  rw [circuit, UnitaryCircuit.evaluatedEventDepth_seq, noSwap_depth,
    bitReverse, reversePrefix_evaluatedEventDepth]

/-- Exact unit-duration depth, including the one-layer nonempty wire reversal. -/
public lemma qftSource_circuit_unit_depth (n : Nat) :
    (circuit oracles n).evaluatedEventDepth (fun _ => 1) =
      n + n.choose 2 + (if n / 2 = 0 then 0 else 1) := by
  simpa using qftSource_circuit_depth oracles (fun _ => 1) n

end
end QuantumAlg.QuantumFourierTransform.Source
