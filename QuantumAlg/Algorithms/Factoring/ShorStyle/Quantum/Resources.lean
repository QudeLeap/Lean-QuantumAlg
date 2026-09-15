/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Construction
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Source.Resources
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Resources
import all QuantumAlg.Primitives.QFT.Construction

/-!
# Independent native resources of each actually selected Shor quantum member

The original parallel Hadamards and inverse QFT surround the real compiled
selected-power multiplication schedule. Its independent native-coordinate
budget applies to every stored sampler parameter, including total fallback
selection. No caller supplies a gate bound or a modular-power oracle event.
The unit-depth bound retains the actual parallel Hadamard layer and serial
controlled multiplication dependencies.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

/-- The original inverse QFT has its actual Hadamard, controlled-phase and swap coordinates. -/
def readoutBudget (width : Nat) : ResourcePool .quantum :=
  width • ResourcePool.singleton (.gate (.builtin "hadamard")) +
    width.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
      (width / 2) • ResourcePool.singleton (.gate (.builtin "swap"))

/-- Independent native gates for the full actual source member on its existing bank. -/
def eventBudget (N : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton WalshHadamard.hadamardEvent (phaseBits N) +
    (MAU.Exponentiation.Gidney.nativeBudget (phaseBits N) (modulusBits N) +
      readoutBudget (phaseBits N))

/-- Independent unit depth preserves the actual parallel preparation and serial source readout. -/
def depthBound (N : Nat) : Nat :=
  (if phaseBits N = 0 then 0 else 1) +
    (MAU.Exponentiation.Gidney.eventBound (phaseBits N) (modulusBits N) +
      (phaseBits N + phaseBits N * (phaseBits N - 1) / 2 + phaseBits N / 2))

private theorem preparation_pool (t n : Nat) :
    (OrderFinding.orderFindingPreparationCircuit t n).eventCost =
      ResourcePool.singleton WalshHadamard.hadamardEvent t := by
  simp [OrderFinding.orderFindingPreparationCircuit, UnitaryCircuit.tensorQubits]

/-- Every actual selected parameter uses the independently counted compiled native program. -/
theorem program_pool_le {N : Nat} (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (program parameter).eventCost ≤ eventBudget N := by
  let preparation := OrderFinding.orderFindingPreparationCircuit (phaseBits N)
    (modulusBits N + modulusBits N)
  let power := MAU.Exponentiation.Gidney.program (phaseBits N) (modulusBits N)
    (modulus N) (selectedUnit (N := N) parameter)
  let readout := OrderFinding.orderFindingReadoutCircuit (phaseBits N)
    (modulusBits N + modulusBits N)
  have readoutCost : readout.eventCost = readoutBudget (phaseBits N) :=
    (OrderFinding.orderFindingReadoutCircuit_eventCost _ _).trans (QFTCircuit_eventCost_eq _)
  exact (UnitaryCircuit.seq_eventCost preparation (power.seq readout)).le.trans
    (add_le_add (preparation_pool _ _).le
      ((UnitaryCircuit.seq_eventCost power readout).le.trans
        (add_le_add (MAU.Exponentiation.Gidney.gidneyExponent_native_bound
          (phaseBits N) (modulusBits N) (modulus N) (selectedUnit (N := N) parameter))
          readoutCost.le)))

/-- Actual controlled multiplication and source transforms satisfy the independent unit depth. -/
theorem program_unitDepth_le {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (program parameter).evaluatedEventDepth (fun _ => 1) ≤ depthBound N := by
  let preparation := OrderFinding.orderFindingPreparationCircuit (phaseBits N)
    (modulusBits N + modulusBits N)
  let power := MAU.Exponentiation.Gidney.program (phaseBits N) (modulusBits N)
    (modulus N) (selectedUnit (N := N) parameter)
  let readout := OrderFinding.orderFindingReadoutCircuit (phaseBits N)
    (modulusBits N + modulusBits N)
  exact (UnitaryCircuit.evaluatedEventDepth_seq (fun _ => 1)
    preparation (power.seq readout)).le.trans
      (Nat.add_le_add (OrderFinding.Sampling.preparation_depth _ _).le
        ((UnitaryCircuit.evaluatedEventDepth_seq (fun _ => 1) power readout).le.trans
          (Nat.add_le_add (MAU.Exponentiation.Gidney.gidneyExponent_depth_bound
            (phaseBits N) (modulusBits N) (modulus N) (selectedUnit (N := N) parameter))
            (OrderFinding.Sampling.readout_depth _ _).le)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
