/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Hadamard.Three
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Phase

/-!
# Native preparation and unpreparation of all three QSVT ancillas

The two selectors and phase ancilla are converted between zero and plus
states by six actual Hadamards. The body retains its original oracle grants,
native events and full source suffix.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

variable {oracles : OracleModel} {m n : Nat}

/-- Six actual boundary Hadamards around the given original circuit. -/
def wrap (body : UnitaryCircuit AlgorithmGate.model oracles (layout m n)) :
    UnitaryCircuit AlgorithmGate.model oracles (layout m n) :=
  ((Gate.Hadamard.three oracles (m + n)).seq body).seq (Gate.Hadamard.three oracles (m + n))

/-- Full matrix equality for native boundaries, preserving every relative phase. -/
theorem fourWrapper_matrix (body : UnitaryCircuit AlgorithmGate.model oracles (layout m n)) :
    (wrap body).binaryMatrix =
      (Gate.HOp.tensor (Gate.HOp.tensor
        (Gate.HOp.tensor (1 : UnitaryOperator (Qubits (m + n)))))) *
      body.binaryMatrix *
      (Gate.HOp.tensor (Gate.HOp.tensor
        (Gate.HOp.tensor (1 : UnitaryOperator (Qubits (m + n)))))) := by
  rw [wrap, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, Gate.Hadamard.threeHadamard_matrix]
  exact (mul_assoc _ _ _).symm

/-- Both native boundaries are charged in the same resource pool as the executed body. -/
theorem fourWrapper_events (body : UnitaryCircuit AlgorithmGate.model oracles (layout m n)) :
    (wrap body).eventCost = body.eventCost +
      6 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [wrap, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    Gate.Hadamard.threeHadamard_events, show (6 : Nat) = 3 + 3 from rfl, add_nsmul]
  ac_rfl

/-- Boundary preparation and unpreparation add six actual dependency steps. -/
theorem fourWrapper_depth (body : UnitaryCircuit AlgorithmGate.model oracles (layout m n)) :
    (wrap body).evaluatedEventDepth (fun _ => 1) =
      body.evaluatedEventDepth (fun _ => 1) + 6 := by
  rw [wrap, UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    Gate.Hadamard.threeHadamard_depth]
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
