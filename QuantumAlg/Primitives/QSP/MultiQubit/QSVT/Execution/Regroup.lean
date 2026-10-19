/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average.Block
import all QuantumAlg.Components.Oracle.SignalProcessing

/-!
# Standard block-encoding interfaces for actual QSVT words

The construction nests transformation ancillas before the source register.
Regrouping the same ordered physical wires gives the standard block-encoding
interface. This is an equality cast, preserving every gate and source query.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution
noncomputable section

/-- Regrouping one transformation ancilla realizes the existing binary block convention. -/
lemma regroup_one_binaryMatrix {gates : GateModel} {oracles : OracleModel} {m n : Nat}
    (word : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (1 + (m + n))).canonicalPlacement.layout)
        (environment : oracles.Interpretation) :
    ((word.castQubitWidth (Nat.add_assoc 1 m n).symm).binaryMatrix environment) =
      reassociatePhaseAncillaOperator (m := m) (n := n) (word.binaryMatrix environment) := by
  rw [UnitaryCircuit.castQubitWidth_binaryMatrix]
  rfl

/-- Regrouping three transformation ancillas realizes the shared-branch block convention. -/
lemma regroup_three_binaryMatrix {gates : GateModel} {oracles : OracleModel} {m n : Nat}
    (word : UnitaryCircuit gates oracles
      (QuantumSignature.qubits (1 + (1 + (1 + (m + n))))).canonicalPlacement.layout)
        (environment : oracles.Interpretation) :
    ((word.castQubitWidth
      (show 1 + (1 + (1 + (m + n))) = (1 + (1 + (1 + m))) + n by omega)).binaryMatrix environment) =
      SharedFour.reassociateThree (m := m) (n := n) (word.binaryMatrix environment) := by
  rw [UnitaryCircuit.castQubitWidth_binaryMatrix]
  rfl

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution
