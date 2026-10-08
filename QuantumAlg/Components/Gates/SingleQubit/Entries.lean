/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Exact entries of a native one-qubit operation

The supplied operator acts on the selected dimension-two system. Every other
system remains unchanged, with no dimension or initialization restriction.
-/

namespace QuantumAlg.Gate

noncomputable section

/-- Every native one-qubit entry retains the exact selected operator and full complement. -/
public theorem singleQubitAt_matrix_entry {count : Nat} (ambient : QuantumLayout count)
    (oracles : OracleModel) (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (ambient.wire target).dimension = 2)
    (row column : ambient.Basis) :
    (singleQubitAt ambient oracles operator target qubit).matrix row column =
      operator
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (row target))
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (column target)) *
          (if ((singleQubitApplication ambient operator target qubit).basisEquiv row).2 =
            ((singleQubitApplication ambient operator target qubit).basisEquiv column).2
              then 1 else 0) := by
  let application := singleQubitApplication ambient operator target qubit
  have selected (basis : ambient.Basis) :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 =
        Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) := by
    have coordinates : (application.basisEquiv basis).1 =
        fun _ => Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) := by
      funext index
      fin_cases index
      apply Fin.ext
      rfl
    rw [coordinates]
    generalize Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) = bit
    fin_cases bit <;> rfl
  change application.operator row column = _
  rw [application.application_operator_entry]
  change operator
    (QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv row).1)
    (QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv column).1) *
      (if (application.basisEquiv row).2 = (application.basisEquiv column).2 then 1 else 0) = _
  rw [selected row, selected column]
  rfl

end

end QuantumAlg.Gate
