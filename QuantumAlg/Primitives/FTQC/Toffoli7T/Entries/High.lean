/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.FTQC.Toffoli7T.Base
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Parity

/-! # Original matrix rows from the exact sparse phase proof -/

section

namespace QuantumAlg.FTQC

noncomputable section

variable {oracles : OracleModel} (environment : oracles.Interpretation)

lemma toffoli7TRow4 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 4 j = toffoliOp 4 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (4 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

lemma toffoli7TRow5 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 5 j = toffoliOp 5 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (5 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

lemma toffoli7TRow6 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 6 j = toffoliOp 6 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (6 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

lemma toffoli7TRow7 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 7 j = toffoliOp 7 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (7 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

end

end QuantumAlg.FTQC

end
