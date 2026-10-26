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

lemma toffoli7TRow0 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 0 j = toffoliOp 0 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (0 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

lemma toffoli7TRow1 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 1 j = toffoliOp 1 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (1 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

lemma toffoli7TRow2 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 2 j = toffoliOp 2 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (2 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

lemma toffoli7TRow3 :
    ∀ j : Fin 8, (toffoli7TCircuit oracles).binaryMatrix environment 3 j = toffoliOp 3 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (3 : Fin 8) column) (toffoli7T_matrix_sparse oracles environment)

end

end QuantumAlg.FTQC

end
