/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.FTQC.ToffoliTDepth3.Base
import all QuantumAlg.Primitives.FTQC.ToffoliTDepth3.Parity

/-! # Original matrix rows from the exact sparse phase proof -/

section

namespace QuantumAlg.FTQC

noncomputable section

variable {oracles : OracleModel} (environment : oracles.Interpretation)

lemma toffoliTDepth3Row4 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 4 j = toffoliOp 4 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (4 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

lemma toffoliTDepth3Row5 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 5 j = toffoliOp 5 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (5 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

lemma toffoliTDepth3Row6 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 6 j = toffoliOp 6 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (6 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

lemma toffoliTDepth3Row7 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 7 j = toffoliOp 7 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (7 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

end

end QuantumAlg.FTQC

end
