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

lemma toffoliTDepth3Row0 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 0 j = toffoliOp 0 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (0 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

lemma toffoliTDepth3Row1 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 1 j = toffoliOp 1 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (1 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

lemma toffoliTDepth3Row2 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 2 j = toffoliOp 2 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (2 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

lemma toffoliTDepth3Row3 :
    ∀ j : Fin 8, (toffoliTDepth3Core oracles).binaryMatrix environment 3 j = toffoliOp 3 j := by
  intro column
  exact congrArg (fun operator : UnitaryOperator (Qubits 3) =>
    operator (3 : Fin 8) column) (toffoliTDepth3Core_matrix_sparse oracles environment)

end

end QuantumAlg.FTQC

end
