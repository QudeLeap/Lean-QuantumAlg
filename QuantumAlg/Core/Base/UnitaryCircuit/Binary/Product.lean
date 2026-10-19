/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Binary matrices of actual indexed execution

The binary view preserves the complete ordered product of actual stage matrices.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

private lemma reindex_fold {R S : Register} (equivalence : R.Index ≃ S.Index)
    (operators : List (UnitaryOperator R)) (initial : UnitaryOperator R) :
    UnitaryOperator.reindex equivalence
        (operators.foldl (fun accumulated next => next * accumulated) initial) =
      (operators.map (UnitaryOperator.reindex equivalence)).foldl
        (fun accumulated next => next * accumulated)
        (UnitaryOperator.reindex equivalence initial) := by
  induction operators generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, ih,
        UnitaryOperator.unitaryOperator_reindex_mul]

/-- Changing matrix coordinates preserves every stage and the original execution order. -/
public lemma unitaryCircuit_binaryMatrix_indexedProduct
    {gates : GateModel} {oracles : OracleModel} {width : Nat}
    (label : String) (steps : Nat)
    (start : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout)
    (step : Fin steps → UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    ((indexedProduct label steps start step).binaryMatrix environment) =
      (List.ofFn (fun index => ((step index).binaryMatrix environment))).foldl
        (fun accumulated next => next * accumulated) (start.binaryMatrix environment) := by
  unfold binaryMatrix
  rw [indexedProduct_matrix]
  have preserved := reindex_fold
    (R := (QuantumSignature.qubits width).canonicalPlacement.layout.register) (S := Qubits width)
    (QuantumSignature.qubitsIndexEquiv width)
    (List.ofFn (fun index => ((step index).matrix environment))) (start.matrix environment)
  simpa only [List.map_ofFn, Function.comp_def] using preserved

end

end QuantumAlg.UnitaryCircuit
