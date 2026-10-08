/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Realization
import Mathlib.Logic.Function.Iterate

/-!
# Exact realization of an actual symbolic circuit repetition

These laws use the matrix of the existing symbolic repetition constructor.
They transport exact normalized states and then the encoded basis action,
with no independently supplied circuit, erased relative phase, or change
to the existing repetition's stored elementary events and depth.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

private theorem normalized_of_matrix_eq {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {layout : QuantumLayout count}
    (first second : UnitaryCircuit gates oracles layout)
    (same : (first.matrix : HilbertOperator layout.register) =
      (second.matrix : HilbertOperator layout.register))
    (state : NormalizedVector layout.register) :
    first.applyNormalized state = second.applyNormalized state := by
  apply NormalizedVector.ext
  intro index
  change HilbertOperator.applyVec (first.matrix : HilbertOperator layout.register)
      (state : HilbertVector layout.register) index =
    HilbertOperator.applyVec (second.matrix : HilbertOperator layout.register)
      (state : HilbertVector layout.register) index
  rw [same]

private theorem iterate_applyNormalized {gates : GateModel} {oracles : OracleModel}
    (count : Nat) {systemCount : Nat} {layout : QuantumLayout systemCount}
    (body : UnitaryCircuit gates oracles layout)
    (state : NormalizedVector layout.register) :
    (iterate count body).applyNormalized state = (body.applyNormalized)^[count] state := by
  induction count with
  | zero =>
    have same : ((iterate 0 body).matrix : HilbertOperator layout.register) =
        (identity gates oracles layout).matrix := by
      rw [iterate_matrix, pow_zero, identity_matrix]
    refine (normalized_of_matrix_eq _ _ same state).trans ?_
    apply NormalizedVector.ext
    intro index
    change (1 : UnitaryOperator layout.register).applyVec state index = state index
    rw [UnitaryOperator.one_applyVec]
  | succ count inductionHypothesis =>
    have same : ((iterate (count + 1) body).matrix : HilbertOperator layout.register) =
        ((iterate count body).seq body).matrix := by
      rw [iterate_matrix, seq_matrix, iterate_matrix, pow_succ']
    rw [normalized_of_matrix_eq _ _ same state, applyNormalized_seq, inductionHypothesis]
    exact (Function.iterate_succ_apply' body.applyNormalized count state).symm

namespace Realizes

/-- Repeating the actual symbolic native circuit repeats its exact encoded semantic action. -/
theorem iterate {Data : Type} {encoding : BinaryLabelEncoding Data}
    {gates : GateModel} {oracles : OracleModel}
    {layout : QubitLayout encoding.width}
    {body : UnitaryCircuit gates oracles layout.toQuantum} {step : Data → Data}
    (realizes : Realizes encoding body step) (count : Nat) :
    Realizes encoding (UnitaryCircuit.iterate count body) (step^[count]) where
  apply_encoded_ket := by
    intro state
    rw [iterate_applyNormalized]
    induction count generalizing state with
    | zero => rfl
    | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis, realizes.apply_encoded_ket,
        Function.iterate_succ_apply']

end Realizes

end

end QuantumAlg.UnitaryCircuit
