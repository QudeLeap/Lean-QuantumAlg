/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Encoding

/-!
# Mathematical correctness of the actual raw extended-Euclidean values

The three actual output reads are related to the original finished state.
Existing mathematical correctness then gives the deterministic selected
values, the Bezout equation and the original public coefficient bounds. These
are read-value theorems; any subsequent public output packing remains a
separate actual instruction sequence.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Three copied finished-state fields are exactly the original deterministic XGCD values. -/
lemma xgcdNativeRawOutputs_finalState_values (outputs : RawOutputs ctx width)
    (store : Store ctx) (input : PureXGCD.Input width)
    (gcdValue : (store.read (GCD.cellRead outputs.gcd)).toNat =
      (PureXGCD.finalState input).second)
    (leftValue : decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient)) =
      (PureXGCD.finalState input).secondLeftCoefficient)
    (rightValue : decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient)) =
      (PureXGCD.finalState input).secondRightCoefficient) :
    (store.read (GCD.cellRead outputs.gcd)).toNat = (PureXGCD.eval input).gcd.val ∧
      decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient)) =
        (PureXGCD.eval input).leftCoefficient.toInt ∧
      decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient)) =
        (PureXGCD.eval input).rightCoefficient.toInt := by
  refine ⟨gcdValue.trans
    (NumberTheory.XGCD.xgcdFinalState_resultGCD_eq_eval input), ?_, ?_⟩
  · exact leftValue.trans
      ((NumberTheory.XGCD.xgcdFinalState_resultLeftCoefficient_eq_gcdA input).trans
        (NumberTheory.XGCD.xgcdEval_leftCoefficient_toInt input).symm)
  · exact rightValue.trans
      ((NumberTheory.XGCD.xgcdFinalState_resultRightCoefficient_eq_gcdB input).trans
        (NumberTheory.XGCD.xgcdEval_rightCoefficient_toInt input).symm)

/-- Actual raw result reads satisfy GCD, Bezout and both original public signed intervals. -/
lemma xgcdNativeRawOutputs_finalState_correct (outputs : RawOutputs ctx width)
    (store : Store ctx) (input : PureXGCD.Input width)
    (gcdValue : (store.read (GCD.cellRead outputs.gcd)).toNat =
      (PureXGCD.finalState input).second)
    (leftValue : decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient)) =
      (PureXGCD.finalState input).secondLeftCoefficient)
    (rightValue : decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient)) =
      (PureXGCD.finalState input).secondRightCoefficient) :
    (store.read (GCD.cellRead outputs.gcd)).toNat = Nat.gcd input.left.val input.right.val ∧
      ((store.read (GCD.cellRead outputs.gcd)).toNat : Int) =
        (input.left.val : Int) *
            decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient)) +
          (input.right.val : Int) *
            decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient)) ∧
      NumberTheory.XGCD.coefficientRepresentable (width := width)
        (decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient))) ∧
      NumberTheory.XGCD.coefficientRepresentable (width := width)
        (decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient))) := by
  have values := xgcdNativeRawOutputs_finalState_values outputs store input
    gcdValue leftValue rightValue
  rw [values.1, values.2.1, values.2.2]
  exact PureXGCD.xgcdEval_accepts input

/-- A public result with these actual raw read-values satisfies the original acceptance relation. -/
lemma xgcdNativeRawOutputs_accepts (outputs : RawOutputs ctx width)
    (store : Store ctx) (input : PureXGCD.Input width)
    (gcdValue : (store.read (GCD.cellRead outputs.gcd)).toNat =
      (PureXGCD.finalState input).second)
    (leftValue : decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient)) =
      (PureXGCD.finalState input).secondLeftCoefficient)
    (rightValue : decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient)) =
      (PureXGCD.finalState input).secondRightCoefficient)
    (output : PureXGCD.Output width)
    (publicGCD : output.gcd.val = (store.read (GCD.cellRead outputs.gcd)).toNat)
    (publicLeft : output.leftCoefficient.toInt =
      decodeRawSignedWord (store.read (GCD.cellRead outputs.leftCoefficient)))
    (publicRight : output.rightCoefficient.toInt =
      decodeRawSignedWord (store.read (GCD.cellRead outputs.rightCoefficient))) :
    PureXGCD.accepts input output := by
  have correct := xgcdNativeRawOutputs_finalState_correct outputs store input
    gcdValue leftValue rightValue
  change output.gcd.val = _ ∧ (output.gcd.val : Int) = _ ∧ _ ∧ _
  rw [publicGCD, publicLeft, publicRight]
  exact correct

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
