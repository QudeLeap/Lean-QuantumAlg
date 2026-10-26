/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Validity.Full
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Validity.High
import all QuantumAlg.Util.NumberTheory.SharedEEA.Geometry.Validity

/-!
# Full finite positive-length validity with no small-width exclusions

Both actual carry branches act on the original Iter and restore the
entire shared pool. Their disjoint mathematical predicates together
test the complete temporary geometry word. The exact-capacity width-one
case and both high lengths at width zero remain part of the contract.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The actual negative-root and high-root programs share the original output and clean prefixes. -/
def fullProgram (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (negativeProgram width).seq (highProgram width)

/-- The independent predicate reads the entire temporary word, including its physical carry. -/
def fullStep (width : Nat) (state : Data width) : Data width :=
  if decide (0 < (ArithmeticGeometry.targetValue width state).toNat ∧
      (ArithmeticGeometry.targetValue width state).toNat ≤ width + 3)
    then (output width).flip state else state

private lemma combined_step (width : Nat) (state : Data width) :
    highStep width (negativeStep width state) = fullStep width state := by
  have pool := negativeStep_pool width state
  have address := congrArg Prod.fst pool
  have carry := congrArg (fun value : Pool width => value.2.2) pool
  unfold highStep
  rw [address, carry, negativeStep_eq, fullStep, ArithmeticGeometry.targetValue,
    ScanGeometry.full_validity]
  cases low : (!state.2.2.2 && decide
      (0 < state.2.1.toNat ∧ state.2.1.toNat ≤ width + 3)) <;>
    cases high : (state.2.2.2 && decide
      (2 ^ ScanMetadata.addressWidth width + state.2.1.toNat ≤ width + 3)) <;>
    simp only [Bool.false_eq_true, Bool.false_xor, Bool.true_xor,
      Bool.not_false, Bool.not_true, if_true, if_false, EncodedBit.flip_flip]

/-- Every finite carrier is accepted or rejected by its exact untruncated physical length. -/
lemma fullProgram_apply_encoded_ket (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (fullProgram width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (fullStep width state))) := by
  have nextClean : (negativeStep width state).2.2.1 =
      0#(ScanMetadata.addressWidth width) :=
    (congrArg (fun value : Pool width => value.2.1) (negativeStep_pool width state)).trans clean
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq
    (negativeProgram_apply_encoded_ket width environment state clean)
    (highProgram_apply_encoded_ket width environment (negativeStep width state) nextClean)
  rw [combined_step] at actual
  exact actual

/-- The complete temporary length and every original prefix return unchanged. -/
lemma fullStep_pool (width : Nat) (state : Data width) : (fullStep width state).2 = state.2 := by
  unfold fullStep
  split <;> rfl

/-- Every other original source position survives, including phase flags and metadata. -/
lemma fullStep_observed (width : Nat) (state : Data width)
    (observed : EncodedBit (encoding width))
    (different : (output width).wire ≠ observed.wire) :
    observed.get (fullStep width state) = observed.get state := by
  unfold fullStep
  split
  · exact get_flip_of_wire_ne _ _ different state
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity
