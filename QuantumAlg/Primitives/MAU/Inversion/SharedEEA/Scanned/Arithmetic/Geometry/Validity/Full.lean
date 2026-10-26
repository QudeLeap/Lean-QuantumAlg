/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Validity
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Readout

/-!
# Paid full-carry validity with an arbitrary original Iter

Two actual X masks use the same complete temporary carry as a negative
root. The native pruned selector toggles only the original Iter, and
both masks and every prefix position are restored. No high carry is
discarded before the physical window test.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def maskGate (width : Nat) : GateSpec (encoding width) := .x (conjunctionBit width)

/-- Execute both negative-root masks around the actual existing unary validity tree. -/
def negativeProgram (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  .seq ((maskGate width).program (QubitLayout.canonical _) .empty)
    (.seq (program width) ((maskGate width).program (QubitLayout.canonical _) .empty))

/-- The exact complete-state action of the paid masks and original predicate. -/
def negativeStep (width : Nat) (state : Data width) : Data width :=
  (conjunctionBit width).flip (step width ((conjunctionBit width).flip state))

/-- The same carry is restored and the original dirty output is toggled by the full predicate. -/
lemma negativeStep_eq (width : Nat) (state : Data width) :
    negativeStep width state =
      if !state.2.2.2 && decide (0 < state.2.1.toNat ∧ state.2.1.toNat ≤ width + 3) then
        (output width).flip state else state := by
  unfold negativeStep step
  change (conjunctionBit width).flip
    (if !state.2.2.2 && decide (0 < state.2.1.toNat ∧ state.2.1.toNat ≤ width + 3) then
      (output width).flip ((conjunctionBit width).flip state)
      else (conjunctionBit width).flip state) = _
  split
  · rw [EncodedBit.flip_comm, EncodedBit.flip_flip]
  · rw [EncodedBit.flip_flip]

/-- Actual negative-root execution preserves every coherent phase on the original full frame. -/
lemma negativeProgram_apply_encoded_ket (width : Nat)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (negativeProgram width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (negativeStep width state))) := by
  have mask := (GateSpec.realizes (QubitLayout.canonical _) .empty (maskGate width)
    environment).apply_encoded_ket
  have maskStep (value : Data width) :
      (maskGate width).step value = (conjunctionBit width).flip value := rfl
  have nextClean : ((conjunctionBit width).flip state).2.2.1 =
      0#(ScanMetadata.addressWidth width) := clean
  rw [negativeProgram, UnitaryCircuit.applyNormalized_seq, mask, maskStep,
    UnitaryCircuit.applyNormalized_seq,
    program_apply_encoded_ket width environment ((conjunctionBit width).flip state) nextClean,
    mask, maskStep]
  rfl

/-- The entire pool returns, including the complete temporary length and the physical carry. -/
lemma negativeStep_pool (width : Nat) (state : Data width) :
    (negativeStep width state).2 = state.2 := by
  rw [negativeStep_eq]
  split <;> rfl

/-- No original register except the designated arbitrary Iter can change. -/
lemma negativeStep_observed (width : Nat) (state : Data width)
    (observed : EncodedBit (encoding width))
    (different : (output width).wire ≠ observed.wire) :
    observed.get (negativeStep width state) = observed.get state := by
  rw [negativeStep_eq]
  split
  · exact get_flip_of_wire_ne _ _ different state
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity
