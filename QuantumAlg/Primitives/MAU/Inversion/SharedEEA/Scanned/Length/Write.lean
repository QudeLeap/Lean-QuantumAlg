/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Prepare
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Value
import all QuantumAlg.Components.Encoded.BitGates.Word.Compute

/-!
# Complete native prepared length XOR and actual uncomputation

The actual preparation, paid copy and full native adjoint restore every
nonoutput bit on all encoded inputs, including arbitrary incoming pool
values and dirty Iter. Identifying the prepared mask with the original
natural region size is a separate clean-pool readout obligation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The actual static copy uses the existing narrow active latch or original wide-case Ctrl. -/
def program (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  WordCompute.program (LengthPrepare.program width field first capacity)
    (LengthCopy.program width (decide (LengthClip.narrow width)) field)

/-- Independent complete output action reads the real physically prepared controls and low word. -/
def step (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) : Data width :=
  let prepared := LengthPrepare.step width field first capacity state
  if (LengthCopy.active width (decide (LengthClip.narrow width))).get prepared &&
      !(conjunctionBit width).get prepared then
    Word.xorConstantStep (LengthCopy.target width field) (LengthCopy.value width prepared).toFin
      state
  else state

/-- The actual preparation, native copy and actual adjoint have this full all-label action. -/
lemma program_realizes (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width field first capacity) environment
      (step width field first capacity) := by
  constructor
  intro state
  let prepared := LengthPrepare.step width field first capacity state
  have copied := (LengthCopy.program_realizes width (decide (LengthClip.narrow width)) field
    environment).apply_encoded_ket prepared
  rw [LengthCopy.step_eq_constant] at copied
  exact WordCompute.program_apply_encoded_ket _ _ _ (LengthCopy.target width field)
    (LengthCopy.value width prepared).toFin
    ((LengthCopy.active width (decide (LengthClip.narrow width))).get prepared &&
      !(conjunctionBit width).get prepared) environment
    (LengthPrepare.program_realizes width field first capacity environment) state copied
    (LengthPrepare.step_output_comm width field first capacity _ state)

private lemma xorConstantStep_pool (width : Nat) (field : Field)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    (Word.xorConstantStep (LengthCopy.target width field) mask state).2 = state.2 := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate member
  obtain ⟨bit, _present, rfl⟩ := List.mem_map.mp member
  intro value
  rfl

/-- The original address, prefix and conjunction return exactly, even when initially dirty. -/
lemma step_pool (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) (state : Data width) :
    (step width field first capacity state).2 = state.2 := by
  unfold step
  dsimp only
  split
  · exact xorConstantStep_pool width field _ state
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite
