/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Execution
import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual first-success latch values and nominal option writes

The existing selector consumes the candidate decoded by the real unpack.
Its two persistent latches represent the first present result, including all
failure cases. The initial closed XOR clears the tag for every incoming store;
the selected word needs no initial-value premise because an absent tag hides
that payload in the actual final option encoding.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Interpretation of the two actual persistent latches as the final nominal result. -/
def latchValue (cells : Cells ctx N) (store : Store ctx) :
    CShape.Value (.option (.unsignedWord (modulusBits N))) :=
  CShape.packOption (.product (store.read (.storage cells.accepted.toCStorageRef))
    (store.read (.storage cells.selected.toCStorageRef)))

/-- The left present result has priority over every later optional candidate. -/
def firstPresent {width : Nat}
    (earlier later : CShape.Value (.option (.unsignedWord width))) :
    CShape.Value (.option (.unsignedWord width)) :=
  match earlier with
  | .optionNone => later
  | .optionSome value => .optionSome value

private theorem packed_latches {width : Nat}
    (accepted eligible finalAccepted : CShape.Value .bit)
    (selected candidate finalSelected : CShape.Word width)
    (tag : finalAccepted.toBool = (accepted.toBool || eligible.toBool))
    (word : finalSelected =
      if (!accepted.toBool) && eligible.toBool then candidate else selected) :
    CShape.packOption (.product finalAccepted finalSelected) =
      if accepted.toBool then CShape.packOption (.product accepted selected)
      else CShape.packOption (.product eligible candidate) := by
  cases accepted with
  | bit accepted =>
      cases eligible with
      | bit eligible =>
          cases finalAccepted with
          | bit finalAccepted =>
              simp only [CShape.Value.toBool] at tag word ⊢
              subst finalAccepted
              subst finalSelected
              cases accepted <;> cases eligible <;> rfl

private theorem firstPresent_packed {width : Nat} (accepted : CShape.Value .bit)
    (selected : CShape.Word width) (later : CShape.Value (.option (.unsignedWord width))) :
    firstPresent (CShape.packOption (.product accepted selected)) later =
      if accepted.toBool then CShape.packOption (.product accepted selected) else later := by
  cases accepted with
  | bit value => cases value <;> rfl

/-- Real nominal unpack exposes exactly the candidate that the recovery program stored. -/
theorem unpack_result (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (store.applyOp (unpackOp cells result)).read (.storage cells.candidate.toCStorageRef) =
      CShape.unpackOption (store.read (.storage result.toCStorageRef)) :=
  Store.read_applyOp_output store (unpackOp cells result)

/-- The actual selection step keeps the earlier present result, otherwise its true candidate. -/
theorem selection_latchValue (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separate : FirstAccepted.Separated (selectorInputs cells) (selectorRefs cells))
    (candidateAccepted : cells.candidate.key ≠ cells.accepted.key)
    (candidateSelected : cells.candidate.key ≠ cells.selected.key) (store : Store ctx) :
    latchValue cells (selectionStep cells result store).1 =
      firstPresent (latchValue cells store) (store.read (.storage result.toCStorageRef)) := by
  let decoded := store.applyOp (unpackOp cells result)
  let selected := FirstAccepted.step (selectorInputs cells) (selectorRefs cells) decoded
  have actual := FirstAccepted.firstAccepted_latches
    (selectorInputs cells) (selectorRefs cells) separate decoded
  change
    (selected.1.read (.storage cells.accepted.toCStorageRef)).toBool =
        ((decoded.read (.storage cells.accepted.toCStorageRef)).toBool ||
          (decoded.read (selectorInputs cells).eligible).toBool) ∧
      selected.1.read (.storage cells.selected.toCStorageRef) =
        if (!(decoded.read (.storage cells.accepted.toCStorageRef)).toBool) &&
            (decoded.read (selectorInputs cells).eligible).toBool then
          decoded.read (selectorInputs cells).candidate
        else decoded.read (.storage cells.selected.toCStorageRef) at actual
  have acceptedSame : decoded.read (.storage cells.accepted.toCStorageRef) =
      store.read (.storage cells.accepted.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys store (unpackOp cells result)
      (.storage cells.accepted.toCStorageRef)
      (fun member => candidateAccepted (List.mem_singleton.mp member))
  have selectedSame : decoded.read (.storage cells.selected.toCStorageRef) =
      store.read (.storage cells.selected.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys store (unpackOp cells result)
      (.storage cells.selected.toCStorageRef)
      (fun member => candidateSelected (List.mem_singleton.mp member))
  have eligibleValue : decoded.read (selectorInputs cells).eligible =
      (CShape.unpackOption (store.read (.storage result.toCStorageRef))).first :=
    congrArg CShape.Value.first (unpack_result cells result store)
  have candidateValue : decoded.read (selectorInputs cells).candidate =
      (CShape.unpackOption (store.read (.storage result.toCStorageRef))).second :=
    congrArg CShape.Value.second (unpack_result cells result store)
  have packed := packed_latches (decoded.read (.storage cells.accepted.toCStorageRef))
    (decoded.read (selectorInputs cells).eligible)
    (selected.1.read (.storage cells.accepted.toCStorageRef))
    (decoded.read (.storage cells.selected.toCStorageRef))
    (decoded.read (selectorInputs cells).candidate)
    (selected.1.read (.storage cells.selected.toCStorageRef)) actual.1 actual.2
  change latchValue cells (selectionStep cells result store).1 = _ at packed
  refine packed.trans ?_
  rw [acceptedSame, selectedSame, eligibleValue, candidateValue]
  have pair : CShape.Value.product
      (CShape.unpackOption (store.read (.storage result.toCStorageRef))).first
      (CShape.unpackOption (store.read (.storage result.toCStorageRef))).second =
      CShape.unpackOption (store.read (.storage result.toCStorageRef)) := by
    cases CShape.unpackOption (store.read (.storage result.toCStorageRef))
    rfl
  rw [pair, CShape.packOption_unpackOption]
  exact (firstPresent_packed _ _ _).symm

/-- The actual initial XOR produces the absent latch result for every original store. -/
theorem clear_latchValue (cells : Cells ctx N) (store : Store ctx) :
    latchValue cells (store.applyOp (clearAcceptedOp cells)) = .optionNone := by
  have actual : (store.applyOp (clearAcceptedOp cells)).read
      (.storage cells.accepted.toCStorageRef) = .bit false := by
    refine (Store.read_applyOp_output store (clearAcceptedOp cells)).trans ?_
    change Resource.BitOpcode.eval .xor
      (.product (store.read (.storage cells.accepted.toCStorageRef))
        (store.read (.storage cells.accepted.toCStorageRef))) = .bit false
    cases store.read (.storage cells.accepted.toCStorageRef) with
    | bit value => cases value <;> rfl
  change CShape.packOption (.product _ _) = _
  rw [actual]
  rfl

/-- The final real option instruction writes exactly the represented persistent latch value. -/
theorem pack_result (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (store.applyOp (packOp cells result)).read (.storage result.toCStorageRef) =
      latchValue cells store :=
  Store.read_applyOp_output store (packOp cells result)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
