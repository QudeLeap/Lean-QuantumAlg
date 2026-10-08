/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Selection

/-!
# Actual complete checks followed by left-priority latch values

The two six-instruction checks produce the actual validity bits consumed by
the two existing first-accepted selectors. Their complete combined store
therefore preserves earlier acceptance and otherwise copies the first valid
divisor in the original source order. Constants and structural separation
remain internal facts furnished by the actual enclosing layouts and loader.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout

open Execution
open ClassicalRoutines

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Both real checks and selectors implement exactly the original ordered divisor decisions. -/
theorem nativeQuadratic_checked_pair_latches (inputs : Operands ctx width)
    (operands : OperandsSeparated inputs) (separated : SelectorSeparated inputs)
    (store : Store (context ctx width))
    (oneValue : (store.read (underRead inputs.one width)).toNat = 1)
    (zeroValue : (store.read (.storage (zero ctx width).toCStorageRef)).toNat = 0) :
    let firstWord := store.read (underRead inputs.first width)
    let secondWord := store.read (underRead inputs.second width)
    let modulus := (store.read (underRead inputs.modulus width)).toNat
    let firstValid := decide (1 < firstWord.toNat ∧ firstWord.toNat < modulus ∧
      modulus % firstWord.toNat = 0)
    let secondValid := decide (1 < secondWord.toNat ∧ secondWord.toNat < modulus ∧
      modulus % secondWord.toNat = 0)
    let oldAccepted :=
      (store.read (underRead (FirstAccepted.cellRead inputs.selection.accepted) width)).toBool
    let oldSelected :=
      store.read (underRead (FirstAccepted.cellRead inputs.selection.selected) width)
    let final := (Pair.step (model := model) (pairRefs inputs) store).1
    (final.read (FirstAccepted.cellRead (pairRefs inputs).selection.accepted)).toBool =
        ((oldAccepted || firstValid) || secondValid) ∧
      final.read (FirstAccepted.cellRead (pairRefs inputs).selection.selected) =
        if oldAccepted then oldSelected else
          if firstValid then firstWord else if secondValid then secondWord else oldSelected := by
  let checked := Pair.checkedStore (pairRefs inputs) store
  have values := nativeQuadratic_checks_values inputs operands store oneValue zeroValue
  have firstResult :
      (checked.read (Pair.selectedInputs (pairRefs inputs).first).eligible).toBool =
        decide (1 < (store.read (underRead inputs.first width)).toNat ∧
          (store.read (underRead inputs.first width)).toNat <
            (store.read (underRead inputs.modulus width)).toNat ∧
          (store.read (underRead inputs.modulus width)).toNat %
            (store.read (underRead inputs.first width)).toNat = 0) := values.1
  have secondResult :
      (checked.read (Pair.selectedInputs (pairRefs inputs).second).eligible).toBool =
        decide (1 < (store.read (underRead inputs.second width)).toNat ∧
          (store.read (underRead inputs.second width)).toNat <
            (store.read (underRead inputs.modulus width)).toNat ∧
          (store.read (underRead inputs.modulus width)).toNat %
            (store.read (underRead inputs.second width)).toNat = 0) := values.2
  have acceptedBefore :
      checked.read (FirstAccepted.cellRead (pairRefs inputs).selection.accepted) =
        store.read (underRead (FirstAccepted.cellRead inputs.selection.accepted) width) :=
    nativeQuadratic_checks_read_original inputs (FirstAccepted.cellRead inputs.selection.accepted)
      (fun present => separated.remainderAccepted (List.mem_singleton.mp present)) store
  have selectedBefore :
      checked.read (FirstAccepted.cellRead (pairRefs inputs).selection.selected) =
        store.read (underRead (FirstAccepted.cellRead inputs.selection.selected) width) :=
    nativeQuadratic_checks_read_original inputs (FirstAccepted.cellRead inputs.selection.selected)
      (fun present => separated.remainderSelected (List.mem_singleton.mp present)) store
  have firstBefore : checked.read (Pair.selectedInputs (pairRefs inputs).first).candidate =
      store.read (underRead inputs.first width) :=
    nativeQuadratic_checks_read_original inputs inputs.first operands.remainderFirst store
  have secondBefore : checked.read (Pair.selectedInputs (pairRefs inputs).second).candidate =
      store.read (underRead inputs.second width) :=
    nativeQuadratic_checks_read_original inputs inputs.second operands.remainderSecond store
  have actual := Selection.nativeQuadratic_selection_latches (model := model)
    (Pair.selectedInputs (pairRefs inputs).first) (Pair.selectedInputs (pairRefs inputs).second)
    (pairRefs inputs).selection (nativeQuadratic_checked_selection_separated inputs separated)
    checked
  refine ⟨actual.1.trans ?_, actual.2.trans ?_⟩
  · rw [acceptedBefore, firstResult, secondResult]
  · rw [acceptedBefore, firstResult, secondResult, selectedBefore, firstBefore, secondBefore]

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckLayout
