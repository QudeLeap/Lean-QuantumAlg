/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction
import all QuantumAlg.Components.Classical.OrderRecovery.Native.FiniteSelection

/-!
# Actual option encoding of the stored recovery decision

The existing closed packing instruction reads the accepted latch and selected
word from the same final scan store. The finite word encoding is injective;
the source's established candidate projection therefore determines the exact
optional result, including the absent-result branch.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.OrderRecovery

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- The natural candidate projection loses no information from an optional finite word. -/
lemma nativeRecovery_output_candidate_injective :
    Function.Injective (fun output : CShape.Value (outputShape phaseBits) =>
      (decodeOutput output).map (fun word => word.val)) := by
  intro first second same
  cases first with
  | optionNone =>
      cases second with
      | optionNone => rfl
      | optionSome second => cases second; cases same
  | optionSome first =>
      cases first with
      | unsignedWord first =>
          cases second with
          | optionNone => cases same
          | optionSome second =>
              cases second with
              | unsignedWord second =>
                  exact congrArg (fun word => CShape.Value.optionSome
                    (CShape.Value.unsignedWord word)) (Fin.ext (Option.some.inj same))

/-- The real output write contains the closed packing of the actual tag and payload reads. -/
lemma nativeRecovery_pack_read
    (output : CWriteRef ctx (outputShape phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    (store.applyOp (packRecoveredOp output)).read
        (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields (cellRead output)) =
      CShape.packOption (.product
        (store.read (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted))
        (store.read (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).selected))) := by
  rw [← nativeRecovery_read_writeUnderFields]
  exact Store.read_applyOp_output store (packRecoveredOp output)

/-- Projecting the actual packed output yields precisely the actual selected-candidate reads. -/
lemma nativeRecovery_pack_candidate
    (output : CWriteRef ctx (outputShape phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    (decodeOutput ((store.applyOp (packRecoveredOp output)).read
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields (cellRead output)))).map
        (fun word => word.val) =
      observedCandidate (recoveryCells ctx modulusWidth (phaseBits + 1)) store := by
  rw [nativeRecovery_pack_read]
  unfold observedCandidate
  cases store.read (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted) with
  | bit tag =>
      cases store.read (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).selected) with
      | unsignedWord word => cases tag <;> rfl

/-- A proved actual selection determines the exact original typed source result. -/
lemma nativeRecovery_pack_source_result
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (output : CWriteRef ctx (outputShape phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1)))
    (selected : observedCandidate (recoveryCells ctx modulusWidth (phaseBits + 1)) store =
      selection spec input) :
    (store.applyOp (packRecoveredOp output)).read
        (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields (cellRead output)) =
      encodeOutput (recoverUnitOrder spec input) := by
  apply nativeRecovery_output_candidate_injective
  dsimp only
  rw [nativeRecovery_pack_candidate, nativeRecovery_decode_encode]
  exact selected.trans (candidate_recoverUnitOrder spec input).symm

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
