/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation

/-!
# Full execution of the original preparation prefix

The actual component records compose on their real intermediate stores.
All quantum-reference matrix blocks and all chronological paths survive the
complete decoder, constant preparation, two scalings and final branch.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual measured decoding and actual word splitting preserve the complete state. -/
theorem preparationDecode_execute
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (preparationDecode input refs).execute Reference state = state.mapClassical (fun entry =>
      ((preparationDecodeStep input refs entry.1).1,
        (entry.2, (preparationDecodeStep input refs entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (measuredDecodeInto_execute input refs.decoded)
    (Word.Split.splitInto_execute refs.split) Reference state

/-- The actual modulus loader and single denominator seed preserve every reference block. -/
theorem preparationConstants_execute (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (preparationConstants spec refs).execute Reference state = state.mapClassical (fun entry =>
      ((preparationConstantsStep spec refs entry.1).1,
        (entry.2, (preparationConstantsStep spec refs entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (ConstantWord.constantWord_fold_execute refs.modulusWide _)
    (scaleSeed_execute refs.denominator) Reference state

/-- Both actual scaling triples share their real scratch and chronological paths. -/
theorem preparationScale_execute (refs : PreparationRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (preparationScale refs).execute Reference state = state.mapClassical (fun entry =>
      ((preparationScaleStep refs entry.1).1,
        (entry.2, (preparationScaleStep refs entry.1).2))) := by
  refine (scalePairBody_execute (scaleRead refs.rawLeft) (scaleRead refs.rawRight)
    (scaleRead refs.modulusWide) (scaleRead refs.denominator)
    refs.product refs.division refs.left refs.right Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual narrowed modulus and stored equality result determine the real final branch. -/
theorem preparationFinalize_execute (refs : PreparationRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (preparationFinalize refs).execute Reference state = state.mapClassical (fun entry =>
      ((preparationFinalizeStep refs entry.1).1,
        (entry.2, (preparationFinalizeStep refs entry.1).2))) := by
  exact Circuit.execute_sequenceRecord _ _ _ _
    (fun reference {_} _ initial => by
      refine (Circuit.execute_classical_mapClassical refs.narrowOp reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (negateBody_execute (scaleRead refs.modulus) (scaleRead refs.right) (scaleRead refs.zero)
      refs.negationFlag refs.negatedRight) Reference state

/-- Every original preparation instruction executes on the same full state and actual store. -/
theorem preparationBody_execute (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (preparationBody spec input refs).execute Reference state = state.mapClassical (fun entry =>
      ((preparationStep spec input refs entry.1).1,
        (entry.2, (preparationStep spec input refs entry.1).2))) := by
  exact Circuit.execute_sequenceRecord _ _ _ _
    (fun reference {_} _ initial => Circuit.execute_sequenceRecord _ _ _ _
      (preparationDecode_execute input refs) (preparationConstants_execute spec refs)
      reference initial)
    (fun reference {_} _ initial => Circuit.execute_sequenceRecord _ _ _ _
      (preparationScale_execute refs) (preparationFinalize_execute refs) reference initial)
    Reference state

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
