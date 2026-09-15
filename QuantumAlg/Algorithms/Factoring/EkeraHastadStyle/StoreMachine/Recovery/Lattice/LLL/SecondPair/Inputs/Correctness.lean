/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Inputs

/-!
# Original second-reduction Gram formulas

The actual six-write circuit realizes the original numerator and denominator
modulo the supplied width, including width zero and arbitrary initial scratch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondReductionInputs

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- All original Gram words represent their supplied integer values in the actual store. -/
def InputsRepresents (inputs : Inputs ctx width) (store : Store ctx)
    (values : InputCell → Int) : Prop :=
  ∀ cell, RawSignedRepresents (store.read (inputRef inputs cell)) (values cell)

private theorem difference_correct (inputs : Inputs ctx width) (refs : Refs ctx width)
    (separation : Separation inputs refs) (store : Store ctx)
    (a b c d : InputCell) (target : MutableCell) (different : .product ≠ target)
    (values : InputCell → Int) (rep : InputsRepresents inputs store values) :
    RawSignedRepresents
      ((productDifferenceStore (inputRef inputs a) (inputRef inputs b)
        (inputRef inputs c) (inputRef inputs d) (mutableRef refs target) refs.product store).read
        (writeInput (mutableRef refs target))) (values a * values b - values c * values d) :=
  ProductDifference.computeInto_correct _ _ _ _ _ _ _ store
    (separation.inputAvoidsMutable c target) (separation.inputAvoidsMutable d target)
    (separation.mutable_ne .product target different)
    _ _ _ _ (rep a) (rep b) (rep c) (rep d)

private theorem difference_preserves_inputs (inputs : Inputs ctx width) (refs : Refs ctx width)
    (separation : Separation inputs refs) (store : Store ctx)
    (a b c d : InputCell) (target : MutableCell)
    (values : InputCell → Int) (rep : InputsRepresents inputs store values) :
    InputsRepresents inputs
      (productDifferenceStore (inputRef inputs a) (inputRef inputs b)
        (inputRef inputs c) (inputRef inputs d) (mutableRef refs target) refs.product store)
      values := by
  intro cell
  rw [productDifference_callerFrame _ _ _ _ _ _ _ _
    (separation.inputAvoidsMutable cell target) (separation.inputAvoidsMutable cell .product)]
  exact rep cell

/-- The actual two outputs represent the original cleared second-direction Gram expressions. -/
theorem secondReductionInputsInto_correct (inputs : Inputs ctx width) (refs : Refs ctx width)
    (separation : Separation inputs refs) (store : Store ctx) (values : InputCell → Int)
    (rep : InputsRepresents inputs store values) :
    RawSignedRepresents ((secondReductionInputsStore inputs refs store).read (writeInput refs.nu32))
        (values .g11 * values .g32 - values .g31 * values .g21) ∧
      RawSignedRepresents
        ((secondReductionInputsStore inputs refs store).read (writeInput refs.d32))
        (values .g11 * values .g22 - values .g21 * values .g21) := by
  have numerator := difference_correct inputs refs separation store
    .g11 .g32 .g31 .g21 .nu32 (by decide) values rep
  have retained := difference_preserves_inputs inputs refs separation store
    .g11 .g32 .g31 .g21 .nu32 values rep
  have denominator := difference_correct inputs refs separation _
    .g11 .g22 .g21 .g21 .d32 (by decide) values retained
  refine ⟨?_, denominator⟩
  unfold secondReductionInputsStore
  rw [productDifference_callerFrame _ _ _ _ _ _ _ _]
  · exact numerator
  · change mutableKey refs .d32 ∉ [mutableKey refs .nu32]
    simpa only [List.mem_singleton] using separation.mutable_ne .d32 .nu32 (by decide)
  · change mutableKey refs .product ∉ [mutableKey refs .nu32]
    simpa only [List.mem_singleton] using separation.mutable_ne .product .nu32 (by decide)

/-- Every original Gram word remains exactly unchanged after both actual product differences. -/
theorem secondReductionInputsInto_preserves_inputs
    (inputs : Inputs ctx width) (refs : Refs ctx width)
    (separation : Separation inputs refs) (store : Store ctx) (cell : InputCell) :
    (secondReductionInputsStore inputs refs store).read (inputRef inputs cell) =
      store.read (inputRef inputs cell) :=
  secondReductionInputsInto_callerFrame inputs refs store (inputRef inputs cell)
    (separation.inputAvoidsMutable cell .nu32) (separation.inputAvoidsMutable cell .d32)
    (separation.inputAvoidsMutable cell .product)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondReductionInputs
