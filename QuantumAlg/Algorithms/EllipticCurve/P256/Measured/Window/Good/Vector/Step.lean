/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Inputs
import all QuantumAlg.Core.Execution.Instrument.Recorded.Feed

/-!
# One exact actual source stage on the coherent admissible component

The specified real reset, mathematical source feed and original measured
middle act on the whole raw vector. Impossible reset outcomes vanish. The
zero outcome uses the literal returned Store and all original Fourier
phases; the original input values are preserved by the paid reset itself.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine

private lemma reset_zero_store (parameters : Sampling.Parameters ctx)
    (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) :
    ((Sampling.Reset.instrument parameters index environment).record before
      (Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index))).1 =
      (parameters.resetParameters.zeroRunRecord (services := services)
        (index.lowerWidth + 1) (parameters.wire index) before).1 := by
  change ((Sampling.Reset.runInstrument parameters.resetParameters environment
    (index.lowerWidth + 1) (parameters.wire index)).record before
      (Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index))).1 = _
  exact congrArg Prod.fst
    (Sampling.Reset.runInstrument_zero_record parameters.resetParameters environment
      (index.lowerWidth + 1) (parameters.wire index) before)

private def CoherentPrefixSourceStepStatement : Prop :=
  ∀ (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256) (position : Fin 34)
    (_assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (_values : Driver.driverInputValues parameters.frame (actualCurveSpec I)
      (chronologicalBasePoint I position) (Sampling.chronologicalIndex position).row before)
    (amplitude : GoodBranch I → Complex)
    {Reference : Register} (reference : HilbertVector Reference),
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    let reset := Sampling.Reset.instrument parameters index environment
    let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
    let zeroStore := (parameters.resetParameters.zeroRunRecord (services := services)
      (index.lowerWidth + 1) (parameters.wire index) before).1
    ∀ (resetOutcome : Sampling.Reset.Outcome (index.lowerWidth + 1) (parameters.wire index))
      (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)),
      HilbertOperator.applyVec
        (recordedFeedOperator reset middle (Sampling.SourceRegister.prod Reference)
          (parameters.sourceFeed index Reference) (before, hidden) resetOutcome
          (pointOutcome, outcome))
        (coherentPrefix parameters I position.val position.isLt.le index.sourceStart
          amplitude reference) =
      if resetOutcome = Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
      then coherentPrefix parameters I (position.val + 1) (Nat.succ_le_of_lt position.isLt)
        index.sourceEnd
        (fun branch => amplitude branch * Sampling.windowScalar parameters index zeroStore
          (sourceBranch I branch.val) outcome) reference
      else 0

/-- Every original reset/point/Fourier outcome has its exact coherent source-stage vector. -/
lemma coherentPrefix_sourceStep :
    CoherentPrefixSourceStepStatement (ctx := ctx) (services := services) := by
  unfold CoherentPrefixSourceStepStatement
  intro parameters I sameSpec scratch position assigned environment before hidden values amplitude
    Reference reference
  dsimp only
  intro resetOutcome pointOutcome outcome
  let index := Sampling.chronologicalIndex position
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  by_cases selected : resetOutcome = Sampling.Reset.zeroOutcome
      ((Sampling.chronologicalIndex position).lowerWidth + 1)
      (parameters.wire (Sampling.chronologicalIndex position))
  · subst resetOutcome
    rw [if_pos rfl, recordedFeedOperator_applyVec, coherentPrefix_reset,
      if_pos rfl, one_smul]
    have recorded := reset_zero_store parameters (Sampling.chronologicalIndex position)
      environment before
    rw [recorded]
    have preserved := Sampling.reset_zero_driverInputValues (services := services)
      parameters
      (Sampling.chronologicalIndex position) (actualCurveSpec I)
      (chronologicalBasePoint I position) (Sampling.chronologicalIndex position).row before values
    have window := coherentPrefix_window parameters I sameSpec scratch position assigned
      environment _ hidden preserved amplitude reference pointOutcome outcome
    dsimp only [Prod.snd]
    generalize_proofs at window ⊢
    exact window
  · rw [if_neg selected, recordedFeedOperator_applyVec, coherentPrefix_reset, if_neg selected,
      HilbertOperator.applyVec_smul, HilbertOperator.applyVec_smul, zero_smul]

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
