/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Action
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.State
import all QuantumAlg.Core.Base.Gate.Basic

/-!
# Actual window action on the complete coherent good component

Every original good branch and every external Reference amplitude remains
in one raw vector. The named measured middle advances this whole sum with
its original Fourier phases and arithmetic factor. No branch is measured,
renormalized or replaced by an independent classical probability.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine

private lemma double_sum_action {R : Register} {Branch Ref : Type}
    [Fintype Branch] [Fintype Ref] (firstOperator lastOperator : HilbertOperator R)
    (initial final : Branch → Ref → HilbertVector R)
    (scalar amplitude : Branch → Complex) (reference : Ref → Complex)
    (columns : ∀ branch ref,
      lastOperator.applyVec (firstOperator.applyVec (initial branch ref)) =
        scalar branch • final branch ref) :
    lastOperator.applyVec (firstOperator.applyVec
        (∑ branch, ∑ ref, (amplitude branch * reference ref) • initial branch ref)) =
      ∑ branch, ∑ ref, ((amplitude branch * scalar branch) * reference ref) • final branch ref := by
  simp_rw [HilbertOperator.applyVec_sum, HilbertOperator.applyVec_smul]
  apply Finset.sum_congr rfl
  intro branch _
  apply Finset.sum_congr rfl
  intro ref _
  rw [columns, smul_smul]
  congr 1
  ring

private def CoherentPrefixWindowStatement : Prop :=
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
    ∀ (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)),
      HilbertOperator.applyVec
        (Instrument.referenceLift (Sampling.SourceRegister.prod Reference)
          ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).operator
            (before, hidden) (pointOutcome, outcome)))
        (HilbertOperator.applyVec
          (parameters.sourceFeed index Reference : HilbertOperator _)
          (coherentPrefix parameters I position.val position.isLt.le index.sourceStart
            amplitude reference)) =
      coherentPrefix parameters I (position.val + 1) (Nat.succ_le_of_lt position.isLt)
        index.sourceEnd
        (fun branch => amplitude branch * Sampling.windowScalar parameters index before
          (sourceBranch I branch.val) outcome) reference

/-- Every actual point/Fourier outcome advances the original coherent sum with all cross terms. -/
lemma coherentPrefix_window :
    CoherentPrefixWindowStatement (ctx := ctx) (services := services) := by
  unfold CoherentPrefixWindowStatement
  intro parameters I sameSpec scratch position assigned environment before hidden values amplitude
    Reference reference
  dsimp only
  intro pointOutcome outcome
  let index := Sampling.chronologicalIndex position
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  unfold coherentPrefix
  refine double_sum_action
    (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
    (Branch := GoodBranch I) (Ref := Reference.Index)
    _ _ _ _
    (fun branch => Sampling.windowScalar parameters index before
      (sourceBranch I branch.val) outcome)
    amplitude reference ?_
  intro branch ref
  have column := good_window_source_ket parameters I sameSpec scratch
    branch.val branch.property position assigned environment before hidden values
    Reference ref pointOutcome outcome
  unfold coherentLabel
  generalize_proofs at column ⊢
  exact column

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
