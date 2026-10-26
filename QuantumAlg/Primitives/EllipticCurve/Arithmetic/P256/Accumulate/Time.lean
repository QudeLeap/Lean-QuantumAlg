/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Schedule.Time

/-! # Actual quantum duration of arbitrary-accumulator MAC and complete source restoration -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit Horner

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

lemma sourceDoubling_quantumTime :
    (sourceDoublingProgram saved).evaluatedEventDepth Resource.Event.quantumDuration = 20954 :=
  (UnitaryCircuit.placeAt_evaluatedEventDepth _ _ _ _ Resource.Event.quantumDuration
    (operandDoublingProgram saved)).trans (operandDoubling_quantumTime saved)

lemma inverseSourceDoubling_quantumTime :
    (inverseSourceDoublingProgram saved).evaluatedEventDepth
        Resource.Event.quantumDuration = 20954 :=
  (UnitaryCircuit.placeAt_evaluatedEventDepth _ _ _ _ Resource.Event.quantumDuration
    (operandInverseDoublingProgram saved)).trans (operandInverseDoubling_quantumTime saved)

private lemma round_quantumTime (index : Fin width) :
    (forwardRoundProgram saved multiplier outer outerMultiplier index).evaluatedEventDepth
      Resource.Event.quantumDuration = if index.val = 0 then 52856 else 20954 + 52856 :=
  Horner.conditional_depth (index.val = 0) (sourceDoublingProgram saved)
    (stageProgram saved (.retained (multiplier.bits index)) outer (outerMultiplier index))
    20954 52856 (sourceDoubling_quantumTime saved) (stage_quantumTime saved outer _ _)

private lemma forward_quantumTime :
    (forwardProgram saved multiplier outer outerMultiplier).evaluatedEventDepth
      Resource.Event.quantumDuration = 18874406 :=
  Horner.depth_ofFn (stages := 255) (forwardRoundProgram saved multiplier outer outerMultiplier) _ _
    (round_quantumTime saved multiplier outer outerMultiplier)

private lemma repeated_time {count : Nat} {layout : QuantumLayout count}
    (repetitions : Nat) (body : UnitaryCircuit AlgorithmGate.model .empty layout) (amount : Nat)
    (law : body.evaluatedEventDepth Resource.Event.quantumDuration = amount) :
    (UnitaryCircuit.iterate repetitions body).evaluatedEventDepth Resource.Event.quantumDuration =
      repetitions * amount :=
  congrArg (fun value => repetitions * value) law

private lemma restoration_quantumTime :
    (restorationProgram saved).evaluatedEventDepth Resource.Event.quantumDuration = 5343270 :=
  repeated_time (width - 1) (inverseSourceDoublingProgram saved) 20954
    (inverseSourceDoubling_quantumTime saved)

/-- Duration includes both full source traversals and every actual bit latch and selected add. -/
lemma program_quantumTime :
    (program saved multiplier outer outerMultiplier).evaluatedEventDepth
      Resource.Event.quantumDuration = 24217676 :=
  (UnitaryCircuit.evaluatedEventDepth_seq _ _ _).trans
    (congrArg₂ Nat.add (forward_quantumTime saved multiplier outer outerMultiplier)
      (restoration_quantumTime saved))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
