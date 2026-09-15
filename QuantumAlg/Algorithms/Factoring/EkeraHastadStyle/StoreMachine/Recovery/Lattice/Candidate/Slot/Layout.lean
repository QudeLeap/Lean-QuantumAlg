/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Prefix.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Comparison.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Exponent.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Selection.Resources

/-!
# Original candidate-slot wiring without obsolete resets
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

/-- Structural input of an original caller-owned writable slot cell. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Caller-owned cells and exact inter-machine wiring for one candidate slot. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (coordinateWidth modulusWidth : Nat) where
  /-- Nested references for the distance stage. -/
  distance : LatticeCandidateDistancePrefix.Refs ctx coordinateWidth
  /-- Nested references for the near target stage. -/
  nearTarget : LatticeNearTargetScale.Refs ctx coordinateWidth
  /-- Nested references for the exponent stage. -/
  exponent : LatticeCandidateExponent.Refs ctx coordinateWidth
  /-- Nested references for the power stage. -/
  power : LatticeCandidatePowerMachine.Refs ctx modulusWidth coordinateWidth
  /-- Nested references for the selector stage. -/
  selector : LatticeCandidateSelector.Refs ctx coordinateWidth
  /-- Input reference for the zero value. -/
  zero : CInputRef ctx (.unsignedWord coordinateWidth)
  /-- Input reference for the upper bound value. -/
  upperBound : CInputRef ctx (.unsignedWord coordinateWidth)
  nearTargetDistance :
    nearTarget.distance = writeInput distance.distance.squaredDistance
  nearTargetUpperBound : nearTarget.upperBound = upperBound
  exponentPoint : exponent.point = distance.candidate.point
  exponentZero : exponent.zero = zero
  exponentUpperBound : exponent.upperBound = upperBound
  powerExponent : power.exponent = writeInput exponent.exponent
  selectorNearTarget :
    selector.nearTarget = LatticeCandidateSelector.writeInput nearTarget.accepted
  selectorExponentInRange :
    selector.exponentInRange = LatticeCandidateSelector.writeInput exponent.accepted
  selectorPowerMatches :
    selector.powerMatches = LatticeCandidatePowerMachine.writeInput power.accepted
  selectorCandidate : selector.candidate = writeInput exponent.exponent

/-- The five actual component separation certificates for one wired slot. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {coordinateWidth modulusWidth : Nat}
    (refs : Refs ctx coordinateWidth modulusWidth) : Prop where
  distance : LatticeCandidateDistancePrefix.Separation refs.distance
  nearTarget : LatticeNearTargetScale.Separation refs.nearTarget
  exponent : LatticeCandidateExponent.Separation refs.exponent
  power : LatticeCandidatePowerMachine.Separation refs.power
  selector : LatticeCandidateSelector.Separation refs.selector


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine
