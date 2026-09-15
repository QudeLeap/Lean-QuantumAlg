/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Frames

/-!
# Actual check-stage separation from the common candidate write inventory
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceSeparation

open Execution
open LatticeCandidateSlotFrames

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {coordinateWidth modulusWidth : Nat}

/-- A named mutable input avoids every differently named physical destination. -/
theorem mutableInput_avoids
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) {shape : CShape} (source : CWriteRef ctx shape)
    (saved written : MutableCell) (sourceKey : source.key = mutableKey refs saved)
    (different : saved ≠ written) :
    mutableKey refs written ∉ (LatticeCandidateSlotMachine.writeInput source).storageKeys := by
  change mutableKey refs written ∉ [source.key]
  simp only [List.mem_singleton]
  rw [sourceKey]
  exact Ne.symm (separation.mutableKey_ne different)

/-- The actual near-target reads and writes satisfy the common physical separation contract. -/
theorem nearTargetSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) : LatticeNearTargetScale.Separation refs.nearTarget := by
  refine ⟨?_, ?_⟩
  · intro source target
    cases source with
    | distance =>
      change mutableKey refs (.nearTarget target) ∉ refs.nearTarget.distance.storageKeys
      rw [refs.nearTargetDistance]
      exact mutableInput_avoids refs separation refs.distance.distance.squaredDistance
        .squaredDistance (.nearTarget target) rfl (by intro equal; cases equal)
    | upperBound =>
      change mutableKey refs (.nearTarget target) ∉ refs.nearTarget.upperBound.storageKeys
      rw [refs.nearTargetUpperBound]
      exact separation.externalAvoids .upperBound (.nearTarget target)
  · intro left right equal
    exact MutableCell.nearTarget.inj (separation.mutableKeyInjective equal)

/-- Actual sign extraction and exponent classification need no obsolete work-word separation. -/
theorem exponentSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) : LatticeCandidateExponent.Separation refs.exponent := by
  refine ⟨?_, ?_⟩
  · intro source target
    cases source with
    | candidateThird =>
      change mutableKey refs (.exponent target) ∉
        (LatticeState.coordinateInput refs.exponent.point.third).storageKeys
      rw [refs.exponentPoint]
      exact mutableInput_avoids refs separation refs.distance.candidate.point.third
        (.candidate .pointThird) (.exponent target) rfl (by intro equal; cases equal)
    | zero =>
      change mutableKey refs (.exponent target) ∉ refs.exponent.zero.storageKeys
      rw [refs.exponentZero]
      exact separation.externalAvoids .zero (.exponent target)
    | upperBound =>
      change mutableKey refs (.exponent target) ∉ refs.exponent.upperBound.storageKeys
      rw [refs.exponentUpperBound]
      exact separation.externalAvoids .upperBound (.exponent target)
  · intro left right equal
    exact MutableCell.exponent.inj (separation.mutableKeyInjective equal)

/-- Actual shared powering and equality require only their four real caller-frame conditions. -/
theorem powerSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) : LatticeCandidatePowerMachine.Separation refs.power :=
  ⟨separation.externalAvoids .modulus .power,
    separation.externalAvoids .targetPower .power,
    separation.externalAvoids .modulus .powerAccepted,
    mutableInput_avoids refs separation refs.power.power .power .powerAccepted rfl (by decide)⟩

private def selectorCell : LatticeCandidateSelector.MutableCell → MutableCell
  | .intermediate => .selectorIntermediate
  | .eligible => .selectorEligible
  | .accepted => .selection .accepted
  | .selected => .selection .selected

private theorem selectorCell_injective : Function.Injective selectorCell := by
  intro left right equal
  cases left <;> cases right <;> simp_all [selectorCell]

private theorem selectorKey
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (cell : LatticeCandidateSelector.MutableCell) :
    LatticeCandidateSelector.mutableKey refs.selector cell =
      mutableKey refs (selectorCell cell) := by
  cases cell <;> rfl

/-- All actual conjunction and direct-selection destinations are distinct from their live inputs. -/
theorem selectorSeparation
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (separation : FrameSeparation refs) : LatticeCandidateSelector.Separation refs.selector := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro cell
    rw [selectorKey, refs.selectorNearTarget]
    exact mutableInput_avoids refs separation refs.nearTarget.accepted
      (.nearTarget .accepted) (selectorCell cell) rfl
      (by cases cell <;> intro equal <;> cases equal)
  · intro cell
    rw [selectorKey, refs.selectorExponentInRange]
    exact mutableInput_avoids refs separation refs.exponent.accepted
      (.exponent .accepted) (selectorCell cell) rfl (by cases cell <;> intro equal <;> cases equal)
  · intro cell
    rw [selectorKey, refs.selectorPowerMatches]
    exact mutableInput_avoids refs separation refs.power.accepted
      .powerAccepted (selectorCell cell) rfl (by cases cell <;> intro equal <;> cases equal)
  · intro cell
    rw [selectorKey, refs.selectorCandidate]
    exact mutableInput_avoids refs separation refs.exponent.exponent
      (.exponent .exponent) (selectorCell cell) rfl (by cases cell <;> intro equal <;> cases equal)
  · intro left right equal
    apply selectorCell_injective
    apply separation.mutableKeyInjective
    simpa only [selectorKey] using equal

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceSeparation
