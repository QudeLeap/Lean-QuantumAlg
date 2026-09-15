/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual recovery of an already retained sample batch

Four selector cells are allocated once in the original order. Every retained
sample is processed by the complete attempt, followed by the original stored
first-accepted selector inside the accumulator scope. All attempts execute;
one final optional pack follows the complete loop. This tail performs no
quantum sampling and preserves the original sample-before-recovery schedule.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum} {width : Nat}

/-- The stack reverses the original accepted, selected, available and take allocation order. -/
def selectorShapes (width : Nat) : List CShape :=
  [.bit, .bit, .unsignedWord width, .bit]

/-- The four real cells supply the original selector without allocating per-attempt latches. -/
def selectorRefs (cells : Cells ctx (selectorShapes width)) : FirstAccepted.Refs ctx width where
  accepted := cells.tail.tail.tail.head.ref
  selected := cells.tail.tail.head.ref
  available := cells.tail.head.ref
  take := cells.head.ref

/-- Transport the original four physical selector destinations through an attempt scope. -/
def liftSelector {inner : RuntimeCtx .quantum} (refs : FirstAccepted.Refs ctx width)
    (transport : Transport ctx inner) : FirstAccepted.Refs inner width where
  accepted := transport.liftWrite refs.accepted
  selected := transport.liftWrite refs.selected
  available := transport.liftWrite refs.available
  take := transport.liftWrite refs.take

/-- Each complete attempt reaches the original selector before its accumulator is released. -/
def selectAttempt (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width) :
    Circuit ctx ctx :=
  withAttempt P input target fun candidate accepted transport =>
    FirstAccepted.circuit ⟨accepted, candidate⟩ (liftSelector refs transport)

/-- Process every already retained sample in its original increasing index order. -/
def selectionLoop (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width) :
    Circuit ctx ctx :=
  Circuit.forRange count fun index => selectAttempt P (samples index) target refs

/-- The original single optional pack reads both actual final selector latches. -/
def selectionPack (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) :
    ClassicalOp (.product .bit (.unsignedWord width)) (.option (.unsignedWord width)) ctx ctx :=
  .packOption ctx (.product (FirstAccepted.cellRead refs.accepted)
    (FirstAccepted.cellRead refs.selected)) output

/-- The single final pack runs after all attempts, including those after the first acceptance. -/
def recoveryBody (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (output : CWriteRef ctx (.option (.unsignedWord P.width))) : Circuit ctx ctx :=
  (selectionLoop P count samples target refs).seq (.classical (selectionPack refs output))

/-- Actual four-cell allocation encloses the complete recovery of already retained samples. -/
def recoveryInto (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width))
    (output : CWriteRef ctx (.option (.unsignedWord P.width))) : Circuit ctx ctx :=
  withCells ctx (selectorShapes P.width) fun cells _ transport _ =>
    recoveryBody P count (fun index => transport.liftInput (samples index))
      (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output)

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
