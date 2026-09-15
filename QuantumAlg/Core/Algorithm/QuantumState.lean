/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Sealed quantum state transitions for canonical algorithm runs

`KnownPreparation n` is the only public description of algorithm-owned input
state.  It is a sealed finite computational-basis family: callers select a
basis value, while normalized semantics and the strict preparation event are
derived together.  There is no arbitrary pure-state, label, resource, depth,
or flow field.

The actual joint quantum frame and all state transitions remain private to the
canonical interpreter defined by `AlgorithmRun`.  Consequently this module
cannot be used as a second execution surface.
-/

section

namespace QuantumAlg

/-- Closed state preparations admitted by the canonical run language.

The constructor is private.  The initial public family contains the all-zero
state and explicit finite computational-basis values; future constructors must
derive their normalized state and preparation event together. There is
intentionally no arbitrary-state constructor. -/
@[nolint structureInType]
structure KnownPreparation (qubitCount : Nat) where
  private mk ::
  private basisValue : Fin (2 ^ qubitCount)

namespace KnownPreparation

/-- Prepare the all-zero computational basis state of one fixed width. -/
def zero (qubitCount : Nat) : KnownPreparation qubitCount :=
  ⟨⟨0, Nat.two_pow_pos qubitCount⟩⟩

/-- Prepare one explicit member of the finite computational basis. -/
def basis {qubitCount : Nat} (value : Fin (2 ^ qubitCount)) :
    KnownPreparation qubitCount :=
  ⟨value⟩

/-- Normalized semantics fixed by a sealed preparation constructor. -/
noncomputable def normalized {qubitCount : Nat} :
    KnownPreparation qubitCount → NormalizedVector (Qubits qubitCount)
  | preparation => NormalizedVector.ket preparation.basisValue

/-- The public semantics of an explicit computational-basis preparation. -/
@[simp] theorem normalized_basis {qubitCount : Nat}
    (value : Fin (2 ^ qubitCount)) :
    (KnownPreparation.basis value).normalized =
      NormalizedVector.ket value :=
  rfl

/-- The public semantics of the all-zero preparation. -/
@[simp] theorem normalized_zero (qubitCount : Nat) :
    (KnownPreparation.zero qubitCount).normalized =
      NormalizedVector.ket (R := Qubits qubitCount)
        ⟨0, Nat.two_pow_pos qubitCount⟩ :=
  rfl

/-- The strict preparation event fixed by the same constructor. -/
def event {qubitCount : Nat} :
    KnownPreparation qubitCount → Resource.Event .quantum
  | preparation =>
      if preparation.basisValue.val = 0 then
        .preparation
          { family := "builtin", name := "zero", parameters := [qubitCount] }
      else
        .preparation
          { family := "builtin"
            name := "computational-basis"
            parameters := [qubitCount, preparation.basisValue.val] }

/-- Every sealed known-state constructor emits a preparation event.  This
shape theorem lets circuit-only depth assignments discount preparation while
the event remains present in the strict resource ledger. -/
theorem event_eq_preparation {qubitCount : Nat}
    (preparation : KnownPreparation qubitCount) :
    ∃ label, preparation.event = Resource.Event.preparation label := by
  rcases preparation with ⟨basisValue⟩
  simp only [event]
  split <;> exact ⟨_, rfl⟩

/-- Actual ordered preparation trace. -/
def eventTrace {qubitCount : Nat}
    (preparation : KnownPreparation qubitCount) :
    List (Resource.Event .quantum) :=
  [preparation.event]

/-- Exact strict event pool derived from the preparation trace. -/
def eventCost {qubitCount : Nat}
    (preparation : KnownPreparation qubitCount) : ResourcePool .quantum :=
  ResourcePool.singleton preparation.event

/-- Strict event-labelled depth derived from the preparation constructor. -/
def eventDepth {qubitCount : Nat}
    (preparation : KnownPreparation qubitCount) :
    DepthExpr (Resource.Event .quantum) :=
  .atom preparation.event

/-- Preparation trace and pool are two views of the same sealed event. -/
@[simp] theorem ofList_eventTrace {qubitCount : Nat}
    (preparation : KnownPreparation qubitCount) :
    ResourcePool.ofList preparation.eventTrace = preparation.eventCost := by
  simp [eventTrace, eventCost]

end KnownPreparation

end QuantumAlg

end
