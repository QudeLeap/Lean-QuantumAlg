/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Packing
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Store

/-!
# Actual paid packing writes the corresponding complete parent Store

The observation below reorders only the existing two exponent tuples.
The native packFiniteBits instruction still executes and pays its real
coordinate. Transport then identifies its exact existing parent destination;
all other original parent values remain [GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Packing

noncomputable section

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- Mathematical frequency-order observation of the original retained chronological vector. -/
def packingReadoutValue (m ell : Nat)
    (readout : CShape.Value (.fixedVector (resultBits m ell) (.finite 2))) :
    CShape.Value (.fixedVector (resultBits m ell) (.finite 2)) :=
  .fixedVector fun index => Fin.addCases
    (fun position => readout.get (Fin.castAdd ell position.rev))
    (fun position => readout.get (Fin.natAdd (ell + m) position.rev)) index

/-- The value written by the paid packing leaf when its original retained vector is given. -/
def packedReadoutValue (m ell : Nat)
    (readout : CShape.Value (.fixedVector (resultBits m ell) (.finite 2))) :
    CShape.Value (.bits (resultBits m ell)) :=
  CShape.packFiniteBits (resultBits m ell) (packingReadoutValue m ell readout)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev PackingParentCtx := context base noQuantum m ell width

/-- The actual native input reads precisely the original retained vector in frequency order. -/
lemma measuredPacking_readout_input (store : Store (PackingParentCtx base noQuantum m ell width)) :
    store.read (frequencyInput base noQuantum m ell width) =
      packingReadoutValue m ell ((resultRead base noQuantum m ell width).eval store) := by
  apply congrArg CShape.Value.fixedVector
  funext index
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index
  · have cell : Fin.addCases
        (fun position => .storage (firstCell base noQuantum m ell width position.rev).toCStorageRef)
        (fun position => .storage
          (secondCell base noQuantum m ell width position.rev).toCStorageRef)
        (Fin.castAdd ell first) =
          (CInputRef.storage (firstCell base noQuantum m ell width first.rev).toCStorageRef) :=
      Fin.addCases_left first
    have value : Fin.addCases (motive := fun _ => CShape.Value (.finite 2))
        (fun position => ((resultRead base noQuantum m ell width).eval store).get
          (Fin.castAdd ell position.rev))
        (fun position => ((resultRead base noQuantum m ell width).eval store).get
          (Fin.natAdd (ell + m) position.rev))
        (Fin.castAdd ell first) =
          ((resultRead base noQuantum m ell width).eval store).get
            (Fin.castAdd ell first.rev) := Fin.addCases_left first
    exact (congrArg (fun input => store.read input) cell).trans value.symm
  · have cell : Fin.addCases
        (fun position => .storage (firstCell base noQuantum m ell width position.rev).toCStorageRef)
        (fun position => .storage
          (secondCell base noQuantum m ell width position.rev).toCStorageRef)
        (Fin.natAdd (ell + m) second) =
          (CInputRef.storage (secondCell base noQuantum m ell width second.rev).toCStorageRef) :=
      Fin.addCases_right second
    have value : Fin.addCases (motive := fun _ => CShape.Value (.finite 2))
        (fun position => ((resultRead base noQuantum m ell width).eval store).get
          (Fin.castAdd ell position.rev))
        (fun position => ((resultRead base noQuantum m ell width).eval store).get
          (Fin.natAdd (ell + m) position.rev))
        (Fin.natAdd (ell + m) second) =
          ((resultRead base noQuantum m ell width).eval store).get
            (Fin.natAdd (ell + m) second.rev) := Fin.addCases_right second
    exact (congrArg (fun input => store.read input) cell).trans value.symm

variable (result : CWriteRef base (.bits (resultBits m ell)))

/-- The real paid instruction updates exactly its original parent destination and no other cell. -/
lemma measuredPacking_parentStore (store : Store (PackingParentCtx base noQuantum m ell width)) :
    parentStore base noQuantum m ell width
        (store.applyOp (operation base noQuantum m ell width
          ((parentTransport base noQuantum m ell width).liftWrite result))) =
      (parentStore base noQuantum m ell width store).write result
        (packedReadoutValue m ell ((resultRead base noQuantum m ell width).eval store)) := by
  change (parentTransport base noQuantum m ell width).restrict
    (store.write ((parentTransport base noQuantum m ell width).liftWrite result)
      (CShape.packFiniteBits (resultBits m ell)
        (store.read (frequencyInput base noQuantum m ell width)))) = _
  refine ((parentTransport base noQuantum m ell width).workspaceTransport_restrict_write
    store result _).trans ?_
  exact congrArg (fun value => (parentStore base noQuantum m ell width store).write result value)
    (congrArg (CShape.packFiniteBits (resultBits m ell))
      (measuredPacking_readout_input base noQuantum m ell width store))

/-- Every complete parent/reference observation follows that same actual native packing update. -/
lemma measuredPacking_parent_referenceFiberSum (environment : model.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (PackingParentCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (weight : Store base → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum m ell width
        ((parentTransport base noQuantum m ell width).liftWrite result)).execute environment
          Reference state)
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight ((parentStore base noQuantum m ell width entry.1).write result
          (packedReadoutValue m ell ((resultRead base noQuantum m ell width).eval entry.1))))
        leftRef rightRef := by
  let update : Store (PackingParentCtx base noQuantum m ell width) ×
      (model.HiddenState × History) → Store (PackingParentCtx base noQuantum m ell width) ×
      (model.HiddenState × (History × (code base noQuantum m ell width
        ((parentTransport base noQuantum m ell width).liftWrite result)).Path)) :=
    fun entry =>
      let next := BitWord.instructionStep (execution := model)
        (operation base noQuantum m ell width
          ((parentTransport base noQuantum m ell width).liftWrite result)) entry.1
      (next.1, (entry.2.1, (entry.2.2, next.2)))
  have executed : (code base noQuantum m ell width
      ((parentTransport base noQuantum m ell width).liftWrite result)).execute environment
        Reference state = state.mapClassical update :=
    measuredPacking_execute base noQuantum m ell width
      ((parentTransport base noQuantum m ell width).liftWrite result) state
  have actual := congrArg
    (fun output : State (PackingParentCtx base noQuantum m ell width) Reference
      (model.HiddenState × (History × (code base noQuantum m ell width
        ((parentTransport base noQuantum m ell width).liftWrite result)).Path)) =>
      ExecutionState.referenceFiberSum output
        (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) leftRef rightRef)
    executed
  refine actual.trans ((ExecutionState.referenceFiberSum_mapClassical (decision := inferInstance)
    state update (fun entry _ => weight (parentStore base noQuantum m ell width entry.1))
      leftRef rightRef).trans ?_)
  apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry basis
  exact congrArg weight (measuredPacking_parentStore base noQuantum m ell width result entry.1)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Packing
