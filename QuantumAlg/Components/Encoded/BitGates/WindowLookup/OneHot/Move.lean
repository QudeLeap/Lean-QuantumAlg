/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor

/-!
# Actual controlled movement into a clean unary range

A sequential controlled word XOR followed by an independent CNOT layer
moves the selected one-hot token into a new clean range. Shared address
controls remain sequential in the Toffoli word. The CNOT layer checks all
physical controls and targets, and the inverse will retain every actual gate.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}

/-- Two distinct existing unary ranges and their original address control. -/
structure UnaryMoveFrame (encoding : BinaryLabelEncoding Data) (count : Nat) where
  control : EncodedBit encoding
  old : Word encoding count
  fresh : Word encoding count
  oldDistinct : Function.Injective (fun index => (old.bit index).wire)
  freshDistinct : Function.Injective (fun index => (fresh.bit index).wire)
  separate : ∀ first second, (old.bit first).wire ≠ (fresh.bit second).wire
  controlOld : ∀ index, control.wire ≠ (old.bit index).wire
  controlFresh : ∀ index, control.wire ≠ (fresh.bit index).wire

namespace UnaryMoveFrame

private def edge (frame : UnaryMoveFrame encoding count) (index : Fin count) :
    CnotEdge encoding :=
  ⟨frame.fresh.bit index, frame.old.bit index, Ne.symm (frame.separate index index)⟩

private lemma edge_disjoint (frame : UnaryMoveFrame encoding count)
    (first second : Fin count) (different : first ≠ second) :
    Disjoint (frame.edge first).support (frame.edge second).support := by
  apply Finset.disjoint_left.mpr
  intro wire firstPresent secondPresent
  simp only [CnotEdge.support, edge, Finset.mem_insert, Finset.mem_singleton]
    at firstPresent secondPresent
  rcases firstPresent with firstFresh | firstOld <;>
    rcases secondPresent with secondFresh | secondOld
  · exact different (frame.freshDistinct (firstFresh.symm.trans secondFresh))
  · exact frame.separate second first (secondOld.symm.trans firstFresh)
  · exact frame.separate first second (firstOld.symm.trans secondFresh)
  · exact different (frame.oldDistinct (firstOld.symm.trans secondOld))

/-- The target-only cleanup layer uses pairwise disjoint full two-wire supports. -/
def cleanupLayer (frame : UnaryMoveFrame encoding count) : CnotLayer encoding where
  edges := List.ofFn frame.edge
  separate := by
    apply List.pairwise_ofFn.mpr
    intro first second before
    exact frame.edge_disjoint first second (by intro same; subst second; omega)

private lemma cleanupLayer_gates (frame : UnaryMoveFrame encoding count) :
    frame.cleanupLayer.gates = Word.xorIntoGates frame.fresh frame.old
      (fun index => Ne.symm (frame.separate index index)) := by
  simp only [CnotLayer.gates, cleanupLayer, List.map_ofFn, Word.xorIntoGates]
  rfl

/-- The actual Toffoli word reads the shared address bit without changing it. -/
def copyProgram (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  Word.controlledXorIntoProgram physical oracles frame.control frame.old frame.fresh
    frame.controlOld frame.controlFresh (fun index => frame.separate index index)

/-- Compute the selected new range, then clean the original range by a physical parallel layer. -/
def program (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (frame.copyProgram physical oracles).seq (frame.cleanupLayer.program physical oracles)

/-- The complete arbitrary-input action of the actual controlled copy word. -/
def copyStep (frame : UnaryMoveFrame encoding count) : Data → Data :=
  Word.controlledXorIntoStep frame.control frame.old frame.fresh
    frame.controlOld frame.controlFresh (fun index => frame.separate index index)

/-- The complete arbitrary-input action of the original two physical ranges. -/
def step (frame : UnaryMoveFrame encoding count) (state : Data) : Data :=
  Word.xorIntoStep frame.fresh frame.old (fun index => Ne.symm (frame.separate index index))
    (frame.copyStep state)

/-- Exact realization retains the existing shared control and all other original data. -/
lemma program_realizes (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (frame.program physical oracles) environment frame.step := by
  have copy := Word.controlledXorInto_realizes physical oracles frame.control frame.old frame.fresh
    frame.controlOld frame.controlFresh (fun index => frame.separate index index) environment
  have cleanup := frame.cleanupLayer.program_realizes physical oracles environment
  rw [frame.cleanupLayer_gates] at cleanup
  exact copy.seq cleanup

private lemma copy_old (frame : UnaryMoveFrame encoding count) (index : Fin count) (state : Data) :
    (frame.old.bit index).get (frame.copyStep state) = (frame.old.bit index).get state :=
  Word.controlledXorIntoStep_get_observed_of_target_ne _ _ _ _ _ _ _
    (fun other => Ne.symm (frame.separate index other)) state

private lemma copy_fresh (frame : UnaryMoveFrame encoding count) (index : Fin count)
    (state : Data) :
    (frame.fresh.bit index).get (frame.copyStep state) =
      ((frame.fresh.bit index).get state ^^
        (frame.control.get state && (frame.old.bit index).get state)) :=
  Word.controlledXorIntoStep_get_target _ _ _ _ _ _ index
    (fun _other different equal => different (frame.freshDistinct equal))
    (fun other => Ne.symm (frame.controlFresh other))
    (fun other => Ne.symm (frame.separate index other)) state

/-- With an initially clean new range, its output is the selected original unary range. -/
lemma fresh_get (frame : UnaryMoveFrame encoding count) (index : Fin count) (state : Data)
    (clean : (frame.fresh.bit index).get state = false) :
    (frame.fresh.bit index).get (frame.step state) =
      (frame.control.get state && (frame.old.bit index).get state) := by
  unfold step
  rw [Word.xorIntoStep_get_observed_of_target_ne _ _ _ _
    (fun other => frame.separate other index), frame.copy_fresh, clean]
  exact Bool.false_xor _

/-- The same movement clears a selected old range while retaining the unselected range. -/
lemma old_get (frame : UnaryMoveFrame encoding count) (index : Fin count) (state : Data)
    (clean : (frame.fresh.bit index).get state = false) :
    (frame.old.bit index).get (frame.step state) =
      ((frame.old.bit index).get state && !frame.control.get state) := by
  unfold step
  rw [Word.xorIntoStep_get_target _ _ _ index
    (fun other different equal => different (frame.oldDistinct equal))
    (fun other => frame.separate other index), frame.copy_old, frame.copy_fresh, clean]
  cases (frame.control.get state) <;> cases (frame.old.bit index).get state <;> rfl

/-- No original readout outside the two unary ranges changes. -/
lemma observed_get (frame : UnaryMoveFrame encoding count) (observed : EncodedBit encoding)
    (outsideOld : ∀ index, (frame.old.bit index).wire ≠ observed.wire)
    (outsideFresh : ∀ index, (frame.fresh.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (frame.step state) = observed.get state := by
  unfold step
  rw [Word.xorIntoStep_get_observed_of_target_ne _ _ _ _ outsideOld]
  exact Word.controlledXorIntoStep_get_observed_of_target_ne _ _ _ _ _ _ _ outsideFresh state

end UnaryMoveFrame

end

end QuantumAlg.EncodedBit.WindowLookup
