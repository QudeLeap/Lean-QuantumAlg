/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask

/-!
# Two native Fredkins with one control and separate payloads

Only the two payload CNOTs share an actual parallel layer. The two
Toffolis retain their real common-control dependency and execute in
sequence. All six original native occurrences and all five physical
systems remain present; no initial value is assumed.
-/

namespace QuantumAlg.EncodedBit.FredkinParallel

noncomputable section

open WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- One common control followed by two physically disjoint payload pairs. -/
structure Frame (encoding : BinaryLabelEncoding Data) where
  bit : Fin 5 → EncodedBit encoding
  distinct : Function.Injective (fun index => (bit index).wire)

namespace Frame

/-- Every declared physical coordinate is distinct from the other four. -/
lemma wire_ne (frame : Frame encoding) {first second : Fin 5} (different : first ≠ second) :
    (frame.bit first).wire ≠ (frame.bit second).wire :=
  fun same => different (frame.distinct same)

def firstCnot (frame : Frame encoding) : GateSpec encoding :=
  .cnot (frame.bit 1) (frame.bit 2) (frame.wire_ne (by decide))

def secondCnot (frame : Frame encoding) : GateSpec encoding :=
  .cnot (frame.bit 3) (frame.bit 4) (frame.wire_ne (by decide))

def firstToffoli (frame : Frame encoding) : GateSpec encoding :=
  .toffoli (frame.bit 0) (frame.bit 2) (frame.bit 1)
    (frame.wire_ne (by decide)) (frame.wire_ne (by decide)) (frame.wire_ne (by decide))

def secondToffoli (frame : Frame encoding) : GateSpec encoding :=
  .toffoli (frame.bit 0) (frame.bit 4) (frame.bit 3)
    (frame.wire_ne (by decide)) (frame.wire_ne (by decide)) (frame.wire_ne (by decide))

/-- Both actual read/write supports are checked, without the common control. -/
def cnotLayer (frame : Frame encoding) : CnotLayer encoding where
  edges := [⟨frame.bit 1, frame.bit 2, frame.wire_ne (by decide)⟩,
    ⟨frame.bit 3, frame.bit 4, frame.wire_ne (by decide)⟩]
  separate := by
    apply List.pairwise_cons.mpr
    constructor
    · intro edge present
      obtain rfl := List.mem_singleton.mp present
      apply Finset.disjoint_left.mpr
      intro index first second
      simp only [CnotEdge.support, Finset.mem_insert, Finset.mem_singleton] at first second
      rcases first with first | first <;> rcases second with second | second
      · exact frame.wire_ne (by decide : (1 : Fin 5) ≠ 3) (first.symm.trans second)
      · exact frame.wire_ne (by decide : (1 : Fin 5) ≠ 4) (first.symm.trans second)
      · exact frame.wire_ne (by decide : (2 : Fin 5) ≠ 3) (first.symm.trans second)
      · exact frame.wire_ne (by decide : (2 : Fin 5) ≠ 4) (first.symm.trans second)
    · simp

lemma cnotLayer_gates (frame : Frame encoding) :
    frame.cnotLayer.gates = [frame.firstCnot, frame.secondCnot] := rfl

/-- The original two complete Fredkins execute one after the other. -/
def serialGates (frame : Frame encoding) : List (GateSpec encoding) :=
  fredkinGates (frame.bit 0) (frame.bit 1) (frame.bit 2)
    (frame.wire_ne (by decide)) (frame.wire_ne (by decide)) (frame.wire_ne (by decide)) ++
  fredkinGates (frame.bit 0) (frame.bit 3) (frame.bit 4)
    (frame.wire_ne (by decide)) (frame.wire_ne (by decide)) (frame.wire_ne (by decide))

/-- Only occurrences from different payload pairs move across one another. -/
def scheduledGates (frame : Frame encoding) : List (GateSpec encoding) :=
  [frame.firstCnot, frame.secondCnot, frame.firstToffoli, frame.secondToffoli,
    frame.firstCnot, frame.secondCnot]

/-- Two real independent CNOT layers surround two necessarily sequential Toffolis. -/
def program (frame : Frame encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (frame.cnotLayer.program physical oracles).seq
    ((frame.firstToffoli.program physical oracles).seq
      ((frame.secondToffoli.program physical oracles).seq
        (frame.cnotLayer.program physical oracles)))

end Frame

end

end QuantumAlg.EncodedBit.FredkinParallel
