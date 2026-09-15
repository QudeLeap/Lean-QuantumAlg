/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Phase
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.Complement
import all QuantumAlg.Components.Encoded.BitGates.Hadamard
import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Conjugation
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.Small.Phase
import all QuantumAlg.Components.Encoded.BitGates.Small.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.DiagonalConjugation
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Actual elementary reflection events and sequential depths

These laws read the literal X, Z, H, CNOT and Toffoli programs. A reindexed
single-wire H or Z has unit depth because every other tensor factor is the
identity. Sequential conjugations retain both halves and the exact global
minus correction in their counts and depth.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

theorem hadamard_unitDepth (target : EncodedBit encoding) :
    target.hadamard.evaluatedEventDepth (fun _ => 1) = 1 := rfl

theorem pauliZ_unitDepth (target : EncodedBit encoding) :
    target.pauliZ.evaluatedEventDepth (fun _ => 1) = 1 := rfl

theorem conjugateHadamard_unitDepth (target : EncodedBit encoding)
    (program : UnitaryCircuit (Qubits encoding.width)) :
    (target.conjugateHadamard program).evaluatedEventDepth (fun _ => 1) =
      program.evaluatedEventDepth (fun _ => 1) + 2 := by
  simp only [conjugateHadamard, UnitaryCircuit.evaluatedEventDepth_seq, hadamard_unitDepth]
  omega

theorem globalMinus_eventCost (target : EncodedBit encoding) :
    target.globalMinus.eventCost =
      2 • ResourcePool.singleton (.gate (.builtin "x")) +
        2 • ResourcePool.singleton
          (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change ResourcePool.ofList
    [.gate (.builtin "x"), .gate (.declared "QuantumAlg.Components.Gate" "pauli-z"),
      .gate (.builtin "x"), .gate (.declared "QuantumAlg.Components.Gate" "pauli-z")] = _
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, two_nsmul]
  abel

theorem globalMinus_unitDepth (target : EncodedBit encoding) :
    target.globalMinus.evaluatedEventDepth (fun _ => 1) = 4 := rfl

theorem pauliZ_eventCost (target : EncodedBit encoding) :
    target.pauliZ.eventCost = ResourcePool.singleton
      (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) := rfl

theorem hadamard_eventCost (target : EncodedBit encoding) :
    target.hadamard.eventCost = ResourcePool.singleton (.gate (.builtin "hadamard")) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, hadamard_eventTrace]
  rfl

theorem conjugateHadamard_eventCost (target : EncodedBit encoding)
    (program : UnitaryCircuit (Qubits encoding.width)) :
    (target.conjugateHadamard program).eventCost =
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) + program.eventCost := by
  simp only [conjugateHadamard, UnitaryCircuit.seq_eventCost, hadamard_eventCost, two_nsmul]
  abel

namespace GateSpec

theorem program_unitDepth (gate : GateSpec encoding) :
    gate.program.evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [UnitaryCircuit.evaluatedEventDepth, program_eventDepth]
  rfl

theorem conjugateProgram_unitDepth (gates : List (GateSpec encoding))
    (program : UnitaryCircuit (Qubits encoding.width)) :
    (conjugateProgram gates program).evaluatedEventDepth (fun _ => 1) =
      2 * gates.length + program.evaluatedEventDepth (fun _ => 1) := by
  simp only [conjugateProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    programList_evaluatedEventDepth_unit, List.length_reverse]
  omega

end GateSpec

theorem controlledZ_eventCost (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    (control.controlledZ target different).eventCost =
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.gate (.builtin "cnot")) := by
  rw [controlledZ, conjugateHadamard_eventCost, GateSpec.program_eventCost]
  rfl

theorem controlledZ_unitDepth (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    (control.controlledZ target different).evaluatedEventDepth (fun _ => 1) = 3 := by
  rw [controlledZ, conjugateHadamard_unitDepth, GateSpec.program_unitDepth]

theorem doubleControlledZ_eventCost (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    (first.doubleControlledZ second target firstSecond firstTarget secondTarget).eventCost =
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.gate (.builtin "toffoli")) := by
  rw [doubleControlledZ, conjugateHadamard_eventCost, GateSpec.program_eventCost]
  rfl

theorem doubleControlledZ_unitDepth (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    (first.doubleControlledZ second target firstSecond firstTarget secondTarget).evaluatedEventDepth
      (fun _ => 1) = 3 := by
  rw [doubleControlledZ, conjugateHadamard_unitDepth, GateSpec.program_unitDepth]

theorem twoWireZeroReflection_eventCost (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) :
    (first.twoWireZeroReflection second different).eventCost =
      2 • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.gate (.builtin "cnot")) := by
  simp only [twoWireZeroReflection, UnitaryCircuit.seq_eventCost,
    pauliZ_eventCost, controlledZ_eventCost, two_nsmul]
  abel

theorem twoWireZeroReflection_unitDepth (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) :
    (first.twoWireZeroReflection second different).evaluatedEventDepth (fun _ => 1) = 5 := by
  simp only [twoWireZeroReflection, UnitaryCircuit.evaluatedEventDepth_seq,
    pauliZ_unitDepth, controlledZ_unitDepth]

theorem threeWireZeroReflection_eventCost (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstThird : first.wire ≠ third.wire)
    (secondThird : second.wire ≠ third.wire) :
    (first.threeWireZeroReflection second third firstSecond firstThird secondThird).eventCost =
      8 • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.gate (.builtin "toffoli")) := by
  rw [threeWireZeroReflection, UnitaryCircuit.seq_eventCost, globalMinus_eventCost,
    GateSpec.conjugateProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost]
  have reversed : ([GateSpec.x first, .x second, .x third] : List (GateSpec encoding)).reverse =
      [.x third, .x second, .x first] := rfl
  rw [reversed]
  simp only [GateSpec.programList_eventCost, List.map_cons, List.map_nil, GateSpec.event,
    ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, doubleControlledZ_eventCost]
  apply Multiset.ext.mpr
  intro event
  simp only [Multiset.count_add, Multiset.count_nsmul]
  ring

theorem threeWireZeroReflection_unitDepth (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstThird : first.wire ≠ third.wire)
    (secondThird : second.wire ≠ third.wire) :
    (first.threeWireZeroReflection second third
      firstSecond firstThird secondThird).evaluatedEventDepth (fun _ => 1) = 13 := by
  simp only [threeWireZeroReflection, UnitaryCircuit.evaluatedEventDepth_seq,
    GateSpec.conjugateProgram_unitDepth, List.length_cons, List.length_nil,
    doubleControlledZ_unitDepth, globalMinus_unitDepth]

namespace Word

theorem complementGates_events {width : Nat} (word : Word encoding width) :
    word.complementGates.map GateSpec.event =
      List.replicate width (.gate (.builtin "x")) := by
  simp only [complementGates, List.map_ofFn]
  exact List.ofFn_const width (Resource.Event.gate (.builtin "x") : Resource.Event .quantum)

theorem complementGates_eventCost {width : Nat} (word : Word encoding width) :
    (GateSpec.programList word.complementGates).eventCost =
      width • ResourcePool.singleton (.gate (.builtin "x")) := by
  rw [GateSpec.programList_eventCost, complementGates_events, ResourcePool.ofList_replicate]
  rfl

theorem complementGates_reverse_eventCost {width : Nat} (word : Word encoding width) :
    (GateSpec.programList word.complementGates.reverse).eventCost =
      width • ResourcePool.singleton (.gate (.builtin "x")) := by
  rw [GateSpec.programList_eventCost, List.map_reverse, complementGates_events,
    List.reverse_replicate, ResourcePool.ofList_replicate]
  rfl

namespace OneDirtyLayout

/-- Independent native gate multiplicities at each multi-control width. -/
def gatePool (controls : Nat) : ResourcePool .quantum :=
  if controls = 0 then ResourcePool.singleton (.gate (.builtin "x"))
  else if controls = 1 then ResourcePool.singleton (.gate (.builtin "cnot"))
  else gateCount controls • ResourcePool.singleton (.gate (.builtin "toffoli"))

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)

theorem gates_program_eventCost :
    (GateSpec.programList layout.gates).eventCost = gatePool controls := by
  rw [GateSpec.programList_eventCost, gates_events]
  unfold gatePool
  split
  · rfl
  · split
    · rfl
    · rw [ResourcePool.ofList_replicate]
      rfl

theorem phaseProgram_eventCost :
    layout.phaseProgram.eventCost =
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) + gatePool controls := by
  rw [phaseProgram, conjugateHadamard_eventCost, gates_program_eventCost]

theorem phaseProgram_unitDepth :
    layout.phaseProgram.evaluatedEventDepth (fun _ => 1) = gateCount controls + 2 := by
  rw [phaseProgram, conjugateHadamard_unitDepth, gates_program_depth]

/-- Complements, both H gates and all four global-minus gates are charged explicitly. -/
theorem zeroReflectionProgram_eventCost :
    layout.zeroReflectionProgram.eventCost =
      (2 * (controls + 1) + 2) • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) + gatePool controls := by
  simp only [zeroReflectionProgram, negativeZeroPhase, UnitaryCircuit.seq_eventCost,
    complementGates_eventCost, complementGates_reverse_eventCost,
    phaseProgram_eventCost, globalMinus_eventCost]
  apply Multiset.ext.mpr
  intro event
  simp only [Multiset.count_add, Multiset.count_nsmul]
  ring

/-- Every literal gate of the reflected one-dirty program lies on its sequential schedule. -/
theorem zeroReflectionProgram_unitDepth :
    layout.zeroReflectionProgram.evaluatedEventDepth (fun _ => 1) =
      2 * (controls + 1) + gateCount controls + 6 := by
  simp only [zeroReflectionProgram, negativeZeroPhase, UnitaryCircuit.evaluatedEventDepth_seq,
    GateSpec.programList_evaluatedEventDepth_unit, List.length_reverse,
    complementGates_length, phaseProgram_unitDepth, globalMinus_unitDepth]
  omega

end OneDirtyLayout
end Word

end

end QuantumAlg.EncodedBit
