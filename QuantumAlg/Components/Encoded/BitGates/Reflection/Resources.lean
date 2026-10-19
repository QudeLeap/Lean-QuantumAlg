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
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Actual elementary reflection events and sequential depths

These laws read the literal X, Z, H, CNOT and Toffoli programs. A native
single-qubit H or Z has unit depth and preserves the complete complementary
subsystem. Sequential conjugations retain both halves and the exact global
minus correction in their counts and depth.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

lemma hadamard_unitDepth (target : EncodedBit encoding) :
    (target.hadamard physical oracles).evaluatedEventDepth (fun _ => 1) = 1 := rfl

lemma pauliZ_unitDepth (target : EncodedBit encoding) :
    (target.pauliZ physical oracles).evaluatedEventDepth (fun _ => 1) = 1 := rfl

lemma conjugateHadamard_unitDepth (target : EncodedBit encoding)
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum) :
    (target.conjugateHadamard physical oracles program).evaluatedEventDepth (fun _ => 1) =
      program.evaluatedEventDepth (fun _ => 1) + 2 := by
  simp only [conjugateHadamard, UnitaryCircuit.evaluatedEventDepth_seq, hadamard_unitDepth]
  omega

lemma globalMinus_eventCost (target : EncodedBit encoding) :
    (target.globalMinus physical oracles).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := rfl

lemma globalMinus_unitDepth (target : EncodedBit encoding) :
    (target.globalMinus physical oracles).evaluatedEventDepth (fun _ => 1) = 1 := rfl

lemma pauliZ_eventCost (target : EncodedBit encoding) :
    (target.pauliZ physical oracles).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
      (.gate .singleQubit) := rfl

lemma hadamard_eventCost (target : EncodedBit encoding) :
    (target.hadamard physical oracles).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, hadamard_eventTrace]
  rfl

lemma conjugateHadamard_eventCost (target : EncodedBit encoding)
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum) :
    (target.conjugateHadamard physical oracles program).eventCost =
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) + program.eventCost := by
  simp only [conjugateHadamard, UnitaryCircuit.seq_eventCost, hadamard_eventCost, two_nsmul]
  abel

namespace GateSpec

lemma program_unitDepth (gate : GateSpec encoding) :
    (gate.program physical oracles).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [UnitaryCircuit.evaluatedEventDepth, program_eventDepth]
  rfl

lemma conjugateProgram_unitDepth (gates : List (GateSpec encoding))
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum) :
    (conjugateProgram physical oracles gates program).evaluatedEventDepth (fun _ => 1) =
      2 * gates.length + program.evaluatedEventDepth (fun _ => 1) := by
  simp only [conjugateProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    programList_evaluatedEventDepth_unit, List.length_reverse]
  omega

end GateSpec

lemma controlledZ_eventCost (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    (control.controlledZ physical oracles target different).eventCost =
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) := by
  rw [controlledZ, conjugateHadamard_eventCost, GateSpec.program_eventCost]
  rfl

lemma controlledZ_unitDepth (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    (control.controlledZ physical oracles target different).evaluatedEventDepth
      (fun _ => 1) = 3 := by
  rw [controlledZ, conjugateHadamard_unitDepth, GateSpec.program_unitDepth]

lemma doubleControlledZ_eventCost (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    (first.doubleControlledZ physical oracles second target
      firstSecond firstTarget secondTarget).eventCost =
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
          (.gate .toffoli) := by
  rw [doubleControlledZ, conjugateHadamard_eventCost, GateSpec.program_eventCost]
  rfl

lemma doubleControlledZ_unitDepth (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstTarget : first.wire ≠ target.wire)
    (secondTarget : second.wire ≠ target.wire) :
    (first.doubleControlledZ physical oracles second target
      firstSecond firstTarget secondTarget).evaluatedEventDepth
      (fun _ => 1) = 3 := by
  rw [doubleControlledZ, conjugateHadamard_unitDepth, GateSpec.program_unitDepth]

lemma twoWireZeroReflection_eventCost (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) :
    (first.twoWireZeroReflection physical oracles second different).eventCost =
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) := by
  simp only [twoWireZeroReflection, UnitaryCircuit.seq_eventCost,
    pauliZ_eventCost, controlledZ_eventCost, two_nsmul]
  abel

lemma twoWireZeroReflection_unitDepth (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) :
    (first.twoWireZeroReflection physical oracles second different).evaluatedEventDepth
      (fun _ => 1) = 5 := by
  simp only [twoWireZeroReflection, UnitaryCircuit.evaluatedEventDepth_seq,
    pauliZ_unitDepth, controlledZ_unitDepth]

lemma threeWireZeroReflection_eventCost (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstThird : first.wire ≠ third.wire)
    (secondThird : second.wire ≠ third.wire) :
    (first.threeWireZeroReflection physical oracles second third
      firstSecond firstThird secondThird).eventCost =
      9 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli) := by
  rw [threeWireZeroReflection, UnitaryCircuit.seq_eventCost, globalMinus_eventCost,
    GateSpec.conjugateProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost]
  have reversed : ([GateSpec.x first, .x second, .x third] : List (GateSpec encoding)).reverse =
      [.x third, .x second, .x first] := rfl
  have nativeX (bit : EncodedBit encoding) :
      GateSpec.event oracles (.x bit) = .gate .singleQubit := rfl
  rw [reversed]
  simp only [GateSpec.programList_eventCost, List.map_cons, List.map_nil, nativeX,
    ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, doubleControlledZ_eventCost]
  apply Multiset.ext.mpr
  intro event
  simp only [Multiset.count_add, Multiset.count_nsmul]
  ring

lemma threeWireZeroReflection_unitDepth (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire) (firstThird : first.wire ≠ third.wire)
    (secondThird : second.wire ≠ third.wire) :
    (first.threeWireZeroReflection physical oracles second third
      firstSecond firstThird secondThird).evaluatedEventDepth (fun _ => 1) = 10 := by
  simp only [threeWireZeroReflection, UnitaryCircuit.evaluatedEventDepth_seq,
    GateSpec.conjugateProgram_unitDepth, List.length_cons, List.length_nil,
    doubleControlledZ_unitDepth, globalMinus_unitDepth]

namespace Word

lemma complementGates_events {width : Nat} (word : Word encoding width) :
    word.complementGates.map (GateSpec.event oracles) =
      List.replicate width (.gate .singleQubit) := by
  simp only [complementGates, List.map_ofFn]
  exact List.ofFn_const width
    (Resource.Event.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model oracles))

lemma complementGates_eventCost {width : Nat} (word : Word encoding width) :
    (GateSpec.programList physical oracles word.complementGates).eventCost =
      width • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [GateSpec.programList_eventCost, complementGates_events, ResourcePool.ofList_replicate]
  rfl

lemma complementGates_reverse_eventCost {width : Nat} (word : Word encoding width) :
    (GateSpec.programList physical oracles word.complementGates.reverse).eventCost =
      width • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [GateSpec.programList_eventCost, List.map_reverse, complementGates_events,
    List.reverse_replicate, ResourcePool.ofList_replicate]
  rfl

namespace OneDirtyLayout

/-- Independent native gate multiplicities at each multi-control width. -/
def gatePool (controls : Nat) : ResourcePool (.quantum AlgorithmGate.model oracles) :=
  if controls = 0 then ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
    (.gate .singleQubit)
  else if controls = 1 then ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
    (.gate .cnot)
  else gateCount controls • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
    (.gate .toffoli)

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)

lemma gates_program_eventCost :
    (GateSpec.programList physical oracles layout.gates).eventCost = gatePool oracles controls := by
  rw [GateSpec.programList_eventCost, gates_events]
  unfold gatePool
  split
  · rfl
  · split
    · rfl
    · rw [ResourcePool.ofList_replicate]
      rfl

lemma phaseProgram_eventCost :
    (layout.phaseProgram physical oracles).eventCost =
      2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) + gatePool oracles controls := by
  rw [phaseProgram, conjugateHadamard_eventCost, gates_program_eventCost]

lemma phaseProgram_unitDepth :
    (layout.phaseProgram physical oracles).evaluatedEventDepth (fun _ => 1) =
      gateCount controls + 2 := by
  rw [phaseProgram, conjugateHadamard_unitDepth, gates_program_depth]

/-- Complements, both H gates and the one global-minus gate are charged explicitly. -/
lemma zeroReflectionProgram_eventCost :
    (layout.zeroReflectionProgram physical oracles).eventCost =
      (2 * (controls + 1) + 3) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
          (.gate .singleQubit) + gatePool oracles controls := by
  simp only [zeroReflectionProgram, negativeZeroPhase, UnitaryCircuit.seq_eventCost,
    complementGates_eventCost, complementGates_reverse_eventCost,
    phaseProgram_eventCost, globalMinus_eventCost]
  apply Multiset.ext.mpr
  intro event
  simp only [Multiset.count_add, Multiset.count_nsmul]
  ring

/-- Every literal gate of the reflected one-dirty program lies on its sequential schedule. -/
lemma zeroReflectionProgram_unitDepth :
    (layout.zeroReflectionProgram physical oracles).evaluatedEventDepth (fun _ => 1) =
      2 * (controls + 1) + gateCount controls + 3 := by
  simp only [zeroReflectionProgram, negativeZeroPhase, UnitaryCircuit.evaluatedEventDepth_seq,
    GateSpec.programList_evaluatedEventDepth_unit, List.length_reverse,
    complementGates_length, phaseProgram_unitDepth, globalMinus_unitDepth]
  omega

end OneDirtyLayout
end Word

end

end QuantumAlg.EncodedBit
