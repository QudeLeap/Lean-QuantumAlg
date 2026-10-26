/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Parallel
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Actual parallel reset X gates selected by the stored measurement word

Every selected event is a native X on its original measured physical position.
The independence check includes every actual target, and the all-input action
is exactly XOR by the selected stored word, preserving every complement wire.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma wordX_separate (physical : QubitLayout encoding.width)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (constant : Fin (2 ^ width)) :
    (Word.xorConstantGates target constant).Pairwise (fun first second =>
      Disjoint (GateSpec.physicalSupport physical first)
        (GateSpec.physicalSupport physical second)) := by
  apply List.pairwise_map.mpr
  apply (Word.constantOneIndices_nodup constant).imp
  intro first second different
  rw [GateSpec.physicalSupport_x, GateSpec.physicalSupport_x, Finset.disjoint_singleton]
  exact fun same => different (distinct same)

/-- The actual native X corrections on distinct original result wires execute in parallel. -/
def wordXProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (constant : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.parallelProgramList physical oracles (Word.xorConstantGates target constant)
    (wordX_separate physical target distinct constant)

/-- The stored correction word has its exact arbitrary-input XOR action, with no phase loss. -/
lemma wordXProgram_realizes (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (constant : Fin (2 ^ width)) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (wordXProgram physical oracles target distinct constant)
      environment (Word.xorConstantStep target constant) :=
  GateSpec.parallelProgramList_realizes physical oracles _ _ environment

/-- Native corrections retain exactly one single-qubit event per selected stored outcome. -/
lemma wordXProgram_eventTrace (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (constant : Fin (2 ^ width)) :
    (wordXProgram physical oracles target distinct constant).eventTrace =
      List.replicate (Word.constantOneIndices constant).length (.gate .singleQubit) := by
  rw [wordXProgram, GateSpec.parallelProgramList_eventTrace, GateSpec.programList_eventTrace]
  simp only [Word.xorConstantGates, List.map_map, Function.comp_def]
  change (Word.constantOneIndices constant).map (fun _ =>
    (Resource.Event.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model oracles))) = _
  exact List.map_const'

/-- The same actual independent corrections retain one quantum dependency at most. -/
lemma wordXProgram_quantumTime_le (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (constant : Fin (2 ^ width)) :
    (wordXProgram physical oracles target distinct constant).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 1 := by
  rw [wordXProgram, GateSpec.parallelProgramList_quantumTime]
  split <;> omega

end

end QuantumAlg.EncodedBit.WindowLookup
