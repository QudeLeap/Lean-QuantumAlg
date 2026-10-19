/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Exact native-coordinate support of literal encoded base gates

The primitive alphabet contains the distinct native X, CNOT, and Toffoli
coordinates. Every event of an actual compiled GateSpec list belongs to
that explicit pool. The support and zero-count proofs inspect the literal
program, with no algorithm-specific dependency or caller-supplied witness.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

/-- The three distinct default-model coordinates emitted by literal encoded base gates. -/
def primitiveAlphabet : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList [.gate .singleQubit, .gate .cnot, .gate .toffoli]

private lemma primitive_event_mem {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gate : EncodedBit.GateSpec encoding) :
    EncodedBit.GateSpec.event .empty gate ∈ primitiveAlphabet := by
  cases gate <;>
    simp [primitiveAlphabet, ResourcePool.ofList, EncodedBit.GateSpec.event,
      EncodedBit.GateSpec.primitive, QubitPrimitive.event,
      QubitPrimitive.nativeToken, AlgorithmGate.model, AlgorithmGate.coordinate]

/-- A literal base-gate list has no event coordinate outside the explicitly declared alphabet. -/
lemma programList_native_support {Data : Type} {encoding : BinaryLabelEncoding Data}
    (layout : QubitLayout encoding.width)
    (gates : List (EncodedBit.GateSpec encoding))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (EncodedBit.GateSpec.programList layout .empty gates).eventCost) :
    focus ∈ primitiveAlphabet := by
  rw [EncodedBit.GateSpec.programList_eventCost] at present
  change focus ∈ gates.map (EncodedBit.GateSpec.event .empty) at present
  obtain ⟨gate, _, rfl⟩ := List.mem_map.mp present
  exact primitive_event_mem gate

/-- Every coordinate outside the literal primitive alphabet has zero actual multiplicity. -/
lemma programList_count_zero_of_not_mem_primitiveAlphabet {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    (layout : QubitLayout encoding.width)
    (gates : List (EncodedBit.GateSpec encoding))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (outside : focus ∉ primitiveAlphabet) :
    ResourcePool.count focus
      (EncodedBit.GateSpec.programList layout .empty gates).eventCost = 0 := by
  exact Multiset.count_eq_zero.mpr (fun present =>
    outside (programList_native_support layout gates focus present))

end

end QuantumAlg.EncodedBit.GateSpec
