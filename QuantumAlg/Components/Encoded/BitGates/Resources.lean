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

/-- The three distinct primitive coordinates emitted by the literal encoded base gates. -/
def primitiveAlphabet : ResourcePool .quantum :=
  ResourcePool.ofList [.gate (.builtin "x"), .gate (.builtin "cnot"), .gate (.builtin "toffoli")]

private theorem primitive_event_mem {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gate : EncodedBit.GateSpec encoding) : EncodedBit.GateSpec.event gate ∈ primitiveAlphabet := by
  cases gate <;> simp [primitiveAlphabet, ResourcePool.ofList, EncodedBit.GateSpec.event]

/-- A literal base-gate list has no event coordinate outside the explicitly declared alphabet. -/
theorem programList_native_support {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding)) (focus : Resource.Event .quantum)
    (present : focus ∈ (EncodedBit.GateSpec.programList gates).eventCost) :
    focus ∈ primitiveAlphabet := by
  rw [EncodedBit.GateSpec.programList_eventCost] at present
  change focus ∈ gates.map EncodedBit.GateSpec.event at present
  obtain ⟨gate, _, rfl⟩ := List.mem_map.mp present
  exact primitive_event_mem gate

/-- Every coordinate outside the literal primitive alphabet has zero actual multiplicity. -/
theorem programList_count_zero_of_not_mem_primitiveAlphabet {Data : Type}
    {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding)) (focus : Resource.Event .quantum)
    (outside : focus ∉ primitiveAlphabet) :
    ResourcePool.count focus (EncodedBit.GateSpec.programList gates).eventCost = 0 := by
  exact Multiset.count_eq_zero.mpr (fun present =>
    outside (programList_native_support gates focus present))

end

end QuantumAlg.EncodedBit.GateSpec
