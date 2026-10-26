/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Conjugation

/-!
# Native occurrences of the actual dirty-target masked-X word

Only the real emitted CNOTs are counted. A nonempty mask of weight m uses
2m-1 CNOTs, and an empty mask uses no gate. The depth bound comes from the same
independent doubling layers; no additional fanout state is allocated.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma edge_event (oracles : OracleModel) (edge : CnotEdge encoding) :
    GateSpec.event oracles edge.gate = (.gate .cnot :
      Resource.Event (.quantum AlgorithmGate.model oracles)) := rfl

/-- The actual layer emits exactly one native CNOT per retained physical edge. -/
lemma CnotLayer.program_eventTrace_exact (layer : CnotLayer encoding)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    (layer.program physical oracles).eventTrace =
      List.replicate layer.edges.length (.gate .cnot) := by
  rw [layer.program_eventTrace]
  simp only [CnotLayer.gates, List.map_map, Function.comp_def, edge_event]
  simp only [List.map_const']

/-- All native occurrences of the actual layered word are CNOTs. -/
lemma layerWordProgram_eventTrace (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (layers : List (CnotLayer encoding)) :
    (layerWordProgram physical oracles layers).eventTrace =
      List.replicate (layerWordSize layers) (.gate .cnot) := by
  induction layers with
  | nil => rfl
  | cons first rest ih =>
      rw [layerWordProgram, UnitaryCircuit.seq_eventTrace, first.program_eventTrace_exact, ih]
      simp only [layerWordSize, List.map_cons, List.sum_cons, List.replicate_add]

/-- Reversing actual self-inverse CNOTs preserves their exact multiplicity. -/
lemma inverseLayerWord_size (layers : List (CnotLayer encoding)) :
    layerWordSize (inverseLayerWord layers) = layerWordSize layers := by
  simp only [inverseLayerWord, layerWordSize, List.map_map, Function.comp_def,
    CnotLayer.reverse, List.length_reverse, List.map_reverse, List.sum_reverse]

/-- One selector CNOT joins the two original forward/backward physical words. -/
lemma conjugatedMaskProgram_eventTrace (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (different : selector.wire ≠ pivot.wire) :
    (conjugatedMaskProgram physical oracles layers selector pivot different).eventTrace =
      List.replicate (2 * layerWordSize layers + 1) (.gate .cnot) := by
  rw [conjugatedMaskProgram, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    layerWordProgram_eventTrace, layerWordProgram_eventTrace, inverseLayerWord_size,
    GateSpec.program_eventTrace]
  let cnot : Resource.Event (.quantum AlgorithmGate.model oracles) := .gate .cnot
  change List.replicate (layerWordSize layers) cnot ++
      ([cnot] ++ List.replicate (layerWordSize layers) cnot) = _
  rw [← List.replicate_one (a := cnot), ← List.replicate_add, ← List.replicate_add]
  congr 1
  omega

variable {count : Nat}

/-- The exact native ledger charges the same original dirty-target masked-X circuit. -/
lemma maskedXProgram_eventTrace (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (covered : count ≤ 2 ^ height) :
    (maskedXProgram physical oracles target distinct selector outside height).eventTrace =
      List.replicate (if count = 0 then 0 else 2 * count - 1) (.gate .cnot) := by
  unfold maskedXProgram
  split
  · rw [conjugatedMaskProgram_eventTrace]
    have size := doublingWord_size target distinct height
    rw [Nat.min_eq_left ‹0 < count›, Nat.min_eq_right covered] at size
    rw [if_neg (by omega)]
    congr 1
    omega
  · have zero : count = 0 := by omega
    subst count
    rfl

/-- Actual native CNOT count for an arbitrary mask, including the empty mask. -/
lemma maskedXProgram_cnot_count (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (covered : count ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (maskedXProgram physical oracles target distinct selector outside height).eventCost =
        if count = 0 then 0 else 2 * count - 1 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    maskedXProgram_eventTrace _ _ _ _ _ _ _ covered]
  simp [ResourcePool.ofList, ResourcePool.count]

end

end QuantumAlg.EncodedBit.WindowLookup
