/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Doubling

/-!
# Concrete logarithmic X propagation on arbitrary dirty targets

The forward word doubles its reached target prefix in each actual native layer.
Its inverse reverses those same layers and actual CNOTs. The word requires no
clean target and allocates no additional system.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

namespace CnotLayer

/-- Reverse the actual self-inverse native instructions in this same independent layer. -/
def reverse (layer : CnotLayer encoding) : CnotLayer encoding where
  edges := layer.edges.reverse
  separate := by
    rw [List.pairwise_reverse]
    apply layer.separate.imp
    intro first second separate
    exact separate.symm

/-- Layer reversal retains precisely the reversed source word. -/
lemma reverse_gates (layer : CnotLayer encoding) : layer.reverse.gates = layer.gates.reverse := by
  simp only [reverse, gates, List.map_reverse]

end CnotLayer

/-- The source instruction word of a sequence of actual independent layers. -/
def layerWordGates (layers : List (CnotLayer encoding)) : List (GateSpec encoding) :=
  layers.flatMap CnotLayer.gates

/-- Execute the original actual independent layers in their required order. -/
def layerWordProgram (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    List (CnotLayer encoding) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum
  | [] => UnitaryCircuit.identity _ _ _
  | first :: rest => (first.program physical oracles).seq (layerWordProgram physical oracles rest)

/-- The actual layered native circuit realizes its complete encoded word on all inputs. -/
lemma layerWordProgram_realizes (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (layers : List (CnotLayer encoding)) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (layerWordProgram physical oracles layers) environment
      (GateSpec.stepList (layerWordGates layers)) := by
  induction layers with
  | nil =>
      simpa only [layerWordProgram, layerWordGates, List.flatMap_nil, GateSpec.stepList] using
        UnitaryCircuit.Realizes.identityAt AlgorithmGate.model oracles encoding physical environment
  | cons first rest ih =>
      change UnitaryCircuit.Realizes encoding
        ((first.program physical oracles).seq (layerWordProgram physical oracles rest)) environment
        (GateSpec.stepList (first.gates ++ layerWordGates rest))
      rw [show GateSpec.stepList (first.gates ++ layerWordGates rest) =
        (fun state => GateSpec.stepList (layerWordGates rest)
          (GateSpec.stepList first.gates state)) by
            funext state
            exact GateSpec.stepList_append _ _ state]
      exact UnitaryCircuit.Realizes.seq (first.program_realizes physical oracles environment) ih


/-- Each independent nonempty layer takes one quantum step; empty layers take none. -/
lemma layerWordProgram_quantumTime_le (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding)) :
    (layerWordProgram physical oracles layers).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ layers.length := by
  induction layers with
  | nil => exact Nat.le_refl 0
  | cons first rest ih =>
      rw [layerWordProgram, UnitaryCircuit.evaluatedEventDepth_seq, first.program_quantumTime]
      simp only [List.length_cons]
      split <;> omega


/-- The inverse uses every original layer and occurrence in reverse execution order. -/
def inverseLayerWord (layers : List (CnotLayer encoding)) : List (CnotLayer encoding) :=
  layers.reverse.map CnotLayer.reverse

/-- The inverse's actual source word is exactly the original word in reverse order. -/
lemma inverseLayerWord_gates (layers : List (CnotLayer encoding)) :
    layerWordGates (inverseLayerWord layers) = (layerWordGates layers).reverse := by
  simp only [inverseLayerWord, layerWordGates, List.flatMap_map, Function.comp_def,
    CnotLayer.reverse_gates, List.reverse_flatMap]

/-- Reversing the same physical word creates no extra layer. -/
lemma inverseLayerWord_length (layers : List (CnotLayer encoding)) :
    (inverseLayerWord layers).length = layers.length := by
  simp only [inverseLayerWord, List.length_map, List.length_reverse]

/-- The actual number of CNOT occurrences in the physical layer word. -/
def layerWordSize (layers : List (CnotLayer encoding)) : Nat :=
  (layers.map fun layer => layer.edges.length).sum

variable {count : Nat}

/-- The concrete target-only word has one doubling stage for each binary level. -/
def doublingWord (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire)) :
    Nat → List (CnotLayer encoding)
  | 0 => []
  | height + 1 => doublingWord target distinct height ++
      [doublingLayer target distinct (2 ^ height) (Nat.pow_pos (by decide))]

/-- The concrete word contains precisely the declared number of actual doubling layers. -/
lemma doublingWord_length (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire)) (height : Nat) :
    (doublingWord target distinct height).length = height := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [doublingWord, List.length_append, List.length_singleton, ih]

/-- Actual CNOT multiplicities telescope to the number of newly reached original wires. -/
lemma doublingWord_size (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire)) (height : Nat) :
    layerWordSize (doublingWord target distinct height) + min 1 count =
      min (2 ^ height) count := by
  induction height with
  | zero => simp only [doublingWord, layerWordSize, List.map_nil, List.sum_nil,
      Nat.zero_add, pow_zero]
  | succ height ih =>
      simp only [doublingWord, layerWordSize, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        doublingLayer_length, doublingSize, pow_succ]
      change layerWordSize (doublingWord target distinct height) +
        min (2 ^ height) (count - 2 ^ height) + min 1 count = min (2 ^ height * 2) count
      omega

/-- Each actual layer propagates the reached X mask on the complete arbitrary input state. -/
lemma doublingWord_propagates (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (height : Nat) (state : Data) :
    GateSpec.stepList (layerWordGates (doublingWord target distinct height))
      (flipBits (prefixBits target 1) state) =
      flipBits (prefixBits target (2 ^ height))
        (GateSpec.stepList (layerWordGates (doublingWord target distinct height)) state) := by
  induction height generalizing state with
  | zero => rfl
  | succ height ih =>
      dsimp only [layerWordGates] at ih
      simp only [doublingWord, layerWordGates, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, GateSpec.stepList_append]
      rw [ih, doublingLayer_propagates]
      simp only [pow_succ, Nat.mul_comm]

end

end QuantumAlg.EncodedBit.WindowLookup
