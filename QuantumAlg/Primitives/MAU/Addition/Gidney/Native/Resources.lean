/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Native.Alphabet
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small.Offset
import all QuantumAlg.Core.Base.Accounting.Support

/-!
# Independent native-coordinate budgets for actual modular offsets

Every comparison and controlled bi-flip is emitted as a literal default-model
list. Its single-qubit/CNOT/Toffoli support and actual gate count give an
independent native resource budget. Small offsets retain their literal X/CNOT
construction and use no borrowed bits.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open Nat.FixedWidth EncodedBit.GateSpec

theorem gidneyComparison_native_support (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (comparisonProgram width pivot).eventCost) :
    focus ∈ primitiveAlphabet := by
  have same : (programList (QubitLayout.canonical _) .empty
      (comparisonGates width pivot)).eventCost = (comparisonProgram width pivot).eventCost :=
    (programList_eventCost _ _ _).trans (gidneyComparisonGates_eventCost width pivot)
  rw [← same] at present
  exact programList_native_support _ _ focus present

theorem gidneyBiFlip_native_support (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (biFlipProgram width pivot).eventCost) :
    focus ∈ primitiveAlphabet :=
  programList_native_support _ (biFlipGates width pivot) focus present

theorem gidneyPivot_native_support (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (pivotProgram width pivot).eventCost) :
    focus ∈ offsetAlphabet :=
  programList_native_support _ (pivotGates width pivot) focus present

/-- Every emitted event is one of the three actual default-model native coordinates. -/
theorem gidneyModularOffset_native_support (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (modularOffsetProgram width modulus constant).eventCost) :
    focus ∈ offsetAlphabet :=
  programList_native_support _ (modularOffsetGates width modulus constant) focus present

/-- The independent resource pool states a closed cap at each explicit native coordinate. -/
def modularOffsetNativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  modularOffsetEventBound width • offsetAlphabet

theorem gidneyModularOffset_native_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).eventCost ≤ modularOffsetNativeBudget width :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (gidneyModularOffset_native_support width modulus constant)
    (gidneyModularOffset_event_count_bound width modulus constant)

theorem gidneySmallPivot_native_support (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (Small.pivotProgram width small pivot).eventCost) :
    focus ∈ primitiveAlphabet := by
  interval_cases width
  · change focus ∈ (Small.Zero.circuit pivot).eventCost at present
    rw [(Small.Zero.gidneySmallZero_interface pivot).1] at present
    simp at present
  · change focus ∈ (Small.One.circuit pivot).eventCost at present
    rw [Small.One.gidneySmallOne_eventCost] at present
    (fin_cases pivot <;> simp [ResourcePool.ofList, primitiveAlphabet] at *); tauto
  · change focus ∈ (Small.Two.circuit pivot).eventCost at present
    rw [Small.Two.gidneySmallTwo_eventCost] at present
    fin_cases pivot <;> simp [ResourcePool.ofList, primitiveAlphabet] at * <;> tauto

/-- Small offsets use only the original primitive labels and allocate no borrowed bits. -/
theorem gidneySmallModularOffset_native_support (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (Small.modularOffsetProgram width small modulus constant).eventCost) :
    focus ∈ primitiveAlphabet := by
  rw [Small.gidneySmallModularOffset_eventCost] at present
  simp only [Multiset.mem_add] at present
  rcases present with (first | second) | third
  · exact gidneySmallPivot_native_support width small
      (offsetFirstPivot modulus constant) focus first
  · exact gidneySmallPivot_native_support width small modulus focus second
  · exact gidneySmallPivot_native_support width small (offsetLastPivot modulus constant) focus third

end

end QuantumAlg.MAU.Addition.Gidney
