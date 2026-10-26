/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Save
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-!
# Actual product-save resources

The false-selector numerator copy is lowered to 256 sequential Toffolis
with two physical X masks. Its shared selector is retained as a real
conflict. Counts and duration are derived from that emitted list and the
same complete clean-Horner program used by the basis and Reference laws.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Save

noncomputable section

open QuantumAlg.EncodedBit GateSpec

variable {Rest : Type} (rest : BinaryLabelEncoding Rest) (selector : EncodedBit rest)

private lemma xor_x_sum {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}
    (source target : EncodedBit.Word encoding count)
    (different : ∀ index, (source.bit index).wire ≠ (target.bit index).wire) :
    ((source.xorIntoGates target different).map xMultiplicity).sum = 0 := by
  apply List.sum_eq_zero
  intro value present
  obtain ⟨gate, gatePresent, rfl⟩ := List.mem_map.mp present
  rw [EncodedBit.Word.xorIntoGates] at gatePresent
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp gatePresent
  rfl

private lemma xor_dirty_sum {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}
    (source target : EncodedBit.Word encoding count)
    (different : ∀ index, (source.bit index).wire ≠ (target.bit index).wire) :
    ((source.xorIntoGates target different).map dirtyControlCount).sum = count := by
  simp [EncodedBit.Word.xorIntoGates, List.sum_ofFn, dirtyControlCount]

private lemma negativeCopy_native_sums :
    ((negativeCopyGates rest selector).map toffoliMultiplicity).sum = 256 ∧
      ((negativeCopyGates rest selector).map cnotMultiplicity).sum = 0 ∧
      ((negativeCopyGates rest selector).map xMultiplicity).sum = 2 := by
  simp only [negativeCopyGates, choiceGates, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons, listWithDirtyControl_toffoliMultiplicity_sum,
    listWithDirtyControl_cnotMultiplicity_sum, listWithDirtyControl_xMultiplicity_sum,
    copyGates, EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum,
    EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum,
    xor_x_sum,
    List.map_nil, List.sum_nil, toffoliMultiplicity, cnotMultiplicity, xMultiplicity]
  exact ⟨rfl, rfl, True.intro⟩

private lemma negativeCopy_length : (negativeCopyGates rest selector).length = 258 := by
  simp only [negativeCopyGates, choiceGates, List.length_append, List.length_cons,
    listWithDirtyControl_length, copyGates, xor_dirty_sum,
    List.map_nil, List.sum_nil]
  change (256 + 1) + (0 + 1) = 258
  omega

lemma negativeCopyProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (negativeCopyProgram rest selector).eventCost = 256 :=
  (GateSpec.programList_toffoli_count_eq_sum _ _ _).trans
    (negativeCopy_native_sums rest selector).1

lemma negativeCopyProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (negativeCopyProgram rest selector).eventCost = 0 :=
  (GateSpec.programList_cnot_count_eq_sum _ _ _).trans
    (negativeCopy_native_sums rest selector).2.1

lemma negativeCopyProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (negativeCopyProgram rest selector).eventCost = 2 :=
  (GateSpec.programList_x_count_eq_sum _ _ _).trans
    (negativeCopy_native_sums rest selector).2.2

lemma negativeCopyProgram_quantumTime :
    (negativeCopyProgram rest selector).evaluatedEventDepth Resource.Event.quantumDuration =
      258 :=
  (GateSpec.programList_quantumTime _ _ _).trans (negativeCopy_length rest selector)

lemma rawProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (rawProgram rest selector).eventCost = 18059429 := by
  rw [rawProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    negativeCopyProgram_toffoli_count]
  exact congrArg (fun amount => amount + 256)
    (Horner.cleanProgram_toffoli_count (savedEncoding rest)
      (Accumulate.Square.multiplier rest).quantum (Accumulate.Square.outerBit rest selector)
      (Accumulate.Square.outer_multiplier_ne rest selector))

lemma rawProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (rawProgram rest selector).eventCost = 685693 := by
  rw [rawProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    negativeCopyProgram_cnot_count, Nat.add_zero]
  exact Horner.cleanProgram_cnot_count (savedEncoding rest)
    (Accumulate.Square.multiplier rest).quantum (Accumulate.Square.outerBit rest selector)
    (Accumulate.Square.outer_multiplier_ne rest selector)

lemma rawProgram_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (rawProgram rest selector).eventCost = 129542 := by
  rw [rawProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    negativeCopyProgram_x_count]
  exact congrArg (fun amount => amount + 2)
    (Horner.cleanProgram_x_count (savedEncoding rest)
      (Accumulate.Square.multiplier rest).quantum (Accumulate.Square.outerBit rest selector)
      (Accumulate.Square.outer_multiplier_ne rest selector))

lemma rawProgram_quantumTime :
    (rawProgram rest selector).evaluatedEventDepth Resource.Event.quantumDuration =
      18874664 := by
  rw [rawProgram, UnitaryCircuit.evaluatedEventDepth_seq, negativeCopyProgram_quantumTime]
  exact congrArg (fun amount => amount + 258)
    (Horner.cleanProgram_quantumTime (savedEncoding rest)
      (Accumulate.Square.multiplier rest).quantum (Accumulate.Square.outerBit rest selector)
      (Accumulate.Square.outer_multiplier_ne rest selector))

lemma program_toffoli_count (assignment : PortAssignment) (selection : Selector) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program assignment selection).eventCost = 18059429 :=
  Native.placed_count (Placement.layout assignment) _ _ _
    (rawProgram_toffoli_count (Placement.restEncoding assignment)
      (selectorBit assignment selection))

lemma program_cnot_count (assignment : PortAssignment) (selection : Selector) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program assignment selection).eventCost = 685693 :=
  Native.placed_count (Placement.layout assignment) _ _ _
    (rawProgram_cnot_count (Placement.restEncoding assignment)
      (selectorBit assignment selection))

lemma program_x_count (assignment : PortAssignment) (selection : Selector) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program assignment selection).eventCost = 129542 :=
  Native.placed_count (Placement.layout assignment) _ _ _
    (rawProgram_x_count (Placement.restEncoding assignment) (selectorBit assignment selection))

lemma program_quantumTime (assignment : PortAssignment) (selection : Selector) :
    (program assignment selection).evaluatedEventDepth Resource.Event.quantumDuration =
      18874664 :=
  ((Placement.layout assignment).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (rawProgram_quantumTime (Placement.restEncoding assignment)
      (selectorBit assignment selection))

end

end Arithmetic.Save

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
