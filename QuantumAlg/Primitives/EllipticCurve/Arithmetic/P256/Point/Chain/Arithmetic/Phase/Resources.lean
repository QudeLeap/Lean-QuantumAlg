/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Phase
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Save.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources.Empty

/-! # Exact native resources of product recomputation and the complete paid character correction -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Phase

noncomputable section

open EncodedBit

/-- The actual stored mask selects these physical phase positions. -/
def selectedCount (outcome : Word) : Nat :=
  (EncodedBit.Word.PhaseCorrection.selected fun index : Fin 256 =>
    outcome.val.testBit index.val).length

lemma selectedCount_le (outcome : Word) : selectedCount outcome ≤ 256 :=
  EncodedBit.Word.PhaseCorrection.phaseCorrection_selected_count_le _

lemma compute_toffoli_count (assignment : PortAssignment) (selection : Selector) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (compute assignment selection).eventCost = 18059173 :=
  Native.placed_count (Placement.layout assignment) _ _ _
    (Horner.cleanProgram_toffoli_count (Save.savedEncoding (Placement.restEncoding assignment))
      (Accumulate.Square.multiplier (Placement.restEncoding assignment)).quantum
      (Accumulate.Square.outerBit (Placement.restEncoding assignment)
        (selectorBit assignment selection))
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding assignment)
        (selectorBit assignment selection)))

lemma compute_cnot_count (assignment : PortAssignment) (selection : Selector) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (compute assignment selection).eventCost = 685693 :=
  Native.placed_count (Placement.layout assignment) _ _ _
    (Horner.cleanProgram_cnot_count (Save.savedEncoding (Placement.restEncoding assignment))
      (Accumulate.Square.multiplier (Placement.restEncoding assignment)).quantum
      (Accumulate.Square.outerBit (Placement.restEncoding assignment)
        (selectorBit assignment selection))
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding assignment)
        (selectorBit assignment selection)))

lemma compute_x_count (assignment : PortAssignment) (selection : Selector) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (compute assignment selection).eventCost = 129540 :=
  Native.placed_count (Placement.layout assignment) _ _ _
    (Horner.cleanProgram_x_count (Save.savedEncoding (Placement.restEncoding assignment))
      (Accumulate.Square.multiplier (Placement.restEncoding assignment)).quantum
      (Accumulate.Square.outerBit (Placement.restEncoding assignment)
        (selectorBit assignment selection))
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding assignment)
        (selectorBit assignment selection)))

lemma compute_quantumTime (assignment : PortAssignment) (selection : Selector) :
    (compute assignment selection).evaluatedEventDepth Resource.Event.quantumDuration =
      18874406 :=
  ((Placement.layout assignment).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (Horner.cleanProgram_quantumTime (Save.savedEncoding (Placement.restEncoding assignment))
      (Accumulate.Square.multiplier (Placement.restEncoding assignment)).quantum
      (Accumulate.Square.outerBit (Placement.restEncoding assignment)
        (selectorBit assignment selection))
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding assignment)
        (selectorBit assignment selection)))

private lemma plain_cost (target : EncodedBit.Word Frame.encoding 256) (outcome : Word) :
    (EncodedBit.Word.PhaseCorrection.program (QubitLayout.canonical _) .empty target
      (fun index => outcome.val.testBit index.val)).eventCost =
        selectedCount outcome • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    EncodedBit.Word.PhaseCorrection.program,
    EncodedBit.Word.PhaseCorrection.phaseCorrection_sequence_trace,
    ResourcePool.ofList_replicate]
  rfl

/-- The full pool includes both actual arithmetic directions and all negative-control gates. -/
lemma program_eventCost (assignment : PortAssignment) (selection : Selector) (outcome : Word) :
    (program assignment selection outcome).eventCost =
      (compute assignment selection).eventCost +
        (selectedCount outcome • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) +
          (compute assignment selection).eventCost) +
        (selectedCount outcome •
          (2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) +
            ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)) +
          2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)) := by
  rw [program, UnitaryCircuit.seq_eventCost, recomputedProgram,
    UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_emptyAdjoints_eventCost, plain_cost,
    inactiveProgram, EncodedBit.Word.PhaseCorrection.Controlled.program,
    EncodedBit.Word.PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_cost]
  rfl

lemma program_toffoli_count (assignment : PortAssignment) (selection : Selector) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program assignment selection outcome).eventCost = 36118346 := by
  rw [program_eventCost]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton,
    compute_toffoli_count, Resource.Event.gate.injEq, reduceCtorEq, if_false,
    Nat.mul_zero, Nat.add_zero]

lemma program_cnot_count (assignment : PortAssignment) (selection : Selector) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program assignment selection outcome).eventCost = 1371386 + selectedCount outcome := by
  rw [program_eventCost]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton,
    compute_cnot_count, Resource.Event.gate.injEq, reduceCtorEq, if_true, if_false,
    Nat.mul_zero, Nat.add_zero]
  omega

lemma program_x_count (assignment : PortAssignment) (selection : Selector) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program assignment selection outcome).eventCost = 259082 + 3 * selectedCount outcome := by
  rw [program_eventCost]
  simp only [ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton,
    compute_x_count, Resource.Event.gate.injEq, reduceCtorEq, if_true, if_false,
    Nat.add_zero, Nat.mul_one]
  omega

private lemma plain_time (target : EncodedBit.Word Frame.encoding 256) (outcome : Word) :
    (EncodedBit.Word.PhaseCorrection.program (QubitLayout.canonical _) .empty target
      (fun index => outcome.val.testBit index.val)).evaluatedEventDepth
        Resource.Event.quantumDuration = selectedCount outcome :=
  (UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth _ .empty .empty).trans
    (EncodedBit.Word.PhaseCorrection.phaseCorrection_sequence_depth _ _ _ _)

lemma program_quantumTime (assignment : PortAssignment) (selection : Selector) (outcome : Word) :
    (program assignment selection outcome).evaluatedEventDepth Resource.Event.quantumDuration =
      37748814 + 4 * selectedCount outcome := by
  have inactive : (inactiveProgram assignment selection outcome).evaluatedEventDepth
      Resource.Event.quantumDuration = 3 * selectedCount outcome + 2 :=
    (UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth _ .empty .empty).trans
      (EncodedBit.Word.PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_depth
        (QubitLayout.canonical _) .empty _ _ _ false _)
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, recomputedProgram,
    UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    AlgorithmGate.algorithmGate_emptyAdjoints_quantumTime, compute_quantumTime,
    plain_time, inactive]
  omega

end

end Arithmetic.Phase

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
