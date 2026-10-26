/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Square.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Complete paid native square-MAC ledger, including the original-word copy and its inverse -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner

variable {Rest : Type} (rest : BinaryLabelEncoding Rest) (outer : EncodedBit rest)

private lemma copy_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (copyProgram rest).eventCost = 256 := by
  rw [copyProgram, programList_cnot_count_eq_sum]
  exact EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum _ _ _

private lemma copy_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (copyProgram rest).eventCost = 0 := by
  rw [copyProgram, programList_toffoli_count_eq_sum]
  exact EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum _ _ _

private lemma xor_x_count {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}
    (source target : EncodedBit.Word encoding count)
    (separate : ∀ index, (source.bit index).wire ≠ (target.bit index).wire) :
    ((EncodedBit.Word.xorIntoGates source target separate).map xMultiplicity).sum = 0 := by
  apply List.sum_eq_zero
  intro amount member
  obtain ⟨gate, gateMember, rfl⟩ := List.mem_map.mp member
  rw [EncodedBit.Word.xorIntoGates] at gateMember
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp gateMember
  rfl

private lemma copy_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (copyProgram rest).eventCost = 0 := by
  rw [copyProgram, programList_x_count_eq_sum]
  exact xor_x_count _ _ _

private lemma uncopy_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (uncopyProgram rest).eventCost =
      ResourcePool.count focus (copyProgram rest).eventCost := by
  simp only [uncopyProgram, copyProgram, programList_eventCost, ResourcePool.count_ofList,
    uncopyGates, List.map_reverse, List.count_reverse]

private lemma three_count {count : Nat} {layout : QuantumLayout count}
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (first middle last : UnitaryCircuit AlgorithmGate.model .empty layout) :
    ResourcePool.count focus (UnitaryCircuit.seq first (UnitaryCircuit.seq middle last)).eventCost =
      ResourcePool.count focus first.eventCost +
        (ResourcePool.count focus middle.eventCost + ResourcePool.count focus last.eventCost) :=
  (ResourcePool.count_add focus _ _).trans
    (congrArg (fun value => ResourcePool.count focus first.eventCost + value)
      (ResourcePool.count_add focus _ _))

private lemma square_count (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (program rest outer).eventCost =
      ResourcePool.count focus (copyProgram rest).eventCost +
        (ResourcePool.count focus
            (Inverse.program (savedEncoding rest) (multiplier rest) (outerBit rest outer)
              (outer_multiplier_ne rest outer)).eventCost +
          ResourcePool.count focus (copyProgram rest).eventCost) :=
  (three_count focus _ _ _).trans
    (congrArg (fun value => ResourcePool.count focus (copyProgram rest).eventCost +
      (ResourcePool.count focus
        (Inverse.program (savedEncoding rest) (multiplier rest) (outerBit rest outer)
          (outer_multiplier_ne rest outer)).eventCost + value)) (uncopy_count rest focus))

/-- Every native square-MAC Toffoli is paid, including both complete source traversals. -/
lemma program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program rest outer).eventCost = 22717258 := by
  rw [square_count, copy_toffoli_count, Inverse.program_toffoli_count]

/-- The two actual original-word XORs add all 512 CNOTs to the inverse MAC body. -/
lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program rest outer).eventCost = 1241850 := by
  rw [square_count, copy_cnot_count, Inverse.program_cnot_count]

lemma program_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program rest outer).eventCost = 259080 := by
  rw [square_count, copy_x_count, Inverse.program_x_count]

private lemma copy_length : (copyGates rest).length = 256 :=
  EncodedBit.Word.xorIntoGates_length _ _ _

private lemma copy_time :
    (copyProgram rest).evaluatedEventDepth Resource.Event.quantumDuration = 256 :=
  (programList_quantumTime (QubitLayout.canonical _) .empty (copyGates rest)).trans
    (copy_length rest)

private lemma uncopy_time :
    (uncopyProgram rest).evaluatedEventDepth Resource.Event.quantumDuration = 256 :=
  (programList_quantumTime (QubitLayout.canonical _) .empty (uncopyGates rest)).trans
    ((List.length_reverse (as := copyGates rest)).trans (copy_length rest))

/-- Complete actual duration includes copying and clearing the existing original multiplier word. -/
lemma program_quantumTime :
    (program rest outer).evaluatedEventDepth Resource.Event.quantumDuration = 24218188 := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, copy_time,
    UnitaryCircuit.evaluatedEventDepth_seq, Inverse.program_quantumTime, uncopy_time]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square
