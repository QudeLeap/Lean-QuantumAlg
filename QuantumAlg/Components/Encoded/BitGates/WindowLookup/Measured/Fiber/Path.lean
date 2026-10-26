/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Character
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Outcome
import Mathlib.Data.Fintype.EquivFin

/-!
# Every actual ordered measurement outcome occurs exactly once

The concrete map names its result bits by their original physical positions,
then takes the actual interpreter path. Its proof of bijectivity uses that
same map and the exact recursive path cardinality. No quantum state-space
isomorphism or extra executable operation is introduced.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The actual path labelled by one result word, using the original physical result positions. -/
def namedResultPath (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (seed : Data) (value : Fin (2 ^ width)) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path :=
  Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts physical sameWires target output)
    (measuredEncodedBasis physical sameWires (resultSetConstant target value seed))

/-- A named actual result path is independent of every original unmeasured value. -/
lemma namedResultPath_seed (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (first second : Data)
    (value : Fin (2 ^ width)) :
    namedResultPath (oracles := oracles) (services := services)
      physical sameWires target output first value =
      namedResultPath (oracles := oracles) (services := services)
        physical sameWires target output second value := by
  apply (resultBasisPath_eq_iff physical sameWires target output _ _).mpr
  intro index
  rw [encodedPhysicalBit, encodedPhysicalBit,
    resultSetConstant_get target distinct, resultSetConstant_get target distinct]

/-- Different original result bit vectors give different actual retained paths. -/
lemma namedResultPath_injective (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (seed : Data) :
    Function.Injective (namedResultPath (oracles := oracles) (services := services)
      physical sameWires target output seed) := by
  intro first second same
  have agree := (resultBasisPath_eq_iff physical sameWires target output _ _).mp same
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases present : bit < width
  · let index : Fin width := ⟨bit, present⟩
    have values := congrArg
      (fun value : Fin (physical.toQuantum.wire (target.bit index).wire).dimension =>
        decide (value.val = 1)) (agree index)
    have firstValue := encodedPhysicalBit_decide physical (target.bit index)
      (resultSetConstant target first seed)
    have secondValue := encodedPhysicalBit_decide physical (target.bit index)
      (resultSetConstant target second seed)
    rw [resultSetConstant_get target distinct] at firstValue secondValue
    exact firstValue.symm.trans (values.trans secondValue)
  · have beyond : width ≤ bit := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le first.isLt
      (Nat.pow_le_pow_right Nat.zero_lt_two beyond)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le second.isLt
        (Nat.pow_le_pow_right Nat.zero_lt_two beyond))]

private lemma measurementSequence_card (readouts : List (ZReadout ctx)) :
    Fintype.card ((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      readouts).Path) =
      (readouts.map fun readout => (ctx.quantumLayout.wire readout.wire).dimension.val).prod := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change Fintype.card (Fin (ctx.quantumLayout.wire head.wire).dimension ×
        (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
          (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
          tail).Path) = _
      rw [Fintype.card_prod, Fintype.card_fin, ih]
      rfl

/-- The actual ordered qubit-measurement paths have exactly the original result word cardinality. -/
lemma resultMeasurement_card (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2)) :
    Fintype.card ((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) = 2 ^ width := by
  rw [measurementSequence_card]
  have dimensions : (resultReadouts physical sameWires target output).map
      (fun readout => (ctx.quantumLayout.wire readout.wire).dimension.val) =
        List.ofFn (fun _ : Fin width => (2 : Nat)) := by
    rw [resultReadouts, List.map_ofFn]
    congr 1
    funext index
    change (ctx.quantumLayout.wire (resultWire physical sameWires (target.bit index))).dimension.val
      = 2
    rw [resultWire_qubit]
    rfl
  rw [dimensions, List.ofFn_const, List.prod_replicate]

/-- Every actual path is precisely one named original result word, with no missing outcomes. -/
lemma namedResultPath_bijective (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (seed : Data) :
    Function.Bijective (namedResultPath (oracles := oracles) (services := services)
      physical sameWires target output seed) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨namedResultPath_injective physical sameWires target distinct output seed, ?_⟩
  rw [Fintype.card_fin, resultMeasurement_card]

end

end QuantumAlg.EncodedBit.WindowLookup
