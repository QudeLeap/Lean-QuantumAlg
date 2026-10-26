/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Records
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Records
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Resources.Measurements
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources.Coordinates

/-!
# Exact actual multiplier measurement recurrence and its closed width bound

The count follows the same original row compiler, with two original vent
passes per nonzero static offset. Literal zero rows and the native exchange
emit no measurement. Reusing the record bank does not remove events
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The actual chronological prefix has exactly the vent recurrence of its literal static bank. -/
lemma accumulatePrefixWord_measurementCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) (count : Nat)
    (bounded : count ≤ width) :
    wordMeasurementCount (layout.accumulatePrefixWord wide modulus constants count bounded) =
      accumulatePrefixVents constants count bounded := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [accumulatePrefixWord, wordMeasurementCount_append, ih (by omega),
        Addition.Gidney.Measured.Reduction.Layout.modularWord_measurementCount,
        accumulatePrefixVents]

/-- Exactly the measured events emitted by the forward and separate explicit inverse MAC words. -/
lemma multiplicationWord_measurementCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) :
    wordMeasurementCount (layout.multiplicationWord wide modulus coefficient inverseCoefficient) =
      multiplicationVents modulus coefficient inverseCoefficient := by
  rw [multiplicationWord, wordMeasurementCount_append, wordMeasurementCount_append]
  have native : wordMeasurementCount (records := width - 2) [.native layout.swapWordGates] = 0 :=
    rfl
  rw [native, Nat.add_zero]
  change wordMeasurementCount
      (layout.accumulatePrefixWord wide modulus (forwardConstant modulus coefficient)
        width le_rfl) +
    wordMeasurementCount
      (layout.accumulatePrefixWord wide modulus (inverseConstant modulus inverseCoefficient)
        width le_rfl) = _
  rw [accumulatePrefixWord_measurementCount, accumulatePrefixWord_measurementCount,
    multiplicationVents]

private lemma accumulatePrefixVents_bound (constants : Fin width → BitVec width)
    (count : Nat) (bounded : count ≤ width) :
    accumulatePrefixVents constants count bounded ≤ count * (2 * (width - 2)) := by
  induction count with
  | zero => simp only [accumulatePrefixVents, Nat.zero_mul, Nat.le_refl]
  | succ count ih =>
      rw [accumulatePrefixVents]
      have earlier := ih (by omega)
      calc
        _ ≤ count * (2 * (width - 2)) + 2 * (width - 2) :=
          Nat.add_le_add earlier (by split <;> omega)
        _ = (count + 1) * (2 * (width - 2)) := (Nat.succ_mul _ _).symm

/-- The actual source-selected event count satisfies the independently stated width bound. -/
lemma multiplicationWord_measurement_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) :
    wordMeasurementCount (layout.multiplicationWord wide modulus coefficient inverseCoefficient) ≤
      4 * width * (width - 2) := by
  rw [multiplicationWord_measurementCount, multiplicationVents]
  have forward := accumulatePrefixVents_bound (forwardConstant modulus coefficient) width le_rfl
  have inverse := accumulatePrefixVents_bound (inverseConstant modulus inverseCoefficient)
    width le_rfl
  nlinarith

/-- Every actual complete multiplier path retains exactly those actual emitted measurements. -/
lemma multiplicationCircuit_measurementCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (path : (layout.multiplicationCircuit (oracles := oracles) (operations := operations)
      (services := services) wide modulus coefficient inverseCoefficient
        physical sameWires output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
      (.measurement (2 : ℕ+))
      ((layout.multiplicationCircuit wide modulus coefficient inverseCoefficient
        physical sameWires output).resourcePool path) =
          multiplicationVents modulus coefficient inverseCoefficient := by
  change (wordCircuit (oracles := oracles) (operations := operations) (services := services)
    physical sameWires output
      (layout.multiplicationWord wide modulus coefficient inverseCoefficient)).Path at path
  exact (wordCircuit_coordinates physical sameWires output _ path).2.1.trans
    (multiplicationWord_measurementCount layout wide modulus coefficient inverseCoefficient)

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
