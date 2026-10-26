/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Coherent
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Semantics
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch

/-!
# Actual multiplier common scalar on every complete original record and reference family

Forward MAC, the paid native controlled exchange, and the separately emitted
inverse MAC compose at their actual intermediate Stores. Their helper-clean
promises follow from the actual preceding stages. All original source,
target, dirty, control, flag and reference amplitudes share one scalar for
every physical outcome word [G25, main.tex:199-295,271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The native middle exchange physically retains the original helper-clean input promise. -/
lemma swapWord_preserves_helpers (layout : Layout encoding width) :
    ∀ state, layout.helpersClean state → layout.helpersClean
      (wordLabel (records := width - 2) [.native layout.swapWordGates] state) := by
  intro state clean helper
  exact (swapWordGates_clean layout state helper).trans (clean helper)

/-- Every actual complete multiplier record has one scalar on arbitrary dirty/reference data. -/
lemma multiplicationWord_recordCoherent (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires bank.output environment
        (layout.multiplicationWord wide modulus coefficient inverseCoefficient)
        (accumulatePrefixAlpha (forwardConstant modulus coefficient) width le_rfl *
          accumulatePrefixAlpha (inverseConstant modulus inverseCoefficient) width le_rfl)
        layout.helpersClean := by
  let first := layout.forwardMACWord wide modulus coefficient
  let middle : List (Instruction encoding (width - 2)) := [.native layout.swapWordGates]
  let final := layout.inverseMACWord wide modulus inverseCoefficient
  let firstAlpha := accumulatePrefixAlpha (forwardConstant modulus coefficient) width le_rfl
  let finalAlpha := accumulatePrefixAlpha (inverseConstant modulus inverseCoefficient) width le_rfl
  have firstAction := forwardMACWord_recordCoherent (operations := operations)
    (services := services) layout wide modulus coefficient physical sameWires bank environment
  have middleAction := recordCoherent_native (operations := operations) (services := services)
    physical sameWires bank.output environment layout.swapWordGates layout.helpersClean
  have finalAction := inverseMACWord_recordCoherent (operations := operations)
    (services := services) layout wide modulus inverseCoefficient
      physical sameWires bank environment
  have firstPreserved : ∀ state, layout.helpersClean state →
      layout.helpersClean (wordLabel first state) := by
    intro state clean
    exact (accumulatePrefixWord_frame layout wide modulus _ width le_rfl state clean).clean
  have middlePreserved := swapWord_preserves_helpers layout
  have pairAction := recordCoherent_append physical sameWires bank.output environment
    first middle firstAlpha 1 layout.helpersClean layout.helpersClean
      firstAction middleAction firstPreserved
  have pairPreserved := wordLabel_preserves_append layout.helpersClean first middle
    firstPreserved middlePreserved
  have complete := recordCoherent_append physical sameWires bank.output environment
    (first ++ middle) final (firstAlpha * 1) finalAlpha layout.helpersClean layout.helpersClean
      pairAction finalAction pairPreserved
  simpa only [multiplicationWord, first, middle, final, firstAlpha, finalAlpha, mul_one]
    using complete

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
