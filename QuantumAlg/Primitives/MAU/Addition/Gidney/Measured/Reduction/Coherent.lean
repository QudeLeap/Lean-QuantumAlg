/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Coherent
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Records.Coherent
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Frame
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program

/-!
# Actual common-alpha coherent modular reduction with reused physical record cells

Each measured addition consumes its own chronological outcomes and actual
intermediate Store. Both native comparisons and the paid middle toggle have
scalar one. The two measured additions have the same accepted scalar, and
their helper promises are discharged at their actual inputs. All original
dirty/control/reference amplitudes remain coherent before records are summed
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Execution EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Only the two original adder helpers are initialized for the common-alpha record law. -/
def helpersClean (layout : Layout encoding width) (state : Data) : Prop :=
  ∀ helper, (layout.clean helper).get state = false

/-- The actual reused measured adder has one common scalar on every original full-label family. -/
lemma reductionAdder_recordCoherent (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires bank.output environment (layout.adderLayout.adderWord wide constant)
        (NormalizedVector.invSqrt2 ^ (width - 2)) layout.helpersClean := by
  intro store measured Reference Index _ state reference amplitude clean
  exact Measured.Layout.adderWord_actual_record_coherent layout.adderLayout wide constant
    physical sameWires bank environment store measured state reference amplitude clean

private lemma comparison_preserves_helpers (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) :
    ∀ state, layout.helpersClean state →
      layout.helpersClean (wordLabel (records := width - 2)
        [.native (layout.comparisonGates wide threshold)] state) := by
  intro state clean
  exact (frameInvariant_comparison (frameInvariant_initial layout state clean) wide threshold).clean

private lemma adder_preserves_helpers (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    ∀ state, layout.helpersClean state →
      layout.helpersClean (wordLabel (layout.adderLayout.adderWord wide constant) state) := by
  intro state clean
  exact reductionAdder_clean layout wide constant state clean

private lemma toggle_preserves_helpers (layout : Layout encoding width) :
    ∀ state, layout.helpersClean state →
      layout.helpersClean
        (wordLabel (records := width - 2) [.native layout.toggleFlagGates] state) := by
  intro state clean
  exact (frameInvariant_toggle (frameInvariant_initial layout state clean)).clean

/-- Every actual nonzero reduction record has one scalar on all dirty/reference amplitudes. -/
lemma modularWord_recordCoherent_nonzero (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (nonzero : constant ≠ 0)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires bank.output environment (layout.modularWord wide modulus constant)
        (NormalizedVector.invSqrt2 ^ (2 * (width - 2))) layout.helpersClean := by
  let first : List (Instruction encoding (width - 2)) :=
    [.native (layout.comparisonGates wide (modulus - constant))]
  let second := layout.adderLayout.adderWord wide constant
  let middle : List (Instruction encoding (width - 2)) := [.native layout.toggleFlagGates]
  let fourth := layout.adderLayout.adderWord wide (constant - modulus)
  let final : List (Instruction encoding (width - 2)) :=
    [.native (layout.comparisonGates wide constant)]
  let α : ℂ := NormalizedVector.invSqrt2 ^ (width - 2)
  have firstAction := recordCoherent_native (operations := operations) (services := services)
    physical sameWires bank.output environment
    (layout.comparisonGates wide (modulus - constant)) layout.helpersClean
  have secondAction := reductionAdder_recordCoherent (operations := operations)
    (services := services) layout wide constant physical sameWires bank environment
  have middleAction := recordCoherent_native (operations := operations) (services := services)
    physical sameWires bank.output environment layout.toggleFlagGates layout.helpersClean
  have fourthAction := reductionAdder_recordCoherent (operations := operations)
    (services := services) layout wide (constant - modulus) physical sameWires bank environment
  have finalAction := recordCoherent_native (operations := operations) (services := services)
    physical sameWires bank.output environment (layout.comparisonGates wide constant)
      layout.helpersClean
  have firstPreserved := comparison_preserves_helpers layout wide (modulus - constant)
  have secondPreserved := adder_preserves_helpers layout wide constant
  have middlePreserved := toggle_preserves_helpers layout
  have fourthPreserved := adder_preserves_helpers layout wide (constant - modulus)
  have pairAction := recordCoherent_append physical sameWires bank.output environment first second
    1 α layout.helpersClean layout.helpersClean firstAction secondAction firstPreserved
  have prefixPreserved := wordLabel_preserves_append layout.helpersClean first second
    firstPreserved secondPreserved
  have throughMiddle := recordCoherent_append physical sameWires bank.output environment
    (first ++ second) middle (1 * α) 1 layout.helpersClean layout.helpersClean
      pairAction middleAction prefixPreserved
  have middleFrame := wordLabel_preserves_append layout.helpersClean (first ++ second) middle
    prefixPreserved middlePreserved
  have throughFourth := recordCoherent_append physical sameWires bank.output environment
    (first ++ second ++ middle) fourth ((1 * α) * 1) α
      layout.helpersClean layout.helpersClean throughMiddle fourthAction middleFrame
  have fourthFrame := wordLabel_preserves_append layout.helpersClean
    (first ++ second ++ middle) fourth middleFrame fourthPreserved
  have complete := recordCoherent_append physical sameWires bank.output environment
    (first ++ second ++ middle ++ fourth) final (((1 * α) * 1) * α) 1
      layout.helpersClean layout.helpersClean throughFourth finalAction fourthFrame
  rw [modularWord, if_neg nonzero, Nat.mul_comm 2 (width - 2), pow_mul]
  simpa only [one_mul, mul_one, pow_two] using complete

/-- The same actual record law includes literal zero-offset identity without extra measurements. -/
lemma modularWord_recordCoherent (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires bank.output environment (layout.modularWord wide modulus constant)
        (if constant = 0 then 1 else NormalizedVector.invSqrt2 ^ (2 * (width - 2)))
          layout.helpersClean := by
  by_cases zero : constant = 0
  · rw [modularWord, if_pos zero, if_pos zero]
    exact recordCoherent_nil physical sameWires bank.output environment layout.helpersClean
  · rw [if_neg zero]
    exact modularWord_recordCoherent_nonzero layout wide modulus constant zero
      physical sameWires bank environment

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
