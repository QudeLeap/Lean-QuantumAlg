/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Remap
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Execution
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Normalization
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record.Readout

/-!
# Actual arithmetic observation after merging only unobserved record fibers

All retained exponent cells and the entire quantum/reference density matrix
remain in the observation. The actual chronological arithmetic outcomes and
overwritten vent-cell fibers are summed using their proved weights. The
result is the independently specified controlled unit action, with no free
instrument callback [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

omit [NeZero modulus.toNat] in
/-- Every actual arithmetic record preserves all original retained exponent outputs. -/
lemma arithmetic_record_resultRead (wide : 2 ≤ width) (coefficient : (ZMod modulus.toNat)ˣ)
    (store : Store (Context base noQuantum m ell width))
    (measured : WordOutcomes (Physical.qubits width) (context_wires base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)) :
    (resultRead base noQuantum m ell width).eval
      (wordActualRecord (oracles := .empty) (operations := BitWord.model) (services := .empty)
        (Physical.qubits width) (context_wires base noQuantum m ell width)
        (ventCell base noQuantum m ell width)
        ((Physical.layout width).multiplicationWord wide modulus
          (coefficient : ZMod modulus.toNat).val
          ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val) store measured).1 =
      (resultRead base noQuantum m ell width).eval store := by
  apply congrArg CShape.Value.fixedVector
  funext index
  exact wordActualRecord_read_other (Physical.qubits width)
    (context_wires base noQuantum m ell width) (ventCell base noQuantum m ell width)
    (resultCell base noQuantum m ell width index).toCStorageRef
    (fun vent => vent_result_distinct base noQuantum m ell width vent index) _ store measured

/-- Merging the actual unobserved arithmetic records keeps the complete retained output block. -/
lemma measuredArithmetic_observed_blocks (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (density : Store (Context base noQuantum m ell width) ×
      (ClassicalOracleModel.empty.HiddenState × History) →
        HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference))
    (encoded : ∀ original,
      (state.block original).matrix =
        BasisEmbedding.matrix
            (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) *
          density original * (BasisEmbedding.matrix
            (arithmeticJointEmbedding base noQuantum m ell width modulus Reference)).conjTranspose)
    (observed : CShape.Value (.fixedVector (resultBits m ell) (.finite 2))) :
    ((((arithmetic base noQuantum m ell width wide modulus coefficient).execute environment
      Reference state).mapClassical
        (fun entry => (resultRead base noQuantum m ell width).eval entry.1)).block
          observed).matrix =
      let embedding := BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference)
      let source : HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference) :=
        UnitaryOperator.ofPerm (arithmeticReferencePermutation modulus coefficient Reference).symm
      ∑ original : Store (Context base noQuantum m ell width) ×
          (ClassicalOracleModel.empty.HiddenState × History),
        if (resultRead base noQuantum m ell width).eval original.1 = observed then
          embedding * (source * density original * source.conjTranspose) * embedding.conjTranspose
        else 0 := by
  let embedding := BasisEmbedding.matrix
    (arithmeticJointEmbedding base noQuantum m ell width modulus Reference)
  let source : HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference) :=
    UnitaryOperator.ofPerm (arithmeticReferencePermutation modulus coefficient Reference).symm
  have actual := Execution.Instrument.mapClassical_retained_matrix
    ((arithmetic base noQuantum m ell width wide modulus coefficient).execute environment
      Reference state)
    (Execution.Instrument.retainedRecord (wordActualRecord (oracles := .empty) (operations :=
      BitWord.model)
      (services := .empty) (Physical.qubits width) (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)))
    (fun original _ => (arithmeticAlpha width modulus coefficient *
      star (arithmeticAlpha width modulus coefficient)) •
        (embedding * (source * density original * source.conjTranspose) * embedding.conjTranspose))
    (by
      intro result
      have proved := measuredArithmetic_execute_blocks base noQuantum m ell width modulus wide
        positive coefficient environment Reference state density encoded result
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      split_ifs with first second third
      · rfl
      · exact False.elim (second first)
      · exact False.elim (first third)
      · rfl)
    (fun entry => (resultRead base noQuantum m ell width).eval entry.1) observed
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  have preserved (measured : WordOutcomes (Physical.qubits width)
      (context_wires base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)) :=
    arithmetic_record_resultRead base noQuantum m ell width modulus wide coefficient
      original.1 measured
  simp_rw [Execution.Instrument.retainedRecord, preserved]
  by_cases selected : (resultRead base noQuantum m ell width).eval original.1 = observed
  · simp only [if_pos selected]
    rw [← Finset.sum_smul, arithmetic_record_weights_sum, one_smul]
  · simp only [if_neg selected, Finset.sum_const_zero]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
