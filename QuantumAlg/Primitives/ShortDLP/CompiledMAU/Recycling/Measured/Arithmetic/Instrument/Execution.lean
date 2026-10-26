/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Mixed
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Execution.Word

/-!
# Actual retained execution blocks on the measured unit/reference carrier

The literal circuit interpreter supplies the original Store/history fibers
and chronological physical outcomes. Each such actual block is then related
to the independently specified controlled unit action. No measurement record
is discarded in this theorem [G25, main.tex:199-295,354-360].
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

/-- Actual arithmetic execution retains every original Store, path and full reference block. -/
lemma measuredArithmetic_execute_blocks (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
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
    (result : Store (Context base noQuantum m ell width) ×
      (ClassicalOracleModel.empty.HiddenState × (History ×
        (arithmetic base noQuantum m ell width wide modulus coefficient).Path))) :
    (((arithmetic base noQuantum m ell width wide modulus coefficient).execute environment
      Reference state).block result).matrix =
      let word := (Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
      let embedding := BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference)
      let source : HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference) :=
        UnitaryOperator.ofPerm (arithmeticReferencePermutation modulus coefficient Reference).symm
      ∑ original : Store (Context base noQuantum m ell width) ×
          (ClassicalOracleModel.empty.HiddenState × History),
        ∑ measured : WordOutcomes (Physical.qubits width)
            (context_wires base noQuantum m ell width) word,
          if Execution.Instrument.retainedRecord (wordActualRecord (oracles := .empty) (operations
            := BitWord.model)
              (services := .empty) (Physical.qubits width)
              (context_wires base noQuantum m ell width)
              (ventCell base noQuantum m ell width) word) original measured = result then
            (arithmeticAlpha width modulus coefficient *
              star (arithmeticAlpha width modulus coefficient)) •
              (embedding * (source * density original * source.conjTranspose) *
                embedding.conjTranspose)
          else 0 := by
  have actual := wordCircuit_block_matrix (Physical.qubits width)
    (context_wires base noQuantum m ell width) (ventCell base noQuantum m ell width) environment
    ((Physical.layout width).multiplicationWord wide modulus
      (coefficient : ZMod modulus.toNat).val
      ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
    Reference state result
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro measured _
  split_ifs
  · rw [encoded original]
    exact measuredArithmetic_record_mixed base noQuantum m ell width modulus wide positive
      coefficient environment original.1 measured Reference (density original)
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
