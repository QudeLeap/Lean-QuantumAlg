/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Reset
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard.Projection

/-!
# Exact encoded columns in each original physical result-measurement fiber

The mathematical label update below names all result outcomes by toggling
only the original result bits. It grants no executable overwrite operation.
Every complement value remains original. Actual stored-outcome correction
maps each named column to the same original label with its result word zero.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The original physical value of a named encoded bit. -/
lemma encodedPhysicalBit (physical : QubitLayout encoding.width) (bit : EncodedBit encoding)
    (state : Data) :
    physical.basisEquiv.symm (encoding.encode state) bit.wire =
      Fin.cast rfl (finTwoEquiv.symm (bit.get state)) :=
  bit.targetBasisEquiv_first state

/-- A mathematical label for a desired result value, keeping every original other coordinate. -/
def resultSetConstant (target : Word encoding width) (value : Fin (2 ^ width)) (state : Data) :
    Data :=
  Word.xorConstantStep target
    ⟨Nat.ofBits (fun index => (target.bit index).get state ^^ value.val.testBit index.val),
      Nat.ofBits_lt_two_pow _⟩ state

/-- Every named original result bit has exactly its requested outcome value. -/
lemma resultSetConstant_get (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (value : Fin (2 ^ width)) (state : Data) (index : Fin width) :
    (target.bit index).get (resultSetConstant target value state) =
      value.val.testBit index.val := by
  rw [resultSetConstant, Word.xorConstantStep_get_target _ _ _
    (fun other different same => different (distinct same)),
    Nat.testBit_ofBits_lt _ index.val index.isLt]
  cases original : (target.bit index).get state <;>
    cases selected : value.val.testBit index.val <;> rfl

/-- Naming a result outcome preserves every original outside readout. -/
lemma resultSetConstant_observed (target : Word encoding width)
    (value : Fin (2 ^ width)) (observed : EncodedBit encoding)
    (outside : ∀ index, (target.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (resultSetConstant target value state) = observed.get state :=
  Word.xorConstantStep_get_observed_of_target_ne target _ observed outside state

/-- Actual constant-XOR label action preserves the complete original physical complement. -/
lemma wordXor_complement (physical : QubitLayout encoding.width) (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (constant : Fin (2 ^ width)) (state : Data) :
    physical.toQuantum.restrictComplementBasis (Finset.univ.map (wordPosition target distinct))
      (physical.basisEquiv.symm (encoding.encode (Word.xorConstantStep target constant state))) =
    physical.toQuantum.restrictComplementBasis (Finset.univ.map (wordPosition target distinct))
      (physical.basisEquiv.symm (encoding.encode state)) := by
  unfold Word.xorConstantStep
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
    (project := fun input : Data => physical.toQuantum.restrictComplementBasis
      (Finset.univ.map (wordPosition target distinct))
      (physical.basisEquiv.symm (encoding.encode input)))
  intro gate member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  intro input
  funext wire
  have outside : wire.val ≠ (target.bit index).wire := by
    intro same
    exact (Finset.mem_compl.mp wire.property)
      (Finset.mem_map.mpr ⟨index, Finset.mem_univ _, same.symm⟩)
  exact congrFun (congrArg Prod.snd ((target.bit index).targetBasisEquiv_flip input))
    ⟨wire.val, outside⟩

/-- Every named outcome has precisely the same original full physical complement. -/
lemma resultSetConstant_complement (physical : QubitLayout encoding.width)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (value : Fin (2 ^ width)) (state : Data) :
    physical.toQuantum.restrictComplementBasis (Finset.univ.map (wordPosition target distinct))
      (physical.basisEquiv.symm (encoding.encode (resultSetConstant target value state))) =
    physical.toQuantum.restrictComplementBasis (Finset.univ.map (wordPosition target distinct))
      (physical.basisEquiv.symm (encoding.encode state)) :=
  wordXor_complement physical target distinct _ state

/-- The actual stored-mask selected X correction preserves the complete original complement. -/
lemma measuredWordResetStep_complement (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx) (state : Data) :
    physical.toQuantum.restrictComplementBasis (Finset.univ.map (wordPosition target distinct))
      (physical.basisEquiv.symm (encoding.encode (measuredWordResetStep (oracles := oracles)
        (services := services) physical sameWires target output mask store state))) =
    physical.toQuantum.restrictComplementBasis (Finset.univ.map (wordPosition target distinct))
      (physical.basisEquiv.symm (encoding.encode state)) :=
  wordXor_complement physical target distinct _ state

/-- Every actual measured outcome resets to the same full original label with a zero result word. -/
lemma measuredWordResetStep_set_eq_zero (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx)
    (value : Fin (2 ^ width)) (state : Data) :
    measuredWordResetStep (oracles := oracles) (services := services)
      physical sameWires target output mask store (resultSetConstant target value state) =
        resultSetConstant target 0 state := by
  apply encoding.encode_injective
  apply physical.basisEquiv.symm.injective
  apply wordBasis_eq_of_coordinates physical target distinct
  · intro index
    rw [encodedPhysicalBit, encodedPhysicalBit,
      measuredWordResetStep_zero physical sameWires target distinct output outputDistinct,
      resultSetConstant_get target distinct]
    simp
  · exact (measuredWordResetStep_complement (oracles := oracles) (services := services)
      physical sameWires target distinct output mask store _).trans
        ((resultSetConstant_complement physical target distinct value state).trans
          (resultSetConstant_complement physical target distinct 0 state).symm)

end

end QuantumAlg.EncodedBit.WindowLookup
