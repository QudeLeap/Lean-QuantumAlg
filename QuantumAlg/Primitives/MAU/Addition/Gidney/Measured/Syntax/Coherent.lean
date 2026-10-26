/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Append
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Composition
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Native
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Execution
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch

/-!
# Composition of actual per-record common-alpha actions at the real intermediate Store

The law quantifies every original Store and every real physical outcome,
with complete encoded/reference superpositions. Concatenation retains the
actual Store written by its first word and separately checks the second
word's input promise. No normalized outcome distribution or free phase
correction is assumed [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Full encoded/reference expansion transported along the complete ordered physical-wire map. -/
def encodedExpansion (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertVector (Register.prod ctx.register Reference) :=
  HilbertVector.reindex
    ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
      (Equiv.refl Reference.Index))
    (∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
        (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec)

/-- The actual retained native product has one common scalar on the entire stated input subspace. -/
def RecordCoherent (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (word : List (Instruction encoding records))
    (α : ℂ) (admitted : Data → Prop) : Prop :=
  ∀ (store : Store ctx) (measured : WordOutcomes physical sameWires word)
    (Reference : Register) (Index : Type) [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ),
    (∀ index, admitted (state index)) →
    (wordActualKraus (operations := operations) (services := services)
      physical sameWires output environment Reference word store measured).applyVec
        (encodedExpansion physical sameWires state reference amplitude) =
      encodedExpansion physical sameWires (fun index => wordLabel word (state index)) reference
        (fun index => amplitude index * α)

/-- The actual chronological label append preserves a promise preserved by both source subwords. -/
lemma wordLabel_preserves_append (admitted : Data → Prop)
    (first second : List (Instruction encoding records))
    (firstPreserved : ∀ state, admitted state → admitted (wordLabel first state))
    (secondPreserved : ∀ state, admitted state → admitted (wordLabel second state)) :
    ∀ state, admitted state → admitted (wordLabel (first ++ second) state) := by
  intro state accepted
  rw [wordLabel_append]
  exact secondPreserved _ (firstPreserved state accepted)

/-- Actual concatenation multiplies the two proved common scalars without Store loss. -/
lemma recordCoherent_append (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) (environment : oracles.Interpretation)
    (first second : List (Instruction encoding records)) (firstAlpha secondAlpha : ℂ)
    (firstAdmitted secondAdmitted : Data → Prop)
    (firstAction : RecordCoherent (operations := operations) (services := services)
      physical sameWires output environment first firstAlpha firstAdmitted)
    (secondAction : RecordCoherent (operations := operations) (services := services)
      physical sameWires output environment second secondAlpha secondAdmitted)
    (preserved : ∀ state, firstAdmitted state → secondAdmitted (wordLabel first state)) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires output environment (first ++ second) (firstAlpha * secondAlpha)
        firstAdmitted := by
  intro store measured Reference Index _ state reference amplitude admitted
  let parts := splitOutcomes physical sameWires first second measured
  have actualOutcome := appendOutcomes_splitOutcomes physical sameWires first second measured
  rw [← actualOutcome, wordActualKraus_append, HilbertOperator.mul_applyVec]
  rw [firstAction store parts.1 Reference Index state reference amplitude admitted]
  rw [secondAction _ parts.2 Reference Index (fun index => wordLabel first (state index))
    reference (fun index => amplitude index * firstAlpha)
    (fun index => preserved (state index) (admitted index))]
  simp only [encodedExpansion, wordLabel_append, mul_assoc]

/-- Actual identity retains every complete encoded/reference state with scalar one. -/
lemma recordCoherent_nil (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) (environment : oracles.Interpretation)
    (admitted : Data → Prop) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires output environment [] 1 admitted := by
  intro store measured Reference Index _ state reference amplitude _admitted
  simp only [wordActualKraus, HilbertOperator.one_applyVec, wordLabel, mul_one]

/-- An actual native instruction has scalar one on every admitted full encoded/reference family. -/
lemma recordCoherent_native (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) (environment : oracles.Interpretation)
    (gates : List (EncodedBit.GateSpec encoding)) (admitted : Data → Prop) :
    RecordCoherent (operations := operations) (services := services)
      physical sameWires output environment [.native gates] 1 admitted := by
  intro store measured Reference Index _ state reference amplitude _admitted
  simpa only [encodedExpansion, wordLabel, labelStep, mul_one] using
    nativeWord_actual_coherent_reference (operations := operations) (services := services)
      physical sameWires output environment gates store measured state reference amplitude

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
