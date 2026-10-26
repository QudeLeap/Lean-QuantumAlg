/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Transport
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch

/-!
# Actual chronological retained vectors beside an arbitrary external reference

The full physical-wire transport acts on the real chronological operator.
Each phase read is certified against its actual intermediate Store before
the native retained-word law is applied. No record is summed or normalized
by this identity [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

private lemma reindex_applyVec {Source Target : Register}
    (coordinates : Source.Index ≃ Target.Index) (operator : HilbertOperator Source)
    (vector : HilbertVector Source) :
    HilbertOperator.applyVec (R := Target) (operator.submatrix coordinates.symm coordinates.symm)
        (HilbertVector.reindex coordinates vector) =
      HilbertVector.reindex coordinates (operator.applyVec vector) := by
  apply WithLp.ofLp_injective
  funext output
  simp only [HilbertOperator.applyVec_apply, HilbertVector.reindex_apply]
  change (∑ input : Target.Index, operator (coordinates.symm output)
      (coordinates.symm input) * vector (coordinates.symm input)) =
    ∑ input : Source.Index, operator (coordinates.symm output) input * vector input
  exact Equiv.sum_comp coordinates.symm
    (fun input => operator (coordinates.symm output) input * vector input)

/-- Every actual consistently retained record preserves all original dirty/reference coherences. -/
lemma wordActualKraus_coherent_reference (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (outcome : Fin records → Fin 2)
    (word : List (Instruction encoding records)) (store : Store ctx)
    (measured : WordOutcomes physical sameWires word)
    (consistent : WordConsistent (oracles := oracles) (operations := operations)
      (services := services) physical sameWires output outcome word store measured)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (wordActualKraus (operations := operations) (services := services) physical sameWires output
      environment Reference word store measured).applyVec
        (HilbertVector.reindex
          ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index))
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
              (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec)) =
      HilbertVector.reindex
        ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
          (Equiv.refl Reference.Index))
        (∑ index, (amplitude index * wordWeight outcome word (state index)) •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (wordLabel word (state index))),
              reference index)).vec) := by
  rw [wordActualKraus_eq_branch physical sameWires output environment Reference outcome word
    store measured consistent, reindex_applyVec, wordBranch_coherent_reference]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
