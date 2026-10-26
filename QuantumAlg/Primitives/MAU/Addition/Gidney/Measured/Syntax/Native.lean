/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Transport.Vector
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Transport
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record

/-!
# Actual native instruction action on complete encoded/reference superpositions

The actual compiler and full ordered physical-wire transport give the
same original-label native word action on every retained branch. No
measurement, stored phase assignment or additional state promise is used
[G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- A real native subword retains every dirty, control and external-reference amplitude. -/
lemma nativeWord_actual_coherent_reference (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (gates : List (EncodedBit.GateSpec encoding))
    (store : Store ctx) (measured : WordOutcomes physical sameWires [.native gates])
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (wordActualKraus (operations := operations) (services := services)
      physical sameWires output environment Reference [.native gates] store measured).applyVec
        (HilbertVector.reindex
          ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index))
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
              (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec)) =
      HilbertVector.reindex
        ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
          (Equiv.refl Reference.Index))
        (∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm
              (encoding.encode (EncodedBit.GateSpec.stepList gates (state index))),
                reference index)).vec) := by
  have actual := wordActualKraus_coherent_reference (operations := operations)
    (services := services) physical sameWires output environment
    (fun _ => 0) [.native gates] store measured (by exact ⟨True.intro, True.intro⟩)
    state reference amplitude
  simpa only [wordWeight, branchWeight, wordLabel, labelStep, mul_one] using actual

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
