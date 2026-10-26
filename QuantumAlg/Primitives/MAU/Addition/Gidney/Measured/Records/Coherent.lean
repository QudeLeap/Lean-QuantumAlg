/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Records
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Coherent

/-!
# Common-alpha coherent addition for every actual physical outcome record

Every actual outcome word supplies its own retained values. Physical write
order and real stored phase reads discharge the consistency condition, so
the law holds for every original caller Store. Dirty/control/reference
coherences are retained before any records are summed
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Execution Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Every actual physical record has the same scalar on the entire clean-helper input subspace. -/
lemma adderWord_actual_record_coherent (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) (store : Store ctx)
    (measured : WordOutcomes physical sameWires (layout.adderWord wide constant))
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    (wordActualKraus (operations := operations) (services := services)
      physical sameWires bank.output
      environment Reference (layout.adderWord wide constant) store measured).applyVec
        (HilbertVector.reindex
          ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
            (Equiv.refl Reference.Index))
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
              (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec)) =
      HilbertVector.reindex
        ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
          (Equiv.refl Reference.Index))
        (∑ index, (amplitude index * NormalizedVector.invSqrt2 ^ (width - 2)) •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm
              (encoding.encode (wordLabel (layout.adderWord wide constant) (state index))),
              reference index)).vec) := by
  exact adderWord_actual_coherent_reference layout wide constant physical sameWires bank.output
    environment (layout.retainedOutcome wide constant physical sameWires measured) store measured
    (adderWord_consistent layout wide constant physical sameWires bank store measured)
    state reference amplitude clean

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
