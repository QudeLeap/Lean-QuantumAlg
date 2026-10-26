/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail.Weight
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Transport.Vector

/-!
# Common-alpha measured addition with arbitrary dirty and external-reference coherences

Every consistently retained actual record has the same scalar on the entire
clean-helper input subspace. Dirty bits, the coherent control and reference
labels remain arbitrary inside the superposition. The actual chronological
Store-consistency premise is explicit; complete normalized instrument claims
are proved only after that premise and the clean-input isometry are discharged
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Execution Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The same scalar applies to every clean-helper original label and arbitrary reference ket. -/
lemma adderWord_branch_reference_ket (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (outcome : Fin (width - 2) → Fin 2)
    (state : Data) (clean : ∀ helper, (layout.clean helper).get state = false)
    {Reference : Register} (reference : Reference.Index) :
    (wordBranch physical environment Reference outcome (layout.adderWord wide constant)).applyVec
      (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
        (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      (NormalizedVector.invSqrt2 ^ (width - 2)) •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (wordLabel (layout.adderWord wide constant) state)), reference)).vec :=
  by
  rw [wordBranch_reference_ket, adderWord_weight layout wide constant state clean]

/-- Every actual consistent record has common alpha on all dirty/control/reference amplitudes. -/
lemma adderWord_actual_coherent_reference (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (outcome : Fin (width - 2) → Fin 2)
    (store : Store ctx)
    (measured : WordOutcomes physical sameWires (layout.adderWord wide constant))
    (consistent : WordConsistent (oracles := oracles) (operations := operations)
      (services := services) physical sameWires output outcome
        (layout.adderWord wide constant) store measured)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    (wordActualKraus (operations := operations) (services := services) physical sameWires output
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
  rw [wordActualKraus_coherent_reference physical sameWires output environment outcome
    (layout.adderWord wide constant) store measured consistent]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  rw [adderWord_weight layout wide constant (state index) (clean index)]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
