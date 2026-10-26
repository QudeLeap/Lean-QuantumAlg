/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Coherent
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Records
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Isometry.Norm
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Records.Norm
import all QuantumAlg.Components.Kets

/-!
# Actual MAC record norms from common alpha and independent clean-input isometry

Every real chronological record has the same scalar on the full original
clean-helper subspace. The independently proved full-label injectivity
preserves the output expansion norm, including arbitrary dirty, control,
flag and external-reference coherences [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Each actual record has its common norm factor on every original clean-helper expansion. -/
lemma accumulatePrefixWord_actual_record_norm (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) (count : Nat)
    (bounded : count ≤ width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) (store : Store ctx)
    (measured : WordOutcomes physical sameWires
      (layout.accumulatePrefixWord wide modulus constants count bounded))
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (distinct : Function.Injective (fun index => (state index, reference index)))
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    let input : HilbertVector (Register.prod physical.toQuantum.register Reference) :=
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec
    ‖(wordActualKraus (operations := operations) (services := services)
      physical sameWires bank.output environment Reference
        (layout.accumulatePrefixWord wide modulus constants count bounded)
        store measured).applyVec
          (HilbertVector.reindex
            ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
              (Equiv.refl Reference.Index)) input)‖ =
      ‖(accumulatePrefixAlpha constants count bounded : ℂ)‖ * ‖input‖ := by
  dsimp only
  have action := accumulatePrefixWord_recordCoherent (operations := operations)
    (services := services)
    layout wide modulus constants count bounded physical sameWires bank environment
  have actual := action store measured Reference Index state reference amplitude clean
  change ‖(wordActualKraus (operations := operations) (services := services)
    physical sameWires bank.output environment Reference
      (layout.accumulatePrefixWord wide modulus constants count bounded)
      store measured).applyVec (encodedExpansion physical sameWires state reference amplitude)‖ = _
  rw [actual, encodedExpansion, HilbertVector.norm_reindex]
  let scalar : ℂ := accumulatePrefixAlpha constants count bounded
  have factored :
      (∑ index, (amplitude index * scalar) •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (wordLabel
              (layout.accumulatePrefixWord wide modulus constants count bounded) (state index))),
              reference index)).vec) =
      scalar • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (wordLabel
              (layout.accumulatePrefixWord wide modulus constants count bounded) (state index))),
              reference index)).vec := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [smul_smul]
    congr 1
    exact mul_comm _ _
  rw [factored, norm_smul,
    accumulatePrefixWord_expansion_norm layout wide modulus constants count bounded
      physical state reference amplitude distinct clean]

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
