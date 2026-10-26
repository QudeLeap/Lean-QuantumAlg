/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Coherent
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Isometry.Norm
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Records.Norm
import all QuantumAlg.Components.Kets

/-!
# Actual reduction record norms from common alpha and independent clean-input isometry

Every real chronological record has the same scalar on the full original
clean-helper subspace. The independently proved full-label injectivity
preserves the output expansion norm, including arbitrary dirty, control,
flag and external-reference coherences [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Execution Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The actual program branch selects exactly the squared magnitude of its common scalar. -/
lemma reduction_commonAlpha_norm_sq (constant : BitVec width) :
    ‖(if constant = 0 then 1 else
      NormalizedVector.invSqrt2 ^ (2 * (width - 2)) : ℂ)‖ ^ 2 =
        if constant = 0 then 1 else (2 : ℝ)⁻¹ ^ (2 * (width - 2)) := by
  by_cases zero : constant = 0
  · simp only [if_pos zero, norm_one, one_pow]
  · rw [if_neg zero, if_neg zero]
    exact Measured.Layout.adder_commonAlpha_norm_sq _

/-- Each actual record has its common norm factor on every original clean-helper expansion. -/
lemma modularWord_actual_record_norm (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) (store : Store ctx)
    (measured : WordOutcomes physical sameWires (layout.modularWord wide modulus constant))
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
        (layout.modularWord wide modulus constant)
        store measured).applyVec
          (HilbertVector.reindex
            ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
              (Equiv.refl Reference.Index)) input)‖ =
      ‖(if constant = 0 then 1 else
        NormalizedVector.invSqrt2 ^ (2 * (width - 2)) : ℂ)‖ * ‖input‖ := by
  dsimp only
  have action := modularWord_recordCoherent (operations := operations) (services := services)
    layout wide modulus constant physical sameWires bank environment
  have actual := action store measured Reference Index state reference amplitude clean
  change ‖(wordActualKraus (operations := operations) (services := services)
    physical sameWires bank.output environment Reference (layout.modularWord wide modulus constant)
      store measured).applyVec (encodedExpansion physical sameWires state reference amplitude)‖ = _
  rw [actual, encodedExpansion, HilbertVector.norm_reindex]
  let scalar : ℂ := if constant = 0 then 1 else NormalizedVector.invSqrt2 ^ (2 * (width - 2))
  have factored :
      (∑ index, (amplitude index * scalar) •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (wordLabel (layout.modularWord wide modulus constant) (state index))),
              reference index)).vec) =
      scalar • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (wordLabel (layout.modularWord wide modulus constant) (state index))),
              reference index)).vec := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [smul_smul]
    congr 1
    exact mul_comm _ _
  rw [factored, norm_smul,
    modularWord_expansion_norm layout wide modulus constant physical state reference amplitude
      distinct clean]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
