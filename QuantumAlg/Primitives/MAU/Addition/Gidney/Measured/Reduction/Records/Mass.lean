/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Records.Norm
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Records.Finite

/-!
# Exact actual modular-reduction record magnitudes and complete normalization

The sum ranges over all chronological physical outcome words of the same
compiled reduction. Reusing storage does not identify distinct histories.
Common alpha, independent clean-input isometry and the exact actual outcome
cardinality establish the complete norm sum, including literal zero-offset
identity [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open Execution Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Every real reduction record has its exact common mass, and all real record masses sum to one. -/
lemma modularWord_actual_record_mass (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) (store : Store ctx)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (distinct : Function.Injective (fun index => (state index, reference index)))
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    let input : HilbertVector (Register.prod physical.toQuantum.register Reference) :=
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec
    let branch := fun measured :
        WordOutcomes physical sameWires (layout.modularWord wide modulus constant) =>
      (wordActualKraus (operations := operations) (services := services)
        physical sameWires bank.output environment Reference
          (layout.modularWord wide modulus constant)
          store measured).applyVec
            (HilbertVector.reindex
              ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
                (Equiv.refl Reference.Index)) input)
    (∀ measured, ‖branch measured‖ ^ 2 =
      (if constant = 0 then 1 else (2 : ℝ)⁻¹ ^ (2 * (width - 2))) * ‖input‖ ^ 2) ∧
      (∑ measured, ‖branch measured‖ ^ 2) = ‖input‖ ^ 2 := by
  dsimp only
  have mass
      (measured : WordOutcomes physical sameWires (layout.modularWord wide modulus constant)) :=
    congrArg (fun value : ℝ => value ^ 2)
      (modularWord_actual_record_norm (operations := operations) (services := services)
        layout wide modulus constant physical sameWires bank environment store measured
          state reference amplitude distinct clean)
  simp only [mul_pow, reduction_commonAlpha_norm_sq] at mass
  refine ⟨mass, ?_⟩
  simp_rw [mass]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    modularWord_outcomes_card_if layout wide modulus constant physical sameWires]
  by_cases zero : constant = 0
  · simp only [if_pos zero, Nat.cast_one, one_mul]
  · rw [if_neg zero, if_neg zero, Nat.cast_pow, Nat.cast_ofNat,
      ← mul_assoc, ← mul_pow]
    norm_num

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
