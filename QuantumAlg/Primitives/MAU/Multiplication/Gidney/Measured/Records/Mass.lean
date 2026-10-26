/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Records.Norm
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Records
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Records.Norm

/-!
# Exact actual multiplier record magnitudes and complete normalization

The sum ranges over all chronological physical outcome words of the same
compiled multiplier. Reusing storage does not identify distinct histories.
Common alpha, independent clean-input isometry and the exact actual outcome
cardinality establish the complete norm sum, including any statically omitted zero-offset
rows [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Execution Addition.Gidney.Measured Addition.Gidney.Measured.Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Each actual multiplier record has its common mass, and all actual record masses sum to one. -/
lemma multiplicationWord_actual_record_mass (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat)
    (physical : QubitLayout encoding.width)
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
        WordOutcomes physical sameWires
          (layout.multiplicationWord wide modulus coefficient inverseCoefficient) =>
      (wordActualKraus (operations := operations) (services := services)
        physical sameWires bank.output environment Reference
          (layout.multiplicationWord wide modulus coefficient inverseCoefficient)
          store measured).applyVec
            (HilbertVector.reindex
              ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
                (Equiv.refl Reference.Index)) input)
    (∀ measured, ‖branch measured‖ ^ 2 =
      ((2 : ℝ)⁻¹ ^ multiplicationVents modulus coefficient inverseCoefficient) * ‖input‖ ^ 2) ∧
      (∑ measured, ‖branch measured‖ ^ 2) = ‖input‖ ^ 2 := by
  dsimp only
  have mass
      (measured : WordOutcomes physical sameWires
        (layout.multiplicationWord wide modulus coefficient inverseCoefficient)) :=
    congrArg (fun value : ℝ => value ^ 2)
      (multiplicationWord_actual_record_norm (operations := operations) (services := services)
        layout wide modulus coefficient inverseCoefficient physical sameWires bank environment
          store measured state reference amplitude distinct clean)
  simp only [mul_pow, multiplication_commonAlpha_eq_power,
    Addition.Gidney.Measured.Layout.adder_commonAlpha_norm_sq] at mass
  refine ⟨mass, ?_⟩
  simp_rw [mass]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    multiplicationWord_outcomes_card layout wide modulus coefficient inverseCoefficient
      physical sameWires]
  rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← mul_pow]
  norm_num

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
