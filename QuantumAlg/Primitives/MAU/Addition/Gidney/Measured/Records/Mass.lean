/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Records.Norm

/-!
# Exact physical record magnitudes and their complete normalization

The sum ranges over the actual physical outcome words of the same compiled
adder. Every record has the common squared norm factor, and the exact actual
outcome cardinality cancels it. The independently proved clean-input isometry
is required throughout; no standalone mathematical outcome PMF replaces
the actual measurement execution [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Execution Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Exact common squared branch norm and normalization over all actual physical adder records. -/
lemma adderWord_actual_record_mass (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
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
    let branch := fun measured : WordOutcomes physical sameWires (layout.adderWord wide constant) =>
      (wordActualKraus (operations := operations) (services := services)
        physical sameWires bank.output environment Reference (layout.adderWord wide constant)
          store measured).applyVec
            (HilbertVector.reindex
              ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
                (Equiv.refl Reference.Index)) input)
    (∀ measured, ‖branch measured‖ ^ 2 = (2 : ℝ)⁻¹ ^ (width - 2) * ‖input‖ ^ 2) ∧
      (∑ measured, ‖branch measured‖ ^ 2) = ‖input‖ ^ 2 := by
  dsimp only
  have mass (measured : WordOutcomes physical sameWires (layout.adderWord wide constant)) :=
    congrArg (fun value : ℝ => value ^ 2)
      (adderWord_actual_record_norm (operations := operations) (services := services)
        layout wide constant physical sameWires bank environment store measured
          state reference amplitude distinct clean)
  simp only [mul_pow, adder_commonAlpha_norm_sq] at mass
  refine ⟨mass, ?_⟩
  simp_rw [mass]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    adderWord_outcomes_card layout wide constant physical sameWires,
    Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← mul_pow]
  norm_num

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
