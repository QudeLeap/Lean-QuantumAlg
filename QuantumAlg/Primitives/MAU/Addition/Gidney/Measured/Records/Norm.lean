/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Records.Coherent
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Isometry.Norm
import all QuantumAlg.Components.Kets

/-!
# Actual retained adder norm on the complete clean-helper reference subspace

The actual chronological Kraus operator has common alpha on every actual
physical record. The independently proved clean-input injectivity preserves
the output norm, so the squared branch magnitude is exactly one half per
physical vent. No norm claim is inferred from an unrestricted reset map
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Execution Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The common branch scalar has exactly one half squared magnitude per actual physical vent. -/
lemma adder_commonAlpha_norm_sq (records : Nat) :
    ‖NormalizedVector.invSqrt2 ^ records‖ ^ 2 = (2 : ℝ)⁻¹ ^ records := by
  rw [norm_pow, ← pow_mul, Nat.mul_comm records 2, pow_mul,
    NormalizedVector.norm_sq_invSqrt2]

/-- Every actual retained record has the same norm multiplier on every admitted reference vector. -/
lemma adderWord_actual_record_norm (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (environment : oracles.Interpretation) (store : Store ctx)
    (measured : WordOutcomes physical sameWires (layout.adderWord wide constant))
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (distinct : Function.Injective (fun index => (state index, reference index)))
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    let input : HilbertVector (Register.prod physical.toQuantum.register Reference) :=
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec
    ‖(wordActualKraus (operations := operations) (services := services)
      physical sameWires bank.output environment Reference (layout.adderWord wide constant)
        store measured).applyVec
          (HilbertVector.reindex
            ((basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).prodCongr
              (Equiv.refl Reference.Index)) input)‖ =
      ‖NormalizedVector.invSqrt2 ^ (width - 2)‖ * ‖input‖ := by
  dsimp only
  rw [adderWord_actual_record_coherent layout wide constant physical sameWires bank environment
    store measured state reference amplitude clean, HilbertVector.norm_reindex]
  have factored :
      (∑ index, (amplitude index * NormalizedVector.invSqrt2 ^ (width - 2)) •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (wordLabel (layout.adderWord wide constant) (state index))),
              reference index)).vec) =
      (NormalizedVector.invSqrt2 ^ (width - 2)) •
        ∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm
              (encoding.encode (wordLabel (layout.adderWord wide constant) (state index))),
                reference index)).vec := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [smul_smul]
    congr 1
    exact mul_comm _ _
  rw [factored, norm_smul,
    adderWord_expansion_norm layout wide constant physical state reference amplitude distinct clean]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
