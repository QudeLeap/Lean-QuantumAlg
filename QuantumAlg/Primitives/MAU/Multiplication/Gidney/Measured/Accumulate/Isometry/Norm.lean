/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Isometry
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Core.Base.Gate.SupportHybrid

/-!
# Norm preservation of the complete actual MAC prefix on clean-helper inputs

Full-label clean-helper injectivity preserves distinct encoded/reference
basis vectors. The arbitrary dirty, active-control and MAC-flag
amplitudes therefore retain their joint norm [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Addition.Gidney.Measured.Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The full actual output basis map is injective on every clean-helper reference family. -/
lemma accumulatePrefixWord_basis_injective (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) (count : Nat)
    (bounded : count ≤ width) (physical : QubitLayout encoding.width)
    {Reference : Register} {Index : Type} (state : Index → Data)
    (reference : Index → Reference.Index)
    (distinct : Function.Injective (fun index => (state index, reference index)))
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    Function.Injective (fun index =>
      (physical.basisEquiv.symm
        (encoding.encode (wordLabel
          (layout.accumulatePrefixWord wide modulus constants count bounded) (state index))),
          reference index)) := by
  intro first second same
  have outputs := encoding.encode_injective
    (physical.basisEquiv.symm.injective (congrArg Prod.fst same))
  have inputs := accumulatePrefixWord_label_injective_clean layout wide modulus constants
    count bounded
    (state first) (state second) (clean first) (clean second) outputs
  have sameReference := congrArg
    (fun pair : physical.toQuantum.register.Index × Reference.Index => pair.2) same
  exact distinct (Prod.ext inputs sameReference)

/-- The complete MAC prefix label preserves the norm of every original clean-helper expansion. -/
lemma accumulatePrefixWord_expansion_norm (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width) (count : Nat)
    (bounded : count ≤ width) (physical : QubitLayout encoding.width)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (distinct : Function.Injective (fun index => (state index, reference index)))
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    ‖∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
        (physical.basisEquiv.symm
          (encoding.encode (wordLabel
            (layout.accumulatePrefixWord wide modulus constants count bounded) (state index))),
            reference index)).vec‖ =
      ‖∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec‖ := by
  have sourceDistinct : Function.Injective (fun index =>
      (physical.basisEquiv.symm (encoding.encode (state index)), reference index)) := by
    intro first second same
    have sameReference := congrArg
      (fun pair : physical.toQuantum.register.Index × Reference.Index => pair.2) same
    exact distinct (Prod.ext (encoding.encode_injective
      (physical.basisEquiv.symm.injective (congrArg Prod.fst same))) sameReference)
  have inputNorm := HilbertVector.norm_sum_smul_ket_eq_sqrt_sum_norm_sq Finset.univ
    (R := Register.prod physical.toQuantum.register Reference)
    (fun index => (physical.basisEquiv.symm (encoding.encode (state index)), reference index))
    sourceDistinct amplitude
  have outputNorm := HilbertVector.norm_sum_smul_ket_eq_sqrt_sum_norm_sq Finset.univ
    (R := Register.prod physical.toQuantum.register Reference)
    (fun index => (physical.basisEquiv.symm
      (encoding.encode (wordLabel
        (layout.accumulatePrefixWord wide modulus constants count bounded) (state index))),
        reference index))
    (accumulatePrefixWord_basis_injective layout wide modulus constants count bounded
      physical state reference distinct clean)
    amplitude
  exact outputNorm.trans inputNorm.symm

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
