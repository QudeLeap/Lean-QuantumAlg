/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Isometry
import all QuantumAlg.Core.Base.Gate.SupportHybrid

/-!
# Norm preservation on arbitrary clean-helper encoded/reference superpositions

The complete actual label map is injective on its admitted clean-helper
subspace. Consequently distinct complete encoded/reference basis vectors
remain distinct and orthonormal after addition, with arbitrary coherent
control and dirty values [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The complete encoded/reference output basis map is injective on clean-helper inputs. -/
lemma adderWord_basis_injective (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    {Reference : Register} {Index : Type} (state : Index → Data)
    (reference : Index → Reference.Index)
    (distinct : Function.Injective (fun index => (state index, reference index)))
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    Function.Injective (fun index =>
      (physical.basisEquiv.symm
        (encoding.encode (wordLabel (layout.adderWord wide constant) (state index))),
          reference index)) := by
  intro first second same
  have outputs := encoding.encode_injective
    (physical.basisEquiv.symm.injective (congrArg Prod.fst same))
  have inputs := adderWord_label_injective_clean layout wide constant (state first) (state second)
    (clean first) (clean second) outputs
  have sameReference := congrArg
    (fun pair : physical.toQuantum.register.Index × Reference.Index => pair.2) same
  exact distinct (Prod.ext inputs sameReference)

/-- Actual selected addition preserves the norm of every admitted full reference expansion. -/
lemma adderWord_expansion_norm (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (distinct : Function.Injective (fun index => (state index, reference index)))
    (clean : ∀ index helper, (layout.clean helper).get (state index) = false) :
    ‖∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
        (physical.basisEquiv.symm
          (encoding.encode (wordLabel (layout.adderWord wide constant) (state index))),
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
      (encoding.encode (wordLabel (layout.adderWord wide constant) (state index))),
        reference index))
    (adderWord_basis_injective layout wide constant physical state reference distinct clean)
    amplitude
  exact outputNorm.trans inputNorm.symm

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
