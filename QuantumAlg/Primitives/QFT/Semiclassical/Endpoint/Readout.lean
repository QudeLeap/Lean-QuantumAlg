/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Util.FinPow.BitReverse

/-!
# Exact mathematical labels of the stored Fourier result

The real output remains the vector of n separately retained binary cells.
Its physical bank label and reversed Fourier frequency are bijective
mathematical interpretations, with no circuit conversion, packed runtime
word or additional storage [GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

noncomputable section

/-- The finite constructors identify the actual shaped output with its n binary values. -/
public def resultBitsEquiv (n : Nat) :
    CShape.Value (.fixedVector n (.finite 2)) ≃ (Fin n → Fin 2) where
  toFun value := match value with
    | .fixedVector entries => fun i => binaryValue (entries i)
  invFun bits := .fixedVector (fun i => .finite (bits i))
  left_inv value := by
    cases value with
    | fixedVector entries =>
        change CShape.Value.fixedVector (fun i =>
            (.finite (binaryValue (entries i)) : CShape.Value (.finite 2))) =
          CShape.Value.fixedVector entries
        congr 1
        funext i
        cases entries i
        rfl
  right_inv bits := rfl

/-- Every output vector has one physical bank label, and each label has exactly one vector. -/
public def physicalLabelEquiv (n : Nat) :
    CShape.Value (.fixedVector n (.finite 2)) ≃ Fin (2 ^ n) :=
  (resultBitsEquiv n).trans (qubitLayout n).binaryIndexEquiv

/-- The mathematical equivalence reads precisely the previously defined physical label. -/
public lemma qftSemiclassical_physicalLabelEquiv_apply (n : Nat)
    (value : CShape.Value (.fixedVector n (.finite 2))) :
    physicalLabelEquiv n value = physicalLabel n value := by
  cases value
  rfl

/-- Reverse the same physical label to obtain the Fourier frequency, without an instruction. -/
public def frequencyEquiv (n : Nat) :
    CShape.Value (.fixedVector n (.finite 2)) ≃ Fin (2 ^ n) :=
  (physicalLabelEquiv n).trans (qftReverseBitsPerm n)

/-- The frequency equivalence uses exactly the output interpretation fixed by the interface. -/
public lemma qftSemiclassical_frequencyEquiv_apply (n : Nat)
    (value : CShape.Value (.fixedVector n (.finite 2))) :
    frequencyEquiv n value = frequency n value := by
  change qftReverseBits n (physicalLabelEquiv n value) = _
  rw [qftSemiclassical_physicalLabelEquiv_apply]
  rfl

/-- Actual stored vectors cannot collide when interpreted as Fourier frequencies. -/
public lemma qftSemiclassical_frequency_injective (n : Nat) :
    Function.Injective (frequency n) := by
  intro left right same
  apply (frequencyEquiv n).injective
  simpa only [qftSemiclassical_frequencyEquiv_apply] using same

/-- Every mathematical Fourier frequency is represented by an actual shaped output value. -/
public lemma qftSemiclassical_frequency_surjective (n : Nat) :
    Function.Surjective (frequency n) := by
  intro label
  refine ⟨(frequencyEquiv n).symm label, ?_⟩
  rw [← qftSemiclassical_frequencyEquiv_apply, Equiv.apply_symm_apply]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
