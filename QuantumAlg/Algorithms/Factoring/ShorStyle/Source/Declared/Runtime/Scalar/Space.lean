/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Space
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Signature

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Space

/-!
# Symbolic complete Shor storage coordinates

The native scalar bound contains every persistent selector head, every retained
source result and the full simultaneously live recovery workspace. Every owned
quantum dimension is counted separately. No fixed operand or bit table is used.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar

noncomputable section

private lemma finite_two_width : Nat.clog 2 2 = 1 := by decide

/-- Every binary bank wire contributes once at dimension two and nowhere else. -/
lemma bank_quantum_coordinate (N : Nat) (dimension : ℕ+) :
    (SpacePool.ofQuantumLayout (layout N)) (.quantumSystems dimension) =
      if 2 = dimension then qubits N else 0 := by
  change (QuantumLayout.uniform (bankQubits N) 2 Fin.val
    Fin.val_injective).dimensionCount dimension = _
  rw [QuantumLayout.dimensionCount_uniform, bankQubits_eq_three_mul]
  rfl

/-- The independent complete memory allowance includes all actual live classical entries. -/
lemma machine_classical_coordinate (N count : Nat) :
    (Machine.additionalSpace N count) .classicalBits = classicalBits N count := by
  simp only [Machine.additionalSpace, Persistent.additionalSpace, Finite.additionalSpace,
    Finite.roundResultSpace, completionAdditionalSpace, Sampler.Retained.additionalSpace,
    Sampler.Retained.resultSpace, Storage.resultSpace, FactorRecovery.NativeFactorScope.spaceBound,
    ClassicalRoutines.OrderRecovery.Native.extraClassicalBits, Pi.add_apply, Pi.smul_apply,
    Nat.nsmul_eq_mul, SpacePool.ofQuantumLayout, SpacePool.ofShape, CShape.bitWidth,
    phaseBits, PNat.val_ofNat, finite_two_width, classicalBits]
  ring_nf
  omega

/-- Classical scopes and results add no quantum dimension to the one physical bank. -/
lemma machine_quantum_coordinate (N count : Nat) (dimension : ℕ+) :
    (Machine.additionalSpace N count) (.quantumSystems dimension) =
      if 2 = dimension then qubits N else 0 := by
  simp only [Machine.additionalSpace, Persistent.additionalSpace, Finite.additionalSpace,
    Finite.roundResultSpace, completionAdditionalSpace, Sampler.Retained.additionalSpace,
    Sampler.Retained.resultSpace, Storage.resultSpace, FactorRecovery.NativeFactorScope.spaceBound,
    Pi.add_apply, Pi.smul_apply, SpacePool.ofShape, smul_zero, add_zero, zero_add]
  exact bank_quantum_coordinate N dimension

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar
