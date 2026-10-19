/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Original order-finding source register and all-zero vector

These physical coordinates and the source input do not depend on the runtime
classical frame. The single executable sampler uses them for both empty and
borrowed-input contexts.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

/-- The phase prefix and target suffix in their original physical order. -/
def sourceLayout (t n : Nat) : QubitLayout (t + n) where
  physical_idx := Fin.val
  physical_idx_injective := Fin.val_injective

lemma sourceLayout_systemIdx (t n : Nat) :
    (sourceLayout t n).systemIdx = List.range (t + n) := by
  simp [sourceLayout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Original phase and target wires, all dimension two. -/
@[implicit_reducible]
def runtimeLayout (t n : Nat) : QuantumLayout (t + n) :=
  (sourceLayout t n).toQuantumLayout

/-- Charge one actual all-zero basis preparation for the entire owned register. -/
def inputPreparation (t n : Nat) : BasisPreparation (runtimeLayout t n) :=
  ⟨(sourceLayout t n).binaryIndexEquiv.symm
    (0 : Fin (2 ^ (t + n)))⟩

/-- The basis vector prepared on the entire actual physical register. -/
def preparedInput (t n : Nat) :
    NormalizedVector (Qubits (t + n)) :=
  NormalizedVector.ket (R := Qubits (t + n)) 0

end

end QuantumAlg.OrderFinding.Sampling
