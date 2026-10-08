/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Actual joint borrowed restoration for both measured arithmetic runs

Both original input words are owned systems. The existing complete-circuit
restoration theorem applies to the actual preparation, actual Z writes,
stored-result dispatch and all emitted arithmetic bodies. It retains the
complete borrowed observation, including its external reference
[LYL+26, sec_point_add/sec_point_add.tex:45-105,119-122; dW19, qcnotes.tex:5381].

These restoration statements hold for arbitrary initial states, independently
of the arithmetic input-support promise. They do not infer restoration from
an output listing, a register-count equality or a canonical basis result.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceRestoration

noncomputable section

open Execution MAU.Inversion.SharedEEA InversePreparation

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem noBorrowedQuantum (width : Nat) : (before width).borrowedQuantumWires = [] := by
  rfl

/-- The same actual division code restores the complete borrowed-reference observation. -/
theorem division_restored (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (InPlaceDivision.code modulus prime).BorrowedRestored Reference state
      ((InPlaceDivision.code modulus prime).execute Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (InPlaceDivision.code modulus prime)
    (noBorrowedQuantum modulus.size) Reference state

/-- Actual multiplication likewise restores all borrowed-reference entries for arbitrary inputs. -/
theorem multiplication_restored (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (InPlaceMultiplication.code modulus prime).BorrowedRestored Reference state
      ((InPlaceMultiplication.code modulus prime).execute Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (InPlaceMultiplication.code modulus prime)
    (noBorrowedQuantum modulus.size) Reference state

end

end QuantumAlg.MeasuredUncompute.InPlaceRestoration
