/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Qubit
public import QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Util.Classical.TerminalDecode
import all QuantumAlg.Util.Order.Finding

public import QuantumAlg.Algorithms.OrderFinding.Construction
import all QuantumAlg.Algorithms.OrderFinding.Construction

/-!
# Order-finding measurement coordinates

The source's phase-register measurement model and bit decoding are isolated
from the reusable unitary construction. Native execution uses the same
phase positions while retaining all physical systems.
-/

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

namespace OrderFinding

/-! ## Layout, input, and terminal measurement -/

/-- Canonical physical placement of phase and target registers. -/
public def layout (t m : Nat) : QubitLayout (t + m) where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp] theorem layout_systemIdx (t m : Nat) :
    (layout t m).systemIdx = List.range (t + m) := by
  simp [layout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Canonical zero input for both registers. -/
def inputState (t m : Nat) : QubitLayout.State (layout t m) where
  state := PureState.ofNormalized
    (NormalizedVector.ket (R := Qubits (t + m))
      (prodEquiv ((0 : Fin (2 ^ t)), (0 : Fin (2 ^ m)))))
    (layout t m).systemIdx
  system_idx_eq := rfl

/-- Terminally measure the complete phase register in logical order. -/
public def measurement (t m : Nat) : TerminalZMeasure (layout t m) t :=
  zMeasureAt (layout t m)
    (fun index => ⟨index.val, Nat.lt_add_right m index.isLt⟩)
    (fun _ _ h => Fin.ext (Fin.mk.inj h))

/-- Classical phase-register output. -/
abbrev Outcome (t : Nat) : Type :=
  TerminalZMeasure.Outcome t

/-- Decode a big-endian terminal phase-register outcome. -/
def decodeOutcome {t : Nat} (outcome : Outcome t) : Fin (2 ^ t) :=
  ClassicalAlgorithms.TerminalDecode.fullRegisterIndex outcome

/-- The typed fixed-width decoder agrees with the legacy terminal-measurement
index used by the general-order compatibility layer. -/
@[simp] theorem decodeOutcome_eq_terminalFullRegisterIndex {t : Nat}
    (outcome : Outcome t) :
    decodeOutcome outcome = TerminalZMeasure.fullRegisterIndex outcome := by
  apply Fin.ext
  change (ClassicalAlgorithms.TerminalDecode.fullRegisterIndex
    outcome).val = (TerminalZMeasure.fullRegisterIndex outcome).val
  rw [ClassicalAlgorithms.TerminalDecode.fullRegisterIndex_val]
  rfl

/-- Big-endian terminal outcome corresponding to an index. -/
def measurementOutcome (t : Nat) (value : Fin (2 ^ t)) : Outcome t :=
  fun outputIndex => value.val.testBit (t - 1 - outputIndex.val)

@[simp, nolint simpNF]
theorem decodeOutcome_measurementOutcome (t : Nat) (value : Fin (2 ^ t)) :
    decodeOutcome (measurementOutcome t value) = value := by
  unfold decodeOutcome
  apply Fin.val_injective
  rw [ClassicalAlgorithms.TerminalDecode.fullRegisterIndex_val]
  have hbits :
      (measurementOutcome t value) ∘ Fin.rev =
        fun bit : Fin t => value.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, measurementOutcome]
    apply congrArg value.val.testBit
    calc
      t - 1 - (Fin.rev bit).val = t - ((Fin.rev bit).val + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

end OrderFinding

end

end QuantumAlg
