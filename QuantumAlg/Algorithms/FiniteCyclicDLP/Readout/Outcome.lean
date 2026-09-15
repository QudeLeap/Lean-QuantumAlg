/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Core.Measure.Distribution

/-!
# Original big-endian terminal outcome encoding

These pure encoding declarations retain their original full names and bodies.
They depend only on the original exponent width and the binary terminal decoder.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Raw terminal outcome type, deliberately left before any classical
interpretation or recovery. -/
abbrev Outcome (P : KnownOrderProblem G) : Type :=
  TerminalZMeasure.Outcome (orderWidth P + orderWidth P)

/-- Big-endian raw terminal outcome for one paired Fourier-register value. -/
def measurementOutcome (P : KnownOrderProblem G)
    (value : Fin (2 ^ (orderWidth P + orderWidth P))) : Outcome P :=
  fun outputIndex =>
    value.val.testBit
      (orderWidth P + orderWidth P - 1 - outputIndex.val)

@[simp] theorem fullRegisterIndex_measurementOutcome
    (P : KnownOrderProblem G)
    (value : Fin (2 ^ (orderWidth P + orderWidth P))) :
    TerminalZMeasure.fullRegisterIndex (measurementOutcome P value) = value := by
  apply Fin.val_injective
  change Nat.ofBits ((measurementOutcome P value) ∘ Fin.rev) = value.val
  have hbits :
      (measurementOutcome P value) ∘ Fin.rev =
        fun bit : Fin (orderWidth P + orderWidth P) =>
          value.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, measurementOutcome]
    apply congrArg value.val.testBit
    calc
      orderWidth P + orderWidth P - 1 - (Fin.rev bit).val =
          orderWidth P + orderWidth P - ((Fin.rev bit).val + 1) := by
        omega
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

theorem measurementOutcome_injective (P : KnownOrderProblem G) :
    Function.Injective (measurementOutcome P) := by
  intro left right equality
  have := congrArg TerminalZMeasure.fullRegisterIndex equality
  simpa using this

end

end QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge
