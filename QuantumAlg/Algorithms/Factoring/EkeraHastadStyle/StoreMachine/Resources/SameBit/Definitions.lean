/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.Scalar

/-!
# Historical same-bit resource formulas for Ekerå--Håstad factoring

These scalar expressions support independent arithmetic estimates. Their
recovery terms are not the current reusable recovery event ledger, and their
total is not asserted to specialize the current typed-run resource envelope.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace PublicResourceBounds

/-- Public tradeoff-register width `ell = floor((b + 2) / 2)`. -/
def tradeoffWidth (b : Nat) : Nat := (b + 2) / 2

/-- Public signed-word width used by the fixed-batch recovery. -/
def coordinateWidth (b : Nat) : Nat :=
  2 ^ 21 * (3 * b + tradeoffWidth b + 2) + 2

/-- Structural event bound of a QFT ledger on `bits` wires. -/
def qftEventBound (bits : Nat) : Nat :=
  bits + bits * (bits - 1) / 2 + bits / 2

/-- Width-only cardinality bound of one complete native short-DLP budget. -/
def memberEventBound (b : Nat) : Nat :=
  ShortDLP.CompiledMAU.polynomialPrimitiveWidthBound
    (b + 1) (tradeoffWidth b) (2 * b)

/-- Shared modular-setup event bound in one recovery batch. -/
def modularSetupEventBound (b : Nat) : Nat :=
  8 * b + 7 + 2 * b * (8 * b + 11)

/-- Saved-target LLL and nearest-plane event bound in one pair recovery. -/
def nearestPlaneEventBound (b : Nat) : Nat :=
  8 * (b + 1) + 12 * tradeoffWidth b + 258 +
    264 * (12 * (tradeoffWidth b + (b + 1)) + 10)

/-- Initialized complete coefficient-scan event bound in one pair recovery. -/
def candidateScanEventBound (b : Nat) : Nat :=
  1 + 404685 *
    (178 + coordinateWidth b * (8 * b + 11))

/-- Guarded quadratic-factor event bound in one pair recovery. -/
def quadraticEventBound (b : Nat) : Nat :=
  14 * coordinateWidth b + 56

/-- Complete fixed-batch recovery event bound. -/
def recoveryEventBound (b : Nat) : Nat :=
  modularSetupEventBound b + 11 +
    120 * (13 +
      ((nearestPlaneEventBound b + (b + 4) +
          modularSetupEventBound b + candidateScanEventBound b) +
        quadraticEventBound b))

/-- Sampled-generator and sixteen-member event bound before recovery. -/
def repetitionEventBound (b : Nat) : Nat :=
  88 * b + 179 +
    16 * (memberEventBound b + b + 2 + 2 * tradeoffWidth b)

/-- Complete public event bound for one typed retry batch. -/
def batchEventBound (b : Nat) : Nat :=
  88 * b + 180 +
    16 * (memberEventBound b + b + 2 + 2 * tradeoffWidth b) +
    recoveryEventBound b

end PublicResourceBounds
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
