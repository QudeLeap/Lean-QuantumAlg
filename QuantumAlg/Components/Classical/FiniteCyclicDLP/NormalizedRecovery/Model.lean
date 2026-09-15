/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Pure normalized Fourier recovery

The original normalized residue carriers, candidate multiplication and
reconstruction check are independent of the machine interpreter. Their
existing names and definition bodies are preserved. This model does not
establish that a supplied candidate inverse is valid or perform allocation.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP

open ClassicalAlgorithms
open ClassicalAlgorithms.Modular

/-- The three normalized machine words needed by finite-cyclic DLP recovery:
the left frequency, the already-negated right frequency, and the inverse of
the left frequency. -/
abbrev InputShape (width : Nat) : CShape :=
  .product (.unsignedWord width)
    (.product (.unsignedWord width) (.unsignedWord width))

/-- The recovered candidate paired with the Boolean reconstruction check. -/
abbrev OutputShape (width : Nat) : CShape :=
  .product (.unsignedWord width) .bit

/-- Semantic normalized measured data.  The inverse is carried explicitly so
this layer never manufactures an unchecked inverse through host evaluation. -/
structure Input {width : Nat} (spec : ModulusSpec width) where
  /-- Normalized left Fourier frequency. -/
  leftFrequency : Residue spec
  /-- Normalized additive inverse of the right Fourier frequency. -/
  negatedRightFrequency : Residue spec
  /-- A typed upstream inverse of `leftFrequency`. -/
  leftInverse : Residue spec

/-- Semantic output of the closed recovery and reconstruction check. -/
structure Output {width : Nat} (spec : ModulusSpec width) where
  /-- The Fourier recovery candidate `(-d) * c⁻¹`. -/
  candidate : Residue spec
  /-- Whether multiplying the candidate by `c` reconstructs `-d`. -/
  verified : Bool

/-- Explicit name for the helper's normalized, non-terminal input boundary. -/
abbrev NormalizedRecoveryInput {width : Nat} (spec : ModulusSpec width) :=
  Input spec

/-- Explicit name for the helper's normalized recovery/check result. -/
abbrev NormalizedRecoveryOutput {width : Nat} (spec : ModulusSpec width) :=
  Output spec

/-- Compute the finite-cyclic Fourier recovery candidate in the canonical
residue carrier. -/
def recoverValue {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : Residue spec :=
  Residue.ofNat spec
    (input.negatedRightFrequency.val * input.leftInverse.val)

/-- Check the defining reconstruction equation for a recovered candidate. -/
def verificationValue {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) (candidate : Residue spec) : Bool :=
  decide ((candidate.val * input.leftFrequency.val) % spec.modulus =
    input.negatedRightFrequency.val)

/-- Pure recovery-and-verification result corresponding to the typed routine. -/
def outputOf {width : Nat} (spec : ModulusSpec width)
    (input : Input spec) : Output spec :=
  { candidate := recoverValue spec input
    verified := verificationValue spec input (recoverValue spec input) }

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP
