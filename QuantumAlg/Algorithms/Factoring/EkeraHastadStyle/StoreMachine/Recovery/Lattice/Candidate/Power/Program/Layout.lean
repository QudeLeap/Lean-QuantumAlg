/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Correctness
import all QuantumAlg.Components.Classical.Modular.NativePower.Preservation

/-!
# Original candidate modular-power inputs and outputs
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine

open Execution
open ClassicalAlgorithms.Modular
open ClassicalRoutines.Modular.NativePower

noncomputable section

/-- Structural input of one actual writable result cell. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Original caller-owned source words and visible modular-power check results. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width exponentWidth : Nat) where
  modulus : CInputRef ctx (.unsignedWord (width + 1))
  generator : CInputRef ctx (.canonicalResidue width)
  exponent : CInputRef ctx (.unsignedWord exponentWidth)
  targetPower : CInputRef ctx (.unsignedWord width)
  power : CWriteRef ctx (.unsignedWord width)
  powerRole : power.toCStorageRef.role = .workspace
  accepted : CWriteRef ctx .bit
  acceptedRole : accepted.toCStorageRef.role = .workspace

/-- Actual writes preserve the compared target, reported modulus and computed power. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width exponentWidth : Nat} (refs : Refs ctx width exponentWidth) : Prop where
  modulusAvoidsPower : refs.power.key ∉ refs.modulus.storageKeys
  targetPowerAvoidsPower : refs.power.key ∉ refs.targetPower.storageKeys
  modulusAvoidsAccepted : refs.accepted.key ∉ refs.modulus.storageKeys
  powerAvoidsAccepted : refs.accepted.key ∉ (writeInput refs.power).storageKeys

/-- Original semantic inputs, without an initial-value requirement on the overwritten power. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width exponentWidth : Nat} (spec : ModulusSpec width) (before : Store ctx)
    (refs : Refs ctx width exponentWidth) (input : Pow.Input spec exponentWidth)
    (target : Residue spec) : Prop where
  modulusRepresents : (before.read refs.modulus).toNat = spec.modulus
  baseRepresents : (before.read refs.generator).residueEncoding.val = input.base.val
  exponentValue : before.read refs.exponent = .unsignedWord input.exponent
  targetRepresents : (before.read refs.targetPower).toNat = target.val

/-- All actual caller reads outside the two original result cells are retained. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {width exponentWidth : Nat}
    (refs : Refs ctx width exponentWidth) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.power.key ∉ other.storageKeys → refs.accepted.key ∉ other.storageKeys →
      after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine
