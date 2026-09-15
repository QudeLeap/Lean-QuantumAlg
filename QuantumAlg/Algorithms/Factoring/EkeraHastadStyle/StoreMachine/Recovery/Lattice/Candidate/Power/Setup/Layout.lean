/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Components.Classical.Modular.NativePower.Correctness
import all QuantumAlg.Components.Classical.Modular.NativePower.Preservation
import all QuantumAlg.Components.Classical.ConstantWord.Preservation

/-!
# Original shared modular-setup data
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Structural read of an original writable output. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Original caller-owned retained parameter and shared modular data for all candidate slots. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  parameter : CInputRef ctx (ParameterShape N)
  generator : CWriteRef ctx (.canonicalResidue (modulusBits N))
  generatorRole : generator.toCStorageRef.role = .workspace
  modulus : CWriteRef ctx (.unsignedWord (modulusBits N + 1))
  modulusRole : modulus.toCStorageRef.role = .workspace
  targetExponent : CWriteRef ctx (.unsignedWord (modulusBits N))
  targetExponentRole : targetExponent.toCStorageRef.role = .workspace
  targetPower : CWriteRef ctx (.unsignedWord (modulusBits N))
  targetPowerRole : targetPower.toCStorageRef.role = .workspace

/-- The original structural projection of the retained sampler parameter. -/
def parameterBaseInput (refs : Refs ctx N) : CInputRef ctx (.unsignedWord (modulusBits N)) :=
  .first refs.parameter

/-- Every original shared output overwritten by actual modular setup. -/
inductive MutableCell where
  | generator
  | modulus
  | targetExponent
  | targetPower
deriving DecidableEq

/-- Actual storage identity of one original modular-setup output. -/
def mutableKey (refs : Refs ctx N) : MutableCell → StorageKey
  | .generator => refs.generator.key
  | .modulus => refs.modulus.key
  | .targetExponent => refs.targetExponent.key
  | .targetPower => refs.targetPower.key

/-- The actual retained parameter avoids all distinct original shared output cells. -/
structure Separation (refs : Refs ctx N) : Prop where
  parameterAvoidsMutable : ∀ cell, mutableKey refs cell ∉ refs.parameter.storageKeys
  mutableKeyInjective : Function.Injective (mutableKey refs)

/-- The original public input induces the same fixed-capacity nontrivial modulus. -/
def modulusSpec (input : Input N) : ModulusSpec (modulusBits N) where
  modulus := N
  two_le := input.samplerInput.modulus_ge_two
  le_capacity := input.samplerInput.register_fits

/-- The original public short-log target exponent fits its declared word. -/
def targetExponentWord (N : Nat) : CShape.Word (modulusBits N) :=
  CShape.wordOfNat (modulusBits N) (RSA.targetExponent N)

/-- The actual numerical base read from the original retained parameter. -/
def parameterBase (refs : Refs ctx N) (store : Store ctx) : Nat :=
  (store.read (parameterBaseInput refs)).toNat

/-- The retained actual parameter was produced by the original fixed-cost sampler. -/
def SampledParameter (input : Input N) (store : Store ctx) (refs : Refs ctx N) : Prop :=
  ∃ sample : Fin (2 ^ residueSamplingBits N),
    store.read refs.parameter = parameterValue input sample

/-- The original sampled parameter has a canonical base, without scratch initialization
assumptions. -/
structure InitialConditions (input : Input N) (store : Store ctx) (refs : Refs ctx N) : Prop where
  sampled : SampledParameter input store refs
  baseLt : parameterBase refs store < N

/-- Actual caller reads outside all four original shared outputs remain unchanged. -/
def CallerFrame (refs : Refs ctx N) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ cell, mutableKey refs cell ∉ other.storageKeys) → after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup
