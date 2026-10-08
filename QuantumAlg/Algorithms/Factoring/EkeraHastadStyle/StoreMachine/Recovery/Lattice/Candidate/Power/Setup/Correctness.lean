/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Frames

/-!
# Original shared modular data from actual setup execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The original public target exponent is strictly below the modulus and fits its original
width. -/
theorem targetExponent_fits (input : Input N) :
    RSA.targetExponent N < 2 ^ modulusBits N := by
  have positive := input.modulus_gt_one
  have targetLt : RSA.targetExponent N < N := by unfold RSA.targetExponent; omega
  exact targetLt.trans_le input.samplerInput.register_fits

/-- The widened actual modulus word contains the original public modulus without truncation. -/
theorem modulus_fits (input : Input N) : N < 2 ^ (modulusBits N + 1) := by
  rw [pow_succ]
  have capacity : N ≤ 2 ^ modulusBits N := input.samplerInput.register_fits
  have positive : 0 < 2 ^ modulusBits N := pow_pos (by decide) _
  omega

/-- Original base packing and both exact public constants after the actual preparation stages. -/
structure PreparedValues (refs : Refs ctx N) (before after : Store ctx) : Prop where
  generator : after.read (writeInput refs.generator) =
    CShape.packCanonicalResidue (modulusBits N) (before.read (parameterBaseInput refs))
  modulus : (after.read (writeInput refs.modulus)).toNat = N
  exponent : (after.read (writeInput refs.targetExponent)).toNat = RSA.targetExponent N

/-- Actual full-width loading overwrites arbitrary previous values and retains the packed base. -/
theorem prepareInto_correct (input : Input N) (refs : Refs ctx N)
    (separation : Separation refs) (store : Store ctx) :
    PreparedValues refs store (prepareStep refs store).1 := by
  let packed := store.applyOp (packOp refs)
  let loaded := (modulusStep refs packed).1
  refine ⟨?_, ?_, ?_⟩
  · change (exponentStep refs loaded).1.read (writeInput refs.generator) = _
    rw [exponentInto_callerFrame refs loaded (writeInput refs.generator)
      (mutable_avoids refs separation refs.generator .generator .targetExponent rfl (by decide)),
      modulusInto_callerFrame refs packed (writeInput refs.generator)
        (mutable_avoids refs separation refs.generator .generator .modulus rfl (by decide))]
    exact Store.read_applyOp_output store (packOp refs)
  · change ((exponentStep refs loaded).1.read (writeInput refs.modulus)).toNat = _
    rw [exponentInto_callerFrame refs loaded (writeInput refs.modulus)
      (mutable_avoids refs separation refs.modulus .modulus .targetExponent rfl (by decide))]
    exact (ClassicalRoutines.ConstantWord.constantWord_read refs.modulus N packed).trans
      (Nat.mod_eq_of_lt (modulus_fits input))
  · exact (ClassicalRoutines.ConstantWord.constantWord_read refs.targetExponent
      (RSA.targetExponent N) loaded).trans (Nat.mod_eq_of_lt (targetExponent_fits input))

/-- Every original shared output and the complete retained caller frame after actual target
power. -/
structure Outcome (refs : Refs ctx N) (before after : Store ctx) : Prop where
  generator : after.read (writeInput refs.generator) =
    CShape.packCanonicalResidue (modulusBits N) (before.read (parameterBaseInput refs))
  generatorValue : (after.read (writeInput refs.generator)).residueEncoding.val =
    parameterBase refs before
  modulus : (after.read (writeInput refs.modulus)).toNat = N
  exponent : (after.read (writeInput refs.targetExponent)).toNat = RSA.targetExponent N
  targetPower : (after.read (writeInput refs.targetPower)).toNat =
    parameterBase refs before ^ RSA.targetExponent N % N
  callerFrame : CallerFrame refs before after

/-- The shared target power is computed from the original retained base and public exponent. -/
theorem setupInto_correct (input : Input N) (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions input store refs) :
    Outcome refs store (setupStep input refs store).1 := by
  let prepared := (prepareStep refs store).1
  have values := prepareInto_correct input refs separation store
  let baseResidue : Residue (modulusSpec input) := ⟨parameterBase refs store, initial.baseLt⟩
  let exponentWord : ClassicalAlgorithms.Word (modulusBits N) :=
    ⟨RSA.targetExponent N, targetExponent_fits input⟩
  let source : Pow.Input (modulusSpec input) (modulusBits N) := ⟨baseResidue, exponentWord⟩
  have generatorValue : (prepared.read (writeInput refs.generator)).residueEncoding.val =
      parameterBase refs store := by
    rw [values.generator]
    change (CShape.packCanonicalResidue _
      (store.read (parameterBaseInput refs))).residueEncoding.val =
      (store.read (parameterBaseInput refs)).toNat
    generalize store.read (parameterBaseInput refs) = raw
    cases raw
    rfl
  have represented : ClassicalRoutines.Modular.NativePower.InputRepresents (modulusSpec input)
      (writeInput refs.generator) (writeInput refs.targetExponent) prepared source := by
    constructor
    · change prepared.read (writeInput refs.generator) = .canonicalResidue baseResidue.toWord
      generalize prepared.read (writeInput refs.generator) = encoded at generatorValue ⊢
      cases encoded with
      | canonicalResidue word =>
          apply congrArg CShape.Value.canonicalResidue
          exact Fin.ext generatorValue
    · have exponentValue := values.exponent
      change prepared.read (writeInput refs.targetExponent) = .unsignedWord exponentWord
      change (prepared.read (writeInput refs.targetExponent)).toNat = _ at exponentValue
      generalize prepared.read (writeInput refs.targetExponent) = encoded at exponentValue ⊢
      cases encoded with
      | unsignedWord word =>
          apply congrArg CShape.Value.unsignedWord
          exact Fin.ext exponentValue
  have generatorFrame := powerInto_callerFrame input refs prepared (writeInput refs.generator)
    (mutable_avoids refs separation refs.generator .generator .targetPower rfl (by decide))
  have modulusFrame := powerInto_callerFrame input refs prepared (writeInput refs.modulus)
    (mutable_avoids refs separation refs.modulus .modulus .targetPower rfl (by decide))
  have exponentFrame := powerInto_callerFrame input refs prepared (writeInput refs.targetExponent)
    (mutable_avoids refs separation refs.targetExponent .targetExponent .targetPower rfl
      (by decide))
  refine ⟨generatorFrame.trans values.generator, ?_, ?_, ?_, ?_,
    setupInto_callerFrame input refs store⟩
  · exact (congrArg (fun value => value.residueEncoding.val) generatorFrame).trans generatorValue
  · exact (congrArg CShape.Value.toNat modulusFrame).trans values.modulus
  · exact (congrArg CShape.Value.toNat exponentFrame).trans values.exponent
  · exact ClassicalRoutines.Modular.NativePower.nativePower_into_toNat (modulusSpec input)
      (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower prepared
      source represented

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup
