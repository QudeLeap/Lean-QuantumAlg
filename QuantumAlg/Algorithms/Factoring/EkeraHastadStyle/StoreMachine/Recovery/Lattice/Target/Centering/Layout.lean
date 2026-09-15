/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources
import all QuantumAlg.Components.Classical.Word.Split.Correctness
import all QuantumAlg.Util.RSA.ShortLog.Target

/-!
# Original actual centered-target allocation

The original source, modulus, scratch, two comparison bits and output keep
their identities and roles. Every original exclusion is stated on actual
structural read support; comparison and arithmetic use the original cells.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget

open Execution
open ClassicalRoutines

noncomputable section

/-- Read the actual word or bit named by an original writable target reference. -/
abbrev writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape := .storage output.toCStorageRef

/-- Caller-owned cells for one centered modular target coordinate. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Input reference for the a value. -/
  a : CInputRef ctx (.unsignedWord width)
  /-- Input reference for the modulus value. -/
  modulus : CInputRef ctx (.unsignedWord width)
  /-- Writable cell for the scratch value. -/
  scratch : CWriteRef ctx (.unsignedWord width)
  scratchWritable : scratch.toCStorageRef.role = .workspace ∨
    scratch.toCStorageRef.role = .retained
  /-- Writable cell for the is zero value. -/
  isZero : CWriteRef ctx .bit
  isZeroWritable : isZero.toCStorageRef.role = .workspace ∨
    isZero.toCStorageRef.role = .retained
  /-- Writable cell for the below half value. -/
  belowHalf : CWriteRef ctx .bit
  belowHalfWritable : belowHalf.toCStorageRef.role = .workspace ∨
    belowHalf.toCStorageRef.role = .retained
  /-- Writable cell for the output value. -/
  output : CWriteRef ctx (.unsignedWord width)
  outputWritable : output.toCStorageRef.role = .workspace ∨
    output.toCStorageRef.role = .retained

/-- Original structural source/write exclusions and distinct written comparison identities. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  aAvoidsIsZero : refs.isZero.key ∉ refs.a.storageKeys
  modulusAvoidsIsZero : refs.isZero.key ∉ refs.modulus.storageKeys
  scratchAvoidsIsZero : refs.isZero.key ∉ (writeInput refs.scratch).storageKeys
  aAvoidsScratch : refs.scratch.key ∉ refs.a.storageKeys
  modulusAvoidsScratch : refs.scratch.key ∉ refs.modulus.storageKeys
  isZeroAvoidsScratch : refs.scratch.key ∉ (writeInput refs.isZero).storageKeys
  aAvoidsBelowHalf : refs.belowHalf.key ∉ refs.a.storageKeys
  modulusAvoidsBelowHalf : refs.belowHalf.key ∉ refs.modulus.storageKeys
  scratchAvoidsBelowHalf : refs.belowHalf.key ∉ (writeInput refs.scratch).storageKeys
  isZeroAvoidsBelowHalf : refs.belowHalf.key ∉ (writeInput refs.isZero).storageKeys
  aAvoidsOutput : refs.output.key ∉ refs.a.storageKeys
  modulusAvoidsOutput : refs.output.key ∉ refs.modulus.storageKeys
  scratchAvoidsOutput : refs.output.key ∉ (writeInput refs.scratch).storageKeys
  isZeroAvoidsOutput : refs.output.key ∉ (writeInput refs.isZero).storageKeys
  belowHalfAvoidsOutput : refs.output.key ∉ (writeInput refs.belowHalf).storageKeys

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
