/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program

/-!
# Actual decoded source basis and target before LLL initialization

The actual original terminal samples determine both the loaded source basis
and target. Loading the target preserves every source-basis cell, preparing
the actual represented basis for the subsequent Gram refresh and phase reset.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The original flat target-write package gives the complete actual target caller frame. -/
theorem target_callerFrame {m ell width : Nat}
    (refs : LatticeWideTargetMachine.Refs ctx m ell width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : AvoidsTargetWrites other refs) :
    (LatticeWideTargetMachine.targetStep refs store).1.read other = store.read other := by
  rcases avoids with ⟨a, b, c, d, e, f, g, h, i, j⟩
  exact LatticeWideTargetMachine.loadTargetInto_callerFrame refs store other
    ⟨a, b⟩ ⟨c, d, e, f⟩ ⟨g, h, i, j⟩

/-- Actual decoding and target loading preserve every read outside their original write sets. -/
theorem decodeTargetInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : DecodeTargetCallerSeparated refs other) :
    (decodeTargetStep refs store).1.read other = store.read other :=
  (target_callerFrame refs.target _ other avoids.2).trans
    (LatticeWideInitializationPrefix.decodeBasisInto_callerFrame (prefixRefs refs) store
      other avoids.1)

/-- Actual prefix decoding supplies the original first sample component to the target loader. -/
theorem prefix_firstK (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx) :
    LatticeWideTargetMachine.SampleKRepresents
      (LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store).1
      refs.target.first.k (sourceSamples refs store).1 := by
  unfold LatticeWideTargetMachine.SampleKRepresents
  rw [refs.firstTargetK]
  exact LatticeWideInitializationPrefix.decodeBasisInto_firstOutputs (prefixRefs refs)
    separation.prefixSeparation store .k

/-- Actual prefix decoding supplies the original second sample component to the target loader. -/
theorem prefix_secondK (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx) :
    LatticeWideTargetMachine.SampleKRepresents
      (LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store).1
      refs.target.second.k (sourceSamples refs store).2 := by
  unfold LatticeWideTargetMachine.SampleKRepresents
  rw [refs.secondTargetK]
  exact LatticeWideInitializationPrefix.decodeBasisInto_secondOutputs (prefixRefs refs)
    separation.prefixSeparation store .k

/-- The actual source-basis modulus cell is the exact original positive unwrapped modulus. -/
theorem prefix_modulus (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (zeros : LatticeWideInitializationPrefix.BasisInitialZero store (prefixRefs refs)) :
    ((LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store).1.read
      refs.target.modulus).toNat = 2 ^ (tradeoffBits N + shortLogBits N) := by
  have loaded := LatticeWideInitializationPrefix.decodeBasisInto_rawBasis (prefixRefs refs)
    separation.prefixSeparation store zeros
  have raw : RawSignedRepresents
      ((LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store).1.read
        (LatticeLoading.writeInput refs.initialization.raw.b21))
      ((2 : Int) ^ (tradeoffBits N + shortLogBits N)) := by
    have b21 := loaded.2.2.2.1
    simp only [LatticeWideInitializationPrefix.sourceBasis, RSA.shortLogLatticeBasis,
      RSA.shortLogLatticeModulus, Nat.cast_pow, Nat.cast_ofNat] at b21
    exact b21
  have fits : 2 ^ (tradeoffBits N + shortLogBits N) < CShape.wordModulus (Width N) := by
    change 2 ^ (tradeoffBits N + shortLogBits N) < 2 ^ Width N
    apply Nat.pow_lt_pow_right (by norm_num)
    have bound := RSA.ShortLogWidths.sourceWidth_le_coordinateWidth N (shortLogBits N)
      (tradeoffBits N)
    change tradeoffBits N + shortLogBits N <
      RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)
    omega
  rw [refs.targetModulus]
  exact rawSignedRepresents_toNat_eq_of_lt _ raw fits

/-- Actual prefix and target loading yield the exact original pure source target. -/
theorem decodeTargetInto_target (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    LatticeArithmetic.PointRawRepresents (decodeTargetStep refs store).1 refs.target.target.point
      (RSA.shortLogLatticeTarget (shortLogBits N) (tradeoffBits N) (sourceSamples refs store)) := by
  have third : RawSignedRepresents
      ((LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store).1.read
        (LatticeState.coordinateInput refs.target.target.point.third)) 0 := by
    rw [LatticeWideInitializationPrefix.decodeBasisInto_callerFrame (prefixRefs refs) store
      _ separation.targetThirdAvoidsPrefix]
    exact initial.2
  exact LatticeWideTargetMachine.loadTargetInto_represents refs.target separation.target
    (LatticeWideInitializationPrefix.decodeBasisStep (prefixRefs refs) store).1
    (sourceSamples refs store)
    (RSA.ShortLogWidths.sourceWidth_le_coordinateWidth N (shortLogBits N) (tradeoffBits N))
    (prefix_firstK refs separation store) (prefix_secondK refs separation store)
    (prefix_modulus refs separation store initial.1) third

/-- Actual target loading preserves all nine original source-basis coordinates of the LLL driver. -/
theorem decodeTargetInto_basis (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx)
    (zeros : LatticeWideInitializationPrefix.BasisInitialZero store (prefixRefs refs)) :
    LatticeMetricMachine.BasisRawRepresents (decodeTargetStep refs store).1
      refs.initialization.driver.machine.basis (sourceBasis refs store) :=
  LatticeFixedFuelMachine.basis_of_frames refs.initialization.driver (sourceBasis refs store)
    (fun cell => target_callerFrame refs.target _ _ (separation.driverBasisAvoidsTarget cell))
    (LatticeFixedFuelInitializationMachine.prefix_basisRepresents refs.initialization
      separation.prefixSeparation store zeros)

/-- Actual original source basis, target and complete caller frame before Gram refresh. -/
structure DecodeTargetOutcome (refs : Refs ctx N) (before after : Store ctx) : Prop where
  basis : LatticeMetricMachine.BasisRawRepresents after refs.initialization.driver.machine.basis
    (sourceBasis refs before)
  target : LatticeArithmetic.PointRawRepresents after refs.target.target.point
    (RSA.shortLogLatticeTarget (shortLogBits N) (tradeoffBits N) (sourceSamples refs before))
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    DecodeTargetCallerSeparated refs other → after.read other = before.read other

/-- Actual decoding and target loading establish both original mathematical objects and frame. -/
theorem decodeTargetInto_correct (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (initial : InitialConditions store refs) :
    DecodeTargetOutcome refs store (decodeTargetStep refs store).1 :=
  ⟨decodeTargetInto_basis refs separation store initial.1,
    decodeTargetInto_target refs separation store initial, decodeTargetInto_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideLllMachine
