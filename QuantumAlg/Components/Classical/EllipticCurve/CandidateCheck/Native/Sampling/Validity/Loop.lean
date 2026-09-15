/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Local
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Original selected-value invariants along actual sampling prefixes

The chronological finite loop preserves the range and checked point equation
of its real selected word. Public-point interpretations are required only on
actual prefixes of the prescribed input, where borrowed restoration supplies
them. Local sampling keeps arbitrary selection-pair predicates; the actual
checked step then uses the original stored invariants. Every history remains
part of the actual execution, including zero further rounds.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def storeSupported {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference H) (predicate : Store ctx → Prop) : Prop :=
  ∀ entry, 0 < (state.block entry).mass → predicate entry.1

private theorem storeSupported_mapHistory {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K) (predicate : Store ctx → Prop) :
    storeSupported (state.mapHistory update) predicate ↔ storeSupported state predicate := by
  constructor
  · intro holds entry positive
    exact holds (entry.1, update entry.2)
      ((mapped_positive _ _ _ _).mpr ⟨entry, rfl, positive⟩)
  · intro holds entry positive
    obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
    rw [← equality]
    exact holds original present

private theorem storeSupported_seq {kind : ProblemKind}
    {origin middle final : RuntimeCtx kind}
    (first : Circuit origin middle) (second : Circuit middle final)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State origin Reference H) (predicate : Store final → Prop) :
    storeSupported ((first.seq second).execute Reference state) predicate ↔
      storeSupported (second.execute Reference (first.execute Reference state)) predicate := by
  rw [Circuit.execute_seq, storeSupported_mapHistory]

private theorem storeSupported_seq_assoc {kind : ProblemKind}
    {origin first second final : RuntimeCtx kind}
    (priorCode : Circuit origin first) (middle : Circuit first second)
    (tail : Circuit second final) {Reference : Register} {H : Type} [Fintype H]
    (state : State origin Reference H) (predicate : Store final → Prop) :
    storeSupported ((priorCode.seq (middle.seq tail)).execute Reference state) predicate ↔
      storeSupported (((priorCode.seq middle).seq tail).execute Reference state) predicate := by
  simp only [Circuit.execute_seq, Circuit.execute_mapHistory, storeSupported_mapHistory]

private theorem storeSupported_forRange {kind : ProblemKind}
    {origin ctx : RuntimeCtx kind} {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference H) (count : Nat) (body : Fin count → Circuit ctx ctx)
    (predicate : Store ctx → Prop)
    (step : ∀ (priorCode : Circuit origin ctx) index,
      storeSupported (priorCode.execute Reference initial) predicate →
        storeSupported ((priorCode.seq (body index)).execute Reference initial) predicate)
    (priorCode : Circuit origin ctx)
    (prior : storeSupported (priorCode.execute Reference initial) predicate) :
    storeSupported ((priorCode.seq (Circuit.forRange count body)).execute Reference initial)
      predicate := by
  induction count generalizing priorCode with
  | zero =>
      rw [Circuit.forRange, storeSupported_seq]
      intro result positive
      rw [Circuit.execute_id_mapClassical] at positive
      obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
      rw [← equality]
      exact prior original present
  | succ count ih =>
      rw [Circuit.forRange, storeSupported_seq_assoc]
      exact ih (fun index => body index.succ) (fun current index => step current index.succ)
        (priorCode.seq (body 0)) (step priorCode 0 prior)

variable {kind : ProblemKind} {ctx origin : RuntimeCtx kind} {width scalarWidth : Nat}

private def selectedInvariant (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (pair : Bool × (CShape.unsignedWord scalarWidth).Value) : Prop :=
  pair.2.toNat < modulus.modulus ∧ (pair.1 = true → pair.2.toNat • basePoint = targetPoint)

private def selectedPair (store : Store (persistentCtx ctx width scalarWidth)) :
    Bool × (CShape.unsignedWord scalarWidth).Value :=
  ((store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
    store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef))

private theorem local_selection_supported
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (width scalarWidth : Nat) (property : Bool × (CShape.unsignedWord scalarWidth).Value → Prop)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (valid : storeSupported state (fun store => property (selectedPair store))) :
    storeSupported
      ((underPersistent sampleCode supported width scalarWidth).execute Reference state)
      (fun store => property (selectedPair store)) := by
  exact @underPersistent_latches_property kind ctx sampleCode supported width scalarWidth property
    Reference H _ state valid

private theorem sampled_step_supported
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H)
    (points : ∀ (priorCode : Circuit origin (persistentCtx ctx width scalarWidth)) entry,
      0 < ((priorCode.execute Reference initial).block entry).mass →
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (priorCode : Circuit origin (persistentCtx ctx width scalarWidth))
    (valid : storeSupported (priorCode.execute Reference initial) (fun store =>
      selectedInvariant curve modulus basePoint targetPoint (selectedPair store))) :
    storeSupported ((priorCode.seq
      (sampledAttempt sampleCode supported curve modulus sample base target)).execute
        Reference initial) (fun store =>
          selectedInvariant curve modulus basePoint targetPoint (selectedPair store)) := by
  let predicate := fun store : Store (persistentCtx ctx width scalarWidth) =>
    selectedInvariant curve modulus basePoint targetPoint (selectedPair store)
  let localCode := underPersistent sampleCode supported width scalarWidth
  let currentState := priorCode.execute Reference initial
  let sampledState := localCode.execute Reference currentState
  have localValid : storeSupported sampledState predicate :=
    local_selection_supported sampleCode supported width scalarWidth
      (selectedInvariant curve modulus basePoint targetPoint) currentState valid
  have localPoints : storeSupported sampledState (fun store =>
      PointRepresents curve (store.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (store.read (persistentInput width scalarWidth target)) targetPoint) :=
    (storeSupported_seq priorCode localCode initial _).mp (points (priorCode.seq localCode))
  apply (storeSupported_seq priorCode
    (sampledAttempt sampleCode supported curve modulus sample base target) initial predicate).mpr
  apply (storeSupported_seq localCode (persistentAttempt curve modulus sample base target)
    currentState predicate).mpr
  intro output present
  have bounded := persistentAttempt_preserves_selected_lt curve modulus sample base target
    sampledState (fun entry positive => (localValid entry positive).1) output present
  have checked := persistentAttempt_preserves_validity curve modulus sample base target
    basePoint targetPoint sampledState (fun entry positive =>
      ⟨(localPoints entry positive).1, (localPoints entry positive).2,
        (localValid entry positive).2⟩) output present
  exact ⟨bounded, checked.2.2⟩

/-- Actual-prefix public points suffice to preserve the original selected invariants in the loop. -/
theorem sampledAttempts_supported_validity_on_prefix
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H)
    (points : ∀ (priorCode : Circuit origin (persistentCtx ctx width scalarWidth)) entry,
      0 < ((priorCode.execute Reference initial).block entry).mass →
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (priorCode : Circuit origin (persistentCtx ctx width scalarWidth))
    (prior : ∀ entry, 0 < ((priorCode.execute Reference initial).block entry).mass →
      (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
          modulus.modulus ∧
        ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
            true →
          (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
            basePoint = targetPoint))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (H × (priorCode.seq
        (sampledAttempts sampleCode supported count curve modulus sample base target)).Path))
    (positive : 0 < (((priorCode.seq
      (sampledAttempts sampleCode supported count curve modulus sample base target)).execute
        Reference initial).block result).mass) :
    (result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus ∧
      ((result.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true →
        (result.1.read
          (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
            basePoint = targetPoint) := by
  let predicate := fun store : Store (persistentCtx ctx width scalarWidth) =>
    selectedInvariant curve modulus basePoint targetPoint (selectedPair store)
  exact storeSupported_forRange initial count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target) predicate
    (fun current _ => sampled_step_supported sampleCode supported curve modulus sample base target
      basePoint targetPoint initial points current) priorCode prior result positive

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
