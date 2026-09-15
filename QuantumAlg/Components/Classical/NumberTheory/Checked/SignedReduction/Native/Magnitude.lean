/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Classification

/-!
# Actual conditional signed-coefficient magnitude

The stored sign bit selects the original copy-only or copy, complement,
increment instruction sequence. The raw input is read before the first
write; no initial output value or input/output separation is required.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The first actual instruction reads the original coefficient into the work word. -/
def magnitudeCopyOp (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) :
    ClassicalOp (.unsignedWord (signedWidth width)) (.unsignedWord (signedWidth width)) ctx ctx :=
  .wordUnary .copy (signedWidth width) ctx raw work

/-- The original branch has three instructions for a negative coefficient and one otherwise. -/
def magnitudeChoice (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then
    .seq (.classical (magnitudeCopyOp raw work))
      (.seq (.classical (signUnaryOp .complement work)) (.classical (signUnaryOp .increment work)))
  else .classical (magnitudeCopyOp raw work)

/-- The literal chosen store is obtained by the same actual operations. -/
def magnitudeChoiceStore (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (value : CShape.Value .bit) (store : Store ctx) : Store ctx :=
  if value.toBool then
    ((store.applyOp (magnitudeCopyOp raw work)).applyOp (signUnaryOp .complement work)).applyOp
      (signUnaryOp .increment work)
  else store.applyOp (magnitudeCopyOp raw work)

/-- The native path records precisely the selected sequence. -/
def magnitudeChoiceStep (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (magnitudeChoice raw work value).Path :=
  match value with
  | .bit false => (magnitudeChoiceStore raw work (.bit false) store, ())
  | .bit true => (magnitudeChoiceStore raw work (.bit true) store, ((), ((), ())))

/-- The branch selector is the actual retained stored sign bit. -/
def signedMagnitude (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CInputRef ctx .bit) : Circuit ctx ctx :=
  .branch negative (magnitudeChoice raw work)

/-- Complete actual selected store and classical branch history. -/
def signedMagnitudeStep (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width)))
    (negative : CInputRef ctx .bit) (store : Store ctx) :
    Store ctx × (signedMagnitude raw work negative).Path :=
  let value := store.read negative
  let chosen := magnitudeChoiceStep raw work value store
  (chosen.1, ⟨value, chosen.2⟩)

/-- Both literal branches preserve complete quantum-reference blocks and the original history. -/
theorem magnitudeChoice_execute (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (magnitudeChoice raw work value).execute Reference state = state.mapClassical (fun entry =>
      ((magnitudeChoiceStep raw work value entry.1).1,
        (entry.2, (magnitudeChoiceStep raw work value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · refine (Circuit.execute_classical_mapClassical
          (magnitudeCopyOp raw work) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · change (Circuit.seq (.classical (magnitudeCopyOp raw work))
          (.seq (.classical (signUnaryOp .complement work))
            (.classical (signUnaryOp .increment work)))).execute Reference state = _
        simp only [Circuit.execute_seq,
          Circuit.execute_classical_mapClassical, State.mapHistory,
          ExecutionState.executionState_mapClassical_comp, Function.comp_def]
        congr 1
        exact Subsingleton.elim _ _

/-- The actual stored-bit branch preserves the full reference-correlated execution state. -/
theorem signedMagnitude_execute (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (signedMagnitude raw work negative).execute Reference state = state.mapClassical (fun entry =>
      ((signedMagnitudeStep raw work negative entry.1).1,
        (entry.2, (signedMagnitudeStep raw work negative entry.1).2))) :=
  Circuit.execute_branch_mapClassical negative (magnitudeChoice raw work)
    (magnitudeChoiceStep raw work) (magnitudeChoice_execute raw work) Reference state

/-- The selected exact fixed-width arithmetic, without a sign-correctness assumption. -/
def magnitudeWord (raw : CShape.Word (signedWidth width)) (negative : Bool) :
    CShape.Word (signedWidth width) :=
  if negative then Resource.WordUnaryOpcode.eval .increment (signedWidth width)
    (Resource.WordUnaryOpcode.eval .complement (signedWidth width) raw) else raw

/-- The actual chosen output equals its exact fixed-width word for arbitrary original stores. -/
theorem magnitudeChoice_value (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (value : CShape.Value .bit)
    (store : Store ctx) :
    (magnitudeChoiceStep raw work value store).1.read (signedRead work) =
      magnitudeWord (store.read raw) value.toBool := by
  have copied : (store.applyOp (magnitudeCopyOp raw work)).read (signedRead work) =
      store.read raw := Store.read_applyOp_output store (magnitudeCopyOp raw work)
  cases value with
  | bit value =>
      cases value
      · exact copied
      · let entered := store.applyOp (magnitudeCopyOp raw work)
        let complemented := entered.applyOp (signUnaryOp .complement work)
        have complementValue : complemented.read (signedRead work) =
            Resource.WordUnaryOpcode.eval .complement (signedWidth width)
              (entered.read (signedRead work)) :=
          Store.read_applyOp_output entered (signUnaryOp .complement work)
        have incrementValue : (complemented.applyOp (signUnaryOp .increment work)).read
            (signedRead work) = Resource.WordUnaryOpcode.eval .increment (signedWidth width)
              (complemented.read (signedRead work)) :=
          Store.read_applyOp_output complemented (signUnaryOp .increment work)
        change (complemented.applyOp (signUnaryOp .increment work)).read (signedRead work) = _
        rw [incrementValue, complementValue, copied]
        rfl

/-- Correct classification yields the original mathematical magnitude. -/
theorem magnitudeWord_original_toNat (raw : CShape.Word (signedWidth width)) :
    (magnitudeWord raw (rawIsNegative raw)).toNat = rawMagnitude raw := by
  unfold magnitudeWord rawMagnitude
  by_cases negative : rawIsNegative raw = true
  · simp only [negative, if_true]
    exact complementIncrement_toNat raw (rawIsNegative_true_toNat_pos raw negative)
  · simp only [negative, Bool.false_eq_true, if_false]

/-- The actual selector yields the original magnitude after its preceding classification. -/
theorem signedMagnitude_original_value
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (store : Store ctx)
    (classified : (store.read negative).toBool = rawIsNegative (store.read raw)) :
    ((signedMagnitudeStep raw work negative store).1.read (signedRead work)).toNat =
      rawMagnitude (store.read raw) := by
  change ((magnitudeChoiceStep raw work (store.read negative) store).1.read
    (signedRead work)).toNat = _
  rw [magnitudeChoice_value, classified, magnitudeWord_original_toNat]

/-- Every actual branch preserves all reads outside its one work-word destination. -/
theorem magnitudeChoice_read_other (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (value : CShape.Value .bit)
    {shape : CShape} (other : CInputRef ctx shape) (separate : work.key ∉ other.storageKeys)
    (store : Store ctx) :
    (magnitudeChoiceStep raw work value store).1.read other = store.read other := by
  cases value with
  | bit value =>
      cases value
      · exact Store.read_applyOp_of_not_mem_storageKeys _
          (magnitudeCopyOp raw work) other separate
      · change (((store.applyOp (magnitudeCopyOp raw work)).applyOp
          (signUnaryOp .complement work)).applyOp (signUnaryOp .increment work)).read other = _
        rw [Store.read_applyOp_of_not_mem_storageKeys _
          (signUnaryOp .increment work) other separate,
          Store.read_applyOp_of_not_mem_storageKeys _
            (signUnaryOp .complement work) other separate,
          Store.read_applyOp_of_not_mem_storageKeys _ (magnitudeCopyOp raw work) other separate]

/-- The stored sign and all caller reads remain available after magnitude selection. -/
theorem signedMagnitude_read_other (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    {shape : CShape} (other : CInputRef ctx shape) (separate : work.key ∉ other.storageKeys)
    (store : Store ctx) :
    (signedMagnitudeStep raw work negative store).1.read other = store.read other :=
  magnitudeChoice_read_other raw work (store.read negative) other separate store

/-- Independent original copy-only or copy, complement, increment event sequence. -/
def signedMagnitudeEvents (kind : ProblemKind) (width : Nat) (negative : Bool) :
    List (Resource.Event kind) :=
  if negative then
    [.classicalOperation (.wordUnary .copy (signedWidth width)),
      .classicalOperation (.wordUnary .complement (signedWidth width)),
      .classicalOperation (.wordUnary .increment (signedWidth width))]
  else [.classicalOperation (.wordUnary .copy (signedWidth width))]

/-- The actual selected path emits precisely the original magnitude instructions. -/
theorem signedMagnitude_eventTrace (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude raw work negative).Path) :
    (signedMagnitude raw work negative).eventTrace path =
      signedMagnitudeEvents kind width path.1.toBool := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- The resource pool is obtained from the same selected true event trace. -/
theorem signedMagnitude_resourcePool (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude raw work negative).Path) :
    (signedMagnitude raw work negative).resourcePool path =
      ResourcePool.ofList (signedMagnitudeEvents kind width path.1.toBool) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Arbitrary native durations charge the selected sequential operations exactly. -/
theorem signedMagnitude_durationDepth (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (duration : Resource.Event kind → Nat) (path : (signedMagnitude raw work negative).Path) :
    (signedMagnitude raw work negative).depth duration path =
      ((signedMagnitudeEvents kind width path.1.toBool).map duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- The original branch has depth three on a negative sign and one otherwise. -/
theorem signedMagnitude_depth (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude raw work negative).Path) :
    (signedMagnitude raw work negative).depth (fun _ => 1) path =
      if path.1.toBool then 3 else 1 := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Both magnitude branches retain exactly the actual resident context. -/
theorem signedMagnitude_resident (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude raw work negative).Path) :
    (signedMagnitude raw work negative).peakResidentSpace path = ctx.residentSpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.residentSpace 0 = _
        exact SpacePool.max_zero _
      · change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace
          (SpacePool.max ctx.residentSpace 0)) = _
        simp only [SpacePool.max_zero, SpacePool.max_self]

/-- Both magnitude branches retain exactly the actual auxiliary context. -/
theorem signedMagnitude_auxiliary (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (work : CWriteRef ctx (.unsignedWord (signedWidth width))) (negative : CInputRef ctx .bit)
    (path : (signedMagnitude raw work negative).Path) :
    (signedMagnitude raw work negative).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change SpacePool.max ctx.auxiliarySpace 0 = _
        exact SpacePool.max_zero _
      · change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace
          (SpacePool.max ctx.auxiliarySpace 0)) = _
        simp only [SpacePool.max_zero, SpacePool.max_self]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
