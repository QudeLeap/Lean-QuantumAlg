/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Conditional
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Inputs

/-!
# Original-data support through the same actual fresh-feedback preparation

The real enclosing factory supplies the two borrowed nominal point storage
references. Its retained and fresh transports preserve those exact reads,
the four original arithmetic words and the joint signed x/y base arrays.
The same preparation preserves their supported properties on every positive
complete block, with arbitrary incoming History, HiddenState and Reference.
No candidate-mass or sampling Born assertion is made here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution Locality ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.WindowTables
open ClassicalRoutines.Modular.NativePower

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

attribute [local irreducible] Inputs.preparation Conditional.inputsSupported

private lemma actual_point_property {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (sampler : Parameters ctx) {width : Nat}
    (observed : CStorageRef ctx (.ellipticCurvePoint width))
    (property : CShape.Value (.ellipticCurvePoint width) → Prop)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      property (entry.1.read (.storage observed))) :
    ∀ entry, 0 < (((original.preparation (services := services) sampler).execute
      environment Reference state).block entry).mass →
      property (entry.1.read (.storage observed)) := by
  classical
  have actual := original.preparation_point_support (ctx := ctx) (services := services)
    sampler observed
    (fun value => decide (property value)) true environment state
    (fun entry positive => by simpa only [decide_eq_true_eq] using supported entry positive)
  intro entry positive
  exact of_decide_eq_true (actual entry positive)

private lemma actual_word_property {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (sampler : Parameters ctx) {width : Nat}
    (observed : CStorageRef ctx (.unsignedWord width))
    (originalWord : observed.key ∈ frameInputKeys sampler.frame)
    (property : CShape.Value (.unsignedWord width) → Prop)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      property (entry.1.read (.storage observed))) :
    ∀ entry, 0 < (((original.preparation (services := services) sampler).execute
      environment Reference state).block entry).mass →
      property (entry.1.read (.storage observed)) := by
  classical
  have actual := original.preparation_word_support (ctx := ctx) (services := services)
    sampler observed originalWord
    (fun value => decide (property value)) true environment state
    (fun entry positive => by simpa only [decide_eq_true_eq] using supported entry positive)
  intro entry positive
  exact of_decide_eq_true (actual entry positive)

private lemma actual_array_pair_property {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx) (sampler : Parameters ctx)
    {width length : Nat}
    (first second : CStorageRef ctx (.fixedVector length (.unsignedWord width)))
    (property : CShape.Value (.fixedVector length (.unsignedWord width)) →
      CShape.Value (.fixedVector length (.unsignedWord width)) → Prop)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      property (entry.1.read (.storage first)) (entry.1.read (.storage second))) :
    ∀ entry, 0 < (((original.preparation (services := services) sampler).execute
      environment Reference state).block entry).mass →
      property (entry.1.read (.storage first)) (entry.1.read (.storage second)) := by
  classical
  have actual := original.preparation_array_pair_support (ctx := ctx) (services := services)
    sampler first second
    (fun xs ys => decide (property xs ys)) true environment state
    (fun entry positive => by simpa only [decide_eq_true_eq] using supported entry positive)
  intro entry positive
  exact of_decide_eq_true (actual entry positive)


namespace Inputs

private lemma frameInputKeys_transport {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {width : Nat} (frame : Outer.Frame outer width)
    (lift : Transport outer inner) :
    frameInputKeys (frame.transport lift) = frameInputKeys frame := by
  simp only [frameInputKeys, Outer.Frame.transport, Transport.liftWrite_key]

private lemma transported_frame_member {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {width : Nat}
    (source : Outer.Frame outer width) (target : Outer.Frame inner width)
    (lift : Transport outer inner) (same : target = source.transport lift)
    {shape : CShape} (observed : CStorageRef outer shape)
    (member : observed.key ∈ frameInputKeys source) :
    (lift.liftStorage observed).key ∈ frameInputKeys target := by
  rw [same, frameInputKeys_transport, Transport.liftStorage_key]
  exact member

private lemma frame_modulus_member {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (frame : Outer.Frame ctx width) :
    frame.modulus.key ∈ frameInputKeys frame := List.Mem.head _

private lemma frame_zero_member {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (frame : Outer.Frame ctx width) :
    frame.zero.key ∈ frameInputKeys frame := List.Mem.tail _ (List.Mem.head _)

private lemma frame_one_member {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (frame : Outer.Frame ctx width) :
    frame.one.key ∈ frameInputKeys frame :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private lemma frame_curveA_member {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat} (frame : Outer.Frame ctx width) :
    frame.curveA.key ∈ frameInputKeys frame :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private lemma lifted_storage_property {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {shape : CShape} (lift : Transport outer inner)
    (input : CInputRef outer shape) (stored : CStorageRef outer shape)
    (same : input = .storage stored) (store : Store inner)
    (property : CShape.Value shape → Prop) :
    property (store.read (lift.liftInput input)) ↔
      property (store.read (.storage (lift.liftStorage stored))) := by
  cases same
  rfl

private def modulusProperty {width : Nat} (curve : CurveSpec width)
    (value : CShape.Value (.unsignedWord (width + 1))) : Prop :=
  value = .unsignedWord curve.field.extendedWord

private def curveAProperty {width : Nat} (curve : CurveSpec width)
    (value : CShape.Value (.unsignedWord width)) : Prop :=
  (value.toNat : ZMod curve.field.modulus) = curve.curve.a

attribute [local irreducible] modulusProperty curveAProperty

private def preparedProperty {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (current : Inputs ctx) (sampler : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (property : Store ctx → Prop) : Prop :=
  ∀ entry, 0 < (((current.preparation (services := services) sampler).execute
    environment Reference state).block entry).mass → property entry.1

attribute [local irreducible] preparedProperty

private def preparationPreserves {outer inner : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs outer) (current : Inputs inner)
    (sampler : Parameters inner) (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (property : Store inner → Prop) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)),
    Conditional.inputsSupported original lift basePoint targetPoint state →
    preparedProperty (ctx := inner) (services := services) current sampler environment state
      property

attribute [local irreducible] preparationPreserves

section

variable {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (current : Inputs inner) (sampler : Parameters inner)
    (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private lemma preparation_preserves_points
    (baseStorage targetStorage : CStorageRef outer (.ellipticCurvePoint 256))
    (baseSame : original.base = .storage baseStorage)
    (targetSame : original.target = .storage targetStorage) :
    preparationPreserves (services := services) original current sampler lift
      basePoint targetPoint environment (fun store =>
        PointRepresents original.curve (store.read (lift.liftInput original.base)) basePoint ∧
        PointRepresents original.curve
          (store.read (lift.liftInput original.target)) targetPoint) := by
  unfold preparationPreserves
  intro Reference History finite state supported
  unfold preparedProperty
  unfold Conditional.inputsSupported at supported
  have baseSupport := actual_point_property (ctx := inner) (services := services)
    current sampler (lift.liftStorage baseStorage)
    (fun value => PointRepresents original.curve value basePoint) environment state
    (by
      intro entry positive
      have fact := (supported entry positive).1.1
      exact (lifted_storage_property lift original.base baseStorage baseSame entry.1
        (fun value => PointRepresents original.curve value basePoint)).mp fact)
  have targetSupport := actual_point_property (ctx := inner) (services := services)
    current sampler (lift.liftStorage targetStorage)
    (fun value => PointRepresents original.curve value targetPoint) environment state
    (by
      intro entry positive
      have fact := (supported entry positive).1.2
      exact (lifted_storage_property lift original.target targetStorage targetSame entry.1
        (fun value => PointRepresents original.curve value targetPoint)).mp fact)
  intro entry positive
  constructor
  · exact (lifted_storage_property lift original.base baseStorage baseSame entry.1
      (fun value => PointRepresents original.curve value basePoint)).mpr
        (baseSupport entry positive)
  · exact (lifted_storage_property lift original.target targetStorage targetSame entry.1
      (fun value => PointRepresents original.curve value targetPoint)).mpr
        (targetSupport entry positive)

private lemma preparation_preserves_modulus
    (frameSame : sampler.frame = original.frame.transport lift) :
    preparationPreserves (services := services) original current sampler lift
      basePoint targetPoint environment (fun store =>
        modulusProperty original.curve
          (store.read (lift.liftInput (wordRead original.frame.modulus)))) := by
  unfold preparationPreserves
  intro Reference History finite state supported
  unfold preparedProperty
  unfold Conditional.inputsSupported at supported
  let observed : CStorageRef inner (.unsignedWord 257) :=
    @Transport.liftStorage .quantum outer inner lift (.unsignedWord 257)
      original.frame.modulus.toCStorageRef
  have member : observed.key ∈ frameInputKeys sampler.frame :=
    transported_frame_member original.frame sampler.frame lift frameSame
      original.frame.modulus.toCStorageRef (frame_modulus_member original.frame)
  exact actual_word_property (ctx := inner) (services := services) current sampler observed member
    (modulusProperty original.curve) environment state
    (by
      intro entry positive
      unfold modulusProperty
      exact (supported entry positive).2.1)

private lemma preparation_preserves_zero
    (frameSame : sampler.frame = original.frame.transport lift) :
    preparationPreserves (services := services) original current sampler lift
      basePoint targetPoint environment (fun store =>
        (store.read (lift.liftInput (.storage original.frame.zero.toCStorageRef))).toNat = 0) := by
  unfold preparationPreserves
  intro Reference History finite state supported
  unfold preparedProperty
  unfold Conditional.inputsSupported at supported
  let observed : CStorageRef inner (.unsignedWord 256) :=
    @Transport.liftStorage .quantum outer inner lift (.unsignedWord 256)
      original.frame.zero.toCStorageRef
  have member : observed.key ∈ frameInputKeys sampler.frame :=
    transported_frame_member original.frame sampler.frame lift frameSame
      original.frame.zero.toCStorageRef (frame_zero_member original.frame)
  exact actual_word_property (ctx := inner) (services := services) current sampler observed member
    (fun value => value.toNat = 0) environment state
    (fun entry positive => (supported entry positive).2.2.1)

private lemma preparation_preserves_one
    (frameSame : sampler.frame = original.frame.transport lift) :
    preparationPreserves (services := services) original current sampler lift
      basePoint targetPoint environment (fun store =>
        (store.read (lift.liftInput (.storage original.frame.one.toCStorageRef))).toNat = 1) := by
  unfold preparationPreserves
  intro Reference History finite state supported
  unfold preparedProperty
  unfold Conditional.inputsSupported at supported
  let observed : CStorageRef inner (.unsignedWord 256) :=
    @Transport.liftStorage .quantum outer inner lift (.unsignedWord 256)
      original.frame.one.toCStorageRef
  have member : observed.key ∈ frameInputKeys sampler.frame :=
    transported_frame_member original.frame sampler.frame lift frameSame
      original.frame.one.toCStorageRef (frame_one_member original.frame)
  exact actual_word_property (ctx := inner) (services := services) current sampler observed member
    (fun value => value.toNat = 1) environment state
    (fun entry positive => (supported entry positive).2.2.2.1)

private lemma preparation_preserves_curveA
    (frameSame : sampler.frame = original.frame.transport lift) :
    preparationPreserves (services := services) original current sampler lift
      basePoint targetPoint environment (fun store =>
        curveAProperty original.curve
          (store.read (lift.liftInput (.storage original.frame.curveA.toCStorageRef)))) := by
  unfold preparationPreserves
  intro Reference History finite state supported
  unfold preparedProperty
  unfold Conditional.inputsSupported at supported
  let observed : CStorageRef inner (.unsignedWord 256) :=
    @Transport.liftStorage .quantum outer inner lift (.unsignedWord 256)
      original.frame.curveA.toCStorageRef
  have member : observed.key ∈ frameInputKeys sampler.frame :=
    transported_frame_member original.frame sampler.frame lift frameSame
      original.frame.curveA.toCStorageRef (frame_curveA_member original.frame)
  exact actual_word_property (ctx := inner) (services := services) current sampler observed member
    (curveAProperty original.curve) environment state
    (by
      intro entry positive
      unfold curveAProperty
      exact (supported entry positive).2.2.2.2.1)

private lemma preparation_preserves_rows :
    preparationPreserves (services := services) original current sampler lift
      basePoint targetPoint environment (fun store =>
        Conditional.rowReadConditions original basePoint targetPoint
      (fun input => store.read (lift.liftInput input))) := by
  unfold preparationPreserves
  intro Reference History finite state supported
  unfold preparedProperty
  unfold Conditional.inputsSupported at supported
  have preserved := actual_array_pair_property (ctx := inner) (services := services)
    current sampler (lift.liftStorage original.frame.x.toCStorageRef)
    (lift.liftStorage original.frame.y.toCStorageRef)
    (Conditional.signedRows original.curve basePoint targetPoint) environment state
    (by
      intro entry positive
      have data := (supported entry positive).2.2.2.2.2
      simpa only [Conditional.rowReadConditions, Conditional.actualArraysRead,
        Transport.liftInput, CInputRef.mapStorage] using data)
  intro entry positive
  simpa only [Conditional.rowReadConditions, Conditional.actualArraysRead,
        Transport.liftInput, CInputRef.mapStorage] using
    preserved entry positive

private lemma preparation_support_of_frame
    (frameSame : sampler.frame = original.frame.transport lift)
    (baseStorage targetStorage : CStorageRef outer (.ellipticCurvePoint 256))
    (baseSame : original.base = .storage baseStorage)
    (targetSame : original.target = .storage targetStorage) :
    preparationPreserves (services := services) original current sampler lift
      basePoint targetPoint environment (fun store =>
        Conditional.readConditions original basePoint targetPoint
        (fun input => store.read (lift.liftInput input))) := by
  unfold preparationPreserves
  intro Reference History finite state supported
  unfold preparedProperty
  intro entry positive
  unfold Conditional.readConditions
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have component := preparation_preserves_points (services := services)
      original current sampler lift
      basePoint targetPoint environment baseStorage targetStorage
      baseSame targetSame
    unfold preparationPreserves preparedProperty at component
    exact @component Reference History finite state supported entry positive
  · have component := preparation_preserves_modulus (services := services)
      original current sampler lift
      basePoint targetPoint environment frameSame
    unfold preparationPreserves preparedProperty at component
    have fact := @component Reference History finite state supported entry positive
    unfold modulusProperty at fact
    exact fact
  · have component := preparation_preserves_zero (services := services)
      original current sampler lift
      basePoint targetPoint environment frameSame
    unfold preparationPreserves preparedProperty at component
    exact @component Reference History finite state supported entry positive
  · have component := preparation_preserves_one (services := services)
      original current sampler lift
      basePoint targetPoint environment frameSame
    unfold preparationPreserves preparedProperty at component
    exact @component Reference History finite state supported entry positive
  · have component := preparation_preserves_curveA (services := services)
      original current sampler lift
      basePoint targetPoint environment frameSame
    unfold preparationPreserves preparedProperty at component
    have fact := @component Reference History finite state supported entry positive
    unfold curveAProperty at fact
    exact fact
  · have component := preparation_preserves_rows (services := services)
      original current sampler lift
      basePoint targetPoint environment
    unfold preparationPreserves preparedProperty at component
    exact @component Reference History finite state supported entry positive

end

private lemma currentSampler_frame {outer inner : RuntimeCtx .quantum}
    (original : Inputs outer)
    (lift : Transport (CandidateCheck.Native.persistentCtx outer 256 260) inner)
    (same : (CandidateCheck.Native.persistentCtx outer 256 260).quantumLayout.wires =
      inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift) :
    (@currentSampler outer inner original lift same scratch fresh).frame =
      original.frame.transport ((Recovery.persistentTransport outer).compose lift) := rfl

attribute [local irreducible] currentInput currentSampler

/-- The actual stored-point construction supplies the complete internal preparation invariant. -/
lemma internal_preparation_of_stored_points {outer : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs outer)
    (baseStorage targetStorage : CStorageRef outer (.ellipticCurvePoint 256))
    (baseSame : original.base = .storage baseStorage)
    (targetSame : original.target = .storage targetStorage)
    (basePoint targetPoint : Pure.Point original.curve)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    original.InternalPreparation environment basePoint targetPoint := by
  unfold InternalPreparation
  intro inner lift same scratch fresh
  unfold PreparedSupport
  intro Reference History finite state supported
  have preserved := preparation_support_of_frame (outer := outer) (inner := inner)
    (services := services) original
    (@currentInput outer inner original lift same)
    (@currentSampler outer inner original lift same scratch fresh)
    ((Recovery.persistentTransport outer).compose lift)
    basePoint targetPoint environment
    (currentSampler_frame original lift same scratch fresh)
    baseStorage targetStorage baseSame targetSame
  unfold preparationPreserves preparedProperty at preserved
  unfold CurrentSupport Conditional.inputsSupported
  exact @preserved Reference History finite state supported

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
