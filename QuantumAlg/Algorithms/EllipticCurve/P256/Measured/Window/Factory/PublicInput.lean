/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Prefix
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Parameters.Representation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Domain
import all QuantumAlg.Core.Execution.Input.Oracle

/-! # Paid preparation from the unchanged original public point domain -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.ClassicalAlgorithms.EllipticCurve

noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] PointRepresents Store.read Circuit.execute paidPrefix
  WindowTables.Outer.Frame.ofRetainedCells RetainedCells.references originalInputAfterTables
  storeFintype ExecutionState.mapClassical

/-- The exact original two-point borrowed frame, before any physical preparation. -/
def publicFrame (I : DomainParameters.PublicKeyInstance) : RuntimeCtx .quantum :=
  ECDLP.Measured.Recovery.PublicInput.frame (DomainParameters.curve I.curveCert)
    (Cascade.exponentWidth I)

/-- The original public input borrows only classical point cells. -/
lemma publicFrame_noQuantum (I : DomainParameters.PublicKeyInstance) :
    (publicFrame I).quantumWires = [] := rfl

/-- Only the type-level coordinate width is transported; the original base key is retained. -/
def publicBaseRef (I : DomainParameters.PublicKeyInstance) :
    CInputRef (publicFrame I) (PointShape 256) :=
  cast (congrArg (fun width => CInputRef (publicFrame I) (PointShape width))
    (originalFieldWidth_eq_256 I))
      (ECDLP.Measured.Recovery.PublicInput.baseRef (DomainParameters.curve I.curveCert)
        (Cascade.exponentWidth I))

/-- Only the type-level coordinate width is transported; the original target key is retained. -/
def publicTargetRef (I : DomainParameters.PublicKeyInstance) :
    CInputRef (publicFrame I) (PointShape 256) :=
  cast (congrArg (fun width => CInputRef (publicFrame I) (PointShape width))
    (originalFieldWidth_eq_256 I))
      (ECDLP.Measured.Recovery.PublicInput.targetRef (DomainParameters.curve I.curveCert)
        (Cascade.exponentWidth I))

private lemma read_width_cast {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {first second : Nat} (same : first = second) (store : Store ctx)
    (input : CInputRef ctx (PointShape first)) :
    store.read (cast (congrArg (fun width => CInputRef ctx (PointShape width)) same) input) =
      cast (congrArg (fun width => CShape.Value (PointShape width)) same) (store.read input) := by
  cases same
  rfl

private lemma original_point_read_represents (I : DomainParameters.PublicKeyInstance)
    {ctx : RuntimeCtx .quantum} (store : Store ctx)
    (input : CInputRef ctx
      (PointShape (ECDLP.Canonical.Layout.fieldWidth (DomainParameters.curve I.curveCert))))
    (point : (DomainParameters.curve I.curveCert).MathlibPoint)
    (value : store.read input =
      ECDLP.Canonical.Runtime.Context.pointValue (DomainParameters.curve I.curveCert) point) :
    PointRepresents (actualCurveSpec I)
      (store.read (cast (congrArg (fun width => CInputRef ctx (PointShape width))
        (originalFieldWidth_eq_256 I)) input)) point := by
  have changed := read_width_cast (originalFieldWidth_eq_256 I) store input
  have encoded := changed.trans
    (congrArg (fun stored : CShape.Value
        (PointShape (ECDLP.Canonical.Layout.fieldWidth (DomainParameters.curve I.curveCert))) =>
      cast (congrArg (fun width => CShape.Value (PointShape width))
        (originalFieldWidth_eq_256 I)) stored) value)
  exact (congrArg (fun stored => PointRepresents (actualCurveSpec I) stored point) encoded).mpr
    (actualCurveSpec_pointValue_represents I point)

/-- Record the original Store as history while preserving the supplied input. -/
def suppliedState (I : DomainParameters.PublicKeyInstance) {Reference : Register}
    (supplied : OracleInput .empty (publicFrame I) Reference) :
    State (publicFrame I) Reference (Unit × Store (publicFrame I)) :=
  supplied.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))

/-- The original domain supplies both nominal point representations at every actual input block. -/
lemma suppliedState_points (I : DomainParameters.PublicKeyInstance) {Reference : Register}
    (supplied : OracleInput .empty (publicFrame I) Reference)
    (valid : ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState)
    (entry : Store (publicFrame I) × (Unit × Store (publicFrame I)))
    (positive : 0 < ((suppliedState I supplied).block entry).mass) :
    PointRepresents (actualCurveSpec I) (entry.1.read (publicBaseRef I))
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib ∧
      PointRepresents (actualCurveSpec I) (entry.1.read (publicTargetRef I))
        I.publicKey.toMathlib := by
  have recorded : suppliedState I supplied =
      supplied.state.mapClassical (fun record => (record.1, (record.2, record.1))) := by
    unfold suppliedState
    exact ExecutionState.executionState_mapClassical_congr_decision supplied.state
      _ _ (fun _ => rfl) _ _
  rw [recorded] at positive
  obtain ⟨original, same, originalPositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff supplied.state
      (fun record => (record.1, (record.2, record.1))) entry).mp positive
  have values := valid original.1
    (supplied.caller_local_mass_pos_of_joint original originalPositive)
  have storeSame : original.1 = entry.1 := congrArg Prod.fst same
  rw [← storeSame]
  constructor
  · exact original_point_read_represents I original.1
      (ECDLP.Measured.Recovery.PublicInput.baseRef (DomainParameters.curve I.curveCert)
        (Cascade.exponentWidth I))
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib values.1
  · exact original_point_read_represents I original.1
      (ECDLP.Measured.Recovery.PublicInput.targetRef (DomainParameters.curve I.curveCert)
        (Cascade.exponentWidth I)) I.publicKey.toMathlib values.2

/-- Actual paid preparation supplies recovery support from the original input domain. -/
lemma public_paidPrefix_inputsSupported (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference)
    (valid : ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState) :
    Sampling.Storage.Conditional.inputsSupported
      (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
        (publicBaseRef I) (publicTargetRef I))
      (Transport.id (tableContext (publicFrame I) (publicFrame_noQuantum I)))
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
      ((paidPrefix (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
        (publicBaseRef I) (publicTargetRef I)).execute environment Reference
          (suppliedState I supplied)) := by
  apply paidPrefix_inputsSupported (publicFrame I) (publicFrame_noQuantum I) I
    (publicBaseRef I) (publicTargetRef I) ?_ environment Reference (suppliedState I supplied)
    (suppliedState_points I supplied valid)
  intro first second same
  have stores := ECDLP.Measured.Recovery.PublicInput.Support.frame_store_eq_of_borrowed_eq
    (DomainParameters.curve I.curveCert)
    (Cascade.exponentWidth I) first second same
  exact ⟨congrArg (fun store => store.read (publicBaseRef I)) stores,
    congrArg (fun store => store.read (publicTargetRef I)) stores⟩

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
