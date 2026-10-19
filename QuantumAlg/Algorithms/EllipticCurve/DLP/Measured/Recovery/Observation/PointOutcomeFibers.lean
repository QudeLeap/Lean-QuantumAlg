/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.BankCompleteness

/-!
# Exact retained Store fibers of the actual point bank family

The complete interface Store contains the point outcome and two retained
frame Stores. Fixing those frame Stores gives exactly one interface Store for
each point outcome. This identifies the real outcome sum without counting
redundant frame values as extra Kraus labels. The original complete Store
remains a parameter, including all its retained classical correlations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace PointOutcomeFibers

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

private abbrev Inner (width : Nat) := Recovery.Point.indexedPointPlacement width (0 : Fin 2)

private abbrev Outer (width m : Nat) :=
  Recovery.Point.cellsPlacement (readyContext width 2) 2 (2 * m)

/-- Both complete frame Stores are retained beside the real point outcome. -/
abbrev FrameStores (width m : Nat) :=
  Store (Inner width).frame × Store (Outer width m).frame

/-- The two actual placement Store equivalences split the whole interface Store. -/
def storeCoordinates (width m : Nat) :
    Store (Interface width m) ≃
      Store (MeasuredPointAddition.context width) × FrameStores width m :=
  (Outer width m).store.trans
    ((((Inner width).store).prodCongr (Equiv.refl (Store (Outer width m).frame))).trans
      (Equiv.prodAssoc (Store (MeasuredPointAddition.context width))
        (Store (Inner width).frame) (Store (Outer width m).frame)))

/-- The first coordinate is exactly the final point Store used by Rows.bankBlock. -/
lemma storeCoordinates_point (width m : Nat) (stored : Store (Interface width m)) :
    (storeCoordinates width m stored).1 =
      ((Inner width).store ((Outer width m).store stored).1).1 := rfl

/-- The actual retains predicate fixes the entire pair of frame Stores. -/
lemma retains_iff_frame (width m : Nat) (stored original : Store (Interface width m)) :
    Recovery.Stage.retains width m stored original ↔
      (storeCoordinates width m stored).2 = (storeCoordinates width m original).2 := by
  change
    ((storeCoordinates width m original).2.1 = (storeCoordinates width m stored).2.1 ∧
      (storeCoordinates width m original).2.2 = (storeCoordinates width m stored).2.2) ↔ _
  constructor
  · intro same
    exact Prod.ext same.1.symm same.2.symm
  · intro same
    exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm⟩

/-- Every real point outcome has one full interface Store with the original retained frame. -/
def retainedStoreEquiv (width m : Nat) (original : Store (Interface width m)) :
    {stored : Store (Interface width m) // Recovery.Stage.retains width m stored original} ≃
      Store (MeasuredPointAddition.context width) where
  toFun stored := (storeCoordinates width m stored.val).1
  invFun finalStore :=
    ⟨(storeCoordinates width m).symm (finalStore, (storeCoordinates width m original).2), by
      apply (retains_iff_frame width m _ original).mpr
      have actual := (storeCoordinates width m).apply_symm_apply
        (finalStore, (storeCoordinates width m original).2)
      have retained := congrArg Prod.snd actual
      exact retained⟩
  left_inv stored := by
    apply Subtype.ext
    apply (storeCoordinates width m).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext rfl ((retains_iff_frame width m stored.val original).mp stored.property).symm
  right_inv finalStore :=
    congrArg Prod.fst ((storeCoordinates width m).apply_symm_apply
      (finalStore, (storeCoordinates width m original).2))

/-- Rows.bankBlock uses the real point outcome and retains the full quantum complement. -/
lemma bankBlock_projection {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Interface p.size m)) (control : Fin 2) :
    Recovery.Stage.PointCoordinates.bankBlock (environment := environment) E Q m Reference
      divisionStore stored control =
      Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q
        (Recovery.Stage.PointCoordinates.ResidualReference p.size m Reference)
        divisionStore (storeCoordinates p.size m stored).1 control := rfl

/-- Summing the exact retained interface fiber counts each real point outcome once. -/
lemma bankBlock_retained_sum_complete {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (original : Store (Interface p.size m)) (control : Fin 2) :
    ∑ stored : {stored : Store (Interface p.size m) //
        Recovery.Stage.retains p.size m stored original},
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        (Recovery.Stage.PointCoordinates.bankBlock (environment := environment) E Q m Reference
          divisionStore
          stored.val control).conjTranspose *
          Recovery.Stage.PointCoordinates.bankBlock (environment := environment) E Q m Reference
            divisionStore
            stored.val control = 1 := by
  simp only [bankBlock_projection]
  change (∑ stored : {stored : Store (Interface p.size m) //
      Recovery.Stage.retains p.size m stored original},
    ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
      (Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q
        (Recovery.Stage.PointCoordinates.ResidualReference p.size m Reference) divisionStore
        (retainedStoreEquiv p.size m original stored) control).conjTranspose *
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q
          (Recovery.Stage.PointCoordinates.ResidualReference p.size m Reference) divisionStore
          (retainedStoreEquiv p.size m original stored) control) = 1
  rw [(retainedStoreEquiv p.size m original).sum_comp (fun finalStore =>
    ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
      (Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q
        (Recovery.Stage.PointCoordinates.ResidualReference p.size m Reference) divisionStore
        finalStore control).conjTranspose *
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q
          (Recovery.Stage.PointCoordinates.ResidualReference p.size m Reference) divisionStore
          finalStore control)]
  exact BankCompleteness.pointBankBlock_complete E Q
    (Recovery.Stage.PointCoordinates.ResidualReference p.size m Reference) control

end

end PointOutcomeFibers
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
