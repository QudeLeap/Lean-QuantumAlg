/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Circuit.Associativity
import all QuantumAlg.Core.Execution.Circuit.OperationalEquiv

/-!
# Structural reassociation of the same actual circuit

These certificates change only sequence parentheses and literal code
equalities. They retain every actual section and its intermediate boundary.
Their full execution equivalence follows from the existing interpreter laws.
No arbitrary equivalence of final channels is a constructor.
-/

namespace QuantumAlg.Circuit

noncomputable section

/-- The same typed instructions, regrouped solely by sequential associativity
and literal equality. Intermediate computation sections remain actual sections. -/
public inductive Reassociation {model : ExecutionModel} :
    {pre post : RuntimeCtx model.kind} → Circuit model pre post →
      Circuit model pre post → Type 1 where
  | refl {pre post : RuntimeCtx model.kind} (code : Circuit model pre post) :
      Reassociation code code
  | ofEq {pre post : RuntimeCtx model.kind} {source target : Circuit model pre post}
      (same : source = target) : Reassociation source target
  | seqAssoc {pre middle₁ middle₂ post : RuntimeCtx model.kind}
      (first : Circuit model pre middle₁) (middle : Circuit model middle₁ middle₂)
      (last : Circuit model middle₂ post) :
      Reassociation ((first.seq middle).seq last) (first.seq (middle.seq last))
  | symm {pre post : RuntimeCtx model.kind} {source target : Circuit model pre post}
      (original : Reassociation source target) : Reassociation target source
  | trans {pre post : RuntimeCtx model.kind} {source middle target : Circuit model pre post}
      (left : Reassociation source middle) (right : Reassociation middle target) :
      Reassociation source target
  | seq {pre middle post : RuntimeCtx model.kind}
      {first changedFirst : Circuit model pre middle}
      {second changedSecond : Circuit model middle post}
      (left : Reassociation first changedFirst) (right : Reassociation second changedSecond) :
      Reassociation (first.seq second) (changedFirst.seq changedSecond)

namespace Reassociation

/-- Structural certificates retain full weighted states, events, chronological
depth and both live-space peaks on the corresponding actual paths. -/
def toOperationalEquiv {model : ExecutionModel} :
    {pre post : RuntimeCtx model.kind} → {source target : Circuit model pre post} →
      Reassociation source target → OperationalEquiv source target
  | _, _, _, _, .refl code => OperationalEquiv.refl code
  | _, _, _, _, .ofEq same => by cases same; exact OperationalEquiv.refl _
  | _, _, _, _, .seqAssoc first middle last => seqAssocOperationalEquiv first middle last
  | _, _, _, _, .symm original => original.toOperationalEquiv.symm
  | _, _, _, _, .trans left right => left.toOperationalEquiv.trans right.toOperationalEquiv
  | _, _, _, _, .seq left right =>
      (left.toOperationalEquiv.append _).trans
        (OperationalEquiv.prepend _ right.toOperationalEquiv)

/-- The exact bijection of actual measurement and branch histories under regrouping. -/
public def path {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {source target : Circuit model pre post} (association : Reassociation source target) :
    source.Path ≃ target.Path := association.toOperationalEquiv.path

/-- Regrouping retains the complete original dependency depth on every path. -/
public theorem reassociation_depth_eq {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {source target : Circuit model pre post}
    (association : Reassociation source target) (duration : Resource.Event model → Nat)
    (sourcePath : source.Path) :
    source.depth duration sourcePath = target.depth duration (association.path sourcePath) :=
  association.toOperationalEquiv.depth duration sourcePath

end Reassociation

end

end QuantumAlg.Circuit
