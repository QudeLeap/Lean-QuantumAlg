/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws

/-!
# Borrowed public point values beside the reduced streaming terminal

Both identity-inclusive public points are present in a genuine borrowed
classical frame. Their keys are chosen successively beyond every live entry
of `ECCCaller.terminal p.size m`, including when `m = 0`. Joining this frame
retains the complete original Store and charges both public point shapes.
No circuit, physical initialization, instrument equality or peak-space claim
is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)

private def pointShape : CShape := ECDLP.Canonical.Runtime.Context.PointShape E

/-- The first public identity is fresh beyond the actual reduced terminal. -/
def baseKey : StorageKey := (Recovery.Layout.terminal p.size m).canonicalFreshKey

lemma baseKey_fresh : baseKey (p := p) m ∉ (Recovery.Layout.terminal p.size m).keys :=
  (Recovery.Layout.terminal p.size m).canonicalFreshKey_fresh

private def reservedBase : RuntimeCtx .quantum :=
  (Recovery.Layout.terminal p.size m).addBorrowedInput (baseKey (p := p) m) (pointShape E)
    (baseKey_fresh (p := p) m)

/-- The second identity is fresh after reserving the first public point. -/
def targetKey : StorageKey := (reservedBase E m).canonicalFreshKey

lemma targetKey_fresh_reserved : targetKey E m ∉ (reservedBase E m).keys :=
  (reservedBase E m).canonicalFreshKey_fresh

lemma targetKey_fresh : targetKey E m ∉ (Recovery.Layout.terminal p.size m).keys := by
  have fresh := targetKey_fresh_reserved E m
  change targetKey E m ∉ baseKey (p := p) m :: (Recovery.Layout.terminal p.size m).keys at fresh
  exact fun present => fresh (List.mem_cons_of_mem _ present)

lemma keys_distinct : targetKey E m ≠ baseKey (p := p) m := by
  intro same
  apply targetKey_fresh_reserved E m
  change targetKey E m ∈ baseKey (p := p) m :: (Recovery.Layout.terminal p.size m).keys
  exact List.mem_cons.mpr (Or.inl same)

private lemma empty_fresh :
    baseKey (p := p) m ∉ (RuntimeCtx.empty : RuntimeCtx .quantum).keys := by
  change baseKey (p := p) m ∉ []
  simp

private def baseContext : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput (baseKey (p := p) m) (pointShape E)
    (empty_fresh (p := p) m)

private lemma baseContext_fresh : targetKey E m ∉ (baseContext E m).keys := by
  change targetKey E m ∉ [baseKey (p := p) m]
  exact fun present => keys_distinct E m (List.mem_singleton.mp present)

/-- Two original public values, with borrowed roles and genuinely fresh keys. -/
def frame : RuntimeCtx .quantum :=
  (baseContext E m).addBorrowedInput (targetKey E m) (pointShape E) (baseContext_fresh E m)

lemma frame_keys : (frame E m).keys = [targetKey E m, baseKey (p := p) m] := rfl

lemma frame_quantumWires : (frame E m).quantumWires = [] := rfl

lemma frame_physicalIdx : (frame E m).physicalIdx = [] := rfl

lemma frame_systemCount : (frame E m).systemCount = 0 := rfl

/-- Both borrowed point encodings contribute their full resident classical capacity. -/
lemma frame_resident : (frame E m).residentSpace =
    2 • SpacePool.ofShape (ECDLP.Canonical.Runtime.Context.PointShape E) := by
  rw [frame, RuntimeCtx.residentSpace_addBorrowedInput, baseContext,
    RuntimeCtx.residentSpace_addBorrowedInput]
  change SpacePool.ofShape (pointShape E) + (SpacePool.ofShape (pointShape E) + 0) = _
  rw [add_zero, two_nsmul]
  rfl

lemma frame_auxiliary : (frame E m).auxiliarySpace = 0 := rfl

/-- No original classical key or physical quantum identity conflicts with either point. -/
lemma terminal_disjoint :
    RuntimeCtx.StorageDisjoint (Recovery.Layout.terminal p.size m) (frame E m) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    rw [frame_keys]
    apply List.disjoint_left.mpr
    intro key original framed
    rcases List.mem_cons.mp framed with same | other
    · exact targetKey_fresh E m (same ▸ original)
    · exact baseKey_fresh (p := p) m ((List.mem_singleton.mp other) ▸ original)
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint (Recovery.Layout.terminal p.size m).physicalIdx []
    exact List.disjoint_nil_right _

def baseRef : CInputRef (frame E m) (ECDLP.Canonical.Runtime.Context.PointShape E) :=
  .storage ((CStorageRef.borrowedInputHead RuntimeCtx.empty (baseKey (p := p) m)
    (pointShape E) (empty_fresh (p := p) m)).underBorrowedInput
      (targetKey E m) (pointShape E) (baseContext_fresh E m))

def targetRef : CInputRef (frame E m) (ECDLP.Canonical.Runtime.Context.PointShape E) :=
  .storage (CStorageRef.borrowedInputHead (baseContext E m)
    (targetKey E m) (pointShape E) (baseContext_fresh E m))

/-- Values include infinity and are supplied before any enclosing execution. -/
def store (base target : E.MathlibPoint) : Store (frame E m) :=
  ⟨(ECDLP.Canonical.Runtime.Context.pointValue E target,
    (ECDLP.Canonical.Runtime.Context.pointValue E base, ()))⟩

lemma store_base (base target : E.MathlibPoint) :
    (store E m base target).read (baseRef E m) =
      ECDLP.Canonical.Runtime.Context.pointValue E base := rfl

lemma store_target (base target : E.MathlibPoint) :
    (store E m base target).read (targetRef E m) =
      ECDLP.Canonical.Runtime.Context.pointValue E target := rfl

/-- The actual combined context retains the terminal and both borrowed public cells. -/
def context : RuntimeCtx .quantum :=
  (Recovery.Layout.terminal p.size m).disjointUnion (frame E m) (terminal_disjoint E m)

lemma context_resident : (context E m).residentSpace =
    (Recovery.Layout.terminal p.size m).residentSpace +
      2 • SpacePool.ofShape (ECDLP.Canonical.Runtime.Context.PointShape E) := by
  rw [context, RuntimeCtx.residentSpace_disjointUnion, frame_resident]

lemma context_auxiliary : (context E m).auxiliarySpace =
    (Recovery.Layout.terminal p.size m).auxiliarySpace := by
  rw [context, RuntimeCtx.auxiliarySpace_disjointUnion, frame_auxiliary, add_zero]

lemma context_physicalIdx : (context E m).physicalIdx =
    (Recovery.Layout.terminal p.size m).physicalIdx := by
  rw [context, RuntimeCtx.physicalIdx_disjointUnion, frame_physicalIdx, List.append_nil]

def contextBaseRef : CInputRef (context E m) (ECDLP.Canonical.Runtime.Context.PointShape E) :=
  ContextUnion.inputRight (terminal_disjoint E m) (baseRef E m)

def contextTargetRef : CInputRef (context E m) (ECDLP.Canonical.Runtime.Context.PointShape E) :=
  ContextUnion.inputRight (terminal_disjoint E m) (targetRef E m)

/-- Joining existing Stores neither creates nor discards any original cell value. -/
def joinStore (original : Store (Recovery.Layout.terminal p.size m)) (base target :
  E.MathlibPoint) :
    Store (context E m) :=
  ContextUnion.join (terminal_disjoint E m) original (store E m base target)

lemma joinStore_base (original : Store (Recovery.Layout.terminal p.size m))
    (base target : E.MathlibPoint) :
    (joinStore E m original base target).read (contextBaseRef E m) =
      ECDLP.Canonical.Runtime.Context.pointValue E base :=
  (ContextUnion.contextUnion_read_join_right (terminal_disjoint E m) original
    (store E m base target) (baseRef E m)).trans (store_base E m base target)

lemma joinStore_target (original : Store (Recovery.Layout.terminal p.size m))
    (base target : E.MathlibPoint) :
    (joinStore E m original base target).read (contextTargetRef E m) =
      ECDLP.Canonical.Runtime.Context.pointValue E target :=
  (ContextUnion.contextUnion_read_join_right (terminal_disjoint E m) original
    (store E m base target) (targetRef E m)).trans (store_target E m base target)

/-- Every structural original read retains its exact value in the combined Store. -/
lemma joinStore_terminal (original : Store (Recovery.Layout.terminal p.size m))
    (base target : E.MathlibPoint) {shape : CShape}
    (input : CInputRef (Recovery.Layout.terminal p.size m) shape) :
    (joinStore E m original base target).read
        (ContextUnion.inputLeft (terminal_disjoint E m) input) = original.read input :=
  ContextUnion.contextUnion_read_join_left (terminal_disjoint E m) original
    (store E m base target) input

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
