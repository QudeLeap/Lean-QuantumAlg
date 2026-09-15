/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Access
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Access
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Store

/-!
# The original finite-cyclic borrowed target in the actual store

The sole borrowed word has the original deterministic key and the original
shared encoding. Its actual store carrier contains exactly that input. No
sample, candidate table, power table or quantum initialization is admitted as
an input. The target may be the encoded identity as in the original domain.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Deterministic key of the sole borrowed classical input. -/
def targetKey : StorageKey :=
  RuntimeCtx.canonicalFreshKey (RuntimeCtx.empty : RuntimeCtx .quantum)

theorem targetFresh :
    targetKey ∉ (RuntimeCtx.empty : RuntimeCtx .quantum).keys :=
  RuntimeCtx.canonicalFreshKey_fresh _

/-- The endpoint starts with one borrowed encoded target word.  Candidate and
group-power tables are absent. -/
@[reducible] public def pre (P : KnownOrderProblem G) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput targetKey
    (.unsignedWord (orderWidth P)) targetFresh

/-- Structural reference to the sole borrowed target word. -/
def targetRef (P : KnownOrderProblem G) :
    CInputRef (pre P) (.unsignedWord (orderWidth P)) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty targetKey
    (.unsignedWord (orderWidth P)) targetFresh)

/-- The target uses the same word encoder as the declared group operations. -/
def targetValue {P : KnownOrderProblem G} (A : Access P) :
    CShape.Value (.unsignedWord (orderWidth P)) :=
  A.recovery.encode P.target

theorem targetValue_eq_quantumEncoding {P : KnownOrderProblem G} (A : Access P) :
    targetValue A = CShape.Value.unsignedWord (A.ux.encode P.target) :=
  A.recovery_encode P.target

/-- The shared recovery encoding is injective because it is definitionally
tied to the injective quantum-oracle encoding. -/
theorem recovery_encode_injective {P : KnownOrderProblem G} (A : Access P) :
    Function.Injective A.recovery.encode := by
  intro left right encoded
  apply A.ux.encode_injective
  apply CShape.Value.unsignedWord.inj
  calc
    CShape.Value.unsignedWord (A.ux.encode left) = A.recovery.encode left :=
      (A.recovery_encode left).symm
    _ = A.recovery.encode right := encoded
    _ = CShape.Value.unsignedWord (A.ux.encode right) :=
      A.recovery_encode right

/-- The unique endpoint input store contains no candidate or power table. -/
def inputStore {P : KnownOrderProblem G} (A : Access P) : Execution.Store (pre P) :=
  ⟨targetValue A, ()⟩

@[simp]
theorem inputStore_target {P : KnownOrderProblem G} (A : Access P) :
    (inputStore A).read (targetRef P) = targetValue A :=
  rfl

/-- The original single borrowed word supplies no quantum input bank. -/
theorem input_quantumWires (P : KnownOrderProblem G) : (pre P).quantumWires = [] := rfl

/-- Every borrowed quantum coordinate is empty at the original input boundary. -/
theorem input_noBorrowedQuantum (P : KnownOrderProblem G) :
    (pre P).borrowedQuantumWires = [] := rfl

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
