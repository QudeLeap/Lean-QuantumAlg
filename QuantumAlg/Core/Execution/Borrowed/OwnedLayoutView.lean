/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit.OwnedLayoutView
public import QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Context.OwnedLayoutView.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Circuit.OwnedLayoutView

/-!
# Borrowed restoration through scoped owned slices

The wrapper and original child have exactly the same borrowed restoration
obligation on their corresponding complete input states. Arbitrary external
references and every borrowed classical and quantum correlation remain joint.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

private lemma transportBorrowed_injective {sourceShape targetShape : CShape}
    {sourceRegister targetRegister : Register} (Reference : Register)
    (sameShape : sourceShape = targetShape) (sameRegister : sourceRegister = targetRegister) :
    Function.Injective (transportBorrowed Reference sameShape sameRegister) := by
  cases sameShape
  cases sameRegister
  exact fun _ _ same => same

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {original viewed : RuntimeCtx .quantum} {allowAllocation : Bool}
  (view : OwnedLayoutView original viewed)
  (body : Circuit (.quantum gates oracles operations services) viewed viewed false)

/-- Regrouping preserves exactly the child's complete borrowed restoration relation. -/
public lemma borrowedRestored_ownedLayoutView_iff
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State original Reference (services.HiddenState × H)) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).BorrowedRestored
      Reference state ((Circuit.ownedLayoutView (allowAllocation := allowAllocation)
        view body).execute environment Reference state) ↔
      body.BorrowedRestored Reference (view.split state)
        (body.execute environment Reference (view.split state)) := by
  simp only [BorrowedRestored, observeBorrowedAfter_sameContext, execute_ownedLayoutView,
    view.observeBorrowed_join]
  rw [← view.observeBorrowed_split state]
  exact (transportBorrowed_injective Reference view.borrowedShape_eq.symm
    view.borrowedRegister_eq.symm).eq_iff

/-- Restoring the child restores the same physical borrowed interface at the caller boundary. -/
lemma borrowedRestored_ownedLayoutView
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State original Reference (services.HiddenState × H))
    (restores : body.BorrowedRestored Reference (view.split state)
      (body.execute environment Reference (view.split state))) :
    (Circuit.ownedLayoutView (allowAllocation := allowAllocation) view body).BorrowedRestored
      Reference state ((Circuit.ownedLayoutView (allowAllocation := allowAllocation)
        view body).execute environment Reference state) :=
  (borrowedRestored_ownedLayoutView_iff view body environment Reference state).mpr restores

end

end QuantumAlg.Circuit
