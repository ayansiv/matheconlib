/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

import MathEconLibExamples.Matching.RespectForImprovements

/-! Regression checks for deferred acceptance respecting improvements. -/

open MathEconLib.Matching MarriageMarket
open MathEconLibExamples.Matching.Improvements

/-! The conclusion is stated in the old market, and reads the same in the new one. -/

example {M W : Type} [Fintype M] [Fintype W] (old new : MarriageMarket M W) {m : M}
    (hM : new.prefM = old.prefM)
    (h : ∀ w, IsUnambiguousImprovement (new.prefW w) (old.prefW w) m) :
    new.leM m (old.galeShapley m) (new.galeShapley m) := by
  have key := old.leM_galeShapley_of_isUnambiguousImprovement new hM h
  unfold MarriageMarket.leM at key ⊢
  rwa [hM]

/-! With unchanged preferences the hypotheses hold by reflexivity. -/

example {M W : Type} [Fintype M] [Fintype W] (mkt : MarriageMarket M W) (m : M) :
    mkt.leM m (mkt.galeShapley m) (mkt.galeShapley m) :=
  mkt.leM_galeShapley_of_isUnambiguousImprovement mkt rfl
    fun _ => ⟨fun _ h => h, fun _ _ _ _ => Iff.rfl, fun _ _ h => h⟩

/-! Applications: the man is weakly better off, and can be strictly better off. -/

example : (market NewlyAcceptable.oldOrder).leM true
    ((market NewlyAcceptable.oldOrder).galeShapley true)
    ((market NewlyAcceptable.newOrder).galeShapley true) :=
  NewlyAcceptable.leM_galeShapley

example : (market Promoted.oldOrder).ltM true
    ((market Promoted.oldOrder).galeShapley true)
    ((market Promoted.newOrder).galeShapley true) :=
  Promoted.ltM_galeShapley

/-! Deferred acceptance can make the distinguished man strictly worse off when the first, the
third or the second clause fails. -/

example : (market Overtaken.oldOrder).ltM true
    ((market Overtaken.newOrder).galeShapley true)
    ((market Overtaken.oldOrder).galeShapley true) :=
  Overtaken.ltM_galeShapley

example : (RivalRejected.market RivalRejected.oldOrder).ltM true
    ((RivalRejected.market RivalRejected.newOrder).galeShapley true)
    ((RivalRejected.market RivalRejected.oldOrder).galeShapley true) :=
  RivalRejected.ltM_galeShapley

example : (RivalsSwapped.market RivalsSwapped.oldOrder).ltM 0
    ((RivalsSwapped.market RivalsSwapped.newOrder).galeShapley 0)
    ((RivalsSwapped.market RivalsSwapped.oldOrder).galeShapley 0) :=
  RivalsSwapped.ltM_galeShapley
