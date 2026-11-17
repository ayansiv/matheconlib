/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

public import MathEconLib.Matching.Classical.Marriage.RespectForImprovements
public import MathEconLibExamples.Matching.Improvements
public import Mathlib.Data.Fin.VecNotation

/-!
# Deferred-acceptance applications and the role of each improvement clause

This module extends the worked markets in `MathEconLibExamples.Matching.Improvements`.
`NewlyAcceptable` applies respect for improvements when a rival becomes acceptable; `Promoted`
applies it when the distinguished proposer overtakes a rival and checks a strict gain independently.
`Overtaken`, `RivalRejected`, and `RivalsSwapped` show strict losses when clauses 1, 3, and 2 fail.
The outcomes are computed by kernel evaluation and transported along
`MarriageMarket.galeShapleyComputable_eq_galeShapley`.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.Improvements

open MathEconLib.Matching MarriageMarket

namespace NewlyAcceptable

/-- Respect for improvements: deferred acceptance does not make `true` worse off. -/
theorem leM_galeShapley :
    (market oldOrder).leM true ((market oldOrder).galeShapley true)
      ((market newOrder).galeShapley true) :=
  (market oldOrder).leM_galeShapley_of_isUnambiguousImprovement (market newOrder) rfl
    fun _ => isUnambiguousImprovement

end NewlyAcceptable

namespace Promoted

/-- `none < some true < some false`: the rival is ranked first. -/
abbrev oldOrder : LinearOrder (Option Bool) := order 0 2 1 (by decide)

/-- `none < some false < some true`: `true` has passed his rival. -/
abbrev newOrder : LinearOrder (Option Bool) := order 0 1 2 (by decide)

theorem isUnambiguousImprovement : IsUnambiguousImprovement newOrder oldOrder true := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [order_lt] <;> decide

/-- Respect for improvements: deferred acceptance does not make `true` worse off. -/
theorem leM_galeShapley :
    (market oldOrder).leM true ((market oldOrder).galeShapley true)
      ((market newOrder).galeShapley true) :=
  (market oldOrder).leM_galeShapley_of_isUnambiguousImprovement (market newOrder) rfl
    fun _ => isUnambiguousImprovement

/-- Independent check by computation: before the change `true` is unmatched. -/
theorem galeShapley_old : (market oldOrder).galeShapley true = none := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- After the change he is matched to the receiver. -/
theorem galeShapley_new : (market newOrder).galeShapley true = some () := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- Here the improvement makes `true` strictly better off. -/
theorem ltM_galeShapley :
    (market oldOrder).ltM true ((market oldOrder).galeShapley true)
      ((market newOrder).galeShapley true) := by
  rw [galeShapley_old, galeShapley_new]
  change (none : Option Unit).isSome.toNat < (some ()).isSome.toNat
  decide

end Promoted

namespace Overtaken

/-- Before the change deferred acceptance matches `true` to the receiver. -/
theorem galeShapley_old : (market oldOrder).galeShapley true = some () := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- After the change he is unmatched. -/
theorem galeShapley_new : (market newOrder).galeShapley true = none := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- Deferred acceptance makes `true` strictly worse off, so respect for improvements needs the
first clause. -/
theorem ltM_galeShapley :
    (market oldOrder).ltM true ((market newOrder).galeShapley true)
      ((market oldOrder).galeShapley true) := by
  rw [galeShapley_old, galeShapley_new]
  change (none : Option Unit).isSome.toNat < (some ()).isSome.toNat
  decide

end Overtaken

/-- Ranks on `Option (Fin 3)`: `none` gets `n` and `some i` gets `v i`. -/
def rank₃ (n : ℕ) (v : Fin 3 → ℕ) : Option (Fin 3) → ℕ
  | none => n
  | some i => v i

/-- The linear order on `Option (Fin 3)` induced by an injective rank; larger rank is better. -/
abbrev order₃ (n : ℕ) (v : Fin 3 → ℕ) (h : Function.Injective (rank₃ n v)) :
    LinearOrder (Option (Fin 3)) :=
  LinearOrder.lift' (rank₃ n v) h

theorem order₃_lt {n : ℕ} {v : Fin 3 → ℕ} {h : Function.Injective (rank₃ n v)}
    {a b : Option (Fin 3)} : (order₃ n v h).lt a b ↔ rank₃ n v a < rank₃ n v b :=
  Iff.rfl

/-! ## Deferred acceptance when the third clause fails

Two men and two women. The distinguished man `true` ranks woman `false` first, and man `false`
ranks woman `true` first. Woman `false` ranks man `false` above man `true`. Only woman `true`
changes her ranking: man `false` becomes unacceptable to her. He then proposes to woman `false`
and displaces the distinguished man. -/

namespace RivalRejected

/-- The market in which woman `true` ranks the men by `ord`. -/
def market (ord : LinearOrder (Option Bool)) : MarriageMarket Bool Bool where
  prefM m := match m with
    | true => order 0 2 1 (by decide)
    | false => order 0 1 2 (by decide)
  prefW w := match w with
    | true => ord
    | false => order 0 2 1 (by decide)

/-- Woman `true` before: `none < some false < some true`. -/
abbrev oldOrder : LinearOrder (Option Bool) := order 0 1 2 (by decide)

/-- Woman `true` after: `some false < none < some true`. -/
abbrev newOrder : LinearOrder (Option Bool) := order 1 0 2 (by decide)

/-- The change satisfies the first and second clauses of the relation for man `true`. -/
theorem other_clauses :
    (∀ ⦃o : Option Bool⦄, oldOrder.lt o (some true) → newOrder.lt o (some true)) ∧
      ∀ ⦃m' m'' : Bool⦄, m' ≠ true → m'' ≠ true →
        (oldOrder.lt (some m'') (some m') ↔ newOrder.lt (some m'') (some m')) := by
  simp only [order_lt]
  decide

/-- The change violates the third clause: man `false` was acceptable and no longer is. -/
theorem not_isUnambiguousImprovement : ¬ IsUnambiguousImprovement newOrder oldOrder true := by
  intro h
  have hlt := h.none_lt_some_of_none_lt_some (m' := false) (by decide)
  simp only [order_lt] at hlt
  exact absurd (hlt (by decide)) (by decide)

/-- Before the change the distinguished man gets woman `false`, his first choice. -/
theorem galeShapley_old : (market oldOrder).galeShapley true = some false := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- After the change he gets woman `true`, his second choice. -/
theorem galeShapley_new : (market newOrder).galeShapley true = some true := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- The distinguished man is strictly worse off after the change. -/
theorem ltM_galeShapley :
    (market oldOrder).ltM true ((market newOrder).galeShapley true)
      ((market oldOrder).galeShapley true) := by
  rw [galeShapley_old, galeShapley_new]
  change rank 0 2 1 (some true) < rank 0 2 1 (some false)
  decide

end RivalRejected

/-! ## Deferred acceptance when the second clause fails

Three men and two women. Man `0` is distinguished and ranks woman `false` first, man `1` ranks
woman `true` first and woman `false` second, and man `2` accepts only woman `true`. Woman `false`
ranks man `1` above man `0`. Only woman `true` changes her ranking: she swaps men `1` and `2`.
Man `1` then proposes to woman `false` and displaces the distinguished man, who stays single. -/

namespace RivalsSwapped

/-- The market in which woman `true` ranks the men by `ord`. -/
def market (ord : LinearOrder (Option (Fin 3))) : MarriageMarket (Fin 3) Bool where
  prefM := ![order 0 2 1 (by decide), order 0 1 2 (by decide), order 1 0 2 (by decide)]
  prefW w := match w with
    | true => ord
    | false => order₃ 1 ![2, 3, 0] (by decide)

/-- Woman `true` before: `none < 0 < 2 < 1`. -/
abbrev oldOrder : LinearOrder (Option (Fin 3)) := order₃ 0 ![1, 3, 2] (by decide)

/-- Woman `true` after: `none < 0 < 1 < 2`. -/
abbrev newOrder : LinearOrder (Option (Fin 3)) := order₃ 0 ![1, 2, 3] (by decide)

/-- The change satisfies the first and third clauses of the relation for man `0`. -/
theorem other_clauses :
    (∀ ⦃o : Option (Fin 3)⦄, oldOrder.lt o (some 0) → newOrder.lt o (some 0)) ∧
      ∀ ⦃m' : Fin 3⦄, m' ≠ 0 → oldOrder.lt none (some m') → newOrder.lt none (some m') := by
  simp only [order₃_lt]
  decide

/-- The change violates the second clause: men `1` and `2` have swapped. -/
theorem not_isUnambiguousImprovement : ¬ IsUnambiguousImprovement newOrder oldOrder 0 := by
  intro h
  have hiff := h.some_lt_some_iff (m' := 1) (m'' := 2) (by decide) (by decide)
  simp only [order₃_lt] at hiff
  exact absurd (hiff.mp (by decide)) (by decide)

/-- Before the change the distinguished man gets woman `false`, his first choice. -/
theorem galeShapley_old : (market oldOrder).galeShapley 0 = some false := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- After the change he is unmatched. -/
theorem galeShapley_new : (market newOrder).galeShapley 0 = none := by
  rw [← galeShapleyComputable_eq_galeShapley]
  decide +kernel

/-- The distinguished man is strictly worse off after the change. -/
theorem ltM_galeShapley :
    (market oldOrder).ltM 0 ((market newOrder).galeShapley 0)
      ((market oldOrder).galeShapley 0) := by
  rw [galeShapley_old, galeShapley_new]
  change rank 0 2 1 none < rank 0 2 1 (some false)
  decide

end RivalsSwapped


end MathEconLibExamples.Matching.Improvements
