/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

public import MathEconLib.Matching.Classical.Marriage.BlockingLemma
public import MathEconLib.Matching.Classical.Marriage.Improvements

/-!
# Deferred acceptance respects unambiguous improvements

If women's preferences change by an unambiguous improvement for a proposer `m` and men's
preferences are unchanged, `m` weakly prefers the new man-optimal stable matching to every old
stable matching. This implies Kominers (2024), Lemma 1, comparing the two deferred-acceptance
outcomes. The improvement hypothesis applies at every woman, as in the paper's profile definition;
unchanged preferences satisfy it by reflexivity.

## Main statements

* `MarriageMarket.IsManOptimal.leM_of_isUnambiguousImprovement`: comparison with any old
  stable matching.
* `MarriageMarket.leM_galeShapley_of_isUnambiguousImprovement`: the deferred-acceptance corollary.
* `MarriageMarket.leM_galeShapleyComputable_of_isUnambiguousImprovement`: its executable version.

## Proof and hypotheses

If `m` strictly preferred an old stable matching to the new man-optimal one, clauses 1 and 3
would make that old matching individually rational for women under the new preferences. The
blocking lemma supplies a blocking pair whose man is not `m`. The woman in this pair had a
partner in the old matching, so she is comparing two proposers. By clauses 1 and 2, she already
preferred the blocking proposer to her old partner. Since the men's preferences are unchanged,
the pair would have blocked the old matching. Worked markets apply the theorem and show that
dropping any clause can harm `m`.

## References

Scott Duke Kominers (2024), *Respect for Improvements and Comparative Statics in Matching
Markets*, *Journal of Mechanism and Institution Design* **9**(1), 83–104, Definition 1, Lemma 1,
and footnote 8, p. 90.
[DOI: 10.22574/jmid.2024.12.005](https://doi.org/10.22574/jmid.2024.12.005).
Footnote 8 explains that this condition is weaker, and the result stronger, than the earlier
version; it derives Lemma 1 from the later Lemma 2. Here we give a direct blocking-lemma proof.

Michel Balinski and Tayfun Sönmez (1999), *A Tale of Two Mechanisms: Student Placement*,
*Journal of Economic Theory* **84**(1), 73–94, Section 8, Theorem 5, pp. 90–91.
[DOI: 10.1006/jeth.1998.2469](https://doi.org/10.1006/jeth.1998.2469).
Their definition on p. 89 fixes every other student's comparison with the outside option;
Kominers allows another proposer to become newly acceptable. We formalize Kominers' classical
one-to-one result, not the many-to-one characterization or its uniqueness assertion in Theorem 5.
-/

@[expose] public section

namespace MathEconLib.Matching

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}

/-- **Respect for improvements.** Suppose the women's preferences change by an unambiguous
improvement for `m` and the men's preferences do not change. Then `m` weakly prefers the new
man-optimal stable matching to every matching that was stable before the change. -/
theorem IsManOptimal.leM_of_isUnambiguousImprovement [Finite M] [Finite W]
    (old new : MarriageMarket M W) {m : M} (hM : new.prefM = old.prefM)
    (h : ∀ w, IsUnambiguousImprovement (new.prefW w) (old.prefW w) m) {μ μ' : M ≃. W}
    (hμ : old.IsStableMatching μ) (hμ' : new.IsManOptimal μ') : old.leM m (μ m) (μ' m) := by
  have hltM : ∀ m' y z, new.ltM m' y z ↔ old.ltM m' y z := fun m' y z => by
    unfold MarriageMarket.ltM
    rw [hM]
  by_contra hnot
  have h₀ : new.ltM m (μ' m) (μ m) := by
    rw [hltM]
    let := old.prefM m
    exact not_le.mp hnot
  -- The old stable matching is individually rational for the women under the new preferences.
  have hν : new.IndividuallyRationalW μ := by
    intro w
    have hw : old.leW w none (μ.symm w) := IsStableMatching.individuallyRationalForW old hμ w
    change new.leW w none (μ.symm w)
    cases hs : μ.symm w with
    | none => exact (new.prefW w).le_refl _
    | some m' =>
        rw [hs] at hw
        have hlt : (old.prefW w).lt none (some m') :=
          @lt_of_le_of_ne _ (old.prefW w).toPartialOrder _ _ hw (Option.some_ne_none m').symm
        by_cases hm' : m' = m
        · rw [hm'] at hlt ⊢
          exact @le_of_lt _ (new.prefW w).toPreorder _ _ ((h w).lt_some_of_lt_some hlt)
        · exact @le_of_lt _ (new.prefW w).toPreorder _ _
            ((h w).none_lt_some_of_none_lt_some hm' hlt)
  obtain ⟨m', w, hm', ⟨m'', -, hw⟩, hbM, hbW⟩ :=
    IsManOptimal.exists_isBlockingPair_of_ltM new hμ' hν h₀
  have hne : m' ≠ m := fun he => hm' (he ▸ h₀)
  have hsymm : μ.symm w = some m'' := μ.eq_some_iff.mpr hw
  have hnew : (new.prefW w).lt (some m'') (some m') := by
    have hb : new.ltW w (μ.symm w) (some m') := hbW
    rwa [hsymm] at hb
  -- The woman already preferred the blocking man before the change.
  have hold : (old.prefW w).lt (some m'') (some m') := by
    by_cases hm : m'' = m
    · rw [hm] at hnew ⊢
      by_contra hcon
      have hlt : (old.prefW w).lt (some m') (some m) := by
        let := old.prefW w
        exact lt_of_le_of_ne (not_lt.mp hcon) fun he => hne (Option.some.inj he)
      let := new.prefW w
      exact lt_asymm hnew ((h w).lt_some_of_lt_some hlt)
    · exact ((h w).some_lt_some_iff hne hm).mpr hnew
  refine (old.unblocked_iff_no_blockingPair μ).mp hμ.2 m' w ⟨(hltM _ _ _).mp hbM, ?_⟩
  change old.ltW w (μ.symm w) (some m')
  rw [hsymm]
  exact hold

/-- **Respect for improvements** for man-proposing deferred acceptance (Kominers 2024, Lemma 1):
an unambiguous improvement for `m` in the women's preferences, with the men's preferences
unchanged, makes `m` weakly better off. -/
theorem leM_galeShapley_of_isUnambiguousImprovement [Fintype M] [Fintype W]
    (old new : MarriageMarket M W) {m : M} (hM : new.prefM = old.prefM)
    (h : ∀ w, IsUnambiguousImprovement (new.prefW w) (old.prefW w) m) :
    old.leM m (old.galeShapley m) (new.galeShapley m) :=
  IsManOptimal.leM_of_isUnambiguousImprovement old new hM h old.stable_galeShapley
    new.isManOptimal_galeShapley

/-- Respect for improvements for the executable algorithm. -/
theorem leM_galeShapleyComputable_of_isUnambiguousImprovement [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W] (old new : MarriageMarket M W) {m : M}
    (hM : new.prefM = old.prefM)
    (h : ∀ w, IsUnambiguousImprovement (new.prefW w) (old.prefW w) m) :
    old.leM m (old.galeShapleyComputable m) (new.galeShapleyComputable m) := by
  rw [old.galeShapleyComputable_eq_galeShapley, new.galeShapleyComputable_eq_galeShapley]
  exact old.leM_galeShapley_of_isUnambiguousImprovement new hM h

end MarriageMarket

end MathEconLib.Matching
