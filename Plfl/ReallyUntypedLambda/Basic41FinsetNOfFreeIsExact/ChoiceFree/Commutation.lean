module
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Commuting relations: the Hindley-Rosen lemma

Generic rewriting theory, in the style of `Relation.church_rosser`:

* `Relation.commute_reflTransGen`: if a single `R`-step and a single `S`-step
  out of the same point can be closed by `S*` on one side and by at most one
  `R`-step on the other, then `R*` and `S*` commute;
* `Relation.reflTransGen_union_confluent` (the **Hindley-Rosen lemma**): if `R`
  and `S` are confluent and `R*` and `S*` commute, then the union `R ∪ S` is
  confluent.

Nothing here uses `Classical.choice`.
-/

namespace Relation

variable {α : Type*} {R S : α → α → Prop}

/-- The key diagram chase: a single `R`-step against an `S*`-sequence. -/
private theorem strip_of_strong_commute
    (h : ∀ a b c, R a b → S a c → ∃ d, ReflTransGen S b d ∧ ReflGen R c d)
    {a b c : α} (hab : R a b) (hac : ReflTransGen S a c) :
    ∃ d, ReflTransGen S b d ∧ ReflGen R c d := by
  induction hac with
  | refl => exact ⟨b, ReflTransGen.refl, ReflGen.single hab⟩
  | @tail e c _ hec ih =>
    obtain ⟨d, hbd, hed⟩ := ih
    cases hed with
    | refl => exact ⟨c, hbd.tail hec, ReflGen.refl⟩
    | single hed =>
      obtain ⟨f, hdf, hcf⟩ := h _ _ _ hed hec
      exact ⟨f, hbd.trans hdf, hcf⟩

/-- **Strong commutation implies commutation of the closures.**  If from
`R a b` and `S a c` one can always reach a common `d` with `S* b d` and at most
one `R`-step from `c`, then `R*` and `S*` commute. -/
theorem commute_reflTransGen
    (h : ∀ a b c, R a b → S a c → ∃ d, ReflTransGen S b d ∧ ReflGen R c d)
    {a b c : α} (hab : ReflTransGen R a b) (hac : ReflTransGen S a c) :
    ∃ d, ReflTransGen S b d ∧ ReflTransGen R c d := by
  induction hab with
  | refl => exact ⟨c, hac, ReflTransGen.refl⟩
  | @tail e b _ heb ih =>
    obtain ⟨d, hed, hcd⟩ := ih
    obtain ⟨f, hbf, hdf⟩ := strip_of_strong_commute h heb hed
    exact ⟨f, hbf, hcd.trans hdf.to_reflTransGen⟩

/-- The union of two relations. -/
def UnionRel (R S : α → α → Prop) : α → α → Prop := fun a b => R a b ∨ S a b

/-- The composite `R* ; S*`. -/
private def StarComp (R S : α → α → Prop) : α → α → Prop :=
  fun a b => ∃ c, ReflTransGen R a c ∧ ReflTransGen S c b

private theorem comp_of_union {a b : α} (h : UnionRel R S a b) : StarComp R S a b := by
  cases h with
  | inl h => exact ⟨b, ReflTransGen.single h, ReflTransGen.refl⟩
  | inr h => exact ⟨a, ReflTransGen.refl, ReflTransGen.single h⟩

private theorem union_star_of_comp {a b : α} (h : StarComp R S a b) :
    ReflTransGen (UnionRel R S) a b := by
  obtain ⟨c, hac, hcb⟩ := h
  have h1 := ReflTransGen.mono (p := UnionRel R S) (fun _ _ => Or.inl) a c hac
  have h2 := ReflTransGen.mono (p := UnionRel R S) (fun _ _ => Or.inr) c b hcb
  exact h1.trans h2

private theorem reflTransGen_comp_eq {a b : α} :
    ReflTransGen (StarComp R S) a b ↔ ReflTransGen (UnionRel R S) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ step ih => exact ih.trans (union_star_of_comp step)
  · exact fun h => ReflTransGen.mono (p := StarComp R S) (fun _ _ => comp_of_union) a b h

/-- **The Hindley-Rosen lemma**: if `R` and `S` are confluent and their
reflexive-transitive closures commute, then their union is confluent. -/
theorem reflTransGen_union_confluent
    (hR : ∀ a b c, ReflTransGen R a b → ReflTransGen R a c → Join (ReflTransGen R) b c)
    (hS : ∀ a b c, ReflTransGen S a b → ReflTransGen S a c → Join (ReflTransGen S) b c)
    (hcomm : ∀ a b c, ReflTransGen R a b → ReflTransGen S a c →
      ∃ d, ReflTransGen S b d ∧ ReflTransGen R c d)
    {a b c : α} (hab : ReflTransGen (UnionRel R S) a b) (hac : ReflTransGen (UnionRel R S) a c) :
    Join (ReflTransGen (UnionRel R S)) b c := by
  have hdiamond : ∀ a b c, StarComp R S a b → StarComp R S a c →
      ∃ d, ReflGen (StarComp R S) b d ∧ ReflTransGen (StarComp R S) c d := by
    rintro a b c ⟨b1, hab1, hb1b⟩ ⟨c1, hac1, hc1c⟩
    obtain ⟨e, hb1e, hc1e⟩ := hR _ _ _ hab1 hac1
    obtain ⟨w1, hew1, hbw1⟩ := hcomm _ _ _ hb1e hb1b
    obtain ⟨w2, hew2, hcw2⟩ := hcomm _ _ _ hc1e hc1c
    obtain ⟨g, hw1g, hw2g⟩ := hS _ _ _ hew1 hew2
    exact ⟨g, ReflGen.single ⟨w1, hbw1, hw1g⟩,
      ReflTransGen.single ⟨w2, hcw2, hw2g⟩⟩
  obtain ⟨d, hbd, hcd⟩ :=
    church_rosser hdiamond (reflTransGen_comp_eq.mpr hab) (reflTransGen_comp_eq.mpr hac)
  exact ⟨d, reflTransGen_comp_eq.mp hbd, reflTransGen_comp_eq.mp hcd⟩

end Relation
