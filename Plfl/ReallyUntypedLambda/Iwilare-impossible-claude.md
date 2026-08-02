Good instinct to push on this — and the answer is **no**, that exact statement is not provable, because it's **false**. This isn't a formalization inconvenience; it's the actual mathematical reason the Takahashi/parallel-reduction detour exists in the first place.

## A counterexample

Work in `Term 1` (one free variable, `v#0`, call it `z`). Let `I := ƛ v#0` (the identity), and let

```
a := (ƛ (v#0 ⬝ v#0)) ⬝ (I ⬝ v#0)     -- (λx. x x) (I z)
```

Take two single `Beta` steps out of `a`:

- **`hab`** (fire the *outer* redex, `basis`): `a —→ (I ⬝ v#0) ⬝ (I ⬝ v#0) =: b`. Substituting `M = v#0` into `N = I ⬝ v#0` just duplicates `N`.
- **`hac`** (fire the *inner* redex, `appl`/`appr` congruence): `a —→ (ƛ(v#0⬝v#0)) ⬝ v#0 =: c`, since `I ⬝ v#0 —→ v#0`.

Now try to find `d` with `b —→≤1 d` and `c —→* d`.

- From `c`, the **only** move is firing its one redex: `c —→ v#0 ⬝ v#0` (`= z z`), which is a normal form. So the only terms reachable from `c` via `—→*` are `{c, z⋅z}`.
- From `b = (I⬝v#0) ⬝ (I⬝v#0)`, a **single** step can reduce only *one* of the two `I⬝v#0` copies (congruence rules only recurse into one side at a time), giving either `v#0 ⬝ (I⬝v#0)` or `(I⬝v#0) ⬝ v#0`. Neither of these, nor `b` itself, equals `c` or `z⋅z`.

So `{b, v#0⬝(I⬝v#0), (I⬝v#0)⬝v#0} ∩ {c, z⋅z} = ∅`. There is **no** `d`. The lemma as you've stated it is false.

## Why this happens

`hab` fired a redex whose body *duplicated* the argument `N = I ⬝ v#0`, which itself still contained an unreduced redex. After duplication there are **two** copies of that inner redex sitting in `b`, but a single ordinary `Beta` step can only ever contract one redex-occurrence at a time (that's what "single-step" congruence rules force). Meanwhile `c` only ever had **one** copy of that redex, so it can reach a common point in one step. To match them up within a bound of "≤ 1 step on one side," you'd need to contract *both* duplicated copies simultaneously — which is precisely what `BetaPar` (parallel reduction) was invented to allow, and precisely what plain `Beta` cannot do.

This is the textbook reason (Tait–Martin-Löf, via Takahashi) that confluence proofs for β-reduction go through parallel reduction rather than working with single β-steps directly: **duplication under substitution breaks the one-step diamond/strip property for `—→`, but not for `⇉`.**

## Consequence for your proof

So your working version is not just stylistically necessary but *mathematically* necessary:

```
theorem beta_church_rosser ... :=
  -- convert —→* to ⇉* (same closure, different step-granularity)
  -- apply Relation.church_rosser to the strip lemma for ⇉ (true, via takahashi)
  -- convert back
```

The round trip through `betapar_star_eq_betastar` isn't boilerplate to eliminate — it's bridging the fact that `—→` and `⇉` generate the *same reflexive-transitive closure* despite `⇉` (and not `—→`) satisfying the local strip property needed by `Relation.church_rosser`. There's no way to instantiate `Relation.church_rosser` at `r := Beta` directly with a true hypothesis, because that hypothesis is false for `Beta`.
