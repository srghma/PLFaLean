# Summary of changes for run b1367b43-b90a-4f6a-94f1-43247e347580
All seven evaluation strategies / reductions from the essay's list are now implemented in the `FinScope` library, and the whole project builds with **no `sorry`, no added axiom and no `native_decide`**. The build-time check in `FinScope/NoChoice.lean` (extended to the new modules) also confirms that nothing in the development — old or new — depends on the axiom of choice; the new theorems use only `propext` and `Quot.sound`.

**New modules**

- `FinScope/Strategies.lean` — **(2) leftmost-innermost (depth-first)** reduction `—→ᵢ` (a redex is contracted only once it contains no other redex) and **(3) applicative order / call-by-value** `—→ᵥ` (the argument is evaluated to a `Value` before the function body is expanded, and no reduction happens under a binder). Both are shown to be beta steps, deterministic, and to satisfy progress (`innermost_progress`, `cbv_progress`, `normal_iff_no_innermost`, `value_iff_no_cbv`). Each comes with an executable one-step function proved to compute exactly the relation (`istep_eq_some_iff`, `istep_none_iff_normal`, `vstep_eq_some_iff`, `vstep_none_iff_value`) and a fuelled evaluator with a soundness theorem (`evalAO_sound`, `evalCBV_sound`).
- `FinScope/Positions.lean` — **(4) parametrized tree-traversal orders**. A position `Pos` is a path in the expression tree; `reduceAt p t` contracts the redex at `p`, and choosing a beta step is exactly choosing a redex position (`reduceAt_sound`, `reduceAt_complete`). A `TraversalOrder` lists the positions to visit, `stepWith order` contracts the first redex met, `evalWith order` iterates it: `stepWith_sound`, `stepWith_none_iff_normal`, `evalWith_sound`. Three traversals are provided — `preorder`, `postorder`, `breadthFirst` — each proved to visit every redex position, and the named strategies are recovered from them: `stepWith_preorder_eq_lstep` (leftmost-outermost = preorder) and `stepWith_postorder_eq_istep` (leftmost-innermost = postorder).
- `FinScope/Multiway.lean` — **(5) multiway / all-paths evaluation**. `allSteps t` computes *all* one-step reducts and is proved to be exactly the beta reducts (`mem_allSteps_iff`, `allSteps_eq_nil_iff_normal`); `multiwayEdges` gives the edges of the multiway graph, `multiway k` its k-th generation (`multiway_sound`, `mem_multiway_of_betaSteps`). Church–Rosser read on that graph is `multiway_confluent`: two states reached along any two trajectories from a common term can always be joined again.
- `FinScope/Alpha.lean` — **(6) alpha conversion**. Since de Bruijn terms carry no bound-variable names, alpha conversion is stated on a named syntax `NTerm`: `—→α` renames the bound variable of an abstraction to a name absent from its body, `≡α` is its equivalence closure, and `NTerm.toDB` translates a named term in a naming context. The main theorem `AlphaEq.toDB_eq` shows alpha-convertible terms have the *same* de Bruijn translation — alpha conversion is the identity in the scope-bounded calculus, which is why it never has to be performed elsewhere.

**Already present, left unchanged**: **(1) leftmost-outermost (normal order)** `—→ₗ` in `FinScope/Leftmost.lean` with determinism, the Normalization Theorem and the executable normal-order evaluator, and **(7) eta reduction** in `FinScope/Eta.lean`, `BetaEta.lean`, `EtaNormal.lean`, `Postponement.lean` (eta confluence, beta-eta Church–Rosser, eta normal forms, eta postponement). Nothing existing was removed; the only edit to an old file is the four added imports in `FinScope/NoChoice.lean` so the constructivity check covers the new modules.

Each new module ends with worked examples: `(λx. (λy. x) x) 𝟙` is evaluated to the identity by the applicative-order, call-by-value, preorder, postorder and breadth-first evaluators, its two one-step reducts are computed by `allSteps`, and the two multiway trajectories are shown to meet again. `FINDINGS.md` was updated with the new modules and a section describing all seven strategies; `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run afbe81ba-147b-491c-b4d5-00d3201ddcf6
Done — the project now contains only the `FinScope` (Fin-indexed `Term : Nat → Type`) development, it builds cleanly, and there is no `sorry`, no added axiom and no `native_decide`.

**1. Removed everything not about `FinScope`.** `IwilareNatIsExactScope.lean` and the whole `IwilareNatIsExactScope/` directory (19 modules) are gone; `lakefile.toml` now declares the single `FinScope` library as the only default target. Every comment and doc reference to the deleted development was rewritten, and `FINDINGS.md` was rewritten as a `FinScope`-only overview (module table, substitution, Church–Rosser, what the scope index means, and the rest of the development). `ARISTOTLE_SUMMARY.md` was left untouched.

**2. On simplifying beta via `shift` / `unshift` / `subst`.** In the scope-bounded setting those three raw operations are not needed as primitives: shifting is a renaming, unshifting is not an operation at all (it is read off the types), and beta substitution stays the one-liner `betaSubst M N = sub (Fin.cons N var) M`. To make that precise rather than just assert it, `FinScope.lean` gained a new section "Shifting and substituting at an arbitrary index" that recovers the raw operations and proves the equations the raw recursive definitions use as their clauses:
- `shiftAt c t = ren c.succAbove t` (the raw `↑ c 1`) with `shiftAt_var`, `shiftAt_app`, `shiftAt_abs` (goes under a binder at `c+1`), and `shiftAt_zero : shiftAt 0 t = wk t`;
- `substAt c M N` (notation `M [ c := N ]`, the raw `M[c := N]` followed by `↓ c 1`) with `substAt_var_same`, `substAt_var_succAbove`, `substAt_app`, and `substAt_abs : (ƛ t) [ c := N ] = ƛ (t [ c.succ := wk N ])`;
- `substAt_zero : M [ 0 := N ] = M [ N ]` — beta substitution *is* the raw `↓ 0 1 (M[0 := ↑ 0 1 N])`;
- `substAt_shiftAt : (shiftAt c M) [ c := N ] = M` — unshifting undoes shifting.

**3. More notation.** Each rule of `—→` and of `⇉` now has its own notation: `L —→-ξₗ h`, `L —→-ξᵣ h`, `—→-ƛ h`, `M —→-β N`, and `⇉-c x`, `⇉-ƛ h`, `h₁ ⇉-ξ h₂`, `hM ⇉-β hN`. The two application congruence rules keep their implicit-argument constructors (so no existing proof changed) and are wrapped by the reducible `match_pattern` abbreviations `Beta.xiL` / `Beta.xiR`, which put the passive argument in front. The notations therefore work both to build a reduction and to case-split on one; `beta_step_test` and `betapar_step_test` check exactly that by matching on all four rules, and the two sample reductions at the end of the file are now written with them. (`⇉-c` takes a single argument, so it is a prefix notation.)

**One correctness fix worth flagging.** `FinScope/NoChoice.lean` advertises a build-time guarantee that no declaration depends on `Classical.choice`. As written it was silently vacuous: inside a `module`, the proofs of imported declarations are not available, so the axiom collection stopped at the first imported lemma and never reported anything — I confirmed this by feeding it a declaration using excluded middle, which it accepted. The file now uses plain `import`s, and I verified that it does fail the build on such a declaration and passes on the current sources. That check also caught that my first version of `substAt` (built on Mathlib's `Fin.insertNth` lemmas) pulled in `Classical.choice`, so the substitution is now built on a self-contained `insertVar`; `beta_church_rosser` and all the new results depend only on `propext` and `Quot.sound`.


# Summary of changes for run 428278cb-31b9-4a9c-bdf4-0fac31592335
The re-implementation for the scope-bounded (`Fin`-indexed) term type is now complete: the whole earlier development has been ported, and everything builds with no `sorry`, no added axioms and no `native_decide`. The original exact-scope development was left untouched — all the new work is additive.

**Where it lives.** The new library is `FinScope.lean` plus 18 modules under `FinScope/`. It is built by `lake build` alongside the old library.

**Core (`FinScope.lean`)** — the requested type `Term : Nat → Type` with `deriving DecidableEq`; renaming/substitution (`ren`, `ext`, `sub`, `exts`) with the full substitution algebra (`ren_ren`, `sub_ren`, `ren_sub`, `sub_sub`, …); **`betaSubst`** (notation `M [ N ]`) as the one-liner `sub (Fin.cons N var) M`; beta reduction, parallel reduction, the complete development `cd`, Takahashi's triangle and **`beta_church_rosser`**, plus confluence and joinability of conversion, and two worked sample reductions.

**Ported this session** (each verified module by module): eta postponement (`FinScope/Postponement.lean`, `eta_postponement`, `betaEtaStar_iff_beta_then_eta`), standardization (`standardization`, `head_reduces_to_abs`), leftmost/normal-order reduction (`Leftmost.deterministic`, `leftmost_normalization`, `leftmost_progress`), weak head reduction and the call-by-name evaluator (`whnf_normalization`, `evalCBN` sound and complete), decidability of `Normal` and the normal order evaluator (`has_normal_form_iff_eval`), primitive recursion (`crec_church`, `crec_represents`) with truncated subtraction, minimisation (`cmin_represents`), the pair-free continuation-passing predecessor and subtraction (`cpredCPS_church`, `csubCPS_church`), and a build-time constructivity check (`FinScope/NoChoice.lean`).

**The predicted simplifications really happen**, and they are documented in `FINDINGS.md` (new Part II): no Sigma type occurs anywhere in `FinScope`; `DecidableEq` is free from `deriving`, so the hand-built decidable-equality module of the old development has no counterpart; closedness is a type (`Term 0`) rather than a hypothesis, so the closedness side conditions disappear — `crec_church`, `crec_represents`, `cmin_represents` hold for arbitrary `F, Z : Term n`; and evaluation preserves the scope (`eval, evalCBN : Nat → Term n → Option (Term n)`). Concrete computations (`pred 3 = 2`, `3 * 4 = 12`, `7 - 4 = 3`, the search for the least zero) are checked by the kernel.

**On your reading of the index.** With `Fin`-indexed variables only half of it survives, and this is now proved both ways in the core file: `closed_of_scope_zero` shows a `Term 0` is closed in the strongest sense (`Fin 0` is empty), but `notExact : Term 1 := ƛ (v# 0)` has no free index at all (`notExact_no_free_index`), so `n > 0` no longer means "the index `n − 1` is used". The exact reading holds in the first implementation, and it is exactly what forced the Sigma types there; dropping the Sigma types costs the exactness.

Verified axiom use: the new results depend only on `propext` and `Quot.sound`; `FinScope/NoChoice.lean` fails the build if any `FinScope` declaration ever comes to depend on `Classical.choice`.

# Summary of changes for run 9dc6f8cc-7732-4c4d-a736-cebb8bda7387
All three questions are answered, and everything is verified by the build (`lake build` is clean: no errors, no warnings, no `sorry`, no `native_decide`, no added axioms).

**1. Can it be done without `Classical.choice`? Yes — and it now is.**

The whole untyped-lambda-calculus development (substitution, beta and eta reduction, Church–Rosser, standardization, normal forms, the evaluator, Church numerals, fixed points) depends on no axiom other than `propext` and `Quot.sound`. This is checked mechanically on every build: the new `IwilareNatIsExactScope/NoChoice.lean` imports every module, walks over every declaration of the project, collects the axioms each depends on, and fails the build if `Classical.choice` appears anywhere. (I confirmed the check really fires by feeding it a declaration that uses excluded middle.)

Ten proofs had to be adjusted; the mathematics did not change:
- `by_cases` on an undecidable-looking property silently uses `Classical.propDecidable`. This happened in the three "progress" theorems (leftmost redex, weak head redex, eta redex). All three properties are genuinely decidable, so I built the decision procedures constructively in the new `IwilareNatIsExactScope/DecEq.lean`: a heterogeneous structural equality test `Term.beq` with its correctness proof, hence `DecidableEq` for terms; plus "is this an abstraction?" and "is this a shifted term `ren succ M`?" (the only possible witness is `sub0 #0 s`, so one equality test settles it). `deriving DecidableEq` cannot be used here, because two terms of the same scope may be built from subterms of *different* scopes — that is explained in comments in the file. A new `eta_progress` theorem replaces the classical case split behind existence of eta normal forms.
- `by_contra`, `omega` closing a goal by contradiction, and Mathlib's `Relation.ReflTransGen.cases_head` also pull in choice; those few spots were replaced by direct arguments.

What genuinely *cannot* be done constructively is recorded in comments in `NoChoice.lean`: a statement like "every term either has a beta normal form or has none" is not provable without excluded middle (beta normalisation is undecidable). No result in the project asserts it — the normalisation theorems here are the conditional, constructively meaningful ones (if a normal form exists, leftmost reduction finds it).

**2. No simple types.** The three modules that implemented Curry-style simple types (`Typing.lean`, `StrombNormalization`, i.e. `StrongNormalization.lean`, and `TypedChurch.lean`) have been removed, together with their entries in `lakefile.toml`; nothing else referred to them. Only the untyped calculus remains.

**3. Church numerals with subtraction — a tuple is *not* needed.** Subtraction was already present via Kleene's pair-based predecessor (`cpred_church`, `csub_church`). The new `IwilareNatIsExactScope/Subtraction.lean` shows the tuple is avoidable: the continuation-passing predecessor `predCPS = ƛn. ƛf. ƛx. n (ƛg. ƛh. h (g f)) (ƛu. x) (ƛu. u)` uses no pairing combinator and no other data encoding. Proved by pure beta reduction:
- `cpredCPS_church : cpredCPS ⬝ church n —→* church (n - 1)`
- `csubCPS_church : csubCPS ⬝ church m ⬝ church n —→* church (m - n)`, with `csubCPS = ƛm ƛn. n predCPS m`,
via the two invariant lemmas `cpredA_app_var` (feeding the k-th iterate `f` runs all k steps) and `cpredA_app_Icomb` (feeding it the identity runs one step less). Four concrete evaluations (`pred 5 = 4`, `pred 0 = 0`, `7 - 4 = 3`, `4 - 7 = 0`) are checked by the project's normal-order evaluator by kernel reduction. What *is* true about tuples is only the truncation: `church (-1)` does not exist, so every lambda-definable subtraction on the numerals is truncated; representing genuine (signed) integers is where a pair encoding becomes the standard device. This is written up in `FINDINGS.md`, which also documents the constructivity work and the removal of the typed modules.


# Summary of changes for run 64d23d8d-e46f-4f55-93da-c02382524924
## What I added: further fundamental theorems, all proved in Lean

Everything below is new, sorry-free, and the whole project builds with no errors or warnings (no `axiom`, no `native_decide`; the new results depend only on `propext`, `Quot.sound` and, through Mathlib, `Classical.choice`). New modules are registered in `lakefile.toml` and documented in `FINDINGS.md` (sections 9-15).

**Eta reduction** (`IwilareNatIsExactScope/Eta.lean`) — the de Bruijn eta rule `ƛ ((ren succ M) #0) —→η M`, stability under renaming/substitution, the fact that renamings *reflect* eta and beta steps (via a pullback property of index maps), subcommutativity, and `eta_church_rosser` (confluence of eta).

**Eta normal forms** (`EtaNormal.lean`) — a size measure that every eta step strictly decreases, hence `eta_strongly_normalizing`, plus existence and uniqueness of eta normal forms; uniqueness of beta-eta normal forms; and `ctrue_not_betaetaEq_cfalse` (consistency of the beta-eta theory).

**Beta-eta reduction** (`BetaEta.lean`) — commutation of beta with eta (`beta_eta_commute`, `betaStar_etaStar_commute`), the **Church-Rosser theorem for beta-eta** (`betaeta_church_rosser`), joinability of beta-eta convertible terms, conversion congruences, and `betaeta_extensionality` (agreeing on a fresh variable implies beta-eta convertibility).

**Eta postponement** (`Postponement.lean`) — a parallel eta reduction and the key swap lemma give `eta_postponement : a —→βη* b → ∃ c, a —→* c ∧ c —→η* b`, with the equivalence form `betaEtaStar_iff_beta_then_eta`.

**Simple types** (`Typing.lean`) — Curry-style simple types with contexts `Nat → Ty`, generation/inversion lemmas, typed renaming, weakening and typed substitution, **subject reduction for beta and for eta**, plus: types are not unique, self-application and `Ω` are untypable, and subject *expansion* fails (each with an explicit witness).

**Strong normalization of the simply typed lambda calculus** (`StrongNormalization.lean`) — Tait's reducibility method: `SN` as accessibility for the converse of beta, reducibility by recursion on the type, the properties CR1-CR3, reducibility of abstractions, and the main lemma, giving `Typing.strong_normalization`, `Typing.has_normal_form` and `Typing.leftmost_normalizes` (normal order evaluation terminates on typable terms).

**Typed Church numerals** (`TypedChurch.lean`) — `church n : (A ⇒ A) ⇒ A ⇒ A` for every `A`, likewise successor, addition and multiplication, so numeral arithmetic is strongly normalizing.

## Answering the question

The theorems above are the ones I judged both fundamental and reachable on this development, and they are now proved rather than merely listed. Natural further targets that remain open here (and are considerably larger undertakings) include: head normal forms and solvability (Wadsworth's theorem), Böhm's separation theorem, undecidability of beta-conversion, standardization for beta-eta, and normalization results for richer type systems such as System F.


# Summary of changes for run 93e0cebf-b56f-4dda-96a5-ed20d16bab62
## 1. Fewer auxiliary layers: `ScopedView` is gone

The helper inductive `ScopedView` and the maps `Term.view` / `Scoped.view` have been **deleted**. The facts they existed to prove — that `Scoped.var / abs / app` are injective (`var_eq_var`, `abs_eq_abs`, `app_eq_app`) and pairwise disjoint (`var_ne_abs`, …) — are now proved directly, from injectivity of `Sigma.mk` together with the no-confusion principle of `Term`. Nothing else in the project referred to the view, so no other proof changed, and everything still builds.

`Scoped` itself (`Σ n, Term n`) could **not** be removed: substituting into a `Term n` may decrease the number of free indexes, and by how much depends on the term, not on its index — so the resulting scope has to be returned rather than imposed. What I did instead was keep it out of new statements wherever it was avoidable: the new scope results are stated about the plain index (`Term.newFreeIndexes_betaSubstSigma_le`), and general substitution/renaming laws are stated for arbitrary terms rather than for the particular shapes needed.

## 2. Further classical theorems of the untyped lambda calculus

Four new files, all sorry-free (`IwilareNatIsExactScope/`):

**`NormalForms.lean`**
- `≡β` is an equivalence and a congruence (`BetaEq.abs`, `BetaEq.app`, …), and `betaeq_iff_join : a ≡β b ↔ ∃ d, a —→* d ∧ b —→* d` (Church-Rosser in `↔` form).
- `Normal M` (no beta step applies), characterised inductively by the usual grammar of normal forms: `normalForm_iff_normal`.
- **Uniqueness of normal forms** `normal_form_unique`, `betaeq_normal_eq`, `betaeq_normal_reduces`.
- **Consistency**: the Church booleans are distinct normal forms, so `ctrue_not_betaeq_cfalse : ¬ (ctrue ≡β cfalse)` — conversion does not identify all terms.
- `Ω = (ƛx. x x)(ƛx. x x)` reduces only to itself (`Omega_betastar_eq`), hence `Omega_has_no_normal_form`.

**`FixedPoint.lean`**
- **The Fixed Point Theorem**: every `F` has a fixed point, reached in one step (`fix_step : fix F —→ F ⬝ (fix F)`, `fixed_point`).
- Curry's closed combinator `Ycomb` produces it uniformly: `Ycomb_step`, `Y_fixed_point : Ycomb ⬝ F ≡β F ⬝ (Ycomb ⬝ F)`.

**`ScopeBounds.lean`** (a soundness check for your reading of the index)
- `newFreeIndexes_sub0_le`, and **`Beta.newFreeIndexes_le` / `BetaStar.newFreeIndexes_le`: reduction never creates free indexes**, so `betastar_closed`: closed terms reduce to closed terms.
- Along the way: a closed term is invariant under any renaming and any substitution.

**`ChurchNumerals.lean`**
- `church n` is closed, and **iterates**: `church_app : church n ⬝ F ⬝ E —→* F(F(…(F E)))` for arbitrary `F`, `E`.
- **Arithmetic is representable**: `csucc_church`, `cadd_church : cadd ⬝ church m ⬝ church n —→* church (m + n)`, `cmul_church : … —→* church (m * n)`. (Multiplication uses `ƛm ƛn ƛf ƛx. m (n f) x`, which works up to beta alone; the shorter `ƛm ƛn ƛf. m (n f)` would need eta.)
- **Faithfulness**: numerals are normal forms and `church_betaeq_iff : church m ≡β church n ↔ m = n`.

## Hygiene

`lake build` is clean (all six modules, no errors and no warnings); no `sorry`, no `native_decide`, no added axioms — the new theorems depend only on `propext`, `Quot.sound` and (through Mathlib) `Classical.choice`. Existing code was not removed or restructured beyond the `ScopedView` deletion; one general lemma (`Scoped.sub0_ren_succ`) was added to the substitution algebra in the main file. `FINDINGS.md` now documents all of the above; `lakefile.toml` lists the new modules.

# Summary of changes for run 83540449-136b-42ce-9000-604b8b94a80b
## What I did

**1. `Raw` is gone, and the new implementation is now the only one**

All raw (extrinsically scoped) de Bruijn syntax has been deleted, together with everything that existed only to support it (the old `Term.betaSubst`, which was defined by transporting along raw terms, and hence also the scope-*preserving* reduction relation built on it and its counterexamples). Nothing in the project mentions raw terms any more — a search for `Raw` in the Lean sources returns nothing.

The existential-scope implementation is now the default and only one:

```
Scoped := Σ n, Term n                       -- ⟨newFreeIndexes, betaReducedTermTree⟩
Term.shiftAt / Term.substAt / Term.betaSubstSigma      -- notation  M ⟦N⟧  and  M [N]
```

all by direct structural recursion on `Term n`, and beta reduction `—→` is the relation on `Scoped` whose redex rule puts no constraint on the scopes of body and argument.

To make ordinary syntactic reasoning possible without a raw syntax, I proved that `Scoped` is a term algebra in its own right (constructor injectivity, disjointness, structural induction and case analysis, all via a one-layer `Scoped.view`), and rebuilt the whole de Bruijn substitution algebra (`ren`, `sub`, `sub0` and their laws) on it. The structurally defined operations are identified with it: `Scoped.substAt_eq_sub` and `Term.betaSubstSigma_eq_sub0`.

**2. Fewer files**

Three Lean files became two: `IwilareNatIsExactScope.lean` (terms, free-index facts, substitution, beta and parallel reduction, Church-Rosser) and `IwilareNatIsExactScope/Standardization.lean`. I kept the second file separate only because merging would push a single file well past 1000 lines.

**3. Church-Rosser, re-proved without raw terms**

`beta_church_rosser` (plus `beta_confluence` and `betaeq_join` for beta conversion) is proved directly on `Scoped`, by Takahashi's complete developments (`Scoped.cd`, `BetaPar.triangle`), with Mathlib's abstract `Relation.church_rosser` supplying the passage from the diamond property to confluence.

**4. Standardization Theorem**

Mathlib has no untyped lambda calculus, so no standardization theorem to reuse; I proved it from scratch, by Kashima's argument:

```
standardization : a —→* b ↔ a —→ₛ b
```

where `—→ₛ` is the inductive relation of standard reduction sequences (head reduction steps first — the head redex being leftmost-outermost — then the subterms standardly, left to right), built on head reduction `—→ₕ`. The key steps are stability of standard reduction under renaming and substitution and the lemma that standard sequences absorb a beta step at the end. A typical corollary is included: a term that reduces to an abstraction already head-reduces to one (`head_reduces_to_abs`).

**5. Your reading of the index is still confirmed**

`Term.occurs` is now defined by recursion on the exactly-scoped term, and `Term.free_lt_scope`, `Term.max_free_occurs`, `Term.closed_iff_scope_zero` re-prove that `n = 0` ⟺ closed and that for `n > 0` the index `n - 1` really is used.

Everything builds with no errors or warnings; no `sorry`, no `native_decide`, no added axioms (only `propext` and `Quot.sound`, via Mathlib). `FINDINGS.md` has been rewritten to describe the current state of the project.


# Summary of changes for run 899e79e0-b46d-44af-84ae-945b7aebd9cf
## What I did

I added a new module, `IwilareNatIsExactScope/SigmaSubst.lean`, that implements substitution **without any detour through `Raw`**, by direct structural recursion on `Term n`, returning the resulting scope existentially — and then proves Church-Rosser for the resulting calculus. Nothing was removed; the existing files are untouched apart from one cross-reference comment.

**1. The existential (Sigma) type**

```
abbrev Scoped : Type := Σ n : Nat, Term n
  Scoped.newFreeIndexes         -- the number of free indexes, computed
  Scoped.betaReducedTermTree    -- the term tree, of exactly that scope
```
with the three constructors lifted to it (`Scoped.var/abs/app`).

**2. Raw-free implementation, by recursion on `Term`**

```
Term.shiftAt        : {n : Nat} → Nat → Term n → Scoped
Term.substAt        : {n : Nat} → Nat → Scoped → Term n → Scoped
Term.betaSubstSigma : Term m → Term n → Scoped          -- notation  M ⟦N⟧
```
This is exactly what the exact-scope discipline forces: no weakening `Term n → Term (n+1)` is needed, because the shift/substitution simply *returns* the new number of free indexes instead of having it imposed. All the sample substitutions compute by `rfl`, including one where the argument is discarded and the scope genuinely *decreases*. `Term.newFreeIndexes_betaSubstSigma_le` bounds the result: `(M ⟦N⟧).newFreeIndexes ≤ max (m - 1) n`.

Correctness: `Term.toRaw_shiftAt`, `Term.toRaw_substAt`, `Term.toRaw_betaSubstSigma` show these operations compute the usual de Bruijn renaming/substitution, and `Term.betaSubstSigma_eq_betaSubst` shows that on the fragment where the previous scope-preserving `betaSubst` is defined (`M : Term (n+1)`, `N : Term n`) the two agree, the returned `newFreeIndexes` being exactly `n`.

**3. `beta_church_rosser` — now TRUE, and proved**

Returning the scope existentially also repairs beta reduction. The new relation `⟶β` (`SBeta`) has redex rule
```
Scoped.app (Scoped.abs ⟨m, M⟩) ⟨n, N⟩  ⟶β  M ⟦N⟧
```
with **no** constraint relating `m` and `n`, so substitution can no longer destroy a redex — which is what made confluence fail for the scope-preserving relation `—→` (`not_beta_church_rosser`). Proved:

- `Scoped.beta_church_rosser : a ⟶β* b → a ⟶β* c → ∃ d, b ⟶β* d ∧ c ⟶β* d`, and `Scoped.beta_confluence` in `Relation.Join` form;
- `sbeta_of_beta` / `sbetastar_of_betastar`: the new calculus extends the old one;
- `sbeta_cexStuck`, `sbeta_cex_join`: the term that was stuck for `—→` now reduces, and the old counterexample to Church-Rosser is joinable here;
- `sbeta_iff_rbeta1`, `sbetastar_iff_rbetastar`: through the bijection `Scoped ≃ Raw` (`Scoped.toRaw` / `Raw.toScoped`), `⟶β` is *the same* relation as ordinary beta reduction on de Bruijn terms — which is how Church-Rosser is obtained, from the raw Church-Rosser theorem already established in the project.

So the definitions and the statements of the new calculus mention no raw syntax at all; raw terms are used only as an already-verified proof device for the confluence transfer.

Everything builds with no errors or warnings, no `sorry`, no `native_decide`, no added axioms (only `propext`, `Quot.sound` via Mathlib). `FINDINGS.md` has a new section 5 describing all of the above; `lakefile.toml` was extended with the new module.


# Summary of changes for run c886ce1f-3f1e-4ec8-8cf9-f47fd155a7db
## What I did

**1. `betaSubst` is implemented** (in `IwilareNatIsExactScope.lean`)

`Term.betaSubst : Term (n+1) → Term n → Term n` is genuine capture-avoiding substitution of the argument for de Bruijn variable `0`, and it computes (e.g. `(v#0 : Term 1)[Term.id] = Term.id` holds by `rfl`).

It cannot be written by direct recursion on `Term (n+1)`: under a binder one must substitute the *shifted* argument, and shifting is not available in an exact-scope discipline (the shift of a closed term is still closed — `Term 0`, not `Term 1`). So substitution is defined on raw de Bruijn terms, where the scope is computed rather than imposed, and transported back along the key exactness theorem `M.scope = N.scope + 1 → (substAt 0 N M).scope = N.scope`.

One typing repair was unavoidable: `ƛ M ⬝ N` lives in `Term (max n n)` and `max n n` is only *propositionally* equal to `n`, so in `Beta.basis` / `BetaPar.subst` the reduct `M[N] : Term n` is re-indexed with a new `Term.reindex`.

**2. Your reading of the index is correct — and now proved**

`Term.scope_toRaw` (the index equals the scope computed from the term), `Term.free_lt_scope` (every free index is `< n`), `Term.max_free_occurs` (for `n > 0` the index `n-1` really occurs), `Term.closed_iff_scope_zero` (`n = 0 ↔` closed).

**3. `beta_church_rosser` is FALSE for this calculus — I proved its negation**

With `𝟙 = ƛ v#0`, the closed term `R = (ƛ ((ƛ v#1) ⬝ v#0)) ⬝ 𝟙` reduces to `(ƛ 𝟙) ⬝ 𝟙` (outer redex first) and to `𝟙` (inner redex first), and these are two *distinct normal forms*: `ƛ 𝟙` has a **closed** body `𝟙 : Term 0`, while `Beta.basis` needs a body of type `Term (n+1)`, so that redex can never be contracted. Root cause: weakening `Term n → Term (n+1)` does not exist in an exact-scope discipline, so the calculus is not closed under substitution — substitution can destroy a redex.

Proved: `not_beta_church_rosser`, `not_beta_confluence`, `not_betapar_diamond`, `not_betapar_subst` (the missing lemma the original proof relied on), and also `not_betapar_refl` (`⇉` is not even reflexive: `Term.zero = ƛ (ƛ v#0)` is `⇉`-stuck), `not_beta_to_betapar`, `not_betastar_to_betaparstar`.

Consequently the following are unprovable and are **kept, commented out, with an explanation** next to each: the `Std.Refl` instance, `beta_to_betapar`, `betapar_star_eq_betastar` (only the `⇉* → —→*` half survives, added as `betaparstar_to_betastar`), `takahashi` (not even well-typed here — in `(ƛ M) ⬝ N` nothing forces the scope of the body to be one more than that of the argument), `takahashi_triangle`, `betapar_diamond`, `betapar_strip`, `beta_confluence`, `beta_strip`, `betapar_church_rosser`, `beta_church_rosser`. Nothing was deleted.

**4. What is true: Church-Rosser for the underlying raw calculus**

`IwilareNatIsExactScope/RawChurchRosser.lean` builds the de Bruijn substitution algebra and proves the Church-Rosser theorem for raw terms by Takahashi's complete developments (`Raw.raw_church_rosser`), then derives `beta_church_rosser_raw`: two reducts of an exactly-scoped term are always joinable **as raw terms** — just not inside `Term n`. So the exact-scope discipline is the only culprit. (`lakefile.toml` was extended to build the new module.)

A prose write-up of all of this is in `FINDINGS.md`.

Everything builds with no errors or warnings; no `sorry`, no `native_decide`, no added axioms (only `propext`, `Quot.sound`, `Classical.choice` via Mathlib).
