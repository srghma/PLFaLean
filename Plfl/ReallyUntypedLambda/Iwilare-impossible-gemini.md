
# `beta_strip_refl` for single-step Beta reduction (`—→`) **cannot be proved because it is mathematically false**

Here is the exact counterexample written in Lean 4 proving why `beta_strip_refl` is false.

---

### The Counterexample in Lean 4

Consider $I = (\lambda y. y)$ and $a = (\lambda x. x\ x) (I\ I)$.

From $a$, we take two single Beta steps $a \longrightarrow b$ and $a \longrightarrow c$:

- $b = (I\ I) (I\ I)$ (by contracting the outer redex)
- $c = (\lambda x. x\ x) I$ (by contracting the inner $I\ I$)

```lean
def I : Term 0 := ƛ (v#0)
def delta : Term 0 := ƛ (v#0 ⬝ v#0)
def term_a : Term 0 := delta ⬝ (I ⬝ I)
def term_b : Term 0 := (I ⬝ I) ⬝ (I ⬝ I)
def term_c : Term 0 := delta ⬝ I

theorem hab : term_a —→ term_b := Beta.basis (v#0 ⬝ v#0) (I ⬝ I)
theorem hac : term_a —→ term_c := Beta.appl delta (Beta.basis (v#0) I)
```

Now let's find all terms $d$ reachable from $c$ via multi-step $c \longrightarrow^* d$:

- $c = (\lambda x. x\ x) I$
- $I\ I$
- $I$

For `beta_strip_refl` to hold, $b$ must be able to reach one of these terms in **at most 1 single step** ($b \longrightarrow^{\le 1} d$):

- $b \longrightarrow^{\le 1} c$ is **false** (`¬ (term_b —→≤1 term_c)`)
- $b \longrightarrow^{\le 1} (I\ I)$ is **false** (`¬ (term_b —→≤1 (I ⬝ I))`)
- $b \longrightarrow^{\le 1} I$ is **false** (`¬ (term_b —→≤1 I)`)

In Lean 4, both of these are proven false in one tactic line:

```lean
theorem not_reflGen_b_c : ¬ (term_b —→≤1 term_c) := by
  intro h; cases h with | single h_step => cases h_step

theorem not_reflGen_b_II : ¬ (term_b —→≤1 (I ⬝ I)) := by
  intro h; cases h with | single h_step => cases h_step
```

---

### Why Does $b$ Fail the $\le 1$ Step Requirement?

To reach $I\ I$ from $b = (I\ I) (I\ I)$, it takes **2 single steps**:
$$b = (I\ I) (I\ I) \longrightarrow I (I\ I) \longrightarrow I\ I$$

Because $b$ requires **2** steps instead of $\le 1$, Mathlib's `Relation.church_rosser` (which requires $\le 1$ step via `ReflGen`) cannot be applied directly to single-step Beta reduction (`—→`).

---

### How to Formalize Church-Rosser Correctly in Lean 4

1. **Use `betapar_strip_refl` with Parallel Reduction ($\rightrightarrows$)**:
   Parallel reduction contracts both $(I\ I)$ redexes in $b$ in **1 parallel step**, so $b \rightrightarrows I\ I$ holds in $\le 1$ parallel step!

   ```lean
   theorem betapar_strip_refl {n : Nat} (a b c : Term n) (hab : a ⇉ b) (hac : a ⇉ c) :
       ∃ d, Relation.ReflGen BetaPar b d ∧ Relation.ReflTransGen BetaPar c d := by
     rcases betapar_diamond hab hac with ⟨d, hbd, hcd⟩
     exact ⟨d, Relation.ReflGen.single hbd, Relation.ReflTransGen.single hcd⟩

   theorem betapar_church_rosser {n : Nat} {a b c : Term n}
       (hab : a ⇉* b) (hac : a ⇉* c) : Relation.Join (Relation.ReflTransGen BetaPar) b c :=
     Relation.church_rosser betapar_strip_refl hab hac
   ```

2. **Transfer to Single-Step `beta_church_rosser` (`—→*`)**:

   ```lean
   theorem beta_church_rosser {n : Nat} {a b c : Term n}
       (hab : a —→* b) (hac : a —→* c) : BetaJoin b c := by
     have hab_par : a ⇉* b := betapar_star_eq_betastar.mpr hab
     have hac_par : a ⇉* c := betapar_star_eq_betastar.mpr hac
     rcases betapar_church_rosser hab_par hac_par with ⟨d, hbd, hcd⟩
     exact ⟨d, betapar_star_eq_betastar.mp hbd, betapar_star_eq_betastar.mp hcd⟩
   ```
