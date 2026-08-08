-- Redexes *as positions in the expression tree*, and evaluation strategies
-- parametrized by a tree-traversal order.
--
-- A position is a path from the root of a term to one of its subterms
-- (`Dir.body` goes under a binder, `Dir.fn` into the function part of an
-- application, `Dir.arg` into the argument).  `reduceAt p t` contracts the
-- redex at the position `p`, if there is one there, and *every* beta step of
-- `t` is `reduceAt p t` for some position `p` (`reduceAt_complete`): choosing a
-- beta step is exactly choosing a redex position.
--
-- A *strategy* is then nothing but a way of ordering the positions of a term:
-- `stepWith order t` contracts the first redex met along the traversal
-- `order`.  Three traversals are given -- preorder (depth-first, root before
-- the subtrees), postorder (depth-first, subtrees before the root) and
-- breadth-first (level by level) -- and the resulting strategies are the
-- leftmost-outermost, the leftmost-innermost and the outermost breadth-first
-- one.  Any traversal that lists all the redex positions gives a strategy which
-- steps exactly when the term is not normal.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Strategies

@[expose] public section

namespace FinScope

open Term

/-! ## 1. Positions in an expression tree -/

/-- A direction to descend in the expression tree of a term. -/
inductive Dir where
  /-- Descend under a binder, into the body of an abstraction. -/
  | body : Dir
  /-- Descend into the function part of an application. -/
  | fn : Dir
  /-- Descend into the argument part of an application. -/
  | arg : Dir
  deriving DecidableEq, Repr

/-- A position in an expression tree: the path from the root to a subterm. -/
abbrev Pos : Type := List Dir

namespace Term

/-- `reduceAt p t` contracts the redex of `t` at the position `p`, if the
    subterm at `p` is a redex (and fails otherwise). -/
def reduceAt : {n : Nat} → Pos → Term n → Option (Term n)
  | _, [], .app a b => contract a b
  | _, [], _ => none
  | _, Dir.body :: r, .abs t => (reduceAt r t).map Term.abs
  | _, Dir.fn :: r, .app a b => (reduceAt r a).map (· ⬝ b)
  | _, Dir.arg :: r, .app a b => (reduceAt r b).map (a ⬝ ·)
  | _, _, _ => none

@[simp] theorem reduceAt_nil_app {n : Nat} (a b : Term n) :
    reduceAt [] (a ⬝ b) = contract a b := rfl
@[simp] theorem reduceAt_nil_abs {n : Nat} (t : Term (n + 1)) : reduceAt [] (ƛ t) = none := rfl
@[simp] theorem reduceAt_body {n : Nat} (r : Pos) (t : Term (n + 1)) :
    reduceAt (Dir.body :: r) (ƛ t) = (reduceAt r t).map Term.abs := rfl
@[simp] theorem reduceAt_body_app {n : Nat} (r : Pos) (a b : Term n) :
    reduceAt (Dir.body :: r) (a ⬝ b) = none := rfl
@[simp] theorem reduceAt_fn {n : Nat} (r : Pos) (a b : Term n) :
    reduceAt (Dir.fn :: r) (a ⬝ b) = (reduceAt r a).map (· ⬝ b) := rfl
@[simp] theorem reduceAt_fn_abs {n : Nat} (r : Pos) (t : Term (n + 1)) :
    reduceAt (Dir.fn :: r) (ƛ t) = none := rfl
@[simp] theorem reduceAt_arg {n : Nat} (r : Pos) (a b : Term n) :
    reduceAt (Dir.arg :: r) (a ⬝ b) = (reduceAt r b).map (a ⬝ ·) := rfl
@[simp] theorem reduceAt_arg_abs {n : Nat} (r : Pos) (t : Term (n + 1)) :
    reduceAt (Dir.arg :: r) (ƛ t) = none := rfl
@[simp] theorem reduceAt_var {n : Nat} (p : Pos) (i : Fin n) : reduceAt p (v# i) = none := by
  cases p with
  | nil => rfl
  | cons d r => cases d <;> rfl

end Term

/-- Mapping an option does not change whether it is defined. -/
theorem isSome_map {α β : Type} (o : Option α) (f : α → β) : (o.map f).isSome = o.isSome := by
  cases o <;> rfl

/-- Contracting the redex at a position is a beta step. -/
theorem reduceAt_sound : ∀ (p : Pos) {n : Nat} {t t' : Term n},
    Term.reduceAt p t = some t' → t —→ t' := by
  intro p
  induction p with
  | nil =>
      intro n t t' h
      cases t with
      | var i => exact absurd h (by simp)
      | abs u => exact absurd h (by simp)
      | app a b =>
          cases a with
          | abs q =>
              rw [Term.reduceAt_nil_app, Term.contract_abs] at h
              obtain rfl : t' = q [ b ] := (Option.some.inj h).symm
              exact Beta.basis q b
          | var i => exact absurd h (by simp)
          | app x y => exact absurd h (by simp)
  | cons d r ih =>
      intro n t t' h
      cases d with
      | body =>
          cases t with
          | abs u =>
              rw [Term.reduceAt_body, Option.map_eq_some_iff] at h
              obtain ⟨q, hq, rfl⟩ := h
              exact Beta.abs (ih hq)
          | var i => exact absurd h (by simp)
          | app a b => exact absurd h (by simp)
      | fn =>
          cases t with
          | app a b =>
              rw [Term.reduceAt_fn, Option.map_eq_some_iff] at h
              obtain ⟨a', ha', rfl⟩ := h
              exact Beta.appL (ih ha')
          | var i => exact absurd h (by simp)
          | abs u => exact absurd h (by simp)
      | arg =>
          cases t with
          | app a b =>
              rw [Term.reduceAt_arg, Option.map_eq_some_iff] at h
              obtain ⟨b', hb', rfl⟩ := h
              exact Beta.appR (ih hb')
          | var i => exact absurd h (by simp)
          | abs u => exact absurd h (by simp)

/-- Every beta step contracts the redex at some position. -/
theorem reduceAt_complete {n : Nat} {t t' : Term n} (h : t —→ t') :
    ∃ p : Pos, Term.reduceAt p t = some t' := by
  induction h with
  | basis M N => exact ⟨[], by simp⟩
  | abs _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨Dir.body :: p, by simp [hp]⟩
  | appL _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨Dir.fn :: p, by simp [hp]⟩
  | appR _ ih => obtain ⟨p, hp⟩ := ih; exact ⟨Dir.arg :: p, by simp [hp]⟩

/-- A normal term has no redex at any position. -/
theorem reduceAt_eq_none_of_normal {n : Nat} {t : Term n} (hn : Normal t) (p : Pos) :
    Term.reduceAt p t = none := by
  cases h : Term.reduceAt p t with
  | none => rfl
  | some t' => exact absurd (reduceAt_sound p h) (hn t')

/-! ## 2. The redex positions of a term, in several traversal orders -/

namespace Term

/-- The redex positions of a term in *preorder* (depth-first, a node before its
    subtrees, the function part before the argument). -/
def redexPre : {n : Nat} → Term n → List Pos
  | _, .var _ => []
  | _, .abs t => (redexPre t).map (Dir.body :: ·)
  | _, .app a b =>
      (if isAbsB a then [([] : Pos)] else []) ++
        (redexPre a).map (Dir.fn :: ·) ++ (redexPre b).map (Dir.arg :: ·)

/-- The redex positions of a term in *postorder* (depth-first, the subtrees
    before the node). -/
def redexPost : {n : Nat} → Term n → List Pos
  | _, .var _ => []
  | _, .abs t => (redexPost t).map (Dir.body :: ·)
  | _, .app a b =>
      (redexPost a).map (Dir.fn :: ·) ++ (redexPost b).map (Dir.arg :: ·) ++
        (if isAbsB a then [([] : Pos)] else [])

/-- Concatenate two lists of levels level by level. -/
def mergeLevels : List (List Pos) → List (List Pos) → List (List Pos)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x ++ y) :: mergeLevels xs ys

/-- The redex positions of a term, grouped by their depth in the tree. -/
def redexLevels : {n : Nat} → Term n → List (List Pos)
  | _, .var _ => []
  | _, .abs t => [] :: (redexLevels t).map (fun l => l.map (Dir.body :: ·))
  | _, .app a b =>
      (if isAbsB a then [([] : Pos)] else []) ::
        mergeLevels ((redexLevels a).map (fun l => l.map (Dir.fn :: ·)))
          ((redexLevels b).map (fun l => l.map (Dir.arg :: ·)))

/-- The redex positions of a term in *breadth-first* order (level by level,
    outermost redexes first). -/
def redexBF {n : Nat} (t : Term n) : List Pos := (redexLevels t).flatten

@[simp] theorem redexPre_var {n : Nat} (i : Fin n) : redexPre (v# i) = [] := rfl
@[simp] theorem redexPre_abs {n : Nat} (t : Term (n + 1)) :
    redexPre (ƛ t) = (redexPre t).map (Dir.body :: ·) := rfl
@[simp] theorem redexPre_app {n : Nat} (a b : Term n) :
    redexPre (a ⬝ b) = (if isAbsB a then [([] : Pos)] else []) ++
      (redexPre a).map (Dir.fn :: ·) ++ (redexPre b).map (Dir.arg :: ·) := rfl
@[simp] theorem redexPost_var {n : Nat} (i : Fin n) : redexPost (v# i) = [] := rfl
@[simp] theorem redexPost_abs {n : Nat} (t : Term (n + 1)) :
    redexPost (ƛ t) = (redexPost t).map (Dir.body :: ·) := rfl
@[simp] theorem redexPost_app {n : Nat} (a b : Term n) :
    redexPost (a ⬝ b) = (redexPost a).map (Dir.fn :: ·) ++ (redexPost b).map (Dir.arg :: ·) ++
      (if isAbsB a then [([] : Pos)] else []) := rfl

end Term

/-! ### The traversals list exactly the redex positions -/

theorem mem_redexPre_iff {n : Nat} {t : Term n} {p : Pos} :
    p ∈ Term.redexPre t ↔ (Term.reduceAt p t).isSome := by
  induction t generalizing p with
  | var i => simp
  | abs u ih =>
      constructor
      · intro h
        simp only [Term.redexPre_abs, List.mem_map] at h
        obtain ⟨q, hq, rfl⟩ := h
        rw [Term.reduceAt_body, isSome_map]
        exact ih.mp hq
      · intro h
        cases p with
        | nil => exact absurd h (by simp)
        | cons d r =>
            cases d with
            | body =>
                rw [Term.reduceAt_body, isSome_map] at h
                simp only [Term.redexPre_abs, List.mem_map]
                exact ⟨r, ih.mpr h, rfl⟩
            | fn => exact absurd h (by simp)
            | arg => exact absurd h (by simp)
  | app a b iha ihb =>
      constructor
      · intro h
        simp only [Term.redexPre_app, List.mem_append, List.mem_map] at h
        rcases h with (h | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
        · cases hab : Term.isAbsB a with
          | false => rw [hab] at h; exact absurd h (by simp)
          | true =>
              rw [hab] at h
              obtain rfl : p = ([] : Pos) := by simpa using h
              obtain ⟨q, rfl⟩ := Term.isAbsB_iff.mp hab
              simp
        · rw [Term.reduceAt_fn, isSome_map]; exact iha.mp hq
        · rw [Term.reduceAt_arg, isSome_map]; exact ihb.mp hq
      · intro h
        simp only [Term.redexPre_app, List.mem_append, List.mem_map]
        cases p with
        | nil =>
            refine Or.inl (Or.inl ?_)
            cases a with
            | abs q => simp
            | var i => rw [Term.reduceAt_nil_app] at h; exact absurd h (by simp)
            | app x y => rw [Term.reduceAt_nil_app] at h; exact absurd h (by simp)
        | cons d r =>
            cases d with
            | body => exact absurd h (by simp)
            | fn =>
                rw [Term.reduceAt_fn, isSome_map] at h
                exact Or.inl (Or.inr ⟨r, iha.mpr h, rfl⟩)
            | arg =>
                rw [Term.reduceAt_arg, isSome_map] at h
                exact Or.inr ⟨r, ihb.mpr h, rfl⟩

theorem mem_redexPost_iff {n : Nat} {t : Term n} {p : Pos} :
    p ∈ Term.redexPost t ↔ (Term.reduceAt p t).isSome := by
  induction t generalizing p with
  | var i => simp
  | abs u ih =>
      constructor
      · intro h
        simp only [Term.redexPost_abs, List.mem_map] at h
        obtain ⟨q, hq, rfl⟩ := h
        rw [Term.reduceAt_body, isSome_map]
        exact ih.mp hq
      · intro h
        cases p with
        | nil => exact absurd h (by simp)
        | cons d r =>
            cases d with
            | body =>
                rw [Term.reduceAt_body, isSome_map] at h
                simp only [Term.redexPost_abs, List.mem_map]
                exact ⟨r, ih.mpr h, rfl⟩
            | fn => exact absurd h (by simp)
            | arg => exact absurd h (by simp)
  | app a b iha ihb =>
      constructor
      · intro h
        simp only [Term.redexPost_app, List.mem_append, List.mem_map] at h
        rcases h with (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | h
        · rw [Term.reduceAt_fn, isSome_map]; exact iha.mp hq
        · rw [Term.reduceAt_arg, isSome_map]; exact ihb.mp hq
        · cases hab : Term.isAbsB a with
          | false => rw [hab] at h; exact absurd h (by simp)
          | true =>
              rw [hab] at h
              obtain rfl : p = ([] : Pos) := by simpa using h
              obtain ⟨q, rfl⟩ := Term.isAbsB_iff.mp hab
              simp
      · intro h
        simp only [Term.redexPost_app, List.mem_append, List.mem_map]
        cases p with
        | nil =>
            refine Or.inr ?_
            cases a with
            | abs q => simp
            | var i => rw [Term.reduceAt_nil_app] at h; exact absurd h (by simp)
            | app x y => rw [Term.reduceAt_nil_app] at h; exact absurd h (by simp)
        | cons d r =>
            cases d with
            | body => exact absurd h (by simp)
            | fn =>
                rw [Term.reduceAt_fn, isSome_map] at h
                exact Or.inl (Or.inl ⟨r, iha.mpr h, rfl⟩)
            | arg =>
                rw [Term.reduceAt_arg, isSome_map] at h
                exact Or.inl (Or.inr ⟨r, ihb.mpr h, rfl⟩)

/-! ### The breadth-first traversal lists the same positions -/

theorem flatten_map_map (f : Pos → Pos) (L : List (List Pos)) :
    (L.map (fun l => l.map f)).flatten = L.flatten.map f := by
  rw [List.map_flatten]

theorem mem_mergeLevels {p : Pos} : ∀ xs ys : List (List Pos),
    p ∈ (Term.mergeLevels xs ys).flatten ↔ p ∈ xs.flatten ∨ p ∈ ys.flatten := by
  intro xs
  induction xs with
  | nil => intro ys; simp [Term.mergeLevels]
  | cons x xs ih =>
      intro ys
      cases ys with
      | nil => simp [Term.mergeLevels]
      | cons y ys =>
          simp only [Term.mergeLevels, List.flatten_cons, List.mem_append, ih ys]
          constructor
          · rintro ((h | h) | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inr h)
          · rintro ((h | h) | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inr h)

theorem redexBF_var {n : Nat} (i : Fin n) : Term.redexBF (v# i) = [] := rfl

theorem redexBF_abs {n : Nat} (t : Term (n + 1)) :
    Term.redexBF (ƛ t) = (Term.redexBF t).map (Dir.body :: ·) := by
  rw [Term.redexBF, Term.redexLevels, List.flatten_cons, List.nil_append,
    flatten_map_map, Term.redexBF]

theorem mem_redexBF_app {n : Nat} {a b : Term n} {p : Pos} :
    p ∈ Term.redexBF (a ⬝ b) ↔
      p ∈ (if Term.isAbsB a then [([] : Pos)] else []) ∨
        p ∈ (Term.redexBF a).map (Dir.fn :: ·) ∨ p ∈ (Term.redexBF b).map (Dir.arg :: ·) := by
  simp only [Term.redexBF, Term.redexLevels, List.flatten_cons, List.mem_append,
    mem_mergeLevels, flatten_map_map]

/-- The breadth-first traversal visits the same positions as the preorder
    traversal. -/
theorem mem_redexBF_iff_mem_redexPre {n : Nat} {t : Term n} {p : Pos} :
    p ∈ Term.redexBF t ↔ p ∈ Term.redexPre t := by
  induction t generalizing p with
  | var i => rw [redexBF_var]; simp
  | abs u ih =>
      rw [redexBF_abs, Term.redexPre_abs]
      simp only [List.mem_map]
      exact ⟨fun ⟨q, hq, hp⟩ => ⟨q, ih.mp hq, hp⟩, fun ⟨q, hq, hp⟩ => ⟨q, ih.mpr hq, hp⟩⟩
  | app a b iha ihb =>
      rw [mem_redexBF_app, Term.redexPre_app]
      simp only [List.mem_append, List.mem_map]
      constructor
      · rintro (h | ⟨q, hq, hp⟩ | ⟨q, hq, hp⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨q, iha.mp hq, hp⟩)
        · exact Or.inr ⟨q, ihb.mp hq, hp⟩
      · rintro ((h | ⟨q, hq, hp⟩) | ⟨q, hq, hp⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨q, iha.mpr hq, hp⟩)
        · exact Or.inr (Or.inr ⟨q, ihb.mpr hq, hp⟩)

theorem mem_redexBF_iff {n : Nat} {t : Term n} {p : Pos} :
    p ∈ Term.redexBF t ↔ (Term.reduceAt p t).isSome :=
  mem_redexBF_iff_mem_redexPre.trans mem_redexPre_iff

/-! ## 3. Strategies parametrized by a traversal order -/

/-- A *tree-traversal order*: for each term, the list of the positions of its
    expression tree to be visited, in the order in which they are visited.  Any
    such order gives an evaluation strategy, `stepWith`. -/
def TraversalOrder : Type := (n : Nat) → Term n → List Pos

/-- The strategy attached to a traversal order: contract the redex at the first
    position of the traversal at which there is one. -/
def stepWith (order : TraversalOrder) {n : Nat} (t : Term n) : Option (Term n) :=
  (order n t).findSome? (fun p => Term.reduceAt p t)

/-- Whatever the traversal order, a step of the strategy it defines is a beta
    step. -/
theorem stepWith_sound {order : TraversalOrder} {n : Nat} {t t' : Term n}
    (h : stepWith order t = some t') : t —→ t' := by
  rw [stepWith, List.findSome?_eq_some_iff] at h
  obtain ⟨_, p, _, _, hp, _⟩ := h
  exact reduceAt_sound p hp

/-- A traversal order is *complete* when it visits every redex position. -/
def Covers (order : TraversalOrder) : Prop :=
  ∀ (n : Nat) (t : Term n) (p : Pos), (Term.reduceAt p t).isSome → p ∈ order n t

/-- A complete traversal order yields a strategy that gets stuck exactly on the
    normal forms. -/
theorem stepWith_none_iff_normal {order : TraversalOrder} (hc : Covers order) {n : Nat}
    {t : Term n} : stepWith order t = none ↔ Normal t := by
  rw [stepWith, List.findSome?_eq_none_iff]
  constructor
  · intro h t' hstep
    obtain ⟨p, hp⟩ := reduceAt_complete hstep
    have hmem : p ∈ order n t := hc n t p (by rw [hp]; rfl)
    rw [h p hmem] at hp
    exact absurd hp (by simp)
  · intro hn p _
    exact reduceAt_eq_none_of_normal hn p

/-- The preorder traversal. -/
def preorder : TraversalOrder := fun _ t => Term.redexPre t

/-- The postorder traversal. -/
def postorder : TraversalOrder := fun _ t => Term.redexPost t

/-- The breadth-first traversal. -/
def breadthFirst : TraversalOrder := fun _ t => Term.redexBF t

theorem preorder_covers : Covers preorder :=
  fun _ _ _ h => mem_redexPre_iff.mpr h

theorem postorder_covers : Covers postorder :=
  fun _ _ _ h => mem_redexPost_iff.mpr h

theorem breadthFirst_covers : Covers breadthFirst :=
  fun _ _ _ h => mem_redexBF_iff.mpr h

/-! ## 4. The named strategies are traversal strategies

The leftmost-outermost strategy of `FinScope/Leftmost.lean` is the strategy of
the preorder traversal, and the leftmost-innermost strategy of
`FinScope/Strategies.lean` is the strategy of the postorder traversal. -/

theorem findSome?_map_option {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases hx : f x with
      | none => simp [hx, ih]
      | some y => simp [hx]

theorem stepWith_preorder_eq_lstep {n : Nat} (t : Term n) :
    stepWith preorder t = Term.lstep t := by
  induction t with
  | var i => rfl
  | abs u ih =>
      rw [stepWith, preorder] at ih ⊢
      simp only [Term.redexPre_abs, List.findSome?_map, Function.comp_def, Term.reduceAt_body,
        findSome?_map_option, ih, Term.lstep_abs]
  | app a b iha ihb =>
      rw [stepWith, preorder] at iha ihb ⊢
      cases hab : Term.isAbsB a with
      | true =>
          obtain ⟨q, rfl⟩ := Term.isAbsB_iff.mp hab
          rfl
      | false =>
          rw [Term.lstep_app_of_not_isAbs hab]
          simp only [Term.redexPre_app, hab, List.findSome?_append,
            List.findSome?_map, Function.comp_def, Term.reduceAt_fn, Term.reduceAt_arg,
            findSome?_map_option, iha, ihb]
          cases Term.lstep a with
          | none => simp
          | some a' => simp

theorem stepWith_postorder_eq_istep {n : Nat} (t : Term n) :
    stepWith postorder t = Term.istep t := by
  induction t with
  | var i => rfl
  | abs u ih =>
      rw [stepWith, postorder] at ih ⊢
      simp only [Term.redexPost_abs, List.findSome?_map, Function.comp_def, Term.reduceAt_body,
        findSome?_map_option, ih, Term.istep_abs]
  | app a b iha ihb =>
      rw [stepWith, postorder] at iha ihb ⊢
      simp only [Term.redexPost_app, List.findSome?_append, List.findSome?_map, Function.comp_def,
        Term.reduceAt_fn, Term.reduceAt_arg, findSome?_map_option, iha, ihb]
      cases ha : Term.istep a with
      | some a' => simp [Term.istep_app_some_left ha]
      | none =>
        cases hb : Term.istep b with
        | some b' => simp [Term.istep_app_some_right ha hb]
        | none =>
            rw [Term.istep_app_of_none ha hb]
            cases a with
            | abs q => simp
            | var i => simp
            | app x y => simp

/-- The breadth-first strategy is a genuine strategy too: it steps exactly when
    the term is not normal, and its steps are beta steps. -/
theorem stepWith_breadthFirst_sound {n : Nat} {t t' : Term n}
    (h : stepWith breadthFirst t = some t') : t —→ t' :=
  stepWith_sound h

theorem stepWith_breadthFirst_none_iff_normal {n : Nat} {t : Term n} :
    stepWith breadthFirst t = none ↔ Normal t :=
  stepWith_none_iff_normal breadthFirst_covers

/-! ## 5. A fuelled evaluator for an arbitrary traversal order -/

/-- Iterate the strategy of a traversal order. -/
def evalWith (order : TraversalOrder) {n : Nat} : Nat → Term n → Option (Term n)
  | 0, s => match stepWith order s with
    | none => some s
    | some _ => none
  | fuel + 1, s =>
    match stepWith order s with
    | none => some s
    | some t => evalWith order fuel t

/-- Whatever the traversal order, the evaluator it defines only performs beta
    reductions, and (if the order is complete) stops on a normal form. -/
theorem evalWith_sound {order : TraversalOrder} (hc : Covers order) {n : Nat} :
    ∀ (fuel : Nat) {s t : Term n}, evalWith order fuel s = some t → s —→* t ∧ Normal t := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      cases hs : stepWith order s with
      | none =>
          rw [evalWith, hs] at h
          cases h
          exact ⟨.refl, (stepWith_none_iff_normal hc).mp hs⟩
      | some u =>
          rw [evalWith, hs] at h
          exact absurd h (by simp)
  | succ f ih =>
      intro s t h
      cases hs : stepWith order s with
      | none =>
          rw [evalWith, hs] at h
          cases h
          exact ⟨.refl, (stepWith_none_iff_normal hc).mp hs⟩
      | some u =>
          rw [evalWith, hs] at h
          obtain ⟨hred, hnorm⟩ := ih h
          exact ⟨Relation.ReflTransGen.head (stepWith_sound hs) hred, hnorm⟩

/-! ## 6. The traversal strategies at work

`sample = (λx. (λy. x) x) 𝟙` is evaluated to `𝟙` by each of the three
traversals. -/

example : evalWith preorder 10 sample = some sid := by rfl

example : evalWith postorder 10 sample = some sid := by rfl

example : evalWith breadthFirst 10 sample = some sid := by rfl

end FinScope
