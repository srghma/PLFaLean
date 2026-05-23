module

public import Lean
public import Plfl.Init.PDecidable

public section

namespace Plfl.Init.Deriving.PDecidable

open Lean Meta Elab Command Term Parser.Term

/-! ── Deriver ───────────────────────────────────────────────────────────── -/
/-
  Generated shape for a two-constructor type:

    match (inferInstance : PDecidable T₁) with
    | .isTrue  a  => .isTrue  (Ctor₁ a)
    | .isFalse na =>
      match (inferInstance : PDecidable T₂) with
      | .isTrue  b   => .isTrue  (Ctor₂ b)
      | .isFalse na₁ =>
        .isFalse (fun x => match x with     -- na, na₁ are BOTH in scope here
          | @Ctor₁ _ _ a => na  a
          | @Ctor₂ _ _ b => na₁ b)
-/

-- Helper to manually construct a match alternative `| pat => rhs`
-- This entirely avoids the confusing `matchAlt| |` syntax and parser alias bugs.
def mkMatchAlt (pat rhs : TSyntax `term) : TSyntax ``Lean.Parser.Term.matchAlt :=
  ⟨Syntax.node .none ``Lean.Parser.Term.matchAlt #[
    Syntax.atom .none "|",
    Syntax.node .none nullKind #[Syntax.node .none nullKind #[pat.raw]],
    Syntax.atom .none "=>",
    rhs.raw
  ]⟩

def mkCleanFreshIdent (base : Name) : TermElabM Ident := do
  let n ← mkFreshUserName base
  let s := n.toString.replace "." "_"
  return mkIdent (Name.mkSimple s)

partial def sanitizeSyntaxDot (stx : Syntax) : Syntax :=
  match stx with
  | .ident info rawVal val prs =>
      let s := val.toString.replace "." "_"
      .ident info rawVal (Name.mkSimple s) prs
  | .node info kind args =>
      .node info kind (args.map sanitizeSyntaxDot)
  | other => other

mutual

  -- Try each constructor; accumulate isFalse arms as we go deeper.
  partial def buildCtors
      (indVal   : InductiveVal)
      (params   : Array Expr)
      (ctors    : List Name)
      (failAlts : Array (TSyntax `Lean.Parser.Term.matchAlt))
      : TermElabM (TSyntax `term) := do
    match ctors with
    | [] =>
      if failAlts.isEmpty then `(PDecidable.isFalse (fun x => nomatch x))
      else `(PDecidable.isFalse (fun x => match x with $failAlts:matchAlt*))
    | ctor :: rest =>
      let ctorInfo ← getConstInfoCtor ctor
      let fields : Array (Name × Expr) ←
        forallTelescope ctorInfo.type fun xs _ => do
          let mut fs := #[]
          let ctorParams := xs[0:indVal.numParams].toArray
          for i in [indVal.numParams : xs.size] do
            let d ← xs[i]!.fvarId!.getDecl
            let tySubst := d.type.replaceFVars ctorParams params
            fs := fs.push (d.userName, tySubst)
          return fs
      buildFields indVal params ctor fields.toList #[] rest failAlts

  -- Decide each field in turn via `inferInstance : PDecidable FieldType`.
  partial def buildFields
      (indVal    : InductiveVal)
      (params    : Array Expr)
      (ctorName  : Name)
      (remaining : List (Name × Expr))
      (doneIds   : Array Ident)
      (restCtors : List Name)
      (failAlts  : Array (TSyntax ``Lean.Parser.Term.matchAlt))
      : TermElabM (TSyntax `term) := do
    match remaining with
    | [] =>
      -- All fields inhabited → .isTrue (Ctor f₁ f₂ …)
      let args : Array (TSyntax `term) := doneIds.map (⟨·.raw⟩)
      let c := mkIdent ctorName
      if args.isEmpty then `(PDecidable.isTrue $c)
      else `(PDecidable.isTrue ($c $args*))
    | (nm, ty) :: rest =>
      let id   ← mkCleanFreshIdent nm
      let naId ← mkCleanFreshIdent `na
      let tySyn ← PrettyPrinter.delab ty
      let tySyn : TSyntax `term := ⟨sanitizeSyntaxDot tySyn.raw⟩

      -- Pattern: @Ctor {params…} prev… id _… (wildcards for remaining fields)
      let mut pats : Array (TSyntax `term) := #[]
      for _ in [:indVal.numParams] do pats := pats.push (← `(_))
      for d  in doneIds            do pats := pats.push ⟨d.raw⟩
      pats := pats.push (← `($id))
      for _ in [:rest.length]      do pats := pats.push (← `(_))

      -- Construct the pattern and RHS safely, then combine them.
      let pat ← `(@$(mkIdent ctorName) $pats*)
      let rhs ← `($naId $id)
      let failAlt := mkMatchAlt pat rhs

      let ok   ← buildFields indVal params ctorName rest (doneIds.push id) restCtors failAlts
      let fail ← buildCtors  indVal params restCtors (failAlts.push failAlt)
      `(match (inferInstance : PDecidable $tySyn) with
        | PDecidable.isTrue  $id   => $ok
        | PDecidable.isFalse $naId => $fail)

end

def mkInst (declName : Name) : CommandElabM Unit := do
  let indVal ← liftTermElabM <| getConstInfoInduct declName
  let cmd ← liftTermElabM do
    -- Collect {implicit param} and [PDecidable type-param] binders
    let (implB, instB, appA, body) ← forallTelescope indVal.type fun params _ => do
      let mut implB : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
      let mut instB : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
      let mut appA  : Array (TSyntax `term)            := #[]
      for i in [:params.size] do
        let d  ← params[i]!.fvarId!.getDecl
        let id := mkIdent (Name.mkSimple (d.userName.toString.replace "." "_"))
        let ty ← PrettyPrinter.delab d.type
        let ty : TSyntax `term := ⟨sanitizeSyntaxDot ty.raw⟩
        appA  := appA.push  (← `($id))
        implB := implB.push (← `(bracketedBinder| {$id : $ty}))
        -- Only add [PDecidable p] for type parameters (those whose type is a Sort)
        if i < indVal.numParams && (← inferType params[i]!).isSort then
          instB := instB.push (← `(bracketedBinder| [PDecidable $id]))
      let body ← buildCtors indVal params indVal.ctors #[]
      return (implB, instB, appA, body)
    let lhs  ←
      if appA.isEmpty then `(PDecidable $(mkIdent declName))
      else `(PDecidable ($(mkIdent declName) $appA*))
    let bs := implB ++ instB          -- one uniform array, one clean splice
    if bs.isEmpty then `(command| instance : $lhs := $body)
    else          `(command| instance $bs:bracketedBinder* : $lhs := $body)
  elabCommand cmd

def derivePDecidable (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do mkInst n
  return true

initialize registerDerivingHandler `PDecidable derivePDecidable
