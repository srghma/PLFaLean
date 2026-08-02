module

public import Mathlib.Tactic

@[expose] public section

namespace DanelnovButBetaIsNotProp

universe u v

inductive ReflTransGen {α : Type u} (r : α → α → Type v) : α → α → Type (max u v) where
  | refl {a : α} : ReflTransGen r a a
  | head {a b c : α} : r a b → ReflTransGen r b c → ReflTransGen r a c

namespace ReflTransGen

def single {α : Type u} {r : α → α → Type v} {a b : α} (h : r a b) : ReflTransGen r a b :=
  head h refl

def trans {α : Type u} {r : α → α → Type v} {a b c : α}
    (h1 : ReflTransGen r a b) (h2 : ReflTransGen r b c) : ReflTransGen r a c :=
  match h1 with
  | refl => h2
  | head hab h1' => head hab (trans h1' h2)

def tail {α : Type u} {r : α → α → Type v} {a b c : α}
    (h1 : ReflTransGen r a b) (h2 : r b c) : ReflTransGen r a c :=
  trans h1 (single h2)

end ReflTransGen

def Diamond {α : Type u} (R : α → α → Type v) := ∀ {A B C}, R A B → R A C → Σ D, R B D × R C D

section Confluence

variable {α : Type u} {R : α → α → Type v}

def weak_confluence (diamond : Diamond R) {A B C : α} (rab : R A B) (rtac : ReflTransGen R A C) :
    Σ D, ReflTransGen R B D × ReflTransGen R C D :=
  match rtac with
  | .refl => ⟨B, .refl, .single rab⟩
  | .head hr h =>
    let ⟨_D', h₂, BD'⟩ := diamond hr rab
    let ⟨D, D'D, CD⟩ := weak_confluence diamond h₂ h
    ⟨D, .head BD' D'D, CD⟩

def confluence (diamond : Diamond R) {A B C : α} (AB : ReflTransGen R A B) (AC : ReflTransGen R A C) :
    Σ D, ReflTransGen R B D × ReflTransGen R C D :=
  match AB with
  | .refl => ⟨C, AC, .refl⟩
  | .head hr h =>
    let ⟨_D, hd₁, hd₂⟩ := weak_confluence diamond hr AC
    let ⟨D', BD', DD'⟩ := confluence diamond h hd₁
    ⟨D', BD', .trans hd₂ DD'⟩

def equiv_confluence {R' : α → α → Type v}
    (toR : ∀ {a b}, R a b → R' a b) (fromR : ∀ {a b}, R' a b → R a b) (diamond : Diamond R)
    {A B C : α} (AB : R' A B) (AC : R' A C) : Σ D, R' B D × R' C D :=
  let ⟨D, BD, CD⟩ := diamond (fromR AB) (fromR AC)
  ⟨D, toR BD, toR CD⟩

end Confluence

end DanelnovButBetaIsNotProp
