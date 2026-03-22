import Mathlib.Logic.Unique
import Mathlib.Tactic.Use

universe u v w

namespace Hilbert


structure Geometry where
  Point : Sort u
  Line : Sort v
  Plane : Sort w
  OnLine : Point → Line → Prop
  OnPlane : Point → Plane → Prop
  Bet : Point → Point → Point → Prop
  /-- SegCong A B C D ≝ AB ≅ CD -/
  SegCong :  Point → Point → Point → Point → Prop
  /-- AngCong A B C D E F ≝ ∠ABC ≅ ∠DEF -/
  AngCong : Point → Point → Point → Point → Point → Point → Prop


namespace Geometry

variable {Γ : Geometry}
  {A B C D E F G : Γ.Point} {l m n : Γ.Line} {α β γ : Γ.Plane}


abbrev onLine (A : Γ.Point) (l : Γ.Line) : Prop := Γ.OnLine A l
notation:50 A:50 " ∈ " l:50 => onLine A l
notation:50 A:50 " ∉ " l:50 => ¬onLine A l

abbrev onPlane (A : Γ.Point) (α : Γ.Plane) : Prop := Γ.OnPlane A α
notation:50 A:50 " ∈ " α:50 => onPlane A α
notation:50 A:50 " ∉ " α:50 => ¬onPlane A α

@[simp]
def LineInPlane (l : Γ.Line) (α : Γ.Plane) : Prop :=
  ∀ (A : Γ.Point), A ∈ l → A ∈ α

abbrev inPlane (l : Γ.Line) (α : Γ.Plane) : Prop := Γ.LineInPlane l α
notation:50 l:50 " ⊂ " α:50 => inPlane l α
notation:50 l:50 " ⊄ " α:50 => ¬inPlane l α

abbrev Segment := Γ.Point × Γ.Point
abbrev inSegment (A : Γ.Point) (l : Segment) := Γ.Bet l.1 A l.2
notation:50 A:50 " ∈ " l:50 => inSegment A l
notation:50 A:50 " ∉ " l:50 => ¬inSegment A l

@[simp]
def Parallel (l m : Γ.Line) : Prop := (∃ α, (l ⊂ α ∧ m ⊂ α)) ∧ ¬∃ A, A ∈ l ∧ A ∈ m
notation:50 l:50 " ∥ " m:50 => Parallel l m
notation:50 l:50 " ∦ " m:50 => ¬Parallel l m

def Col (A B C : Γ.Point) : Prop :=
  ∃ l : Γ.Line, (A ∈ l) ∧ (B ∈ l) ∧ (C ∈ l)

@[simp]
def PointDistinct3 (A B C : Γ.Point) : Prop :=
  A ≠ B ∧ B ≠ C ∧ A ≠ C

@[simp]
def PointDistinct4 (A B C D : Γ.Point) : Prop :=
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧
  B ≠ C ∧ B ≠ D ∧
  C ≠ D

def Cop (A B C D : Γ.Point) : Prop :=
  ∃ (α : Γ.Plane), (A ∈ α) ∧ (B ∈ α) ∧ (C ∈ α) ∧ (D ∈ α)

class IncidentAxioms (Γ : Geometry) where
  I₁ : ∀ {A B}, A ≠ B → ∃ l : Γ.Line, A ∈ l ∧ B ∈ l
  I₂ : ∀ {A B} {l m : Γ.Line} ,A ≠ B → A ∈ l → B ∈ l → A ∈ m → B ∈ m → l = m
  I₃ :
    (∀ (l : Γ.Line), (∃ A B, A ≠ B ∧ A ∈ l ∧ B ∈ l)) ∧
      ∃ A B C : Γ.Point, PointDistinct3 A B C ∧ ¬Col A B C
  I₄ : ∀ (A B C), ∃ α : Γ.Plane, A ∈ α ∧ B ∈ α ∧ C ∈ α
  I₅ : ∀ {A B C : Γ.Point} {α β : Γ.Plane}, ¬Col A B C →
    A ∈ α → B ∈ α → C ∈ α → A ∈ β → B ∈ β → C ∈ β → α = β
  I₆ : ∀ {A B} {l : Γ.Line} {α : Γ.Plane},
    A ≠ B → A ∈ l → B ∈ l → A ∈ α → B ∈ α → l ⊂ α
  I₇ : ∀ {α β : Γ.Plane} {A : Γ.Point},
    α ≠ β → A ∈ α → A ∈ β → ∃ B : Γ.Point, A ≠ B ∧ B ∈ α ∧ B ∈ β
  I₈ : ∃ A B C D : Γ.Point, PointDistinct4 A B C D ∧ ¬Cop A B C D

theorem T₁_₁ [hΓ : IncidentAxioms Γ] {l m : Γ.Line} {α : Γ.Plane} :
  l ≠ m → l ⊂ α → m ⊂ α → (∃!A, A ∈ l ∧ A ∈ m) ∨ l ∥ m := by
  intro hnlm hlα hmα
  by_cases h₁ : l ∥ m
  · exact Or.inr h₁
  · simp only [Parallel, not_and_or, not_exists, not_forall, not_or, not_not] at h₁
    rcases h₁ with h₁ | h₁
    · have h₂ := h₁ α
      rcases h₂ with h₂ | h₂
      · contradiction
      · contradiction
    · left
      rcases h₁ with ⟨A, hAl ,hAm⟩
      use A
      constructor
      · simp only
        exact ⟨hAl, hAm⟩
      · intro B
        simp only
        intro ⟨hBl, hBm⟩
        by_contra hnBA
        have h₃ := hΓ.I₂ hnBA hBl hAl hBm hAm
        contradiction

theorem T₁_₂ [hΓ : IncidentAxioms Γ] {α β : Γ.Plane} :
  α ≠ β → (¬∃A, (A ∈ α ∧ A ∈ β)) ∨ ∃ l, (l ⊂ α ∧ l ⊂ β) := by
  intro hnαβ
  by_cases h₁ : (¬∃ A, A ∈ α ∧ A ∈ β)
  · exact Or.inl h₁
  · rw [not_not] at h₁
    rcases h₁ with ⟨A, hAα, hAβ⟩
    right
    rcases hΓ.I₇ hnαβ hAα hAβ with ⟨B, hnAB, hBα, hBβ⟩
    rcases hΓ.I₁ hnAB with ⟨l, hAl, hBl⟩
    use l
    constructor
    · exact hΓ.I₆ hnAB hAl hBl hAα hBα
    · exact hΓ.I₆ hnAB hAl hBl hAβ hBβ

theorem T₂_₁ [hΓ : IncidentAxioms Γ] {l : Γ.Line} {A : Γ.Point} :
  A ∉ l → ∃!α, l ⊂ α ∧ A ∈ α := by
  intro hnAl
  rcases hΓ.I₃.1 l with ⟨B, C, hnBC, hBl ,hCl⟩
  have h₁ : ¬Col A B C := by
    simp only [Col, not_exists]
    intro m
    rw [and_comm]
    simp only [not_and]
    intro ⟨hBm, hCm⟩
    have h₂ := hΓ.I₂ hnBC hBl hCl hBm hCm
    rw [h₂] at hnAl
    exact hnAl
  rcases hΓ.I₄ A B C with ⟨α, hAα, hBα, hCα⟩
  use α
  constructor
  · simp only
    have hlα := hΓ.I₆ hnBC hBl hCl hBα hCα
    exact ⟨hlα, hAα⟩
  · intro β
    simp only
    intro ⟨hlβ, hAβ⟩
    have hBβ := hlβ B hBl
    have hCβ := hlβ C hCl
    exact hΓ.I₅ h₁ hAβ hBβ hCβ hAα hBα hCα

lemma L₁ [hΓ : IncidentAxioms Γ] {l m : Γ.Line} :
  l ≠ m → ∃ B, B ∈ l ∧ B ∉ m := by
  intro hnlm
  by_contra h₁
  simp only [not_exists, not_and, not_not] at h₁
  rcases hΓ.I₃.1 l with ⟨A, B, hnAB, hAl, hBl⟩
  have hAm := h₁ A hAl
  have hBm := h₁ B hBl
  have h₂ := hΓ.I₂ hnAB hAl hBl hAm hBm
  contradiction

lemma L₂ [hΓ : IncidentAxioms Γ] {A B C : Γ.Point} {l : Γ.Line} :
  A ≠ B → A ∈ l → B ∈ l → C ∉ l → ¬Col A B C := by
  intro hnAB hAl hBl hnCl
  simp only [Col, not_exists]
  intro m ⟨hAm, hBm, hCm⟩
  have hlm := hΓ.I₂ hnAB hAl hBl hAm hBm
  rw [hlm] at hnCl
  contradiction

theorem T₂_₂ [hΓ : IncidentAxioms Γ] {l m : Γ.Line} :
  (∃ A, (A ∈ l ∧ A ∈ m)) → l ≠ m → ∃!α, (l ⊂ α ∧ m ⊂ α) := by
  intro h₁ hnlm
  rcases h₁ with ⟨A, hAl, hAm⟩
  rcases L₁ hnlm with ⟨B, hBl, hnBm⟩
  rcases L₁ (Ne.symm hnlm) with ⟨C, hCm, hnCl⟩
  rcases hΓ.I₄ A B C with ⟨α, hAα, hBα, hCα⟩
  have hnAB : A ≠ B := by
    intro hAB
    rw [hAB] at hAm
    contradiction
  have hlα : l ⊂ α := by
    exact hΓ.I₆ hnAB hAl hBl hAα hBα
  have hmα : m ⊂ α := by
    have hnAC : A ≠ C := by
      intro hAC
      rw [hAC] at hAl
      contradiction
    exact hΓ.I₆ hnAC hAm hCm hAα hCα
  use α
  simp only
  constructor
  · exact ⟨hlα, hmα⟩
  · intro β ⟨hlβ, hmβ⟩
    have hAβ := hlβ A hAl
    have hBβ := hlβ B hBl
    have hCβ := hmβ C hCm
    have hnCol := L₂ hnAB hAl hBl hnCl
    exact hΓ.I₅ hnCol hAβ hBβ hCβ hAα hBα hCα

class OrderAxioms (Γ : Geometry) where

class AxiomOfParallelLine (Γ : Geometry) where
  III : ∀ {A} {l : Γ.Line} {α : Γ.Plane},
    l ⊂ α → A ∈ α → A ∉ l →
      ∃! m : Γ.Line, m ⊂ α ∧ A ∈ m ∧ l ∥ m


end Geometry

end Hilbert
