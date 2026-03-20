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
  (A B C D E F G : Γ.Point) (l m n : Γ.Line) (α β γ : Γ.Plane)


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

def Col (A B C : Γ.Point) : Prop :=
  ∃ l : Γ.Line, (A ∈ l) ∧ (B ∈ l) ∧ (C ∈ l)

def PointDistinct3 : Prop :=
  A ≠ B ∧ B ≠ C ∧ A ≠ C

def PointDistinct4 : Prop :=
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧
  B ≠ C ∧ B ≠ D ∧
  C ≠ D

def Cop : Prop :=
  ∃ (α : Γ.Plane), (A ∈ α) ∧ (B ∈ α) ∧ (C ∈ α) ∧ (D ∈ α)

class IncidentAxioms (Γ : Geometry) where
  I1 :
    ∀ {A B : Γ.Point}, A ≠ B → ∃ (l : Γ.Line), (A ∈ l) ∧ (B ∈ l)
  I2 :
    ∀ {A B : Γ.Point} {l m : Γ.Line},
      A ≠ B → A ∈ l → B ∈ l → A ∈ m → B ∈ m → l = m
  I3 :
    ∀ {A B C : Γ.Point}, ¬Col A B C → ∃ (α : Γ.Plane), A ∈ α ∧ B ∈ α ∧ C ∈ α
  I4 :
    ∀ {A B C : Γ.Point} {α β : Γ.Plane},
      ¬Col A B C → A ∈ α → B ∈ α → C ∈ α → A ∈ β → B ∈ β → C ∈ β → α = β
  I5 :
    ∀ {A B : Γ.Point} {l : Γ.Line} {α : Γ.Plane},
      A ∈ l → B ∈ l → A ∈ α → B ∈ α → l ⊂ α
  I6 :
    ∀ {α β : Γ.Plane} {A : Γ.Point},
      A ∈ α → A ∈ β → ∃ (B : Γ.Point), A ≠ B ∧ B ∈ α ∧ B ∈ β
  I7_line :
    ∀ (l : Γ.Line), ∃ (A B : Γ.Point), A ≠ B ∧ A ∈ l ∧ B ∈ l
  I7_plane :
    ∀ (α : Γ.Plane), ∃ (A B C : Γ.Point),
      PointDistinct3 A B C ∧ A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ ¬Col A B C
  I7_space :
    ∃ (A B C D : Γ.Point), PointDistinct4 A B C D ∧ ¬Cop A B C D

lemma exists_second_point_on_line [h : IncidentAxioms Γ] {A : Γ.Point} {l : Γ.Line} :
  A ∈ l → ∃ (B : Γ.Point), B ≠ A ∧ B ∈ l := by
  intro hAl
  rcases h.I7_line l with ⟨X, Y, hXY, hXl, hYl⟩
  by_cases h₁ : A = X
  · use Y
    rw [h₁]
    exact ⟨id (Ne.symm hXY), hYl⟩
  · use X
    exact ⟨fun a ↦ h₁ (id (Eq.symm a)), hXl⟩

@[simp]
lemma inplane_iff {l : Γ.Line} {α : Γ.Plane} : l ⊂ α ↔ ∀ (A : Γ.Point), A ∈ l → A ∈ α := by
  simp

theorem T₁_line [hΓ : IncidentAxioms Γ] {l m : Γ.Line} :
  l ≠ m → (∃ (α : Γ.Plane), l ⊂ α ∧ m ⊂ α) →
    ∀ (A B : Γ.Point), A ∈ l → B ∈ l → A ∈ m → B ∈ m → A = B := by
  intro hlm h_ex_plane A B hAl hBl hAm hBm
  by_contra hAB
  have h₁ := hΓ.I2 hAB hAl hBl hAm hBm
  exact hlm h₁

theorem T₁_plane [hΓ : IncidentAxioms Γ] {α β : Γ.Plane} :
  α ≠ β → (∃ (A : Γ.Point), A ∈ α ∧ A ∈ β) → ∃ (l : Γ.Line), l ⊂ α ∧ l ⊂ β := by
  intro hαβ hAαβ
  rcases hAαβ with ⟨A, hAα, hAβ⟩
  have h₁ := hΓ.I6 hAα hAβ
  rcases h₁ with ⟨B, hAB, hBα, hBβ⟩
  have h₂ := hΓ.I1 hAB
  rcases h₂ with ⟨l, hAl, hBl⟩
  use l
  have h₃ := hΓ.I5 hAl hBl hAα hBα
  have h₄ := hΓ.I5 hAl hBl hAβ hBβ
  exact ⟨h₃, h₄⟩

theorem T₁_line_plane [hΓ : IncidentAxioms Γ] {l : Γ.Line} {α : Γ.Plane} :
  l ⊄ α → ∀ (A B : Γ.Point), A ∈ l → B ∈ l → A ∈ α → B ∈ α → A = B := by
    intro hnlα A B hAl hBl hAα hBα
    by_contra hAB
    have h₁ := hΓ.I5 hAl hBl hAα hBα
    exact hnlα h₁

theorem T₂_₁ [hΓ : IncidentAxioms Γ] {l : Γ.Line} {A : Γ.Point} :
  A ∉ l → ∃! (α : Γ.Plane), l ⊂ α ∧ A ∈ α := by
  intro hnAl
  rcases hΓ.I7_line l with ⟨P, Q, hPQ, hPl, hQl⟩
  have h₁ : ¬Col A P Q := by
    simp only [Col, not_exists]
    intro m ⟨hAm, hPm, hQm⟩
    have h₂ : l = m := hΓ.I2 hPQ hPl hQl hPm hQm
    rw [h₂] at hnAl
    exact hnAl hAm
  rcases hΓ.I3 h₁ with ⟨α, hAα, hPα, hQα⟩
  use α
  simp only [and_imp]
  constructor
  · constructor
    · exact hΓ.I5 hPl hQl hPα hQα
    · exact hAα
  · intro β hlβ hAβ
    have hPβ := hlβ P hPl
    have hQβ := hlβ Q hQl
    have h₂ := hΓ.I4 h₁ hAα hPα hQα hAβ hPβ hQβ
    exact Eq.symm h₂

theorem T₂_₂ [hΓ : IncidentAxioms Γ] {l m : Γ.Line} :
  l ≠ m → (∃ (A : Γ.Point), A ∈ l ∧ A ∈ m) → ∃! (α : Γ.Plane), l ⊂ α ∧ m ⊂ α := by
  intro hlm h₁
  rcases h₁ with ⟨A, hAl, hAm⟩
  have h₂ := exists_second_point_on_line hAl
  have h₃ := exists_second_point_on_line hAm
  rcases h₂ with ⟨B, hBA, hBl⟩
  rcases h₃ with ⟨C, hCA, hCm⟩
  by_cases h₄ : B = C
  · rw [h₄] at hBl
    have h₅ := hΓ.I2 hCA hBl hAl hCm hAm
    contradiction
  · have h₁ : ¬Col A B C := by
      simp only [Col, not_exists]
      intro n
      simp only [not_and]
      intro hAn hBn hCn
      have hln := hΓ.I2 hBA hBl hAl hBn hAn
      rw [← hln] at hCn
      have hlm := hΓ.I2 hCA hCn hAl hCm hAm
      contradiction
    rcases hΓ.I3 h₁ with ⟨α, hAα, hBα, hCα⟩
    use α
    constructor
    · simp only
      constructor
      · exact hΓ.I5 hAl hBl hAα hBα
      · exact hΓ.I5 hAm hCm hAα hCα
    · intro β ⟨hlβ, hmβ⟩
      have hAβ := hlβ A hAl
      have hBβ := hlβ B hBl
      have hCβ := hmβ C hCm
      exact hΓ.I4 h₁ hAβ hBβ hCβ hAα hBα hCα

end Geometry

end Hilbert
