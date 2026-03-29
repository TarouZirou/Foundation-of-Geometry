import Mathlib.Logic.Unique
import Mathlib.Tactic.Use
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Check

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
    {A' B' C' : Γ.Point}


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

abbrev Segment (Γ : Geometry) := Γ.Point × Γ.Point
abbrev onSegment (A : Γ.Point) (l : Γ.Segment) := Γ.Bet l.1 A l.2
notation:50 A:50 " ∈ " l:50 => onSegment A l
notation:50 A:50 " ∉ " l:50 => ¬onSegment A l

@[simp]
def Parallel (l m : Γ.Line) : Prop := (∃ α, (l ⊂ α ∧ m ⊂ α)) ∧ ¬∃ A, A ∈ l ∧ A ∈ m
notation:50 l:50 " ∥ " m:50 => Parallel l m
notation:50 l:50 " ∦ " m:50 => ¬Parallel l m

def Col (A B C : Γ.Point) : Prop :=
  ∃ l : Γ.Line, (A ∈ l) ∧ (B ∈ l) ∧ (C ∈ l)

theorem col_right_comm : Col A B C ↔ Col A C B := by
  constructor <;> intro ⟨l, hl₁, hl₂, hl₃⟩ <;> use l

theorem col_left_comm : Col A B C ↔ Col B A C := by
  constructor <;> intro ⟨l, hl₁, hl₂, hl₃⟩ <;> use l

theorem col_symm : Col A B C ↔ Col C B A := by
  constructor <;> intro ⟨l, hl₁, hl₂, hl₃⟩ <;> use l

theorem col_left_rot : Col A B C ↔ Col B C A := by
  constructor <;> intro ⟨l, hl₁, hl₂, hl₃⟩ <;> use l

theorem col_right_rot : Col A B C ↔ Col C A B := by
  constructor <;> intro ⟨l, hl₁, hl₂, hl₃⟩ <;> use l

@[simp]
def PointDistinct3 (A B C : Γ.Point) : Prop := A ≠ B ∧ B ≠ C ∧ A ≠ C
notation:50 "≠₃" A:arg B:arg C:arg => PointDistinct3 A B C

@[simp]
def PointDistinct4 (A B C D : Γ.Point) : Prop :=
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧
  B ≠ C ∧ B ≠ D ∧
  C ≠ D
notation:50 "≠₄" A:arg B:arg C:arg D:arg => PointDistinct4 A B C D


def Cop (A B C D : Γ.Point) : Prop :=
  ∃ (α : Γ.Plane), (A ∈ α) ∧ (B ∈ α) ∧ (C ∈ α) ∧ (D ∈ α)

theorem neq_of_online_and_not_online : A ∈ l → B ∉ l → A ≠ B := by
  intro hAl hnBl hAB
  subst hAB
  contradiction

class IncidentAxioms (Γ : Geometry) where
  I₁ : ∀ {A B}, A ≠ B → ∃ l : Γ.Line, A ∈ l ∧ B ∈ l
  I₂ : ∀ {A B} {l m : Γ.Line} ,A ≠ B → A ∈ l → B ∈ l → A ∈ m → B ∈ m → l = m
  I₃ :
    (∀ (l : Γ.Line), (∃ A B, A ≠ B ∧ A ∈ l ∧ B ∈ l)) ∧
      ∃ A B C : Γ.Point, ≠₃ A B C ∧ ¬Col A B C
  I₄ : ∀ (A B C), ∃ α : Γ.Plane, A ∈ α ∧ B ∈ α ∧ C ∈ α
  I₅ : ∀ {A B C : Γ.Point} {α β : Γ.Plane}, ¬Col A B C →
    A ∈ α → B ∈ α → C ∈ α → A ∈ β → B ∈ β → C ∈ β → α = β
  I₆ : ∀ {A B} {l : Γ.Line} {α : Γ.Plane},
    A ≠ B → A ∈ l → B ∈ l → A ∈ α → B ∈ α → l ⊂ α
  I₇ : ∀ {α β : Γ.Plane} {A : Γ.Point},
    α ≠ β → A ∈ α → A ∈ β → ∃ B : Γ.Point, A ≠ B ∧ B ∈ α ∧ B ∈ β
  I₈ : ∃ A B C D : Γ.Point, ≠₄ A B C D ∧ ¬Cop A B C D

theorem exists_line_of_forall_point [hΓ : IncidentAxioms Γ] (A : Γ.Point) :
  ∃ l : Γ.Line, A ∈ l := by
  rcases hΓ.I₈ with ⟨B, C, D, E, hnBCDE, hncop⟩
  by_cases hAB : A = B
  · have hnAC := hnBCDE.1
    rw [← hAB] at hnAC
    rcases hΓ.I₁ hnAC with ⟨l, hAl, hCl⟩
    use l
  · rcases hΓ.I₁ hAB with ⟨l, hAl, hBl⟩
    use l

theorem exists_not_online_point [hΓ : IncidentAxioms Γ] (l : Γ.Line) : ∃ C, C ∉ l := by
  by_contra h
  simp only [not_exists, not_not] at h
  rcases hΓ.I₃.2 with ⟨C, D, E, hnCDE, hncCDE⟩
  simp only [Col, not_exists] at hncCDE
  have h₁ := hncCDE l
  have hCl := h C
  have hDl := h D
  have hEl := h E
  exact h₁ ⟨hCl, hDl, hEl⟩

theorem exists_neq_point [hΓ : IncidentAxioms Γ] (A : Γ.Point) : ∃ B, A ≠ B := by
  rcases exists_line_of_forall_point A with ⟨l, hAl⟩
  rcases exists_not_online_point l with ⟨B, hnBl⟩
  use B
  exact neq_of_online_and_not_online hAl hnBl

theorem exists_line_of_point [hΓ : IncidentAxioms Γ] (A B : Γ.Point) :
  ∃ l : Γ.Line, A ∈ l ∧ B ∈ l := by
  by_cases h : A = B
  · subst h
    simp only [and_self]
    exact exists_line_of_forall_point A
  · exact hΓ.I₁ h

theorem col_4 [hΓ : IncidentAxioms Γ] : A ≠ B → Col A B C → Col A B D → Col A C D := by
  intro hnAB ⟨l, hAl, hBl, hCl⟩ ⟨m, hAm, hBm, hDm⟩
  have hlm := hΓ.I₂ hnAB hAl hBl hAm hBm
  rw [hlm] at hAl hCl
  use m

theorem col_of_eq [hΓ : IncidentAxioms Γ] : A = B → Col A B C := by
  intro hAB
  by_cases h : A = C
  · rcases exists_line_of_forall_point A with ⟨l, hAl⟩
    use l
    simp only [← hAB, ← h, and_self]
    assumption
  · rcases hΓ.I₁ h with ⟨l, hAl, hCl⟩
    rw [← hAB]
    use l

theorem online_of_col [hΓ : IncidentAxioms Γ] : A ≠ B → Col A B C → A ∈ l → B ∈ l → C ∈ l := by
  intro hnAB ⟨m, hAm, hBm, hCm⟩ hAl hBl
  have h₁ := hΓ.I₂ hnAB hAl hBl hAm hBm
  rw [h₁]
  exact hCm

theorem col_of_online : A ∈ l → B ∈ l → C ∈ l → Col A B C := by
  intro hAl hBl hCl
  use l

theorem not_online_of_online_and_not_col : ¬Col A B C → A ∈ l → B ∈ l → C ∉ l := by
  intro hncABC hAl hBl hCl
  have hcABC : Col A B C := ⟨l, hAl ,hBl, hCl⟩
  contradiction

theorem not_col_of_online_and_not_online [hΓ : IncidentAxioms Γ] :
  A ≠ B → A ∈ l → B ∈ l → C ∉ l → ¬Col A B C := by
  intro hnAB hAl hBl hnCl ⟨m, hAm, hBm, hCm⟩
  have hlm := hΓ.I₂ hnAB hAl hBl hAm hBm
  rw [hlm] at hnCl
  contradiction

theorem T₁_₁ [hΓ : IncidentAxioms Γ] :
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

theorem T₁_₁_₁ [hΓ : IncidentAxioms Γ] :
  l ≠ m → l ⊂ α → m ⊂ α → l ∦ m → (∃!A, A ∈ l ∧ A ∈ m) := by
  intro hnlm hlα hmα hn_para_lm
  have h₁ := T₁_₁ hnlm hlα hmα
  rcases h₁ with h₁ | h₁
  · exact h₁
  · contradiction

theorem T₁_₂ [hΓ : IncidentAxioms Γ] :
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

theorem T₂_₁ [hΓ : IncidentAxioms Γ] :
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

lemma L₂ [hΓ : IncidentAxioms Γ] :
  l ≠ m → ∃ B, B ∈ l ∧ B ∉ m := by
  intro hnlm
  by_contra h₁
  simp only [not_exists, not_and, not_not] at h₁
  rcases hΓ.I₃.1 l with ⟨A, B, hnAB, hAl, hBl⟩
  have hAm := h₁ A hAl
  have hBm := h₁ B hBl
  have h₂ := hΓ.I₂ hnAB hAl hBl hAm hBm
  contradiction

lemma L₃ [hΓ : IncidentAxioms Γ] :
  A ≠ B → A ∈ l → B ∈ l → C ∉ l → ¬Col A B C := by
  intro hnAB hAl hBl hnCl
  simp only [Col, not_exists]
  intro m ⟨hAm, hBm, hCm⟩
  have hlm := hΓ.I₂ hnAB hAl hBl hAm hBm
  rw [hlm] at hnCl
  contradiction

theorem T₂_₂ [hΓ : IncidentAxioms Γ] :
  (∃ A, (A ∈ l ∧ A ∈ m)) → l ≠ m → ∃!α, (l ⊂ α ∧ m ⊂ α) := by
  intro h₁ hnlm
  rcases h₁ with ⟨A, hAl, hAm⟩
  rcases L₂ hnlm with ⟨B, hBl, hnBm⟩
  rcases L₂ (Ne.symm hnlm) with ⟨C, hCm, hnCl⟩
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
    have hnCol := L₃ hnAB hAl hBl hnCl
    exact hΓ.I₅ hnCol hAβ hBβ hCβ hAα hBα hCα


abbrev bet (A B C : Γ.Point) := Γ.Bet A B C
notation:50 A:50 "≺" B:51 "≺" C:51 => bet A B C

def SameSide (A B : Γ.Point) (l : Γ.Line) : Prop := A ∉ l ∧ B ∉ l ∧ ¬∃ C, C ∈ l ∧ A ≺ C ≺ B
def OppoSide (A B : Γ.Point) (l : Γ.Line) : Prop := A ∉ l ∧ B ∉ l ∧ ∃ C, C ∈ l ∧ A ≺ C ≺ B

class OrderAxioms (Γ : Geometry) where
  II₁ : ∀ {A B C : Γ.Point}, A ≺ B ≺ C → Col A B C ∧ ≠₃ A B C ∧ C ≺ B ≺ A
  II₂ : ∀ {A B}, A ≠ B → ∃ C : Γ.Point, A ≺ B ≺ C
  II₃ : ∀ {A B C : Γ.Point}, Col A B C →
    ¬(A ≺ B ≺ C ∧ B ≺ C ≺ A) ∧
      ¬(B ≺ C ≺ A ∧ C ≺ A ≺ B) ∧
        ¬(C ≺ A ≺ B ∧ A ≺ B ≺ C)
  II₄ : ∀ {A B C} {l : Γ.Line} {α : Γ.Plane},
    PointDistinct3 A B C → ¬Col A B C →
      l ⊂ α → A ∈ α → B ∈ α → C ∈ α → A ∉ l → B ∉ l → C ∉ l →
        (∃ D, D ∈ l ∧ A ≺ D ≺ B) → (∃ E, E ∈ l ∧ A ≺ E ≺ C) ∨ (∃ F, F ∈ l ∧ B ≺ F ≺ C)

theorem bet_symm [hΓ : OrderAxioms Γ] : A ≺ B ≺ C ↔ C ≺ B ≺ A := by
  constructor
  <;> intro hb
  <;> have h₁ := hΓ.II₁ hb
  <;> exact h₁.2.2

theorem col_of_bet [hΓ : OrderAxioms Γ] : A ≺ B ≺ C → Col A B C := by
  intro hb
  exact (hΓ.II₁ hb).1

theorem neq3_of_bet [hΓ : OrderAxioms Γ] : A ≺ B ≺ C → ≠₃ A B C := by
  intro hb
  exact (hΓ.II₁ hb).2.1

theorem not_bet_of_bet [hΓ : OrderAxioms Γ] : A ≺ B ≺ C → ¬B ≺ C ≺ A ∧ ¬C ≺ A ≺ B := by
  intro hb₁
  constructor
  <;> intro hb₂
  <;> have hc := (hΓ.II₁ hb₁).1
  · have h₁ := (hΓ.II₃ hc).1
    exact h₁ ⟨hb₁, hb₂⟩
  · have h₁ := (hΓ.II₃ hc).2.2
    exact h₁ ⟨hb₂, hb₁⟩

theorem not_bet_of_bet_or [hΓ : OrderAxioms Γ] : A ≺ B ≺ C ∨ B ≺ C ≺ A → ¬C ≺ A ≺ B := by
  intro hb₁
  rcases hb₁ with hb₁ | hb₁
  <;> have h₁ := not_bet_of_bet hb₁
  <;> have ⟨hb₂, hb₃⟩ := h₁
  <;> assumption


theorem exists_unique_bet_point_of_exists [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  A ∉ l → B ∉ l → (∃ C, (C ∈ l ∧ A ≺ C ≺ B)) → ∃! C, (C ∈ l ∧ A ≺ C ≺ B) := by
  intro hnAl hnBl ⟨C, hCl, hbACB⟩
  have hnAB : A ≠ B := (hΓ₂.II₁ hbACB).2.1.2.2
  use C
  simp only
  constructor
  · exact ⟨hCl, hbACB⟩
  · intro D ⟨hDl, hbADB⟩
    by_contra hnDC
    rcases hΓ₁.I₁ hnAB with ⟨m, hAm, hBm⟩
    have hcACB := col_of_bet hbACB
    have hcADB := col_of_bet hbADB
    rw [col_right_comm] at hcACB hcADB
    have hCm := online_of_col hnAB hcACB hAm hBm
    have hDm := online_of_col hnAB hcADB hAm hBm
    have hlm := hΓ₁.I₂ hnDC hDl hCl hDm hCm
    rw [hlm] at hnAl
    contradiction

theorem L₅ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  A ∉ l →  (∃ C, (C ∈ l ∧ A ≺ C ≺ B)) → ¬∃ C, (C ∈ l ∧ A ≺ B ≺ C) := by
  intro hnAl h₁
  rcases h₁ with ⟨C, hCl, hbACB⟩
  intro h₂
  rcases h₂ with ⟨D, hDl, hbABD⟩
  have hnAB : A ≠ B := (neq3_of_bet hbACB).2.2
  have hnCB : C ≠ B := (neq3_of_bet hbACB).2.1
  have hnBC : B ≠ C := Ne.symm hnCB
  rcases hΓ₁.I₁ hnBC with ⟨m, hBm, hCm⟩
  have hcBCA : Col B C A := (col_symm).mp (col_of_bet hbACB)
  have hAm : A ∈ m := online_of_col hnBC hcBCA hBm hCm
  have hcABD : Col A B D := col_of_bet hbABD
  have hDm : D ∈ m := online_of_col hnAB hcABD hAm hBm
  have hnCD : C ≠ D := by
    intro hCD
    subst D
    have hbBCA : B ≺ C ≺ A := (bet_symm).mp hbACB
    exact ((not_bet_of_bet hbBCA).2) hbABD
  have hlm : l = m := hΓ₁.I₂ hnCD hCl hDl hCm hDm
  rw [hlm] at hnAl
  exact hnAl hAm

theorem L₆ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  A ∉ l → (∃ C, (C ∈ l ∧ A ≺ B ≺ C)) → ¬∃ C, (C ∈ l ∧ A ≺ C ≺ B) := by
  intro hnAl h₁
  rcases h₁ with ⟨C, hCl, hbABC⟩
  intro h₂
  rcases h₂ with ⟨D, hDl, hbADB⟩
  have hnAD : A ≠ D := (neq3_of_bet hbADB).1
  rcases hΓ₁.I₁ hnAD with ⟨m, hAm, hDm⟩
  have hBm : B ∈ m := online_of_col hnAD (col_of_bet hbADB) hAm hDm
  have hnAB : A ≠ B := (neq3_of_bet hbABC).1
  have hCm : C ∈ m := online_of_col hnAB (col_of_bet hbABC) hAm hBm
  have hnCD : C ≠ D := by
    intro hCD
    subst D
    have hbCBA : C ≺ B ≺ A := (bet_symm).mp hbABC
    exact ((not_bet_of_bet hbCBA).2) hbADB
  have hlm : l = m := hΓ₁.I₂ hnCD hCl hDl hCm hDm
  rw [hlm] at hnAl
  exact hnAl hAm

theorem T₃ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  ∀ (A C), A ≠ C → ∃ B : Γ.Point, A ≺ B ≺ C := by
  intro A C hnAC
  rcases hΓ₁.I₁ hnAC with ⟨l, hAl ,hCl⟩
  rcases exists_not_online_point l with ⟨E, hnEl⟩
  have hnAE : A ≠ E := by
    intro hAE
    rw [hAE] at hAl
    contradiction
  rcases hΓ₂.II₂ hnAE with ⟨F, hbAEF⟩
  have hnFC : F ≠ C := by
    intro hFC
    rw [hFC] at hbAEF
    have hcAEC := col_of_bet hbAEF
    rw [col_right_comm] at hcAEC
    have hEl := online_of_col hnAC hcAEC hAl hCl
    contradiction
  rcases hΓ₂.II₂ hnFC with ⟨G, hbFCG⟩
  have hcAEF := col_of_bet hbAEF
  have hcFCG := col_of_bet hbFCG
  have hnAF := (neq3_of_bet hbAEF).2.2
  have hnEF := (neq3_of_bet hbAEF).2.1
  have hnFC := (neq3_of_bet hbFCG).1
  have hnCG := (neq3_of_bet hbFCG).2.1
  have hnFl : F ∉ l := by
    intro hFl
    rcases hcAEF with ⟨m, hAm, hEm, hFm⟩
    have hlm := hΓ₁.I₂ hnAF hAl hFl hAm hFm
    rw [hlm] at hnEl
    exact hnEl hEm
  have hnGl : G ∉ l := by
    intro hGl
    rcases hcFCG with ⟨m, hFm, hCm, hGm⟩
    have hlm := hΓ₁.I₂ hnCG hCl hGl hCm hGm
    rw [hlm] at hnFl
    exact hnFl hFm
  have hnbFGC := (not_bet_of_bet hbFCG).1
  rw [bet_symm] at hnbFGC
  rcases hΓ₁.I₄ A F G with ⟨α, hAα, hFα, hGα⟩
  have hnAFG : ≠₃ A F G := by
    have hnAG : A ≠ G := by
      intro hAG
      rw [hAG] at hAl
      contradiction
    have hnFG := (neq3_of_bet hbFCG).2.2
    exact ⟨hnAF, hnFG, hnAG⟩
  have hlα : l ⊂ α := by
    have hCα : C ∈ α := by
      rcases hcFCG with ⟨m, hFm, hCm, hGm⟩
      have hmα : m ⊂ α := by
        have hnFG := (neq3_of_bet hbFCG).2.2
        exact hΓ₁.I₆ hnFG hFm hGm hFα hGα
      exact hmα C hCm
    exact hΓ₁.I₆ hnAC hAl hCl hAα hCα
  have hncAFG : ¬Col A F G := by
    intro hcAFG
    rw [col_left_rot] at hcAFG
    rw [col_right_comm] at hcFCG
    have hcFAC := col_4 hnAFG.2.1 hcAFG hcFCG
    rw [col_left_rot] at hcFAC
    have hFl := online_of_col hnAC hcFAC hAl hCl
    contradiction
  have hnEG : E ≠ G := by
    intro hEG
    rw[hEG, col_right_comm] at hcAEF
    contradiction
  rcases hΓ₁.I₁ hnEG with ⟨m, hEm, hGm⟩
  have hnAm : A ∉ m := by
    intro hAm
    have hFm := online_of_col (neq3_of_bet hbAEF).1 hcAEF hAm hEm
    have hcAFG := col_of_online hAm hFm hGm
    contradiction
  have hnFm : F ∉ m := by
    intro hFm
    rcases hcAEF with ⟨n, hAn, hEn, hFn⟩
    have hmn := hΓ₁.I₂ hnEF hEm hFm hEn hFn
    rw [hmn] at hnAm
    contradiction
  have hnCm : C ∉ m := by
    intro hCm
    rcases hcFCG with ⟨n, hFn, hCn, hGn⟩
    have hmn := hΓ₁.I₂ hnCG hCm hGm hCn hGn
    rw [hmn] at hnFm
    contradiction
  have hnAFC : ≠₃ A F C := by
    exact ⟨hnAF, hnFC, hnAC⟩
  have hncAFC := not_col_of_online_and_not_online hnAC hAl hCl hnFl
  rw [col_right_comm] at hncAFC
  have hmα : m ⊂ α := by
    have hEα : E ∈ α := by
      rcases hcAEF with ⟨n, hAn, hEn ,hFn⟩
      have hnα := hΓ₁.I₆ hnAF hAn hFn hAα hFα
      exact hnα E hEn
    exact hΓ₁.I₆ hnEG hEm hGm hEα hGα
  have hCα := hlα C hCl
  have h₁ := hΓ₂.II₄ hnAFC hncAFC hmα hAα hFα hCα hnAm hnFm hnCm ⟨E, hEm, hbAEF⟩
  have hnotFC : ¬ ∃ D : Γ.Point, D ∈ m ∧ F ≺ D ≺ C := by
    exact L₆ hnFm ⟨G, hGm, hbFCG⟩
  have h₂ : (∃ E, E ∈ m ∧ A ≺ E ≺ C) := by
    rcases h₁ with h₁ | h₁
    · exact h₁
    · contradiction
  rcases h₂ with ⟨B, hBm, hb_B⟩
  use B

theorem T₄ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  Col A B C → ≠₃ A B C → A ≺ B ≺ C ∨ B ≺ C ≺ A ∨ C ≺ A ≺ B := by
  intro hcABC ⟨hnAB, hnBC, hnAC⟩
  rw [or_comm, or_assoc, or_iff_not_imp_left, or_iff_not_imp_left]
  intro hnbBCA hnbCAB
  rcases hΓ₁.I₁ hnAC with ⟨l, hAl, hCl⟩
  rcases exists_not_online_point l with ⟨D, hnDl⟩
  have hBl := online_of_col hnAC (col_right_comm.mp hcABC) hAl hCl
  have hnAD : A ≠ D := by
    intro hAD
    rw [hAD] at hAl
    contradiction
  have hnBD : B ≠ D := by
    intro hBD
    rw [hBD] at hBl
    contradiction
  have hnCD : C ≠ D := by
    intro hBD
    rw [hBD] at hCl
    contradiction
  rcases hΓ₁.I₁ hnAD with ⟨m₁, hAm₁, hDm₁⟩
  rcases hΓ₁.I₁ hnBD with ⟨m₂, hBm₂, hDm₂⟩
  rcases hΓ₂.II₂ hnBD with ⟨G, hbBDG⟩
  rcases hΓ₁.I₄ B C G with ⟨α, hBα, hCα, hGα⟩
  have hnBG : B ≠ G := (neq3_of_bet hbBDG).2.2
  have hnDG : D ≠ G := (neq3_of_bet hbBDG).2.1
  have hnBm₁ : ¬ B ∈ m₁ := by
    intro hBm₁'
    have hm₁l : m₁ = l := hΓ₁.I₂ hnAB hAm₁ hBm₁' hAl hBl
    have hDl : D ∈ l := by simpa [hm₁l] using hDm₁
    exact hnDl hDl
  have hnCm₁ : ¬ C ∈ m₁ := by
    intro hCm₁
    have hm₁l : m₁ = l := hΓ₁.I₂ hnAC hAm₁ hCm₁ hAl hCl
    have hDl : D ∈ l := by simpa [hm₁l] using hDm₁
    exact hnDl hDl
  have hnGC : G ≠ C := by
    intro hGC'
    have hbBDC : B ≺ D ≺ C := by simpa [hGC'] using hbBDG
    rcases col_of_bet hbBDC with ⟨n, hBn, hDn, hCn⟩
    have hnl : n = l := hΓ₁.I₂ hnBC hBn hCn hBl hCl
    have hDl : D ∈ l := by simpa [hnl] using hDn
    contradiction
  have hnGm₁ : ¬ G ∈ m₁ := by
    intro hGm₁
    rcases col_of_bet hbBDG with ⟨n, hBn, hDn, hGn⟩
    have hnm₁ : n = m₁ := hΓ₁.I₂ hnDG hDn hGn hDm₁ hGm₁
    have hBm₁' : B ∈ m₁ := by simpa [hnm₁] using hBn
    exact hnBm₁ hBm₁'
  have hncBGC : ¬ Col B G C := by
    intro hCol
    rcases hCol with ⟨n, hBn, hGn, hCn⟩
    have hnl : n = l := hΓ₁.I₂ hnBC hBn hCn hBl hCl
    have hGl : G ∈ l := by simpa [hnl] using hGn
    rcases col_of_bet hbBDG with ⟨k, hBk, hDk, hGk⟩
    have hkl : k = l := hΓ₁.I₂ hnBG hBk hGk hBl hGl
    have hDl : D ∈ l := by simpa [hkl] using hDk
    exact hnDl hDl
  have hnBGC : ≠₃ B G C := by
    exact ⟨hnBG, hnGC, hnBC⟩
  have hlα : l ⊂ α := hΓ₁.I₆ hnBC hBl hCl hBα hCα
  have hAα : A ∈ α := hlα A hAl
  rcases col_of_bet hbBDG with ⟨n, hBn, hDn, hGn⟩
  have hnα : n ⊂ α := hΓ₁.I₆ hnBG hBn hGn hBα hGα
  have hDα : D ∈ α := hnα D hDn
  have hm₁α : m₁ ⊂ α := hΓ₁.I₆ hnAD hAm₁ hDm₁ hAα hDα
  have h₁ : ∃ A, A ∈ m₁ ∧ B ≺ A ≺ G := ⟨D, hDm₁, hbBDG⟩
  have h₂ := hΓ₂.II₄ hnBGC hncBGC hm₁α hBα hGα hCα hnBm₁ hnGm₁ hnCm₁ h₁
  have hnot_left : ¬ ∃ E, E ∈ m₁ ∧ B≺E≺C := by
    intro h
    rcases h with ⟨E, hEm₁, hBEC⟩
    have hEl : E ∈ l := by
      rcases col_of_bet hBEC with ⟨r, hBr, hEr, hCr⟩
      have hr_eq_l : r = l := hΓ₁.I₂ hnBC hBr hCr hBl hCl
      simpa [hr_eq_l] using hEr
    by_cases hEA : E = A
    · subst hEA
      have hCAB : C ≺ E ≺ B := (hΓ₂.II₁ hBEC).2.2
      exact hnbCAB hCAB
    · have hm₁_eq_l : m₁ = l := hΓ₁.I₂ hEA hEm₁ hAm₁ hEl hAl
      have hDl' : D ∈ l := by simpa [hm₁_eq_l] using hDm₁
      exact hnDl hDl'
  have hright : ∃ F, F ∈ m₁ ∧ G≺F≺C := by
    rcases h₂ with hleft | hright
    · exact False.elim (hnot_left hleft)
    · exact hright
  rcases hright with ⟨E, hEm₁, hbGEC⟩
  have h₃ : ≠₃ A E C ∧ ¬Col A E C ∧ A ∉ n ∧ E ∉ n ∧ C ∉ n:= by
    have hnAn : A ∉ n := by
      intro hAn
      have hnl : n = l := hΓ₁.I₂ hnAB hAn hBn hAl hBl
      have hDl : D ∈ l := by simpa [hnl] using hDn
      exact hnDl hDl
    have hnCn : C ∉ n := by
      intro hCn
      have hnl : n = l := hΓ₁.I₂ hnBC hBn hCn hBl hCl
      have hDl : D ∈ l := by simpa [hnl] using hDn
      exact hnDl hDl
    have hnGl : G ∉ l := by
      intro hGl
      exact hncBGC ⟨l, hBl, hGl, hCl⟩
    have hnAE : A ≠ E := by
      intro hAE
      subst hAE
      rcases col_of_bet hbGEC with ⟨r, hGr, hEr, hCr⟩
      have hrl : r = l := hΓ₁.I₂ hnAC hEr hCr hAl hCl
      have hGl : G ∈ l := by simpa [hrl] using hGr
      exact hnGl hGl
    have hnEC : E ≠ C := (neq3_of_bet hbGEC).2.1
    have hnEn : E ∉ n := by
      intro hEn
      rcases col_of_bet hbGEC with ⟨r, hGr, hEr, hCr⟩
      have hrn : r = n := hΓ₁.I₂ (neq3_of_bet hbGEC).1 hGr hEr hGn hEn
      have hCn : C ∈ n := by simpa [hrn] using hCr
      exact hnCn hCn
    have hncAEC : ¬Col A E C := by
      intro hcAEC
      rcases hcAEC with ⟨r, hAr, hEr, hCr⟩
      have hrl : r = l := hΓ₁.I₂ hnAC hAr hCr hAl hCl
      have hEl : E ∈ l := by simpa [hrl] using hEr
      have hm₁l : m₁ = l := hΓ₁.I₂ hnAE hAm₁ hEm₁ hAl hEl
      have hDl : D ∈ l := by simpa [hm₁l] using hDm₁
      exact hnDl hDl
    exact ⟨⟨hnAE, hnEC, hnAC⟩, hncAEC, hnAn, hnEn, hnCn⟩
  obtain ⟨hnAEC, hncAEC, hnAn, hnEn, hnCn⟩ := h₃
  have hEα := hm₁α E hEm₁
  have hnDE : D ≠ E := by
    intro hDE
    subst hDE
    exact hnEn hDn
  have hnADE : ≠₃ A D E := by
    exact ⟨hnAD, hnDE, hnAEC.1⟩
  have hColADE : Col A D E := col_of_online hAm₁ hDm₁ hEm₁
  rcases hΓ₁.I₁ hnCD with ⟨m₃, hCm₃, hDm₃⟩
  have hm₃α : m₃ ⊂ α := hΓ₁.I₆ hnCD hCm₃ hDm₃ hCα hDα
  have hnAG : A ≠ G := by
    intro hAG
    subst hAG
    rcases col_of_bet hbBDG with ⟨r, hBr, hDr, hAr⟩
    have hrl : r = l := hΓ₁.I₂ hnAB hAr hBr hAl hBl
    have hDl : D ∈ l := by simpa [hrl] using hDr
    exact hnDl hDl
  have hnAm₃ : ¬ A ∈ m₃ := by
    intro hAm₃
    have hm₃l : m₃ = l := hΓ₁.I₂ hnAC hAm₃ hCm₃ hAl hCl
    have hDl : D ∈ l := by simpa [hm₃l] using hDm₃
    exact hnDl hDl
  have hnBm₃ : ¬ B ∈ m₃ := by
    intro hBm₃
    have hm₃l : m₃ = l := hΓ₁.I₂ hnBC hBm₃ hCm₃ hBl hCl
    have hDl : D ∈ l := by simpa [hm₃l] using hDm₃
    exact hnDl hDl
  have hnGm₃ : ¬ G ∈ m₃ := by
    intro hGm₃
    rcases col_of_bet hbBDG with ⟨r, hBr, hDr, hGr⟩
    have hm₃r : m₃ = r := hΓ₁.I₂ hnDG hDm₃ hGm₃ hDr hGr
    have hCr : C ∈ r := by simpa [hm₃r] using hCm₃
    have hrl : r = l := hΓ₁.I₂ hnBC hBr hCr hBl hCl
    have hDl : D ∈ l := by simpa [hrl] using hDr
    exact hnDl hDl
  have hncBGA : ¬ Col B G A := by
    intro hCol
    rcases hCol with ⟨r, hBr, hGr, hAr⟩
    have hrl : r = l := hΓ₁.I₂ hnAB hAr hBr hAl hBl
    have hGl : G ∈ l := by simpa [hrl] using hGr
    rcases col_of_bet hbBDG with ⟨s, hBs, hDs, hGs⟩
    have hsl : s = l := hΓ₁.I₂ hnBG hBs hGs hBl hGl
    have hDl : D ∈ l := by simpa [hsl] using hDs
    exact hnDl hDl
  have hnBGA : ≠₃ B G A := by
    exact ⟨hnBG, Ne.symm hnAG, Ne.symm hnAB⟩
  have hBG_on_m₃ : ∃ X, X ∈ m₃ ∧ B ≺ X ≺ G := by
    exact ⟨D, hDm₃, hbBDG⟩
  have hpaschBGA :=
    hΓ₂.II₄ hnBGA hncBGA hm₃α hBα hGα hAα hnBm₃ hnGm₃ hnAm₃ hBG_on_m₃
  have hnot_left_BGA : ¬ ∃ X, X ∈ m₃ ∧ B ≺ X ≺ A := by
    intro h
    rcases h with ⟨X, hXm₃, hBXA⟩
    have hXl : X ∈ l := by
      rcases col_of_bet hBXA with ⟨r, hBr, hXr, hAr⟩
      have hrl : r = l := hΓ₁.I₂ hnAB hAr hBr hAl hBl
      simpa [hrl] using hXr
    have hXC : X = C := by
      by_cases hXC : X = C
      · exact hXC
      · have hm₃l : m₃ = l := hΓ₁.I₂ hXC hXm₃ hCm₃ hXl hCl
        have hDl : D ∈ l := by simpa [hm₃l] using hDm₃
        exact False.elim (hnDl hDl)
    have hBCA : B ≺ C ≺ A := by simpa [hXC] using hBXA
    exact hnbBCA hBCA
  have hF_on_m₃ : ∃ F, F ∈ m₃ ∧ A ≺ F ≺ G := by
    rcases hpaschBGA with hleft | hright
    · exact False.elim (hnot_left_BGA hleft)
    · rcases hright with ⟨F, hFm₃, hGFA⟩
      exact ⟨F, hFm₃, (hΓ₂.II₁ hGFA).2.2⟩
  rcases hF_on_m₃ with ⟨F, hFm₃, hAFG⟩
  have hnAGE : ≠₃ A G E := by
    exact ⟨hnAG, (neq3_of_bet hbGEC).1, hnAEC.1⟩
  have hncAGE : ¬ Col A G E := by
    intro hCol
    rcases hCol with ⟨r, hAr, hGr, hEr⟩
    have hrm₁ : r = m₁ := hΓ₁.I₂ hnAEC.1 hAr hEr hAm₁ hEm₁
    have hGm₁' : G ∈ m₁ := by simpa [hrm₁] using hGr
    exact hnGm₁ hGm₁'
  have hnEm₃ : ¬ E ∈ m₃ := by
    intro hEm₃
    have hm₃m₁ : m₃ = m₁ := hΓ₁.I₂ hnDE hDm₃ hEm₃ hDm₁ hEm₁
    have hCm₁' : C ∈ m₁ := by simpa [hm₃m₁] using hCm₃
    exact hnCm₁ hCm₁'
  have hAE_on_n : ∃ X, X ∈ n ∧ A ≺ X ≺ E := by
    have hpaschAGE :=
      hΓ₂.II₄ hnAGE hncAGE hm₃α hAα hGα hEα hnAm₃ hnGm₃ hnEm₃
        ⟨F, hFm₃, hAFG⟩
    have hnot_right_AGE : ¬ ∃ X, X ∈ m₃ ∧ G ≺ X ≺ E := by
      intro h
      rcases h with ⟨X, hXm₃, hGXE⟩
      rcases col_of_bet hGXE with ⟨r, hGr, hXr, hEr⟩
      rcases col_of_bet hbGEC with ⟨s, hGs, hEs, hCs⟩
      have hrs : r = s := hΓ₁.I₂ (neq3_of_bet hbGEC).1 hGr hEr hGs hEs
      have hCr : C ∈ r := by simpa [hrs] using hCs
      have hXC : X = C := by
        by_cases hXC : X = C
        · exact hXC
        · have hm₃r : m₃ = r := hΓ₁.I₂ hXC hXm₃ hCm₃ hXr hCr
          have hGm₃' : G ∈ m₃ := by simpa [hm₃r] using hGr
          exact False.elim (hnGm₃ hGm₃')
      have hGCE : G ≺ C ≺ E := by simpa [hXC] using hGXE
      have hCEG : C ≺ E ≺ G := (hΓ₂.II₁ hbGEC).2.2
      have hnot := (hΓ₂.II₃ (col_of_bet hGCE)).1
      exact hnot ⟨hGCE, hCEG⟩
    have hAXE_on_m₃ : ∃ X, X ∈ m₃ ∧ A ≺ X ≺ E := by
      rcases hpaschAGE with hleft | hright
      · exact hleft
      · exact False.elim (hnot_right_AGE hright)
    rcases hAXE_on_m₃ with ⟨X, hXm₃, hAXE⟩
    have hXm₁ : X ∈ m₁ := by
      rcases col_of_bet hAXE with ⟨r, hAr, hXr, hEr⟩
      have hrm₁ : r = m₁ := hΓ₁.I₂ hnAEC.1 hAr hEr hAm₁ hEm₁
      simpa [hrm₁] using hXr
    have hXD : X = D := by
      by_cases hXD : X = D
      · exact hXD
      · have hm₁m₃ : m₁ = m₃ := hΓ₁.I₂ hXD hXm₁ hDm₁ hXm₃ hDm₃
        have hCm₁' : C ∈ m₁ := by simpa [hm₁m₃] using hCm₃
        exact False.elim (hnCm₁ hCm₁')
    exact ⟨D, hDn, by simpa [hXD] using hAXE⟩
  have h₄ := hΓ₂.II₄ hnAEC hncAEC hnα hAα hEα hCα hnAn hnEn hnCn hAE_on_n
  rcases h₄ with hleft | hright
  · rcases hleft with ⟨X, hXn, hAXC⟩
    have hXl : X ∈ l := by
      rcases col_of_bet hAXC with ⟨r, hAr, hXr, hCr⟩
      have hrl : r = l := hΓ₁.I₂ hnAC hAr hCr hAl hCl
      simpa [hrl] using hXr
    have hXB : X = B := by
      by_cases hXB : X = B
      · exact hXB
      · have hnl : n = l := hΓ₁.I₂ hXB hXn hBn hXl hBl
        have hDl : D ∈ l := by simpa [hnl] using hDn
        exact False.elim (hnDl hDl)
    simpa [hXB] using hAXC
  · rcases hright with ⟨X, hXn, hEXC⟩
    have hGX : G ≠ X := by
      intro hGX
      subst hGX
      have hCGE : C ≺ G ≺ E := (hΓ₂.II₁ hEXC).2.2
      have hCol := col_of_bet hbGEC
      have hnot := (hΓ₂.II₃ hCol).2.2
      exact hnot ⟨hCGE, hbGEC⟩
    have hCn' : C ∈ n := by
      rcases col_of_bet hEXC with ⟨r, hEr, hXr, hCr⟩
      rcases col_of_bet hbGEC with ⟨m, hGm, hEm, hCm⟩
      have hrm : r = m := hΓ₁.I₂ hnAEC.2.1 hEr hCr hEm hCm
      have hGr : G ∈ r := by simpa [hrm] using hGm
      have hrn : r = n := hΓ₁.I₂ hGX hGr hXr hGn hXn
      simpa [hrn] using hCr
    exact False.elim (hnCn hCn')

theorem C₁_₁ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  ≠₃ A B C → ¬Col A B C →
    l ⊂ α → A ∈ α → B ∈ α → C ∈ α → A ∉ l → B ∉ l → C ∉ l →
      (∃ D, D ∈ l ∧ A ≺ D ≺ B) →
        (∃ E, E ∈ l ∧ (E ≺ A ≺ C ∨ A ≺ C ≺ E)) →
          (∃ F, F ∈ l ∧ B ≺ F ≺ C) := by
  intro hnABC hncABC hlα hAα hBα hCα hnAl hnBl hnCl hlAB hlAC
  have h₁ := hΓ₂.II₄ hnABC hncABC hlα hAα hBα hCα hnAl hnBl hnCl hlAB
  simp only [and_or_left, exists_or] at hlAC
  rcases h₁ with h₁ | h₁
  · rcases hlAC with h₂ | h₂
    · have h₁ : ∃ E, E ∈ l ∧ C ≺ E ≺ A := by
        rcases h₁ with ⟨E, hEl, hbAEC⟩
        refine ⟨E, hEl, ?_⟩
        rw [bet_symm]
        exact hbAEC
      have h₃ := L₅ hnCl h₁
      simp only [not_exists, not_and] at h₃
      rcases h₂ with ⟨E, hEl, hb₁⟩
      have h₄ := h₃ E hEl
      rw [bet_symm] at h₄
      contradiction
    · have h₃ := L₅ hnAl h₁
      simp only [not_exists, not_and] at h₃
      rcases h₂ with ⟨E, hEl, hb₁⟩
      have h₄ := h₃ E hEl
      contradiction
  · exact h₁

theorem C₁_₂ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  ≠₃ A B C → ¬Col A B C →
    l ⊂ α → A ∈ α → B ∈ α → C ∈ α → A ∉ l → B ∉ l → C ∉ l →
      (∃ D, D ∈ l ∧ A ≺ D ≺ B) →
        (∃ E, E ∈ l ∧ E ≺ A ≺ C) ∨ (∃ E, E ∈ l ∧ A ≺ C ≺ E) →
          (∃ F, F ∈ l ∧ B ≺ F ≺ C) := by
  intro hnABC hncABC hlα hAα hBα hCα hnAl hnBl hnCl hlAB hlAC
  have h₁ := hΓ₂.II₄ hnABC hncABC hlα hAα hBα hCα hnAl hnBl hnCl hlAB
  rcases h₁ with h₁ | h₁
  · rcases hlAC with h₂ | h₂
    · have h₁ : ∃ E, E ∈ l ∧ C ≺ E ≺ A := by
        rcases h₁ with ⟨E, hEl, hbAEC⟩
        refine ⟨E, hEl, ?_⟩
        rw [bet_symm]
        exact hbAEC
      have h₃ := L₅ hnCl h₁
      simp only [not_exists, not_and] at h₃
      rcases h₂ with ⟨E, hEl, hb₁⟩
      have h₄ := h₃ E hEl
      rw [bet_symm] at h₄
      contradiction
    · have h₃ := L₅ hnAl h₁
      simp only [not_exists, not_and] at h₃
      rcases h₂ with ⟨E, hEl, hb₁⟩
      have h₄ := h₃ E hEl
      contradiction
  · exact h₁


theorem L₇ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] : A ≺ B ≺ C → B ≺ C ≺ D → A ≺ C ≺ D := by
  intro hbABC hbBCD
  have hcABC := col_of_bet hbABC
  have ⟨hnAB, hnBC, hnAC⟩ := neq3_of_bet hbABC
  rcases hcABC with ⟨g, hAg, hBg, hCg⟩
  have hcABC := col_of_bet hbABC
  have hcBCD := col_of_bet hbBCD
  have hDg : D ∈ g := by
    rcases hcBCD with ⟨l, hBl, hCl, hDl⟩
    have h₁ := hΓ₁.I₂ (neq3_of_bet hbABC).2.1 hBl hCl hBg hCg
    subst h₁
    exact hDl
  have hnAD : A ≠ D := by
    intro hAD
    subst hAD
    have h₁ := (hΓ₂.II₃ hcABC).1
    exact h₁ ⟨hbABC, hbBCD⟩
  rcases exists_not_online_point g with ⟨E, hnEg⟩
  have hnCE := neq_of_online_and_not_online hCg hnEg
  rcases hΓ₂.II₂ hnCE with ⟨F, hbCEF⟩
  rcases hΓ₁.I₄ B C E with ⟨α, hBα, hCα, hEα⟩
  have hgα : g ⊂ α := hΓ₁.I₆ hnBC hBg hCg hBα hCα
  have hAα := hgα A hAg
  have hDα := hgα D hDg
  have ⟨_, hnEF, hnCF⟩ := neq3_of_bet hbCEF
  have hnFg : F ∉ g := by
    intro hFg
    have hcCEF := col_of_bet hbCEF
    rw [col_right_comm] at hcCEF
    have hEg : E ∈ g := online_of_col hnCF hcCEF hCg hFg
    contradiction
  have hnAE := neq_of_online_and_not_online hAg hnEg
  rcases hΓ₁.I₁ hnAE with ⟨l₁, hAl₁, hEl₁⟩
  have hl₁α : l₁ ⊂ α := hΓ₁.I₆ hnAE hAl₁ hEl₁ hAα hEα
  have hFα : F ∈ α := by
    rcases hΓ₁.I₁ hnCE with ⟨m₁, hCm₁, hEm₁⟩
    have hm₁α : m₁ ⊂ α := hΓ₁.I₆ hnCE hCm₁ hEm₁ hCα hEα
    have hFm₁ := online_of_col hnCE (col_of_bet hbCEF) hCm₁ hEm₁
    exact hm₁α F hFm₁
  have hnBF : B ≠ F := neq_of_online_and_not_online hBg hnFg
  have hnFCB : ≠₃ F C B := ⟨Ne.symm hnCF, Ne.symm hnBC, Ne.symm hnBF⟩
  have hncFCB := not_col_of_online_and_not_online hnBC hBg hCg hnFg
  rw [col_right_comm, col_left_rot] at hncFCB
  have hnCl₁ : C ∉ l₁:= by
    intro hCl₁
    have hl₁g := hΓ₁.I₂ hnAC hAl₁ hCl₁ hAg hCg
    subst hl₁g
    contradiction
  have hnBl₁ : B ∉ l₁ := by
    intro hBl₁
    have hl₁g := hΓ₁.I₂ hnAB hAl₁ hBl₁ hAg hBg
    subst hl₁g
    contradiction
  have hnFl₁ : F ∉ l₁ := by
    intro hFl₁
    have hcCEF : Col C E F := col_of_bet hbCEF
    rcases hcCEF with ⟨m, hCm, hEm, hFm⟩
    have hl₁m : l₁ = m := hΓ₁.I₂ hnEF hEl₁ hFl₁ hEm hFm
    subst hl₁m
    contradiction
  have h₁ := hΓ₂.II₄ hnFCB hncFCB hl₁α hFα hCα hBα hnFl₁ hnCl₁ hnBl₁ ⟨E, hEl₁, bet_symm.mp hbCEF⟩
  have h₂ : ∃ A, A ∈ l₁ ∧ C ≺ B ≺ A := ⟨A, hAl₁, bet_symm.mp hbABC⟩
  apply L₆ hnCl₁ at h₂
  have h₁ : ∃ E, E ∈ l₁ ∧ F ≺ E ≺ B := by
    rcases h₁ with h₁ | h₁
    · exact h₁
    · contradiction
  rcases h₁ with ⟨G, hGl₁, hbFGB⟩
  have hcFGB := col_of_bet hbFGB
  have ⟨hnFG, hnGB, hnFB⟩ := neq3_of_bet hbFGB
  have hnGg : G ∉ g := by
    intro hGg
    rw [col_left_rot] at hcFGB
    have hFg := online_of_col hnGB hcFGB hGg hBg
    contradiction
  have hnBG : B ≠ G := neq_of_online_and_not_online hBg hnGg
  have hnDG : D ≠ G := neq_of_online_and_not_online hDg hnGg
  have hnBD : B ≠ D := (neq3_of_bet hbBCD).2.2
  have hnBDG : ≠₃ B D G := ⟨hnBD, hnDG, hnBG⟩
  have hncBDG : ¬Col B D G := by
    intro ⟨m, hBm, hDm, hGm⟩
    have hgm := hΓ₁.I₂ hnBD hBg hDg hBm hDm
    subst hgm
    contradiction
  rcases hΓ₁.I₁ hnCF with ⟨l₂, hCl₂, hFl₂⟩
  have hEl₂ : E ∈ l₂ := online_of_col hnCF ((col_right_comm.mp ∘ col_of_bet) (hbCEF)) hCl₂ hFl₂
  have hnBl₂ : B ∉ l₂ := by
    intro hBl₂
    have hgl₂ := hΓ₁.I₂ hnBC hBg hCg hBl₂ hCl₂
    subst hgl₂
    contradiction
  have hnCD := (neq3_of_bet hbBCD).2.1
  have hnDl₂ : D ∉ l₂ := by
    intro hDl₂
    have hgl₂ := hΓ₁.I₂ hnCD hCg hDg hCl₂ hDl₂
    subst hgl₂
    contradiction
  have hnGl₂ : G ∉ l₂ := by
    intro hGl₂
    rcases hcFGB with ⟨m, hFm, hGm, hBm⟩
    have hnFG := (neq3_of_bet hbFGB).1
    have hl₂m := hΓ₁.I₂ hnFG hFl₂ hGl₂ hFm hGm
    subst hl₂m
    contradiction
  have hl₂α : l₂ ⊂ α := hΓ₁.I₆ hnCF hCl₂ hFl₂ hCα hFα
  have hGα : G ∈ α := hl₁α G hGl₁
  have h₃ := hΓ₂.II₄ hnBDG hncBDG hl₂α hBα hDα hGα hnBl₂ hnDl₂ hnGl₂ ⟨C, hCl₂, hbBCD⟩
  have h₄ : ∃ F, F ∈ l₂ ∧ B ≺ G ≺ F := ⟨F, hFl₂, bet_symm.mp hbFGB⟩
  have h₅ := L₆ hnBl₂ h₄
  have h₆ : ∃ H, H ∈ l₂ ∧ D ≺ H ≺ G := by
    rcases h₃ with h₃ | h₃
    · contradiction
    · exact h₃
  rcases h₆ with ⟨H, hHl₂, hbDHG⟩
  have hnACE : ≠₃ A C E := ⟨hnAC, hnCE, hnAE⟩
  have hncACE := not_col_of_online_and_not_online hnAC hAg hCg hnEg
  rcases hΓ₁.I₁ hnBF with ⟨l₃, hBl₃, hFl₃⟩
  have hGl₃ : G ∈ l₃:= by
    rw [col_symm, col_right_comm] at hcFGB
    exact online_of_col hnBF hcFGB hBl₃ hFl₃
  have hnAl₃ : A ∉ l₃ := by
    intro hAl₃
    have hgl₃ := hΓ₁.I₂ hnAB hAg hBg hAl₃ hBl₃
    subst hgl₃
    contradiction
  have hnCl₃ : C ∉ l₃ := by
    intro hCl₃
    have hgl₃ := hΓ₁.I₂ hnBC hBg hCg hBl₃ hCl₃
    subst hgl₃
    contradiction
  have hnEl₃ : E ∉ l₃ := by
    intro hEl₃
    rcases col_of_bet hbCEF with ⟨m, hCm, hEm, hFm⟩
    have hml₃ := hΓ₁.I₂ hnEF hEm hFm hEl₃ hFl₃
    subst hml₃
    contradiction
  have hl₃α : l₃ ⊂ α := hΓ₁.I₆ hnBF hBl₃ hFl₃ hBα hFα
  have h₆ := hΓ₂.II₄ hnACE hncACE hl₃α hAα hCα hEα hnAl₃ hnCl₃ hnEl₃ ⟨B, hBl₃, hbABC⟩
  have h₇ : ∃ F, F ∈ l₃ ∧ C ≺ E ≺ F := ⟨F, hFl₃, hbCEF⟩
  have h₇ := L₆ hnCl₃ h₇
  have h₈ : ∃ G, G ∈ l₃ ∧ A ≺ G ≺ E := by
    rcases h₆ with h | h
    · exact h
    · contradiction
  rcases h₈ with ⟨G', hG'l₃, hbAG'E⟩
  have hGG' : G = G' := by
    by_contra hnGG'
    have hcAEG' := col_of_bet hbAG'E
    rw [col_right_comm] at hcAEG'
    have hG'l₁ := online_of_col hnAE hcAEG' hAl₁ hEl₁
    have hl₁l₃ := hΓ₁.I₂ hnGG' hGl₁ hG'l₁ hGl₃ hG'l₃
    subst hl₁l₃
    contradiction
  subst hGG'
  have hHα := hl₂α H hHl₂
  have hnAG : A ≠ G := neq_of_online_and_not_online hAg hnGg
  have hnDGA : ≠₃ D G A := ⟨hnDG, Ne.symm hnAG, Ne.symm hnAD⟩
  have hncDGA : ¬Col D G A := by
    intro ⟨m, hDm, hGm, hAm⟩
    have hgm := hΓ₁.I₂ hnAD hAg hDg hAm hDm
    subst hgm
    contradiction
  have hnAl₂ : A ∉ l₂ := by
    intro hAl₂
    have hgl₂ := hΓ₁.I₂ hnAC hAg hCg hAl₂ hCl₂
    subst hgl₂
    contradiction
  have h₇ := hΓ₂.II₄ hnDGA hncDGA hl₂α hDα hGα hAα hnDl₂ hnGl₂ hnAl₂ ⟨H, hHl₂, hbDHG⟩
  have h₈ : ∃ E, E ∈ l₂ ∧ A ≺ G ≺ E := ⟨E, hEl₂, hbAG'E⟩
  have h₉ := L₆ hnAl₂ h₈
  have h₉ : ¬∃ C, C ∈ l₂ ∧ G≺C≺A := by
    simp only [not_exists, not_and] at h₉ ⊢
    intro E hEl₂
    have h₉E := h₉ E hEl₂
    rw [bet_symm]
    exact h₉E
  have h₁₀ : ∃ E, E ∈ l₂ ∧ D ≺ E ≺ A := by
    rcases h₇ with h | h
    · exact h
    · contradiction
  rcases h₁₀ with ⟨C', hC'l₂, hbAC'D⟩
  rw [bet_symm] at hbAC'D
  have hCC' : C = C' := by
    by_contra hnCC'
    have hC'g := online_of_col hnAD ((col_right_comm.mp ∘ col_of_bet) hbAC'D) hAg hDg
    have hgl₂ := hΓ₁.I₂ hnCC' hCg hC'g hCl₂ hC'l₂
    subst hgl₂
    contradiction
  subst hCC'
  exact hbAC'D

theorem T₅_₁ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  A ≺ B ≺ C → B ≺ C ≺ D → A ≺ B ≺ D ∧ A ≺ C ≺ D := by
  intro hbABC hbBCD
  constructor
  · rw [bet_symm] at hbABC hbBCD ⊢
    exact L₇ hbBCD hbABC
  · exact L₇ hbABC hbBCD

def PointSameSide (O A X : Γ.Point) : Prop := O = X ∨ (Col O A X ∧ ¬A ≺ O ≺ X)

def SameRayPt (O A B : Γ.Point) : Prop :=
  PointSameSide O A B ∧ PointSameSide O B A

structure Ray (Γ : Geometry) (O : Γ.Point) where
  dir : Γ.Point
  neq : O ≠ dir

def PointRay {Γ : Geometry} (O A : Γ.Point) (hOA : O ≠ A) : Γ.Ray O where
  dir := A
  neq := hOA

def inRay {Γ : Geometry} {O : Γ.Point} (X : Γ.Point) (r : Γ.Ray O) : Prop :=
  PointSameSide O r.dir X

notation:50 X:50 "∈" r:50 => inRay X r

structure Angle (Γ : Geometry) (O : Γ.Point) where
  left : Γ.Ray O
  right : Γ.Ray O

def angle {Γ : Geometry} {O : Γ.Point} (h k : Γ.Ray O) : Γ.Angle O where
  left := h
  right := k

def pointAngle {Γ : Geometry} (A O B : Γ.Point)
    {hOA : O ≠ A} {hOB : O ≠ B} : Γ.Angle O where
  left := PointRay O A hOA
  right := PointRay O B hOB
notation:50 "∠" "(" h "," k ")" => angle h k
notation:50 "∠" A:arg O:arg B:arg => pointAngle A O B

abbrev segCong (A A' : Γ.Segment) : Prop := Γ.SegCong A.1 A.2 A'.1 A'.2
abbrev segCong' (A B A' B' : Γ.Point) : Prop := Γ.SegCong A B A' B'
notation:50 "[" A:arg "," B:arg "]" "≡" "[" A':arg "," B':arg "]" => segCong' A B A' B'

abbrev angCong := Γ.AngCong
notation:50 "∠" A:arg B:arg C:arg "≡" "∠" A':arg B':arg C':arg => angCong A B C A' B' C'

def RayInLine {O : Γ.Point} (h : Γ.Ray O) (l : Γ.Line) : Prop := ∀ A, A ∈ h → A ∈ l
notation:50 h:50 "⊂" l:50 => RayInLine h l
theorem exists_line_of_ray [hΓ : IncidentAxioms Γ] : ∀ {O} (h : Γ.Ray O), ∃ l, h ⊂ l := by
  intro O h
  rcases hΓ.I₁ h.neq with ⟨l, hOl, hdl⟩
  use l
  intro A hAl
  rcases hAl with hOA | hA
  · subst hOA
    exact hOl
  · exact online_of_col h.neq hA.1 hOl hdl

theorem SourceInRay {O : Γ.Point} (h : Γ.Ray O) : O ∈ h := by
  simp [inRay, PointSameSide]

theorem exists_ray [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] (A : Γ.Point) :
  ∃ (O : Γ.Point) (h : Γ.Ray O), A ∈ h := by
  rcases exists_line_of_forall_point A with ⟨l, hAl⟩
  rcases exists_not_online_point l with ⟨B, hnBl⟩
  have hnAB : A ≠ B := neq_of_online_and_not_online hAl hnBl
  use B
  use {
    dir := A
    neq := Ne.symm hnAB
  }
  simp only [inRay, PointSameSide]
  right
  constructor
  · rw [col_symm]
    exact col_of_eq rfl
  · intro hbABA
    have hnAA := (neq3_of_bet hbABA).2.2
    have hAA : A = A := rfl
    contradiction

class CongruenceAxioms (Γ : Geometry) where
  III₁ :
    ∀ {A B A'} {l : Γ.Line} (h : Γ.Ray A'),
      A ∈ l → B ∈ l → ∃ B', B' ∈ h ∧ [A, B] ≡ [A', B']
  III₂ :
    ∀ {A B A' B' A'' B'' : Γ.Point},
      [A', B'] ≡ [A, B] → [A'', B''] ≡ [A, B] → [A', B'] ≡ [A'', B'']
  III₃ :
    ∀ {A B C A' B' C' : Γ.Point},
      A ≺ B ≺ C → A' ≺ B' ≺ C' →
        [A, B] ≡ [A', B'] → [B, C] ≡ [B', C'] → [A, C] ≡ [A', C']
  III₄ :
    (∀ {A B C : Γ.Point}, ∠ A B C ≡ ∠ A B C) ∧
      (∀ {A B C : Γ.Point}, ∠ A B C ≡ ∠ C B A) ∧
      ∀ {A B C A' B' P : Γ.Point} {l : Γ.Line} {α : Γ.Plane},
        ¬Col A B C → l ⊂ α → A' ∈ l → B' ∈ l → A' ≠ B' → P ∈ α → P ∉ l →
          ∃ C',
            C' ∈ α ∧ C' ∉ l ∧ SameSide C' P l ∧ ∠ B A C ≡ ∠ B' A' C' ∧
              ∀ {C'' : Γ.Point},
                C'' ∈ α → C'' ∉ l → SameSide C'' P l → ∠ B A C ≡ ∠ B' A' C'' →
                  SameRayPt A' C' C''
  III₅ :
    ∀ {A B C A' B' C' : Γ.Point},
      [A, B] ≡ [A', B'] → [A, C] ≡ [A', C'] → ∠ B A C ≡ ∠ B' A' C' → ∠ A B C ≡ ∠ A' B' C'

theorem seg_cong_refl [hΓ₁ : IncidentAxioms Γ] [hΓ₃ : CongruenceAxioms Γ] (A B : Γ.Point) :
  [A, B] ≡ [A, B] := by
  rcases exists_line_of_point A B with ⟨l, hAl, hBl⟩
  rcases exists_not_online_point l with ⟨P, hnPl⟩
  rcases exists_neq_point P with ⟨Q', hnPQ'⟩
  let h : Γ.Ray P := {
    dir := Q'
    neq := hnPQ'
  }
  rcases hΓ₃.III₁ h hAl hBl with ⟨Q, hQh, hABPQ⟩
  exact hΓ₃.III₂ hABPQ hABPQ

theorem seg_cong_symm [IncidentAxioms Γ] [hΓ₃ : CongruenceAxioms Γ] :
  [A, B] ≡ [A', B'] → [A', B'] ≡ [A, B] := by
  intro hABA'B'
  have hA'B'A'B' : [A', B'] ≡ [A', B'] := seg_cong_refl A' B'
  exact hΓ₃.III₂ hA'B'A'B' hABA'B'

theorem seg_cong_trans [IncidentAxioms Γ] [hΓ₃ : CongruenceAxioms Γ] {A'' B'' : Γ.Point} :
  [A, B] ≡ [A', B'] → [A', B'] ≡ [A'', B''] → [A, B] ≡ [A'', B''] := by
  intro hABA'B' hA'B'A''B''
  apply seg_cong_symm at hA'B'A''B''
  exact hΓ₃.III₂ hABA'B' hA'B'A''B''

theorem seg_cong_point [hΓ₃ : CongruenceAxioms Γ] : [A, A] ≡ [B, B] := by sorry

theorem exists_unique_cong_point [hΓ₁ : IncidentAxioms Γ] [hΓ₃ : CongruenceAxioms Γ] :
  ∀ {A B A'} {l : Γ.Line} {h : Γ.Ray A'},
    A ∈ l → B ∈ l → ∃! B', B' ∈ h ∧ [A, B] ≡ [A', B'] := by
  intro A B A' l h hAl hBl
  rcases hΓ₃.III₁ h hAl hBl with ⟨B', hB'h, hABA'B'⟩
  use B'
  simp only
  constructor
  · exact ⟨hB'h, hABA'B'⟩
  · intro B'' ⟨hB''h, hABA'B''⟩
    rcases exists_not_online_point l with ⟨C', hC'l⟩
    sorry

theorem seg_cong_comm [hΓ₁ : IncidentAxioms Γ] [hΓ₃ : CongruenceAxioms Γ] : [A, B] ≡ [B, A] := by
  rcases exists_line_of_point A B with ⟨l, hAl, hBl⟩
  by_cases h : A = B
  · subst h
    exact seg_cong_refl A A
  · let k : Γ.Ray B := {
      dir := A
      neq := Ne.symm h
    }
    rcases hΓ₃.III₁ k hAl hBl with ⟨A', hA'k, hABBA'⟩
    simp only [inRay, PointSameSide] at hA'k
    sorry

class AxiomOfParallelLine (Γ : Geometry) where
  IV : ∀ {A} {l : Γ.Line} {α : Γ.Plane},
    l ⊂ α → A ∈ α → A ∉ l →
      ∃! m : Γ.Line, m ⊂ α ∧ A ∈ m ∧ l ∥ m

end Geometry

end Hilbert
