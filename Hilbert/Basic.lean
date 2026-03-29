import Mathlib.Logic.Unique
import Mathlib.Tactic.Use
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Check
import Mathlib.Data.List.Basic

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
abbrev onSegment (A : Γ.Point) (l : Segment) := Γ.Bet l.1 A l.2
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

theorem T₈_₁ : OppoSide A B l → ∃ C, C ∈ l ∧ A ≺ C ≺ B := by
  intro h
  exact h.2.2

theorem T₈_₂ : SameSide A B l → ¬∃ C, C ∈ l ∧ A ≺ C ≺ B := by
  intro h
  exact h.2.2

def OnOpenSegment (A X B : Γ.Point) : Prop := A ≺ X ≺ B

def OnClosedSegment (A X B : Γ.Point) : Prop :=
  X = A ∨ X = B ∨ OnOpenSegment A X B

notation:50 X:50 " ∈ₒ[" A:50 ", " B:50 "]" => OnOpenSegment A X B
notation:50 X:50 " ∈ₛ[" A:50 ", " B:50 "]" => OnClosedSegment A X B

theorem onClosedSegment_left : A ∈ₛ[A, B] := by
  left
  rfl

theorem onClosedSegment_right : B ∈ₛ[A, B] := by
  right
  left
  rfl

theorem onClosedSegment_of_open (h : X ∈ₒ[A, B]) : X ∈ₛ[A, B] := by
  right
  right
  exact h

theorem onClosedSegment_on_line [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
    A ≠ B → A ∈ l → B ∈ l → X ∈ₛ[A, B] → X ∈ l := by
  intro hnAB hAl hBl hX
  rcases hX with rfl | rfl | hXB
  · exact hAl
  · exact hBl
  · exact online_of_col hnAB (col_right_comm.mp (col_of_bet hXB)) hAl hBl

theorem sameSide_symm [hΓ : OrderAxioms Γ] : SameSide A B l → SameSide B A l := by
  intro h
  rcases h with ⟨hnAl, hnBl, hno⟩
  refine ⟨hnBl, hnAl, ?_⟩
  intro hcross
  rcases hcross with ⟨C, hCl, hBCA⟩
  apply hno
  exact ⟨C, hCl, (bet_symm.mp hBCA)⟩

theorem oppoSide_symm [hΓ : OrderAxioms Γ] : OppoSide A B l → OppoSide B A l := by
  intro h
  rcases h with ⟨hnAl, hnBl, hcross⟩
  rcases hcross with ⟨C, hCl, hACB⟩
  refine ⟨hnBl, hnAl, ?_⟩
  exact ⟨C, hCl, (bet_symm.mp hACB)⟩

def SameSideThrough (A B X Y : Γ.Point) : Prop :=
  A ≠ B ∧ ∃ l : Γ.Line, A ∈ l ∧ B ∈ l ∧ SameSide X Y l

def OppoSideThrough (A B X Y : Γ.Point) : Prop :=
  A ≠ B ∧ ∃ l : Γ.Line, A ∈ l ∧ B ∈ l ∧ OppoSide X Y l

theorem sameSideThrough_symm [hΓ : OrderAxioms Γ] :
    SameSideThrough A B X Y → SameSideThrough A B Y X := by
  intro h
  rcases h with ⟨hnAB, l, hAl, hBl, hXY⟩
  exact ⟨hnAB, l, hAl, hBl, sameSide_symm hXY⟩

theorem oppoSideThrough_symm [hΓ : OrderAxioms Γ] :
    OppoSideThrough A B X Y → OppoSideThrough A B Y X := by
  intro h
  rcases h with ⟨hnAB, l, hAl, hBl, hXY⟩
  exact ⟨hnAB, l, hAl, hBl, oppoSide_symm hXY⟩

theorem not_sameSideThrough_of_on_line [hΓ : IncidentAxioms Γ]
    (hnAB : A ≠ B) (hAl : A ∈ l) (hBl : B ∈ l) (hXl : X ∈ l) :
    ¬ SameSideThrough A B X Y := by
  intro h
  rcases h with ⟨_, m, hAm, hBm, hsame⟩
  have hml : m = l := hΓ.I₂ hnAB hAm hBm hAl hBl
  exact hsame.1 (by simpa [hml] using hXl)

structure BrokenLine (Γ : Geometry) where
  carrier : List Γ.Point
  neq : ∀ (n : Fin (carrier.length - 1)),
    carrier.get ⟨n.1, Nat.lt_of_lt_pred n.isLt⟩ ≠
      carrier.get ⟨n.1 + 1, (Nat.lt_sub_iff_add_lt).mp n.isLt⟩

namespace BrokenLine

abbrev EdgeIndex (L : Γ.BrokenLine) := Fin (L.carrier.length - 1)

def edgeStart (L : Γ.BrokenLine) (n : L.EdgeIndex) : Γ.Point :=
  L.carrier.get ⟨n.1, Nat.lt_of_lt_pred n.isLt⟩

def edgeEnd (L : Γ.BrokenLine) (n : L.EdgeIndex) : Γ.Point :=
  L.carrier.get ⟨n.1 + 1, (Nat.lt_sub_iff_add_lt).mp n.isLt⟩

def InPlane (L : Γ.BrokenLine) (α : Γ.Plane) : Prop :=
  ∀ n : Fin L.carrier.length, L.carrier.get n ∈ α

def Connects (L : Γ.BrokenLine) (A B : Γ.Point) : Prop :=
  ∃ h : 0 < L.carrier.length,
    L.carrier.get ⟨0, h⟩ = A ∧
      L.carrier.get ⟨L.carrier.length - 1, Nat.sub_lt h (by decide)⟩ = B

end BrokenLine

def PointOnEdge (L : Γ.BrokenLine) (n : L.EdgeIndex) (X : Γ.Point) : Prop :=
  X = L.edgeStart n ∨ X = L.edgeEnd n ∨ L.edgeStart n ≺ X ≺ L.edgeEnd n

def PointOnBrokenLine (L : Γ.BrokenLine) (X : Γ.Point) : Prop :=
  ∃ n : L.EdgeIndex, PointOnEdge L n X

notation:50 X:50 " ∈ᵇ " L:50 => PointOnBrokenLine L X

structure Polygon (Γ : Geometry) extends Γ.BrokenLine where
  nonempty : 0 < carrier.length
  le_4 : 4 ≤ carrier.length
  looping : carrier.get ⟨0, nonempty⟩ =
    carrier.get ⟨carrier.length - 1, Nat.sub_lt nonempty (by decide)⟩

namespace Polygon

abbrev EdgeIndex (P : Γ.Polygon) := P.toBrokenLine.EdgeIndex
abbrev ConsecutiveIndex (P : Γ.Polygon) := Fin (P.carrier.length - 2)

def edgeStart (P : Γ.Polygon) (n : P.EdgeIndex) : Γ.Point :=
  P.toBrokenLine.edgeStart n

def edgeEnd (P : Γ.Polygon) (n : P.EdgeIndex) : Γ.Point :=
  P.toBrokenLine.edgeEnd n

def firstVertexOfTriple (P : Γ.Polygon) (n : P.ConsecutiveIndex) : Γ.Point :=
  P.carrier.get ⟨n.1, Nat.lt_of_lt_of_le n.isLt (Nat.sub_le _ _)⟩

def secondVertexOfTriple (P : Γ.Polygon) (n : P.ConsecutiveIndex) : Γ.Point :=
  P.carrier.get
    ⟨n.1 + 1, Nat.lt_trans (Nat.lt_succ_self (n.1 + 1)) ((Nat.lt_sub_iff_add_lt).mp n.isLt)⟩

def thirdVertexOfTriple (P : Γ.Polygon) (n : P.ConsecutiveIndex) : Γ.Point :=
  P.carrier.get ⟨n.1 + 2, (Nat.lt_sub_iff_add_lt).mp n.isLt⟩

def InPlane (P : Γ.Polygon) (α : Γ.Plane) : Prop :=
  P.toBrokenLine.InPlane α

def IsCoplanar (P : Γ.Polygon) : Prop :=
  ∃ α : Γ.Plane, P.InPlane α

def PointOnEdge (P : Γ.Polygon) (n : P.EdgeIndex) (X : Γ.Point) : Prop :=
  X ∈ₛ[P.edgeStart n, P.edgeEnd n]

def ProperEdgeIntersection (P : Γ.Polygon) (n m : P.EdgeIndex) (X : Γ.Point) : Prop :=
  X ∈ₒ[P.edgeStart n, P.edgeEnd n] ∧
    X ∈ₒ[P.edgeStart m, P.edgeEnd m]

def EdgeAdjacent (P : Γ.Polygon) (n m : P.toBrokenLine.EdgeIndex) : Prop :=
  n = m ∨
    n.1 + 1 = m.1 ∨
      m.1 + 1 = n.1 ∨
        (n.1 = 0 ∧ m.1 + 1 = P.carrier.length - 1) ∨
          (m.1 = 0 ∧ n.1 + 1 = P.carrier.length - 1)

theorem properEdgeIntersection_symm
    (P : Γ.Polygon) (i j : P.EdgeIndex) (X : Γ.Point) :
    ProperEdgeIntersection P i j X → ProperEdgeIntersection P j i X := by
  intro h
  exact ⟨h.2, h.1⟩

theorem pointOnEdge_of_properEdgeIntersection_left
    (P : Γ.Polygon) (i j : P.EdgeIndex) (X : Γ.Point) :
    ProperEdgeIntersection P i j X → P.PointOnEdge i X := by
  intro h
  exact onClosedSegment_of_open h.1

theorem pointOnEdge_of_properEdgeIntersection_right
    (P : Γ.Polygon) (i j : P.EdgeIndex) (X : Γ.Point) :
    ProperEdgeIntersection P i j X → P.PointOnEdge j X := by
  intro h
  exact onClosedSegment_of_open h.2

end Polygon

def PointOnPolygon (P : Γ.Polygon) (X : Γ.Point) : Prop :=
  ∃ n : P.EdgeIndex, P.PointOnEdge n X

notation:50 X:50 " ∈ᵖ " P:50 => PointOnPolygon P X

structure SimplePolygon (Γ : Geometry) extends Γ.Polygon where
  vertices_nodup : carrier.dropLast.Nodup
  no_collinear_consecutive : ∀ (n : Fin (carrier.length - 2)),
    ¬Col
      (Polygon.firstVertexOfTriple toPolygon n)
      (Polygon.secondVertexOfTriple toPolygon n)
      (Polygon.thirdVertexOfTriple toPolygon n)
  adjacent_intersections :
    ∀ (n m : Fin (carrier.length - 1)),
      n ≠ m → Polygon.EdgeAdjacent toPolygon n m →
        ∀ X,
          Polygon.PointOnEdge toPolygon n X →
            Polygon.PointOnEdge toPolygon m X →
              X = Polygon.edgeStart toPolygon n ∨ X = Polygon.edgeEnd toPolygon n
  no_incidents : ∀ (n m : Fin (carrier.length - 1)),
    ¬ Polygon.EdgeAdjacent toPolygon n m →
      ¬∃ P,
        carrier.get ⟨n.1, Nat.lt_of_lt_pred n.isLt⟩ ≺
          P ≺
            carrier.get ⟨n.1 + 1, (Nat.lt_sub_iff_add_lt).mp n.isLt⟩ ∧
              carrier.get ⟨m.1, Nat.lt_of_lt_pred m.isLt⟩ ≺
                P ≺
                  carrier.get ⟨m.1 + 1, (Nat.lt_sub_iff_add_lt).mp m.isLt⟩

namespace SimplePolygon

def InPlane (P : Γ.SimplePolygon) (α : Γ.Plane) : Prop :=
  P.toPolygon.InPlane α

def IsCoplanar (P : Γ.SimplePolygon) : Prop :=
  ∃ α : Γ.Plane, P.InPlane α

end SimplePolygon

def BrokenLine.AvoidsPolygon (L : Γ.BrokenLine) (P : Γ.Polygon) : Prop :=
  ¬∃ X, X ∈ᵇ L ∧ X ∈ᵖ P

def BrokenLine.CrossesPolygon (L : Γ.BrokenLine) (P : Γ.Polygon) : Prop :=
  ∃ X, X ∈ᵇ L ∧ X ∈ᵖ P

theorem brokenLine_crossesPolygon_iff_not_avoids (L : Γ.BrokenLine) (P : Γ.Polygon) :
    L.CrossesPolygon P ↔ ¬L.AvoidsPolygon P := by
  unfold BrokenLine.CrossesPolygon BrokenLine.AvoidsPolygon
  constructor
  · intro h havoids
    exact havoids h
  · intro h
    by_contra hcross
    exact h hcross

theorem simplePolygon_no_properEdgeIntersection
    (P : Γ.SimplePolygon) (n m : P.toPolygon.EdgeIndex)
    (hnm : ¬ Polygon.EdgeAdjacent P.toPolygon n m) :
    ¬∃ X, Polygon.ProperEdgeIntersection P.toPolygon n m X := by
  intro h
  apply P.no_incidents n m hnm
  rcases h with ⟨X, hX₁, hX₂⟩
  exact ⟨X, hX₁, hX₂⟩

theorem simplePolygon_adjacent_intersections_are_endpoints
    (P : Γ.SimplePolygon) (n m : P.toPolygon.EdgeIndex)
    (hnm : n ≠ m) (hadj : Polygon.EdgeAdjacent P.toPolygon n m) :
    ∀ X,
      Polygon.PointOnEdge P.toPolygon n X →
        Polygon.PointOnEdge P.toPolygon m X →
          X = Polygon.edgeStart P.toPolygon n ∨ X = Polygon.edgeEnd P.toPolygon n := by
  exact P.adjacent_intersections n m hnm hadj

structure Triangle (Γ : Geometry) where
  A : Γ.Point
  B : Γ.Point
  C : Γ.Point

def Triangle.InPlane (T : Γ.Triangle) (α : Γ.Plane) : Prop :=
  T.A ∈ α ∧ T.B ∈ α ∧ T.C ∈ α

def Triangle.Nondegenerate (T : Γ.Triangle) : Prop :=
  ≠₃ T.A T.B T.C ∧ ¬Col T.A T.B T.C

def TriangleBoundary (T : Γ.Triangle) (X : Γ.Point) : Prop :=
  X ∈ₛ[T.A, T.B] ∨ X ∈ₛ[T.B, T.C] ∨ X ∈ₛ[T.C, T.A]

def TriangleInside (T : Γ.Triangle) (α : Γ.Plane) (X : Γ.Point) : Prop :=
  X ∈ α ∧
    SameSideThrough T.A T.B X T.C ∧
      SameSideThrough T.B T.C X T.A ∧
        SameSideThrough T.C T.A X T.B

def TriangleOutside (T : Γ.Triangle) (α : Γ.Plane) (X : Γ.Point) : Prop :=
  X ∈ α ∧ ¬TriangleBoundary T X ∧ ¬TriangleInside T α X

notation:50 X:50 " ∈∂△ " T:50 => TriangleBoundary T X
notation:50 X:50 " ∈ᵢ[" T:50 "; " α:50 "]" => TriangleInside T α X
notation:50 X:50 " ∈ᵉ[" T:50 "; " α:50 "]" => TriangleOutside T α X

theorem triangleInside_mem_plane :
    X ∈ᵢ[T; α] → X ∈ α := by
  intro h
  exact h.1

theorem triangleOutside_mem_plane :
    X ∈ᵉ[T; α] → X ∈ α := by
  intro h
  exact h.1

theorem triangleOutside_not_boundary :
    X ∈ᵉ[T; α] → ¬ X ∈∂△ T := by
  intro h
  exact h.2.1

theorem triangleOutside_not_inside :
    X ∈ᵉ[T; α] → ¬ X ∈ᵢ[T; α] := by
  intro h
  exact h.2.2

theorem triangleInside_not_on_AB [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
    X ∈ᵢ[T; α] → ¬ X ∈ₛ[T.A, T.B] := by
  intro hX hseg
  rcases hX with ⟨_, hAB, _, _⟩
  rcases hAB with ⟨hnAB, l, hAl, hBl, hsame⟩
  have hXl : X ∈ l := onClosedSegment_on_line hnAB hAl hBl hseg
  exact hsame.1 hXl

theorem triangleInside_not_on_BC [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
    X ∈ᵢ[T; α] → ¬ X ∈ₛ[T.B, T.C] := by
  intro hX hseg
  rcases hX with ⟨_, _, hBC, _⟩
  rcases hBC with ⟨hnBC, l, hBl, hCl, hsame⟩
  have hXl : X ∈ l := onClosedSegment_on_line hnBC hBl hCl hseg
  exact hsame.1 hXl

theorem triangleInside_not_on_CA [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
    X ∈ᵢ[T; α] → ¬ X ∈ₛ[T.C, T.A] := by
  intro hX hseg
  rcases hX with ⟨_, _, _, hCA⟩
  rcases hCA with ⟨hnCA, l, hCl, hAl, hsame⟩
  have hXl : X ∈ l := onClosedSegment_on_line hnCA hCl hAl hseg
  exact hsame.1 hXl

theorem triangleInside_not_boundary [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
    X ∈ᵢ[T; α] → ¬ X ∈∂△ T := by
  intro hX hB
  rcases hB with hAB | hBC | hCA
  · exact triangleInside_not_on_AB hX hAB
  · exact triangleInside_not_on_BC hX hBC
  · exact triangleInside_not_on_CA hX hCA

theorem triangleInside_outside_disjoint :
    X ∈ᵢ[T; α] → ¬ X ∈ᵉ[T; α] := by
  intro hIn hOut
  exact hOut.2.2 hIn

theorem triangle_boundary_inside_outside_cover (hXα : X ∈ α) :
    X ∈∂△ T ∨ X ∈ᵢ[T; α] ∨ X ∈ᵉ[T; α] := by
  classical
  by_cases hB : X ∈∂△ T
  · exact Or.inl hB
  · by_cases hI : X ∈ᵢ[T; α]
    · exact Or.inr (Or.inl hI)
    · exact Or.inr (Or.inr ⟨hXα, hB, hI⟩)

theorem triangle_inside_or_outside_of_not_boundary
    (hXα : X ∈ α) (hXb : ¬ X ∈∂△ T) :
    X ∈ᵢ[T; α] ∨ X ∈ᵉ[T; α] := by
  rcases triangle_boundary_inside_outside_cover (T := T) (α := α) hXα with hB | hI | hO
  · contradiction
  · exact Or.inl hI
  · exact Or.inr hO

theorem triangle_inside_outside_partition
    (hX : X ∈ α ∧ ¬ X ∈∂△ T) :
    X ∈ᵢ[T; α] ∨ X ∈ᵉ[T; α] := by
  exact triangle_inside_or_outside_of_not_boundary (T := T) (α := α) hX.1 hX.2

theorem triangle_inside_outside_not_both :
    ¬ (X ∈ᵢ[T; α] ∧ X ∈ᵉ[T; α]) := by
  intro h
  exact triangleInside_outside_disjoint h.1 h.2

theorem triangle_separation_core [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
    (∀ X, X ∈ᵢ[T; α] → X ∈ α ∧ ¬ X ∈∂△ T) ∧
      (∀ X, X ∈ᵉ[T; α] → X ∈ α ∧ ¬ X ∈∂△ T) ∧
        (∀ X, X ∈ α ∧ ¬ X ∈∂△ T →
          X ∈ᵢ[T; α] ∨ X ∈ᵉ[T; α]) ∧
          ∀ X, ¬ (X ∈ᵢ[T; α] ∧ X ∈ᵉ[T; α]) := by
  constructor
  · intro X hX
    exact ⟨triangleInside_mem_plane hX, triangleInside_not_boundary hX⟩
  constructor
  · intro X hX
    exact ⟨triangleOutside_mem_plane hX, triangleOutside_not_boundary hX⟩
  constructor
  · intro X hX
    exact triangle_inside_outside_partition (T := T) (α := α) hX
  · intro X
    exact triangle_inside_outside_not_both (T := T) (α := α)

theorem triangleOutside_of_AB_extension [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hABX : T.A≺T.B≺X) :
    X ∈ᵉ[T; α] := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnAB : T.A ≠ T.B := hneq.1
  rcases hΓ₁.I₁ hnAB with ⟨l, hAl, hBl⟩
  have hXcol : Col T.A T.B X := col_of_bet hABX
  have hXl : X ∈ l := online_of_col hnAB hXcol hAl hBl
  have hlα : l ⊂ α := hΓ₁.I₆ hnAB hAl hBl hAα hBα
  have hXα : X ∈ α := hlα X hXl
  refine ⟨hXα, ?_, ?_⟩
  · intro hBd
    rcases hBd with hABseg | hBCseg | hCAseg
    · rcases hABseg with hXA | hXB | hAXB
      · exact (neq3_of_bet hABX).2.2 hXA.symm
      · exact (neq3_of_bet hABX).2.1 hXB.symm
      · have hBXA : T.B ≺ X ≺ T.A := (bet_symm).mp hAXB
        exact ((not_bet_of_bet hABX).1) hBXA
    · rcases hBCseg with hXB | hXC | hBXC
      · exact (neq3_of_bet hABX).2.1 hXB.symm
      · have hABC : Col T.A T.B T.C := by
          simpa [hXC] using hXcol
        exact hncol hABC
      · have hBXCcol : Col T.B X T.C := col_of_bet hBXC
        have hnXB : X ≠ T.B := by
          exact Ne.symm ((neq3_of_bet hABX).2.1)
        rcases hΓ₁.I₁ hnXB with ⟨m, hXm, hBm⟩
        have hAm : T.A ∈ m := by
          exact online_of_col hnXB (col_symm.mp hXcol) hXm hBm
        have hCm : T.C ∈ m := by
          exact online_of_col hnXB (col_left_comm.mp hBXCcol) hXm hBm
        exact hncol (col_of_online hAm hBm hCm)
    · rcases hCAseg with hXC | hXA | hCXA
      · have hABC : Col T.A T.B T.C := by
          simpa [hXC] using hXcol
        exact hncol hABC
      · exact (neq3_of_bet hABX).2.2 hXA.symm
      · have hCXAcol : Col T.C X T.A := col_of_bet hCXA
        have hnXA : X ≠ T.A := by
          exact Ne.symm ((neq3_of_bet hABX).2.2)
        rcases hΓ₁.I₁ hnXA with ⟨m, hXm, hAm⟩
        have hBm : T.B ∈ m := by
          exact online_of_col hnXA (col_right_rot.mp hXcol) hXm hAm
        have hCm : T.C ∈ m := by
          exact online_of_col hnXA ((col_left_comm).mp ((col_symm).mp hCXAcol)) hXm hAm
        exact hncol (col_of_online hAm hBm hCm)
  · intro hIn
    exact not_sameSideThrough_of_on_line
      (A := T.A) (B := T.B) (X := X) (Y := T.C) hnAB hAl hBl hXl hIn.2.1

theorem triangle_nonempty_outside [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) :
    ∃ X, X ∈ᵉ[T; α] := by
  have hnAB : T.A ≠ T.B := hnd.1.1
  rcases hΓ₂.II₂ hnAB with ⟨X, hABX⟩
  exact ⟨X, triangleOutside_of_AB_extension (T := T) (α := α) hplane hnd hABX⟩

theorem sameSideThrough_of_open_AC_wrt_AB [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hX : T.A≺X≺T.C) :
    SameSideThrough T.A T.B X T.C := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnAB : T.A ≠ T.B := hneq.1
  rcases hΓ₁.I₁ hnAB with ⟨l, hAl, hBl⟩
  refine ⟨hnAB, l, hAl, hBl, ?_⟩
  have hnCl : T.C ∉ l := not_online_of_online_and_not_col hncol hAl hBl
  constructor
  · intro hXl
    have hnAX : T.A ≠ X := (neq3_of_bet hX).1
    have hAXC : Col T.A X T.C := col_of_bet hX
    have hCl : T.C ∈ l := online_of_col hnAX hAXC hAl hXl
    exact hnCl hCl
  constructor
  · exact hnCl
  · intro hcross
    rcases hcross with ⟨D, hDl, hXDC⟩
    have hnXC : X ≠ T.C := (neq3_of_bet hX).2.1
    rcases hΓ₁.I₁ hnXC with ⟨m, hXm, hCm⟩
    have hAXC : Col T.A X T.C := col_of_bet hX
    have hXDCcol : Col X D T.C := col_of_bet hXDC
    have hAm : T.A ∈ m := online_of_col hnXC (col_left_rot.mp hAXC) hXm hCm
    have hDm : D ∈ m := online_of_col hnXC (col_right_comm.mp hXDCcol) hXm hCm
    have hnAD : T.A ≠ D := by
      intro hAD
      subst D
      have hCXA : T.C ≺ X ≺ T.A := (bet_symm.mp hX)
      exact ((not_bet_of_bet hCXA).1) hXDC
    have hml : m = l := hΓ₁.I₂ hnAD hAm hDm hAl hDl
    have hCl : T.C ∈ l := by simpa [hml] using hCm
    exact hnCl hCl

theorem sameSideThrough_of_open_BC_wrt_AB [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hX : T.B≺X≺T.C) :
    SameSideThrough T.A T.B X T.C := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnAB : T.A ≠ T.B := hneq.1
  rcases hΓ₁.I₁ hnAB with ⟨l, hAl, hBl⟩
  refine ⟨hnAB, l, hAl, hBl, ?_⟩
  have hnCl : T.C ∉ l := not_online_of_online_and_not_col hncol hAl hBl
  constructor
  · intro hXl
    have hnBX : T.B ≠ X := (neq3_of_bet hX).1
    have hBXC : Col T.B X T.C := col_of_bet hX
    have hCl : T.C ∈ l := online_of_col hnBX hBXC hBl hXl
    exact hnCl hCl
  constructor
  · exact hnCl
  · intro hcross
    rcases hcross with ⟨D, hDl, hXDC⟩
    have hnXC : X ≠ T.C := (neq3_of_bet hX).2.1
    rcases hΓ₁.I₁ hnXC with ⟨m, hXm, hCm⟩
    have hBXC : Col T.B X T.C := col_of_bet hX
    have hXDCcol : Col X D T.C := col_of_bet hXDC
    have hBm : T.B ∈ m := online_of_col hnXC (col_left_rot.mp hBXC) hXm hCm
    have hDm : D ∈ m := online_of_col hnXC (col_right_comm.mp hXDCcol) hXm hCm
    have hnBD : T.B ≠ D := by
      intro hBD
      subst D
      have hCXB : T.C ≺ X ≺ T.B := (bet_symm.mp hX)
      exact ((not_bet_of_bet hCXB).1) hXDC
    have hml : m = l := hΓ₁.I₂ hnBD hBm hDm hBl hDl
    have hCl : T.C ∈ l := by simpa [hml] using hCm
    exact hnCl hCl

theorem sameSideThrough_of_open_AB_wrt_BC [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hX : T.A≺X≺T.B) :
    SameSideThrough T.B T.C X T.A := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnBC : T.B ≠ T.C := hneq.2.1
  rcases hΓ₁.I₁ hnBC with ⟨l, hBl, hCl⟩
  refine ⟨hnBC, l, hBl, hCl, ?_⟩
  have hnAl : T.A ∉ l := by
    intro hAl
    exact hncol (col_of_online hAl hBl hCl)
  constructor
  · intro hXl
    have hnXB : X ≠ T.B := (neq3_of_bet hX).2.1
    have hAXB : Col T.A X T.B := col_of_bet hX
    have hAl : T.A ∈ l := online_of_col hnXB (col_left_rot.mp hAXB) hXl hBl
    exact hnAl hAl
  constructor
  · exact hnAl
  · intro hcross
    rcases hcross with ⟨D, hDl, hXDA⟩
    have hnXA : X ≠ T.A := Ne.symm (neq3_of_bet hX).1
    rcases hΓ₁.I₁ hnXA with ⟨m, hXm, hAm⟩
    have hAXB : Col T.A X T.B := col_of_bet hX
    have hXDAcol : Col X D T.A := col_of_bet hXDA
    have hBm : T.B ∈ m := online_of_col hnXA (col_left_comm.mp hAXB) hXm hAm
    have hDm : D ∈ m := online_of_col hnXA (col_right_comm.mp hXDAcol) hXm hAm
    have hnBD : T.B ≠ D := by
      intro hBD
      subst D
      exact ((not_bet_of_bet hXDA).2) hX
    have hml : m = l := hΓ₁.I₂ hnBD hBm hDm hBl hDl
    have hAl : T.A ∈ l := by simpa [hml] using hAm
    exact hnAl hAl

theorem sameSideThrough_of_open_AC_wrt_BC [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hX : T.A≺X≺T.C) :
    SameSideThrough T.B T.C X T.A := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnBC : T.B ≠ T.C := hneq.2.1
  rcases hΓ₁.I₁ hnBC with ⟨l, hBl, hCl⟩
  refine ⟨hnBC, l, hBl, hCl, ?_⟩
  have hnAl : T.A ∉ l := by
    intro hAl
    exact hncol (col_of_online hAl hBl hCl)
  constructor
  · intro hXl
    have hnXC : X ≠ T.C := (neq3_of_bet hX).2.1
    have hAXC : Col T.A X T.C := col_of_bet hX
    have hAl : T.A ∈ l := online_of_col hnXC (col_left_rot.mp hAXC) hXl hCl
    exact hnAl hAl
  constructor
  · exact hnAl
  · intro hcross
    rcases hcross with ⟨D, hDl, hXDA⟩
    have hnXA : X ≠ T.A := Ne.symm (neq3_of_bet hX).1
    rcases hΓ₁.I₁ hnXA with ⟨m, hXm, hAm⟩
    have hAXC : Col T.A X T.C := col_of_bet hX
    have hXDAcol : Col X D T.A := col_of_bet hXDA
    have hCm : T.C ∈ m := online_of_col hnXA (col_left_comm.mp hAXC) hXm hAm
    have hDm : D ∈ m := online_of_col hnXA (col_right_comm.mp hXDAcol) hXm hAm
    have hnCD : T.C ≠ D := by
      intro hCD
      subst D
      exact ((not_bet_of_bet hXDA).2) hX
    have hml : m = l := hΓ₁.I₂ hnCD hCm hDm hCl hDl
    have hAl : T.A ∈ l := by simpa [hml] using hAm
    exact hnAl hAl

theorem sameSideThrough_of_open_AB_wrt_CA [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hX : T.A≺X≺T.B) :
    SameSideThrough T.C T.A X T.B := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnCA : T.C ≠ T.A := Ne.symm hneq.2.2
  rcases hΓ₁.I₁ hnCA with ⟨l, hCl, hAl⟩
  refine ⟨hnCA, l, hCl, hAl, ?_⟩
  have hnBl : T.B ∉ l := by
    intro hBl
    exact hncol (col_of_online hAl hBl hCl)
  constructor
  · intro hXl
    have hnAX : T.A ≠ X := (neq3_of_bet hX).1
    have hAXB : Col T.A X T.B := col_of_bet hX
    have hBl : T.B ∈ l := online_of_col hnAX hAXB hAl hXl
    exact hnBl hBl
  constructor
  · exact hnBl
  · intro hcross
    rcases hcross with ⟨D, hDl, hXDB⟩
    have hnXB : X ≠ T.B := (neq3_of_bet hX).2.1
    rcases hΓ₁.I₁ hnXB with ⟨m, hXm, hBm⟩
    have hAXB : Col T.A X T.B := col_of_bet hX
    have hXDBcol : Col X D T.B := col_of_bet hXDB
    have hAm : T.A ∈ m := online_of_col hnXB (col_left_rot.mp hAXB) hXm hBm
    have hDm : D ∈ m := online_of_col hnXB (col_right_comm.mp hXDBcol) hXm hBm
    have hnAD : T.A ≠ D := by
      intro hAD
      subst D
      have hBXA : T.B ≺ X ≺ T.A := (bet_symm.mp hX)
      exact ((not_bet_of_bet hBXA).1) hXDB
    have hml : m = l := hΓ₁.I₂ hnAD hAm hDm hAl hDl
    have hBl : T.B ∈ l := by simpa [hml] using hBm
    exact hnBl hBl

theorem sameSideThrough_of_open_BC_wrt_CA [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hX : T.B≺X≺T.C) :
    SameSideThrough T.C T.A X T.B := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnCA : T.C ≠ T.A := Ne.symm hneq.2.2
  rcases hΓ₁.I₁ hnCA with ⟨l, hCl, hAl⟩
  refine ⟨hnCA, l, hCl, hAl, ?_⟩
  have hnBl : T.B ∉ l := by
    intro hBl
    exact hncol (col_of_online hAl hBl hCl)
  constructor
  · intro hXl
    have hnXC : X ≠ T.C := (neq3_of_bet hX).2.1
    have hBXC : Col T.B X T.C := col_of_bet hX
    have hBl : T.B ∈ l := online_of_col hnXC (col_left_rot.mp hBXC) hXl hCl
    exact hnBl hBl
  constructor
  · exact hnBl
  · intro hcross
    rcases hcross with ⟨D, hDl, hXDB⟩
    have hnXB : X ≠ T.B := Ne.symm (neq3_of_bet hX).1
    rcases hΓ₁.I₁ hnXB with ⟨m, hXm, hBm⟩
    have hBXC : Col T.B X T.C := col_of_bet hX
    have hXDBcol : Col X D T.B := col_of_bet hXDB
    have hCm : T.C ∈ m := online_of_col hnXB (col_left_comm.mp hBXC) hXm hBm
    have hDm : D ∈ m := online_of_col hnXB (col_right_comm.mp hXDBcol) hXm hBm
    have hnCD : T.C ≠ D := by
      intro hCD
      subst D
      exact ((not_bet_of_bet hXDB).2) hX
    have hml : m = l := hΓ₁.I₂ hnCD hCm hDm hCl hDl
    have hBl : T.B ∈ l := by simpa [hml] using hBm
    exact hnBl hBl

theorem sameSideThrough_of_open_AC_open_BC_wrt_AB [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hD : T.A≺D≺T.C) (hE : T.B≺E≺T.C) :
    SameSideThrough T.A T.B D E := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnAB : T.A ≠ T.B := hneq.1
  rcases hΓ₁.I₁ hnAB with ⟨l, hAl, hBl⟩
  have hlα : l ⊂ α := hΓ₁.I₆ hnAB hAl hBl hAα hBα
  have hDC0 := sameSideThrough_of_open_AC_wrt_AB (T := T) (α := α)
    (hplane := ⟨hAα, hBα, hCα⟩) (hnd := ⟨hneq, hncol⟩) hD
  have hEC0 := sameSideThrough_of_open_BC_wrt_AB (T := T) (α := α)
    (hplane := ⟨hAα, hBα, hCα⟩) (hnd := ⟨hneq, hncol⟩) hE
  rcases hDC0 with ⟨_, lD, hAlD, hBlD, hDC⟩
  rcases hEC0 with ⟨_, lE, hAlE, hBlE, hEC⟩
  have hlD : lD = l := hΓ₁.I₂ hnAB hAlD hBlD hAl hBl
  have hlE : lE = l := hΓ₁.I₂ hnAB hAlE hBlE hAl hBl
  have hnDl : D ∉ l := by simpa [hlD] using hDC.1
  have hnEl : E ∉ l := by simpa [hlE] using hEC.1
  have hnCl : T.C ∉ l := not_online_of_online_and_not_col hncol hAl hBl
  have hnoDC : ¬ ∃ C, C ∈ l ∧ D ≺ C ≺ T.C := by
    intro h
    apply hDC.2.2
    simpa [hlD] using h
  have hnoEC : ¬ ∃ C, C ∈ l ∧ E ≺ C ≺ T.C := by
    intro h
    apply hEC.2.2
    simpa [hlE] using h
  refine ⟨hnAB, l, hAl, hBl, ?_⟩
  constructor
  · exact hnDl
  constructor
  · exact hnEl
  · intro hcross
    rcases hcross with ⟨P, hPl, hDPE⟩
    have hnAC : T.A ≠ T.C := hneq.2.2
    rcases hΓ₁.I₁ hnAC with ⟨mAC, hAmAC, hCmAC⟩
    have hADC : Col T.A D T.C := col_of_bet hD
    have hDmAC : D ∈ mAC := online_of_col hnAC (col_right_comm.mp hADC) hAmAC hCmAC
    have hmACα : mAC ⊂ α := hΓ₁.I₆ hnAC hAmAC hCmAC hAα hCα
    have hDα : D ∈ α := hmACα D hDmAC
    have hnBC : T.B ≠ T.C := hneq.2.1
    rcases hΓ₁.I₁ hnBC with ⟨mBC, hBmBC, hCmBC⟩
    have hBEC : Col T.B E T.C := col_of_bet hE
    have hEmBC : E ∈ mBC := online_of_col hnBC (col_right_comm.mp hBEC) hBmBC hCmBC
    have hmBCα : mBC ⊂ α := hΓ₁.I₆ hnBC hBmBC hCmBC hBα hCα
    have hEα : E ∈ α := hmBCα E hEmBC
    have hncDEC : ¬ Col D E T.C := by
      intro hDEC
      have hnDC : D ≠ T.C := (neq3_of_bet hD).2.1
      rcases hΓ₁.I₁ hnDC with ⟨m, hDm, hCm⟩
      have hAm : T.A ∈ m := online_of_col hnDC (col_left_rot.mp hADC) hDm hCm
      have hEm : E ∈ m := online_of_col hnDC (col_right_comm.mp hDEC) hDm hCm
      have hnEC : E ≠ T.C := (neq3_of_bet hE).2.1
      have hBm : T.B ∈ m := online_of_col hnEC (col_left_rot.mp hBEC) hEm hCm
      exact hncol (col_of_online hAm hBm hCm)
    have hnDE : D ≠ E := by
      intro hDE
      subst E
      exact hncDEC (col_of_eq rfl)
    have hnEC : E ≠ T.C := (neq3_of_bet hE).2.1
    have hnDC : D ≠ T.C := (neq3_of_bet hD).2.1
    have hpasch := hΓ₂.II₄ ⟨hnDE, hnEC, hnDC⟩ hncDEC hlα hDα hEα hCα hnDl hnEl hnCl
      ⟨P, hPl, hDPE⟩
    rcases hpasch with hleft | hright
    · exact hnoDC hleft
    · exact hnoEC hright

theorem sameSideThrough_of_open_AB_open_AC_wrt_BC [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hD : T.A≺D≺T.B) (hE : T.A≺E≺T.C) :
    SameSideThrough T.B T.C D E := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnBC : T.B ≠ T.C := hneq.2.1
  rcases hΓ₁.I₁ hnBC with ⟨l, hBl, hCl⟩
  have hlα : l ⊂ α := hΓ₁.I₆ hnBC hBl hCl hBα hCα
  have hDA0 := sameSideThrough_of_open_AB_wrt_BC (T := T) (α := α)
    (hplane := ⟨hAα, hBα, hCα⟩) (hnd := ⟨hneq, hncol⟩) hD
  have hEA0 := sameSideThrough_of_open_AC_wrt_BC (T := T) (α := α)
    (hplane := ⟨hAα, hBα, hCα⟩) (hnd := ⟨hneq, hncol⟩) hE
  rcases hDA0 with ⟨_, lD, hBlD, hClD, hDA⟩
  rcases hEA0 with ⟨_, lE, hBlE, hClE, hEA⟩
  have hlD : lD = l := hΓ₁.I₂ hnBC hBlD hClD hBl hCl
  have hlE : lE = l := hΓ₁.I₂ hnBC hBlE hClE hBl hCl
  have hnDl : D ∉ l := by simpa [hlD] using hDA.1
  have hnEl : E ∉ l := by simpa [hlE] using hEA.1
  have hncBCA : ¬ Col T.B T.C T.A := by
    intro hBCA
    exact hncol ((col_left_rot).mpr hBCA)
  have hnAl : T.A ∉ l := not_online_of_online_and_not_col hncBCA hBl hCl
  have hnoDA : ¬ ∃ A, A ∈ l ∧ D ≺ A ≺ T.A := by
    intro h
    apply hDA.2.2
    simpa [hlD] using h
  have hnoEA : ¬ ∃ A, A ∈ l ∧ E ≺ A ≺ T.A := by
    intro h
    apply hEA.2.2
    simpa [hlE] using h
  refine ⟨hnBC, l, hBl, hCl, ?_⟩
  constructor
  · exact hnDl
  constructor
  · exact hnEl
  · intro hcross
    rcases hcross with ⟨P, hPl, hDPE⟩
    have hnAB : T.A ≠ T.B := hneq.1
    rcases hΓ₁.I₁ hnAB with ⟨mAB, hAmAB, hBmAB⟩
    have hADB : Col T.A D T.B := col_of_bet hD
    have hDmAB : D ∈ mAB := online_of_col hnAB (col_right_comm.mp hADB) hAmAB hBmAB
    have hmABα : mAB ⊂ α := hΓ₁.I₆ hnAB hAmAB hBmAB hAα hBα
    have hDα : D ∈ α := hmABα D hDmAB
    have hnAC : T.A ≠ T.C := hneq.2.2
    rcases hΓ₁.I₁ hnAC with ⟨mAC, hAmAC, hCmAC⟩
    have hAEC : Col T.A E T.C := col_of_bet hE
    have hEmAC : E ∈ mAC := online_of_col hnAC (col_right_comm.mp hAEC) hAmAC hCmAC
    have hmACα : mAC ⊂ α := hΓ₁.I₆ hnAC hAmAC hCmAC hAα hCα
    have hEα : E ∈ α := hmACα E hEmAC
    have hncDEA : ¬ Col D E T.A := by
      intro hDEA
      have hnDA : D ≠ T.A := Ne.symm (neq3_of_bet hD).1
      rcases hΓ₁.I₁ hnDA with ⟨m, hDm, hAm⟩
      have hBm : T.B ∈ m := online_of_col hnDA (col_left_comm.mp hADB) hDm hAm
      have hEm : E ∈ m := online_of_col hnDA (col_right_comm.mp hDEA) hDm hAm
      have hnEA : E ≠ T.A := Ne.symm (neq3_of_bet hE).1
      have hCm : T.C ∈ m := online_of_col hnEA (col_left_comm.mp hAEC) hEm hAm
      exact hncol (col_of_online hAm hBm hCm)
    have hnDE : D ≠ E := by
      intro hDE
      subst E
      exact hncDEA (col_of_eq rfl)
    have hnEA : E ≠ T.A := Ne.symm (neq3_of_bet hE).1
    have hnDA : D ≠ T.A := Ne.symm (neq3_of_bet hD).1
    have hpasch := hΓ₂.II₄ ⟨hnDE, hnEA, hnDA⟩ hncDEA hlα hDα hEα hAα hnDl hnEl hnAl
      ⟨P, hPl, hDPE⟩
    rcases hpasch with hleft | hright
    · exact hnoDA hleft
    · exact hnoEA hright

theorem sameSideThrough_of_open_AC_open_AB_wrt_BC [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hD : T.A≺D≺T.C) (hE : T.A≺E≺T.B) :
    SameSideThrough T.B T.C D E := by
  exact sameSideThrough_symm <|
    sameSideThrough_of_open_AB_open_AC_wrt_BC (T := T) (α := α) hplane hnd hE hD

theorem sameSideThrough_of_open_AB_open_BC_wrt_CA [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hD : T.A≺D≺T.B) (hE : T.B≺E≺T.C) :
    SameSideThrough T.C T.A D E := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  have hnCA : T.C ≠ T.A := Ne.symm hneq.2.2
  rcases hΓ₁.I₁ hnCA with ⟨l, hCl, hAl⟩
  have hlα : l ⊂ α := hΓ₁.I₆ hnCA hCl hAl hCα hAα
  have hDB0 := sameSideThrough_of_open_AB_wrt_CA (T := T) (α := α)
    (hplane := ⟨hAα, hBα, hCα⟩) (hnd := ⟨hneq, hncol⟩) hD
  have hEB0 := sameSideThrough_of_open_BC_wrt_CA (T := T) (α := α)
    (hplane := ⟨hAα, hBα, hCα⟩) (hnd := ⟨hneq, hncol⟩) hE
  rcases hDB0 with ⟨_, lD, hClD, hAlD, hDB⟩
  rcases hEB0 with ⟨_, lE, hClE, hAlE, hEB⟩
  have hlD : lD = l := hΓ₁.I₂ hnCA hClD hAlD hCl hAl
  have hlE : lE = l := hΓ₁.I₂ hnCA hClE hAlE hCl hAl
  have hnDl : D ∉ l := by simpa [hlD] using hDB.1
  have hnEl : E ∉ l := by simpa [hlE] using hEB.1
  have hncCAB : ¬ Col T.C T.A T.B := by
    intro hCAB
    exact hncol ((col_right_rot).mpr hCAB)
  have hnBl : T.B ∉ l := not_online_of_online_and_not_col hncCAB hCl hAl
  have hnoDB : ¬ ∃ B, B ∈ l ∧ D ≺ B ≺ T.B := by
    intro h
    apply hDB.2.2
    simpa [hlD] using h
  have hnoEB : ¬ ∃ B, B ∈ l ∧ E ≺ B ≺ T.B := by
    intro h
    apply hEB.2.2
    simpa [hlE] using h
  refine ⟨hnCA, l, hCl, hAl, ?_⟩
  constructor
  · exact hnDl
  constructor
  · exact hnEl
  · intro hcross
    rcases hcross with ⟨P, hPl, hDPE⟩
    have hnAB : T.A ≠ T.B := hneq.1
    rcases hΓ₁.I₁ hnAB with ⟨mAB, hAmAB, hBmAB⟩
    have hADB : Col T.A D T.B := col_of_bet hD
    have hDmAB : D ∈ mAB := online_of_col hnAB (col_right_comm.mp hADB) hAmAB hBmAB
    have hmABα : mAB ⊂ α := hΓ₁.I₆ hnAB hAmAB hBmAB hAα hBα
    have hDα : D ∈ α := hmABα D hDmAB
    have hnBC : T.B ≠ T.C := hneq.2.1
    rcases hΓ₁.I₁ hnBC with ⟨mBC, hBmBC, hCmBC⟩
    have hBEC : Col T.B E T.C := col_of_bet hE
    have hEmBC : E ∈ mBC := online_of_col hnBC (col_right_comm.mp hBEC) hBmBC hCmBC
    have hmBCα : mBC ⊂ α := hΓ₁.I₆ hnBC hBmBC hCmBC hBα hCα
    have hEα : E ∈ α := hmBCα E hEmBC
    have hncDEB : ¬ Col D E T.B := by
      intro hDEB
      have hnDB : D ≠ T.B := (neq3_of_bet hD).2.1
      rcases hΓ₁.I₁ hnDB with ⟨m, hDm, hBm⟩
      have hAm : T.A ∈ m := online_of_col hnDB (col_left_rot.mp hADB) hDm hBm
      have hEm : E ∈ m := online_of_col hnDB (col_right_comm.mp hDEB) hDm hBm
      have hnEB : E ≠ T.B := Ne.symm (neq3_of_bet hE).1
      have hCm : T.C ∈ m := online_of_col hnEB (col_left_comm.mp hBEC) hEm hBm
      exact hncol (col_of_online hAm hBm hCm)
    have hnDE : D ≠ E := by
      intro hDE
      subst E
      exact hncDEB (col_of_eq rfl)
    have hnEB : E ≠ T.B := Ne.symm (neq3_of_bet hE).1
    have hnDB : D ≠ T.B := (neq3_of_bet hD).2.1
    have hpasch := hΓ₂.II₄ ⟨hnDE, hnEB, hnDB⟩ hncDEB hlα hDα hEα hBα hnDl hnEl hnBl
      ⟨P, hPl, hDPE⟩
    rcases hpasch with hleft | hright
    · exact hnoDB hleft
    · exact hnoEB hright

theorem sameSideThrough_of_open_BC_open_AB_wrt_CA [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hD : T.B≺D≺T.C) (hE : T.A≺E≺T.B) :
    SameSideThrough T.C T.A D E := by
  exact sameSideThrough_symm <|
    sameSideThrough_of_open_AB_open_BC_wrt_CA (T := T) (α := α) hplane hnd hE hD

theorem sameSideThrough_of_open_BC_open_AC_wrt_AB [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate) (hD : T.B≺D≺T.C) (hE : T.A≺E≺T.C) :
    SameSideThrough T.A T.B D E := by
  exact sameSideThrough_symm <|
    sameSideThrough_of_open_AC_open_BC_wrt_AB (T := T) (α := α) hplane hnd hE hD

theorem triangle_inner_chord_exists [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (hnd : T.Nondegenerate) :
    ∃ D E X : Γ.Point, T.A≺D≺T.B ∧ T.A≺E≺T.C ∧ D≺X≺E := by
  have hnAB : T.A ≠ T.B := hnd.1.1
  have hnAC : T.A ≠ T.C := hnd.1.2.2
  rcases T₃ T.A T.B hnAB with ⟨D, hD⟩
  rcases T₃ T.A T.C hnAC with ⟨E, hE⟩
  have hnDE : D ≠ E := by
    intro hDE
    subst E
    have hnAD : T.A ≠ D := (neq3_of_bet hD).1
    have hADB : Col T.A D T.B := col_of_bet hD
    have hADC : Col T.A D T.C := col_of_bet hE
    have hABC : Col T.A T.B T.C := col_4 hnAD hADB hADC
    exact hnd.2 hABC
  rcases T₃ D E hnDE with ⟨X, hX⟩
  exact ⟨D, E, X, hD, hE, hX⟩

theorem mem_plane_of_open_AB_open_AC_between [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E X : Γ.Point}
    (hplane : T.InPlane α) (hD : T.A≺D≺T.B) (hE : T.A≺E≺T.C) (hX : D≺X≺E) :
    X ∈ α := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  have hnAB : T.A ≠ T.B := (neq3_of_bet hD).2.2
  rcases hΓ₁.I₁ hnAB with ⟨lAB, hAlAB, hBlAB⟩
  have hADB : Col T.A D T.B := col_of_bet hD
  have hDlAB : D ∈ lAB := online_of_col hnAB (col_right_comm.mp hADB) hAlAB hBlAB
  have hlABα : lAB ⊂ α := hΓ₁.I₆ hnAB hAlAB hBlAB hAα hBα
  have hDα : D ∈ α := hlABα D hDlAB
  have hnAC : T.A ≠ T.C := (neq3_of_bet hE).2.2
  rcases hΓ₁.I₁ hnAC with ⟨lAC, hAlAC, hClAC⟩
  have hAEC : Col T.A E T.C := col_of_bet hE
  have hElAC : E ∈ lAC := online_of_col hnAC (col_right_comm.mp hAEC) hAlAC hClAC
  have hlACα : lAC ⊂ α := hΓ₁.I₆ hnAC hAlAC hClAC hAα hCα
  have hEα : E ∈ α := hlACα E hElAC
  have hnDE : D ≠ E := (neq3_of_bet hX).2.2
  rcases hΓ₁.I₁ hnDE with ⟨lDE, hDlDE, hElDE⟩
  have hDXE : Col D X E := col_of_bet hX
  have hXlDE : X ∈ lDE := online_of_col hnDE (col_right_comm.mp hDXE) hDlDE hElDE
  have hlDEα : lDE ⊂ α := hΓ₁.I₆ hnDE hDlDE hElDE hDα hEα
  exact hlDEα X hXlDE

theorem not_boundary_of_open_AB_open_AC_between [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate)
    (hD : T.A≺D≺T.B) (hE : T.A≺E≺T.C) (hX : D≺X≺E) :
    ¬ X ∈∂△ T := by
  rcases hplane with ⟨hAα, hBα, hCα⟩
  rcases hnd with ⟨hneq, hncol⟩
  intro hBd
  rcases hBd with hAB | hBC | hCA
  · have hnAB : T.A ≠ T.B := hneq.1
    rcases hΓ₁.I₁ hnAB with ⟨lAB, hAlAB, hBlAB⟩
    have hADB : Col T.A D T.B := col_of_bet hD
    have hDlAB : D ∈ lAB := online_of_col hnAB (col_right_comm.mp hADB) hAlAB hBlAB
    have hXlAB : X ∈ lAB := onClosedSegment_on_line hnAB hAlAB hBlAB hAB
    have hnDX : D ≠ X := (neq3_of_bet hX).1
    rcases hΓ₁.I₁ hnDX with ⟨m, hDm, hXm⟩
    have hDXE : Col D X E := col_of_bet hX
    have hEm : E ∈ m := online_of_col hnDX hDXE hDm hXm
    have hmAB : m = lAB := hΓ₁.I₂ hnDX hDm hXm hDlAB hXlAB
    have hElAB : E ∈ lAB := by simpa [hmAB] using hEm
    have hnAE : T.A ≠ E := (neq3_of_bet hE).1
    have hAEC : Col T.A E T.C := col_of_bet hE
    have hClAB : T.C ∈ lAB := online_of_col hnAE hAEC hAlAB hElAB
    exact hncol (col_of_online hAlAB hBlAB hClAB)
  · have hsame :=
      sameSideThrough_of_open_AB_open_AC_wrt_BC
        (T := T) (α := α) ⟨hAα, hBα, hCα⟩ ⟨hneq, hncol⟩ hD hE
    rcases hsame with ⟨hnBC, l, hBl, hCl, hDE⟩
    have hXl : X ∈ l := onClosedSegment_on_line hnBC hBl hCl hBC
    exact hDE.2.2 ⟨X, hXl, hX⟩
  · have hnCA : T.C ≠ T.A := Ne.symm hneq.2.2
    rcases hΓ₁.I₁ hnCA with ⟨lCA, hClCA, hAlCA⟩
    have hAEC : Col T.A E T.C := col_of_bet hE
    have hElCA : E ∈ lCA := online_of_col hnCA (col_right_rot.mp hAEC) hClCA hAlCA
    have hXlCA : X ∈ lCA := onClosedSegment_on_line hnCA hClCA hAlCA hCA
    have hnEX : E ≠ X := Ne.symm (neq3_of_bet hX).2.1
    rcases hΓ₁.I₁ hnEX with ⟨m, hEm, hXm⟩
    have hDXE : Col D X E := col_of_bet hX
    have hDm : D ∈ m := online_of_col hnEX (col_symm.mp hDXE) hEm hXm
    have hmCA : m = lCA := hΓ₁.I₂ hnEX hEm hXm hElCA hXlCA
    have hDlCA : D ∈ lCA := by simpa [hmCA] using hDm
    have hnAD : T.A ≠ D := (neq3_of_bet hD).1
    have hADB : Col T.A D T.B := col_of_bet hD
    have hBlCA : T.B ∈ lCA := online_of_col hnAD hADB hAlCA hDlCA
    exact hncol (col_of_online hAlCA hBlCA hClCA)

theorem triangle_nonboundary_point_exists [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) (hplane : T.InPlane α) (hnd : T.Nondegenerate) :
    ∃ X, X ∈ α ∧ ¬ X ∈∂△ T := by
  rcases triangle_inner_chord_exists (T := T) hnd with ⟨D, E, X, hD, hE, hX⟩
  refine ⟨X, ?_, ?_⟩
  · exact mem_plane_of_open_AB_open_AC_between (T := T) (α := α) hplane hD hE hX
  · exact not_boundary_of_open_AB_open_AC_between (T := T) (α := α) hplane hnd hD hE hX

theorem triangle_partition_of_open_AB_open_AC_between [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ]
    (T : Γ.Triangle) (α : Γ.Plane) {D E X : Γ.Point}
    (hplane : T.InPlane α) (hnd : T.Nondegenerate)
    (hD : T.A≺D≺T.B) (hE : T.A≺E≺T.C) (hX : D≺X≺E) :
    X ∈ᵢ[T; α] ∨ X ∈ᵉ[T; α] := by
  apply triangle_inside_outside_partition (T := T) (α := α)
  constructor
  · exact mem_plane_of_open_AB_open_AC_between (T := T) (α := α) hplane hD hE hX
  · exact not_boundary_of_open_AB_open_AC_between (T := T) (α := α) hplane hnd hD hE hX


class AxiomOfParallelLine (Γ : Geometry) where
  IV : ∀ {A} {l : Γ.Line} {α : Γ.Plane},
    l ⊂ α → A ∈ α → A ∉ l →
      ∃! m : Γ.Line, m ⊂ α ∧ A ∈ m ∧ l ∥ m


end Geometry

end Hilbert
