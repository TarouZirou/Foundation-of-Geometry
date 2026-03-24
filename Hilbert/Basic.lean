import Mathlib.Logic.Unique
import Mathlib.Tactic.Use
import Mathlib.Tactic.ApplyAt

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

theorem exist_line_of_forall_point [hΓ : IncidentAxioms Γ] (A : Γ.Point) : ∃ l : Γ.Line, A ∈ l := by
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
  · rcases exist_line_of_forall_point A with ⟨l, hAl⟩
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

theorem T₁_₁_₁ [hΓ : IncidentAxioms Γ] {l m : Γ.Line} {α : Γ.Plane} :
  l ≠ m → l ⊂ α → m ⊂ α → l ∦ m → (∃!A, A ∈ l ∧ A ∈ m) := by
  intro hnlm hlα hmα hn_para_lm
  have h₁ := T₁_₁ hnlm hlα hmα
  rcases h₁ with h₁ | h₁
  · exact h₁
  · contradiction

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

lemma L₂ [hΓ : IncidentAxioms Γ] {l m : Γ.Line} :
  l ≠ m → ∃ B, B ∈ l ∧ B ∉ m := by
  intro hnlm
  by_contra h₁
  simp only [not_exists, not_and, not_not] at h₁
  rcases hΓ.I₃.1 l with ⟨A, B, hnAB, hAl, hBl⟩
  have hAm := h₁ A hAl
  have hBm := h₁ B hBl
  have h₂ := hΓ.I₂ hnAB hAl hBl hAm hBm
  contradiction

lemma L₃ [hΓ : IncidentAxioms Γ] {A B C : Γ.Point} {l : Γ.Line} :
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

def SameSide (A B : Γ.Point) (l : Γ.Line) : Prop := ¬∃ C, C ∈ l ∧ A ≺ C ≺ B
def OppoSide (A B : Γ.Point) (l : Γ.Line) : Prop := ∃ C, C ∈ l ∧ A ≺ C ≺ B

class OrderAxioms (Γ : Geometry) where
  II₁ : ∀ {A B C : Γ.Point}, A ≺ B ≺ C → Col A B C ∧ ≠₃ A B C ∧ C ≺ B ≺ A
  II₂ : ∀ A B : Γ.Point, ∃ C : Γ.Point, A ≺ B ≺ C
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


theorem L₄ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
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

theorem C₁ [hΓ₁ : IncidentAxioms Γ] [hΓ₂ : OrderAxioms Γ] :
  ≠₃ A B C → ¬Col A B C →
    l ⊂ α → A ∈ α → B ∈ α → C ∈ α → A ∉ l → B ∉ l → C ∉ l →
      (∃ D, D ∈ l ∧ A ≺ D ≺ B) → (∃ E, E ∈ l ∧ A ≺ E ≺ C) → ¬(∃ F, F ∈ l ∧ B ≺ F ≺ C) := by
  intro hnABC hnColABC hlα hAα hBα hCα hnAl hnBl hnCl hAB hAC
  sorry

--theorem bet_4 : A ≺ B ≺ C → B ≺ C ≺ D → A ≺ C ≺ D ∧ A ≺ B ≺ D := by
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
  rcases hΓ₂.II₂ A E with ⟨F, hbAEF⟩
  rcases hΓ₂.II₂ F C with ⟨G, hbFCG⟩
  have hcAEF := col_of_bet hbAEF
  have hcFCG := col_of_bet hbFCG
  have hnFl : F ∉ l := by
    intro hFl
    have hnAF := (neq3_of_bet hbAEF).2.2
    rcases hcAEF with ⟨m, hAm, hEm, hFm⟩
    have hlm := hΓ₁.I₂ hnAF hAl hFl hAm hFm
    rw [hlm] at hnEl
    exact hnEl hEm
  have hnGl : G ∉ l := by
    intro hGl
    rcases hcFCG with ⟨m, hFm, hCm, hGm⟩
    have hnCG := (neq3_of_bet hbFCG).2.1
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
    have hnAF := (neq3_of_bet hbAEF).2.2
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
    have hnEF := (neq3_of_bet hbAEF).2.1
    rcases hcAEF with ⟨n, hAn, hEn, hFn⟩
    have hmn := hΓ₁.I₂ hnEF hEm hFm hEn hFn
    rw [hmn] at hnAm
    contradiction
  have hnCm : C ∉ m := by
    intro hCm
    rcases hcFCG with ⟨n, hFn, hCn, hGn⟩
    have hnCG := (neq3_of_bet hbFCG).2.1
    have hmn := hΓ₁.I₂ hnCG hCm hGm hCn hGn
    rw [hmn] at hnFm
    contradiction
  have hnAFC : ≠₃ A F C := by
    have hnAF := (neq3_of_bet hbAEF).2.2
    have hnFC := (neq3_of_bet hbFCG).1
    exact ⟨hnAF, hnFC, hnAC⟩
  have hncAFC := not_col_of_online_and_not_online hnAC hAl hCl hnFl
  rw [col_right_comm] at hncAFC
  have hmα : m ⊂ α := by
    have hEα : E ∈ α := by
      rcases hcAEF with ⟨n, hAn, hEn ,hFn⟩
      have hnAF := (neq3_of_bet hbAEF).2.2
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

class AxiomOfParallelLine (Γ : Geometry) where
  IV : ∀ {A} {l : Γ.Line} {α : Γ.Plane},
    l ⊂ α → A ∈ α → A ∉ l →
      ∃! m : Γ.Line, m ⊂ α ∧ A ∈ m ∧ l ∥ m


end Geometry

end Hilbert
