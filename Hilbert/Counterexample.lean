import Hilbert.Basic

namespace Hilbert
namespace Geometry

variable {Γ : Geometry}
variable [hΓ₁ : IncidentAxioms Γ]

/- 
このファイルの目的は、次を示すことです。

`III₁` を
"任意の直線 `l'` 上には、与えられた線分と合同な点を 1 つ取れる"
という弱い形に落としてしまうと、

`exists_segCong_points_onray`
("任意の ray 上に合同な点を取れる")

はもう導けません。

そのために、ここでは `IncidentAxioms` と `OrderAxioms` だけを仮定して、
"直線ごとに既定の向きの ray を 1 本だけ選び、その ray 上の点だけを合同とみなす"
という人工的な関係 `LineOnlySegCong` を作ります。
-/

/-- 任意の直線には、相異なる 2 点がある。 -/
theorem exists_distinct_points_on_line (l : Γ.Line) :
    ∃ p : Γ.Point × Γ.Point, p.1 ≠ p.2 ∧ p.1 ∈ l ∧ p.2 ∈ l := by
  rcases hΓ₁.I₃.1 l with ⟨U, V, hUV, hUl, hVl⟩
  exact ⟨(U, V), hUV, hUl, hVl⟩

/--
各直線ごとに、まず 1 点目の代表点を 1 つ固定して選ぶ。
`Classical.choose` を使っているので noncomputable です。
-/
noncomputable def lineWitness₁ (l : Γ.Line) : Γ.Point :=
  (Classical.choose (exists_distinct_points_on_line (Γ := Γ) l)).1

/-- 各直線ごとに、2 点目の代表点を 1 つ固定して選ぶ。 -/
noncomputable def lineWitness₂ (l : Γ.Line) : Γ.Point :=
  (Classical.choose (exists_distinct_points_on_line (Γ := Γ) l)).2

theorem lineWitness₁_ne₂ (l : Γ.Line) :
    lineWitness₁ (Γ := Γ) l ≠ lineWitness₂ (Γ := Γ) l := by
  simpa [lineWitness₁, lineWitness₂] using
    (Classical.choose_spec (exists_distinct_points_on_line (Γ := Γ) l)).1

theorem lineWitness₁_mem (l : Γ.Line) :
    lineWitness₁ (Γ := Γ) l ∈ l := by
  simpa [lineWitness₁, lineWitness₂] using
    (Classical.choose_spec (exists_distinct_points_on_line (Γ := Γ) l)).2.1

theorem lineWitness₂_mem (l : Γ.Line) :
    lineWitness₂ (Γ := Γ) l ∈ l := by
  simpa [lineWitness₁, lineWitness₂] using
    (Classical.choose_spec (exists_distinct_points_on_line (Γ := Γ) l)).2.2

/--
直線 `l` と点 `A` に対して、
`l` 上の既定の 2 点のうち `A` と違う方を 1 つ返す。

要するに、`l` 上で「A と違う代表点」を機械的に選ぶ関数です。
-/
noncomputable def otherPointOnLine (A : Γ.Point) (l : Γ.Line) : Γ.Point :=
  by
    classical
    exact if h : A = lineWitness₁ (Γ := Γ) l then
      lineWitness₂ (Γ := Γ) l
    else
      lineWitness₁ (Γ := Γ) l

theorem otherPointOnLine_mem (A : Γ.Point) (l : Γ.Line) :
    otherPointOnLine (Γ := Γ) A l ∈ l := by
  classical
  by_cases h : A = lineWitness₁ (Γ := Γ) l
  · simpa [otherPointOnLine, h] using lineWitness₂_mem (Γ := Γ) l
  · simpa [otherPointOnLine, h] using lineWitness₁_mem (Γ := Γ) l

theorem otherPointOnLine_ne (A : Γ.Point) (l : Γ.Line) :
    A ≠ otherPointOnLine (Γ := Γ) A l := by
  classical
  by_cases h : A = lineWitness₁ (Γ := Γ) l
  · simpa [otherPointOnLine, h] using lineWitness₁_ne₂ (Γ := Γ) l
  · simp [otherPointOnLine, h]

/-- ray の defining point は必ずその ray 上にある。 -/
theorem point_mem_ray (h : Γ.Ray) : h.point ∈ h := by
  rw [onRay, h.carrier_eq, RaySet]
  refine ⟨?_, h.source_ne_point⟩
  refine ⟨?_, Or.inr <| Or.inr <| Or.inr rfl⟩
  exact col_symm.mp (col_of_eq (Γ := Γ) (A := h.point) (B := h.point) (C := h.source) rfl)

/--
直線 `l` 上に点 `A` があるとき、
`A` から `otherPointOnLine A l` の方向へ伸びる「既定の ray」を作る。
-/
noncomputable def canonicalRayOnLine (A : Γ.Point) (l : Γ.Line) : Γ.Ray where
  source := A
  point := otherPointOnLine (Γ := Γ) A l
  source_ne_point := otherPointOnLine_ne (Γ := Γ) A l

/-- `A ∈ l` なら、その既定 ray は確かに `l` 上に載っている。 -/
theorem canonicalRayOnLine_subset_line (A : Γ.Point) (l : Γ.Line) (hA : A ∈ l) :
    canonicalRayOnLine (Γ := Γ) A l ⊂ l := by
  intro X hX
  rw [onRay, (canonicalRayOnLine (Γ := Γ) A l).carrier_eq, RaySet] at hX
  exact online_of_col (otherPointOnLine_ne (Γ := Γ) A l) hX.1.1 hA
    (otherPointOnLine_mem (Γ := Γ) A l)

/--
反例用の「偽の合同関係」。

意味は:
"右辺の点 `B'` が、ある直線 `l'` 上で `A'` から見た既定 ray の上にあり、
しかも `A'` 自身ではないなら、`[A,B]` と `[A',B']` は合同とみなす"。

ここで左辺 `[A,B]` は実はまったく見ていません。
つまり、かなり人工的な関係です。
-/
def LineOnlySegCong (_A _B A' B' : Γ.Point) : Prop :=
  ∃ l' : Γ.Line, A' ∈ l' ∧ B' ∈ canonicalRayOnLine (Γ := Γ) A' l' ∧ B' ≠ A'

/--
この偽合同関係は、"直線上にはコピーを置ける" という弱い existence は満たす。

なぜなら、`A' ∈ l'` なら `l'` 上の既定 ray の defining point をそのまま取ればよいからです。
-/
theorem lineOnly_exists_on_line :
    ∀ {A B A'} {l l' : Γ.Line},
      A ∈ l → B ∈ l → A' ∈ l' →
        ∃ B', B' ∈ l' ∧ LineOnlySegCong (Γ := Γ) A B A' B' := by
  intro A B A' l l' hAl hBl hA'l'
  let B' := otherPointOnLine (Γ := Γ) A' l'
  have hB'l' : B' ∈ l' := otherPointOnLine_mem (Γ := Γ) A' l'
  have hB'ray : B' ∈ canonicalRayOnLine (Γ := Γ) A' l' := by
    simpa [B', canonicalRayOnLine] using
      point_mem_ray (canonicalRayOnLine (Γ := Γ) A' l')
  have hA'neB' : B' ≠ A' := by
    exact Ne.symm (otherPointOnLine_ne (Γ := Γ) A' l')
  exact ⟨B', hB'l', l', hA'l', hB'ray, hA'neB'⟩

variable [hΓ₂ : OrderAxioms Γ]

/--
しかしこの偽合同関係では、"任意の ray 上にコピーを置ける" は失敗する。

証明の考え方:

1. ある直線 `l` と、その上の既定 ray `r` を 1 本取る。
2. 同じ直線 `l` 上で、`r` に属さない点 `Q` を取る。
3. `A` から `Q` への ray `h` を考える。これは `r` と反対向きの ray です。
4. `LineOnlySegCong` は「既定 ray 側」にしか点を置けないように作ってあるので、
   `h` の上にはそのような点は存在しません。
-/
theorem lineOnly_fails_on_some_ray :
    ∃ (A B : Γ.Point) (l : Γ.Line) (h : Γ.Ray),
      A ∈ l ∧ B ∈ l ∧ A = h.source ∧
        ¬ ∃ B', B' ∈ h ∧ LineOnlySegCong (Γ := Γ) A B A B' := by
  classical
  rcases hΓ₁.I₈ with ⟨A₀, _, _, _, _, _⟩
  rcases exists_line_of_forall_point A₀ with ⟨l, hAl⟩
  -- `l` 上の既定 ray をまず 1 本固定する。
  let r := canonicalRayOnLine (Γ := Γ) A₀ l
  let B := r.point
  have hrl : r ⊂ l := canonicalRayOnLine_subset_line (Γ := Γ) A₀ l hAl
  have hBr : B ∈ r := by
    simpa [B] using point_mem_ray r
  have hBl : B ∈ l := hrl B hBr
  -- 同じ直線上で、`r` に属さない点 `Q` を取る。
  rcases exists_not_onray_and_online_point (Γ := Γ) r with ⟨Q, m, hQm, hrm, hQr⟩
  have hA₀m : A₀ ∈ m := hrm _ (source_mem_ray r)
  have hBm : B ∈ m := hrm _ hBr
  have hm_eq_l : m = l := by
    have hA₀neB : A₀ ≠ B := by simpa [B] using r.source_ne_point
    exact hΓ₁.I₂ hA₀neB hA₀m hBm hAl hBl
  have hQl : Q ∈ l := by simpa [hm_eq_l] using hQm
  have hA₀Q : A₀ ≠ Q := by
    intro hEq
    subst hEq
    exact hQr (source_mem_ray r)
  -- `A₀Q` の ray を考える。これは `r` と反対向きになるはず。
  let h : Γ.Ray := {
    source := A₀
    point := Q
    source_ne_point := hA₀Q
  }
  have hhl : h ⊂ l := by
    intro X hX
    rw [onRay, h.carrier_eq, RaySet] at hX
    exact online_of_col hA₀Q hX.1.1 hAl hQl
  refine ⟨A₀, B, l, h, hAl, hBl, rfl, ?_⟩
  intro hExists
  rcases hExists with ⟨X, hXh, l', hA₀l', hXr', hXA₀⟩
  have hXl : X ∈ l := hhl X hXh
  have hXl' : X ∈ l' := by
    exact canonicalRayOnLine_subset_line (Γ := Γ) A₀ l' hA₀l' X hXr'
  have hl_eq_l' : l = l' := by
    exact hΓ₁.I₂ (Ne.symm hXA₀) hAl hXl hA₀l' hXl'
  subst hl_eq_l'
  -- ここで `X` は、既定 ray `r` と反対向き ray `h` の両方に載っている。
  -- もし `X ≠ A₀` なら、2 本の ray は同じ carrier を持つことになってしまう。
  have hSameQX : SameSidePoint A₀ Q X := by
    rw [onRay, h.carrier_eq, RaySet] at hXh
    exact hXh.1
  have hSameBX : SameSidePoint A₀ B X := by
    rw [onRay, r.carrier_eq, RaySet] at hXr'
    simpa [r, B, canonicalRayOnLine] using hXr'.1
  have hEqQX : Γ.RaySet A₀ Q = Γ.RaySet A₀ X :=
    (same_raySet_iff (Γ := Γ) A₀ Q X hA₀Q (Ne.symm hXA₀)).mp hSameQX
  have hA₀neB : A₀ ≠ B := by
    simpa [B] using r.source_ne_point
  have hEqBX : Γ.RaySet A₀ B = Γ.RaySet A₀ X :=
    (same_raySet_iff (Γ := Γ) A₀ B X hA₀neB (Ne.symm hXA₀)).mp hSameBX
  have hEqQB : Γ.RaySet A₀ Q = Γ.RaySet A₀ B := hEqQX.trans hEqBX.symm
  have hQinQ : Q ∈ Γ.RaySet A₀ Q := by
    refine ⟨?_, hA₀Q⟩
    refine ⟨?_, Or.inr <| Or.inr <| Or.inr rfl⟩
    exact col_symm.mp (col_of_eq (Γ := Γ) (A := Q) (B := Q) (C := A₀) rfl)
  have hQinB : Q ∈ Γ.RaySet A₀ B := by
    simpa [hEqQB] using hQinQ
  have hQr' : Q ∈ r := by
    rw [onRay, r.carrier_eq]
    simpa [r, B, canonicalRayOnLine] using hQinB
  exact hQr hQr'

end Geometry
end Hilbert
