import GameTheory.Math.SourceColoringTiles
import GameTheory.Math.GridRoutedColoring
import GameTheory.Math.GridRoutedSourceStep
import GameTheory.Math.GridWireBounds
import GameTheory.Math.GridSperner

/-! A boundary entrance replaces the known routed source's endpoint tile.
The remaining routed graph is shifted into the interior; padding keeps canonical
outer-boundary overrides away from its live image. -/

namespace GameTheory.Math.GridWire

open Sperner EndOfLine

/-- Source collars and shifted ordinary tiles form the local routing coloring. -/
def gridSpernerRoutingTileColor (n : ℕ) (P S : ℕ → ℕ) (i j x y : ℕ) : Fin 3 :=
  if i = 0 then
    if j = 0 then sourceCornerTileColor x y
    else if j = 1 then sourceTurnTileColor x y else sourceLeftTileColor x y
  else if j = 0 then sourceBottomTileColor x y
  else if i = 1 ∧ j = 1 then wireTileColor (some 3) (some 1) x y
  else wireTileColor
    (gridIncomingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (i-1,j-1))
    (gridOutgoingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (i-1,j-1)) x y

/-- The unbounded interior coloring reads one size-six tile locally. -/
def gridSpernerRoutingInterior (n : ℕ) (P S : ℕ → ℕ) (x y : ℕ) : Fin 3 :=
  gridSpernerRoutingTileColor n P S (x / 6) (y / 6) (x % 6) (y % 6)

/-- Canonical boundary colors enclose the shifted routing construction. -/
def gridSpernerRoutingColor (n : ℕ) (P S : ℕ → ℕ) (M : ℕ) : ℕ → ℕ → Fin 3 :=
  standardGridColor M (gridSpernerRoutingInterior n P S)

/-- The canonical finite routing coloring satisfies the square Sperner boundary. -/
theorem gridSpernerRoutingColor_boundary (n : ℕ) (P S : ℕ → ℕ) {M : ℕ} (hM : 0 < M) :
    GridBoundary (gridSpernerRoutingColor n P S M) M :=
  standardGridColor_boundary M _ hM

private theorem incoming_not_west (P S : (ℕ × ℕ) → ℕ × ℕ) (j : ℕ) :
    gridIncomingPort P S (0,j) ≠ some 3 := by
  intro h
  rw [gridIncomingPort, gridDirection_eq_some_iff] at h
  simp only [Fin.reduceEq, ite_false] at h
  omega

private theorem outgoing_not_west (P S : (ℕ × ℕ) → ℕ × ℕ) (j : ℕ) :
    gridOutgoingPort P S (0,j) ≠ some 3 := by
  intro h
  rw [gridOutgoingPort, gridDirection_eq_some_iff] at h
  simp only [Fin.reduceEq, ite_false] at h
  omega

private theorem incoming_not_south (P S : (ℕ × ℕ) → ℕ × ℕ) (i : ℕ) :
    gridIncomingPort P S (i,0) ≠ some 2 := by
  intro h
  rw [gridIncomingPort, gridDirection_eq_some_iff] at h
  simp only [Fin.reduceEq, ite_false, ite_true] at h
  omega

private theorem outgoing_not_south (P S : (ℕ × ℕ) → ℕ × ℕ) (i : ℕ) :
    gridOutgoingPort P S (i,0) ≠ some 2 := by
  intro h
  rw [gridOutgoingPort, gridDirection_eq_some_iff] at h
  simp only [Fin.reduceEq, ite_false, ite_true] at h
  omega

private theorem origin_ports {n : ℕ} {P S : ℕ → ℕ}
    (hi : 0 < n) (hSi : S 0 < n) (hP : P 0 = 0) (hS : S 0 ≠ 0)
    (hlink : P (S 0) = 0) :
    gridIncomingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (0,0) = none ∧
    gridOutgoingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (0,0) = some 1 := by
  have h := gridRouted_origin_step hi hSi hP hS hlink
  simp [gridIncomingPort, gridOutgoingPort, eraseTwoCyclePredecessor, eraseTwoCycleSuccessor,
    h.1, h.2, gridDirection]

private theorem background_outside {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hp : 3*n*n ≤ p.1 ∨ 6*n ≤ p.2) :
    gridRoutedPredecessor n P S p = p ∧ gridRoutedSuccessor n P S p = p := by
  have hd : decodeWireNode n P S p = none := by
    cases he : decodeWireNode n P S p with
    | none => rfl
    | some node =>
      obtain ⟨hl,hc⟩ := decodeWireNode_eq_some_iff.mp he
      have hb := routedCoordinate_bounds hl
      rw [hc] at hb
      omega
  exact gridRouted_background hd

private theorem ports_outside {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hp : 3*n*n ≤ p.1 ∨ 6*n ≤ p.2) :
    gridIncomingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) p = none ∧
    gridOutgoingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) p = none := by
  have h := background_outside (P:=P) (S:=S) hp
  simp [gridIncomingPort, gridOutgoingPort, eraseTwoCyclePredecessor, eraseTwoCycleSuccessor,
    h.1, h.2]


private def tileBoundary (color : ℕ → ℕ → Fin 3) (d : Fin 4) (k : ℕ) : Fin 3 :=
  if d=0 then color k 6 else if d=1 then color 6 k else if d=2 then color k 0 else color 0 k

private def ordinaryIn (n : ℕ) (P S : ℕ → ℕ) (i j : ℕ) : Option (Fin 4) :=
  gridIncomingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (i,j)

private def ordinaryOut (n : ℕ) (P S : ℕ → ℕ) (i j : ℕ) : Option (Fin 4) :=
  gridOutgoingPort (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (i,j)

private theorem ordinary_boundary (n : ℕ) (P S : ℕ → ℕ) (i j : ℕ)
    (d : Fin 4) {k : ℕ} (hk : k≤6) :
    tileBoundary (wireTileColor (ordinaryIn n P S i j) (ordinaryOut n P S i j)) d k =
      wireTilePortColor (ordinaryIn n P S i j) (ordinaryOut n P S i j) d k :=
  wireTileColor_boundary _ _ (gridPorts_valid _ _ (gridRoutedPredecessor_adjacent n P S) (i,j)) d hk

private theorem positive_tile_boundary (n : ℕ) (P S : ℕ → ℕ) {i j : ℕ}
    (hi : 0<i) (hj : 0<j) (ho : ¬(i=1 ∧ j=1)) (d : Fin 4) {k : ℕ} (hk : k≤6) :
    tileBoundary (gridSpernerRoutingTileColor n P S i j) d k =
      wireTilePortColor (ordinaryIn n P S (i-1) (j-1)) (ordinaryOut n P S (i-1) (j-1)) d k := by
  unfold tileBoundary
  simp only [gridSpernerRoutingTileColor, Nat.ne_of_gt hi, Nat.ne_of_gt hj, ho, ite_false]
  exact ordinary_boundary n P S (i-1) (j-1) d hk

private theorem origin_tile_boundary (n : ℕ) (P S : ℕ → ℕ)
    (d : Fin 4) {k : ℕ} (hk : k≤6) :
    tileBoundary (gridSpernerRoutingTileColor n P S 1 1) d k =
      wireTilePortColor (some 3) (some 1) d k := by
  unfold tileBoundary
  simp only [gridSpernerRoutingTileColor, Nat.one_ne_zero, ite_false, and_self, ite_true]
  exact wireTileColor_boundary _ _ (by decide) d hk

private theorem zero_col_boundary (n : ℕ) (P S : ℕ → ℕ) (j : ℕ)
    (d : Fin 4) {k : ℕ} (hk : k≤6) :
    tileBoundary (gridSpernerRoutingTileColor n P S 0 j) d k =
      if j=0 then sourceCornerBoundaryColor d k
      else if j=1 then sourceTurnBoundaryColor d k else sourceLeftBoundaryColor d k := by
  by_cases hj : j=0
  · subst j
    simp only [gridSpernerRoutingTileColor, ite_true, tileBoundary]
    exact sourceCornerTileColor_boundary d hk
  · by_cases hj1 : j=1
    · subst j
      simp only [gridSpernerRoutingTileColor, ite_true, Nat.one_ne_zero, ite_false, tileBoundary]
      exact sourceTurnTileColor_boundary d hk
    · simp only [gridSpernerRoutingTileColor, ite_true, hj, hj1, ite_false, tileBoundary]
      exact sourceLeftTileColor_boundary d hk

private theorem zero_row_boundary (n : ℕ) (P S : ℕ → ℕ) {i : ℕ}
    (hi : 0<i) (d : Fin 4) {k : ℕ} (hk : k≤6) :
    tileBoundary (gridSpernerRoutingTileColor n P S i 0) d k = sourceBottomBoundaryColor d k := by
  simp only [gridSpernerRoutingTileColor, Nat.ne_of_gt hi, ite_false, ite_true, tileBoundary]
  exact sourceBottomTileColor_boundary d hk

private theorem positive_nonwest {n : ℕ} {P S : ℕ → ℕ}
    (hn : 0<n) (hSi : S 0<n) (hP : P 0=0) (hS : S 0≠0) (hl : P (S 0)=0)
    {i j : ℕ} (hi : 0<i) (hj : 0<j) (d : Fin 4) (hd : d≠3)
    {k : ℕ} (hk : k≤6) :
    tileBoundary (gridSpernerRoutingTileColor n P S i j) d k =
      wireTilePortColor (ordinaryIn n P S (i-1) (j-1)) (ordinaryOut n P S (i-1) (j-1)) d k := by
  by_cases ho : i=1 ∧ j=1
  · obtain ⟨rfl,rfl⟩ := ho
    rw [origin_tile_boundary n P S d hk]
    have hp := origin_ports hn hSi hP hS hl
    simp only [ordinaryIn, ordinaryOut, Nat.sub_self, hp.1, hp.2]
    fin_cases d <;> simp_all [wireTilePortColor, wireTileOutwardFirst]
  · exact positive_tile_boundary n P S hi hj ho d hk

private theorem east_seam {n : ℕ} {P S : ℕ → ℕ}
    (hn : 0<n) (hSi : S 0<n) (hP : P 0=0) (hS : S 0≠0) (hl : P (S 0)=0)
    (i j k : ℕ) (hk : k≤6) :
    tileBoundary (gridSpernerRoutingTileColor n P S i j) 1 k =
      tileBoundary (gridSpernerRoutingTileColor n P S (i+1) j) 3 k := by
  by_cases hj : j=0
  · subst j
    rw [zero_row_boundary n P S (by omega) 3 hk]
    by_cases hi : i=0
    · subst i
      rw [zero_col_boundary n P S 0 1 hk]
      simp [sourceCornerBoundaryColor, sourceBottomBoundaryColor]
    · rw [zero_row_boundary n P S (by omega) 1 hk]
      simp [sourceBottomBoundaryColor]
  · by_cases hi : i=0
    · subst i
      rw [zero_col_boundary n P S j 1 hk]
      by_cases hj1 : j=1
      · subst j
        rw [origin_tile_boundary n P S 3 hk]
        by_cases hk2 : k=2 <;> by_cases hk3 : k=3 <;>
          simp [sourceTurnBoundaryColor, wireTilePortColor, wireTileOutwardFirst, hk2, hk3]
      · rw [positive_tile_boundary n P S (by omega) (by omega) (by omega) 3 hk]
        have hin := incoming_not_west (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P
          S) (j-1)
        have hout := outgoing_not_west (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P
          S) (j-1)
        simp [hj, hj1, sourceLeftBoundaryColor, wireTilePortColor, ordinaryIn, ordinaryOut,
          hin, hout]
    · rw [positive_nonwest hn hSi hP hS hl (by omega) (by omega) 1 (by decide) hk,
          positive_tile_boundary n P S (by omega) (by omega) (by omega) 3 hk]
      have he := gridPorts_east_seam (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S)
        (gridRouted_predecessor_consistent n P S) (gridRouted_successor_consistent n P S)
          (i-1) (j-1) k
      have hei : i+1-1 = i-1+1 := by omega
      simpa only [ordinaryIn, ordinaryOut, hei] using he

private theorem north_seam {n : ℕ} {P S : ℕ → ℕ}
    (hn : 0<n) (hSi : S 0<n) (hP : P 0=0) (hS : S 0≠0) (hl : P (S 0)=0)
    (i j k : ℕ) (hk : k≤6) :
    tileBoundary (gridSpernerRoutingTileColor n P S i j) 0 k =
      tileBoundary (gridSpernerRoutingTileColor n P S i (j+1)) 2 k := by
  by_cases hi : i=0
  · subst i
    rw [zero_col_boundary n P S j 0 hk, zero_col_boundary n P S (j+1) 2 hk]
    by_cases hj : j=0
    · subst j; simp [sourceCornerBoundaryColor, sourceTurnBoundaryColor]
    · by_cases hj1 : j=1
      · subst j; simp [sourceTurnBoundaryColor, sourceLeftBoundaryColor]
      · 
        simp [hj, hj1, sourceLeftBoundaryColor]
  · by_cases hj : j=0
    · subst j
      rw [zero_row_boundary n P S (by omega) 0 hk,
          positive_nonwest hn hSi hP hS hl (by omega) (by omega) 2 (by decide) hk]
      have hin := incoming_not_south (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (i-1)
      have hout := outgoing_not_south (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P
        S) (i-1)
      simp [sourceBottomBoundaryColor, wireTilePortColor, ordinaryIn, ordinaryOut, hin, hout]
    · rw [positive_nonwest hn hSi hP hS hl (by omega) (by omega) 0 (by decide) hk,
          positive_nonwest hn hSi hP hS hl (by omega) (by omega) 2 (by decide) hk]
      have he := gridPorts_north_seam (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S)
        (gridRouted_predecessor_consistent n P S) (gridRouted_successor_consistent n P S)
          (i-1) (j-1) k
      have hei : j+1-1 = j-1+1 := by omega
      simpa only [ordinaryIn, ordinaryOut, hei] using he

private theorem local_agreement {n : ℕ} {P S : ℕ → ℕ}
    (hn : 0<n) (hSi : S 0<n) (hP : P 0=0) (hS : S 0≠0) (hl : P (S 0)=0)
    (i j x y : ℕ) (hx : x≤6) (hy : y≤6) :
    gridSpernerRoutingInterior n P S (6*i+x) (6*j+y) =
      gridSpernerRoutingTileColor n P S i j x y := by
  have he := east_seam hn hSi hP hS hl
  have hnorth := north_seam hn hSi hP hS hl
  by_cases hxe : x=6 <;> by_cases hye : y=6
  · subst x; subst y
    have ha : (6*i+6)/6=i+1 ∧ (6*i+6)%6=0 := by omega
    have hb : (6*j+6)/6=j+1 ∧ (6*j+6)%6=0 := by omega
    rw [gridSpernerRoutingInterior, ha.1,ha.2,hb.1,hb.2]
    have h1 := he i j 6 (by omega)
    have h2 := hnorth (i+1) j 0 (by omega)
    simp only [tileBoundary, Fin.reduceEq, ite_false, ite_true] at h1 h2
    exact (h1.trans h2).symm
  · subst x
    have ha : (6*i+6)/6=i+1 ∧ (6*i+6)%6=0 := by omega
    have hb : (6*j+y)/6=j ∧ (6*j+y)%6=y := by omega
    rw [gridSpernerRoutingInterior, ha.1,ha.2,hb.1,hb.2]
    have h1 := he i j y hy
    simpa only [tileBoundary, Fin.reduceEq, ite_false, ite_true] using h1.symm
  · subst y
    have ha : (6*i+x)/6=i ∧ (6*i+x)%6=x := by omega
    have hb : (6*j+6)/6=j+1 ∧ (6*j+6)%6=0 := by omega
    rw [gridSpernerRoutingInterior, ha.1,ha.2,hb.1,hb.2]
    have h1 := hnorth i j x hx
    simpa only [tileBoundary, Fin.reduceEq, ite_false, ite_true] using h1.symm
  · have ha : (6*i+x)/6=i ∧ (6*i+x)%6=x := by omega
    have hb : (6*j+y)/6=j ∧ (6*j+y)%6=y := by omega
    simp only [gridSpernerRoutingInterior,ha.1,ha.2,hb.1,hb.2]

private theorem tile_triangle_endpoint (n : ℕ) (P S : ℕ → ℕ) (i j : ℕ)
    {x y : ℕ} (hx : x<6) (hy : y<6) (upper : Bool)
    (ht : Trichromatic (gridSpernerRoutingTileColor n P S i j x y)
      (if upper then gridSpernerRoutingTileColor n P S i j (x+1) (y+1)
        else gridSpernerRoutingTileColor n P S i j (x+1) y)
      (if upper then gridSpernerRoutingTileColor n P S i j x (y+1)
        else gridSpernerRoutingTileColor n P S i j (x+1) (y+1))) :
    0<i ∧ 0<j ∧ ¬(i=1 ∧ j=1) ∧
      IsEndpoint (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (i-1,j-1) ∧
      x=2 ∧ y=2 ∧ upper=false := by
  by_cases hi : i=0
  · subst i
    by_cases hj : j=0
    · simp only [gridSpernerRoutingTileColor, ite_true, hj] at ht
      exact False.elim (sourceCornerTileColor_not_trichromatic hx hy upper ht)
    · by_cases hj1 : j=1
      · simp only [gridSpernerRoutingTileColor, ite_true, hj1] at ht
        exact False.elim (sourceTurnTileColor_not_trichromatic hx hy upper ht)
      · simp only [gridSpernerRoutingTileColor, ite_true, hj, hj1, ite_false] at ht
        exact False.elim (sourceLeftTileColor_not_trichromatic hx hy upper ht)
  · by_cases hj : j=0
    · simp only [gridSpernerRoutingTileColor, hi, ite_false, hj, ite_true] at ht
      exact False.elim (sourceBottomTileColor_not_trichromatic hx hy upper ht)
    · by_cases ho : i=1 ∧ j=1
      · obtain ⟨rfl,rfl⟩ := ho
        simp only [gridSpernerRoutingTileColor, Nat.one_ne_zero, ite_false, and_self,
          ite_true] at ht
        have he := (wireTileColor_trichromatic_iff (some 3) (some 1) (by decide) hx hy upper).mp ht
        simp [TileEndpoint] at he
      · simp only [gridSpernerRoutingTileColor, hi, hj, ho, ite_false] at ht
        have he := (wireTileColor_trichromatic_iff _ _
          (gridPorts_valid _ _ (gridRoutedPredecessor_adjacent n P S) (i-1,j-1)) hx hy upper).mp ht
        rw [gridPorts_endpoint_iff _ _ (gridRouted_predecessor_consistent n P S)
          (gridRouted_successor_consistent n P S) (gridRoutedPredecessor_adjacent n P S)
          (gridRoutedSuccessor_adjacent n P S)] at he
        exact ⟨by omega,by omega,ho,he⟩

/-- Every interior trichromatic triangle labels a non-source original endpoint.
The boundary entrance removes the original source's local endpoint witness. -/
theorem gridSpernerRoutingInterior_endpoint_label {n : ℕ} {P S : ℕ → ℕ}
    (hn : 0<n) (hSi : S 0<n) (hp0 : P 0=0) (hs0 : S 0≠0) (hlink : P (S 0)=0)
    (hP : ∀ i, i<n → P i<n) (hS : ∀ i, i<n → S i<n) {t : GridTriangle}
    (ht : Trichromatic (gridSpernerRoutingInterior n P S (corner t 0).1 (corner t 0).2)
      (gridSpernerRoutingInterior n P S (corner t 1).1 (corner t 1).2)
      (gridSpernerRoutingInterior n P S (corner t 2).1 (corner t 2).2)) :
    ∃ i, i<n ∧ i≠0 ∧ IsEndpoint P S i ∧ t.x=8 ∧ t.y=36*i+8 := by
  have hx : t.x%6<6 := Nat.mod_lt _ (by omega)
  have hy : t.y%6<6 := Nat.mod_lt _ (by omega)
  have h00 := local_agreement hn hSi hp0 hs0 hlink (t.x/6) (t.y/6) (t.x%6) (t.y%6) (by omega)
    (by omega)
  have h10 := local_agreement hn hSi hp0 hs0 hlink (t.x/6) (t.y/6) (t.x%6+1) (t.y%6) (by
    omega) (by omega)
  have h01 := local_agreement hn hSi hp0 hs0 hlink (t.x/6) (t.y/6) (t.x%6) (t.y%6+1) (by
    omega) (by omega)
  have h11 := local_agreement hn hSi hp0 hs0 hlink (t.x/6) (t.y/6) (t.x%6+1) (t.y%6+1) (by
    omega) (by omega)
  have hxe : 6*(t.x/6)+t.x%6=t.x := by omega
  have hye : 6*(t.y/6)+t.y%6=t.y := by omega
  simp only [←Nat.add_assoc,hxe,hye] at h00 h10 h01 h11
  have htlocal : Trichromatic
      (gridSpernerRoutingTileColor n P S (t.x/6) (t.y/6) (t.x%6) (t.y%6))
      (if t.upper then gridSpernerRoutingTileColor n P S (t.x/6) (t.y/6) (t.x%6+1) (t.y%6+1)
        else gridSpernerRoutingTileColor n P S (t.x/6) (t.y/6) (t.x%6+1) (t.y%6))
      (if t.upper then gridSpernerRoutingTileColor n P S (t.x/6) (t.y/6) (t.x%6) (t.y%6+1)
        else gridSpernerRoutingTileColor n P S (t.x/6) (t.y/6) (t.x%6+1) (t.y%6+1)) := by
    cases hu : t.upper <;> simpa only [corner,hu,Bool.false_eq_true,ite_false,ite_true,
      Fin.reduceEq,h00,h10,h01,h11] using ht
  obtain ⟨hi,hj,ho,he,hxm,hym,_⟩ := tile_triangle_endpoint n P S (t.x/6) (t.y/6) hx hy
    t.upper htlocal
  obtain ⟨i,hin,hpoint,hei⟩ := gridRouted_endpoint_decodes hP hS he
  have hxpoint := congrArg Prod.fst hpoint
  have hypoint := congrArg Prod.snd hpoint
  simp only [vertexPoint] at hxpoint hypoint
  refine ⟨i,hin,?_,hei,by omega,by omega⟩
  intro hz
  subst i
  apply ho
  constructor <;> omega

/-- The left edge of the unbounded routing coloring has color zero. -/
theorem gridSpernerRoutingInterior_left (n : ℕ) (P S : ℕ → ℕ) (y : ℕ) :
    gridSpernerRoutingInterior n P S 0 y = 0 := by
  have h := zero_col_boundary n P S (y/6) 3 (k:=y%6) (by omega)
  simp only [tileBoundary,Fin.reduceEq,ite_false] at h
  simp [sourceCornerBoundaryColor,sourceTurnBoundaryColor,sourceLeftBoundaryColor] at h
  exact h

/-- The bottom edge has the canonical zero corner and color one elsewhere. -/
theorem gridSpernerRoutingInterior_bottom (n : ℕ) (P S : ℕ → ℕ) (x : ℕ) :
    gridSpernerRoutingInterior n P S x 0 = if x=0 then 0 else 1 := by
  by_cases hx : x/6=0
  · have h := zero_col_boundary n P S 0 2 (k:=x%6) (by omega)
    simp only [tileBoundary,Fin.reduceEq,ite_false,ite_true] at h
    have he : x%6=x := by omega
    simpa [gridSpernerRoutingInterior,hx,he,sourceCornerBoundaryColor] using h
  · have h := zero_row_boundary n P S (i:=x/6) (by omega) 2 (k:=x%6) (by omega)
    simp only [tileBoundary,Fin.reduceEq,ite_false,ite_true] at h
    have he : x≠0 := by omega
    simpa [gridSpernerRoutingInterior,he,sourceBottomBoundaryColor] using h

/-- Outside the routed rectangle every positive macrocell is uniformly background. -/
theorem gridSpernerRoutingTileColor_background {n : ℕ} {P S : ℕ → ℕ} {i j x y : ℕ}
    (hi : 0<i) (hj : 0<j) (hout : 3*n*n+2≤i ∨ 6*n+2≤j)
    (hx : x<6) (hy : y<6) : gridSpernerRoutingTileColor n P S i j x y=2 := by
  have ho : ¬(i=1 ∧ j=1) := by omega
  have hp := ports_outside (n:=n) (P:=P) (S:=S) (p:=(i-1,j-1)) (by omega)
  simp only [gridSpernerRoutingTileColor,Nat.ne_of_gt hi,Nat.ne_of_gt hj,ho,ite_false,hp.1,hp.2]
  have h : ∀ x y : Fin 6, wireTileColor none none x y=2 := by decide
  exact h ⟨x,hx⟩ ⟨y,hy⟩

/-- The far-right padding and bottom collar never use color zero. -/
theorem gridSpernerRoutingInterior_ne_zero_of_large_x {n : ℕ} {P S : ℕ → ℕ} {x y : ℕ}
    (hx : 6*(3*n*n+2)≤x) : gridSpernerRoutingInterior n P S x y≠0 := by
  have hi : 3*n*n+2≤x/6 := by omega
  have his : 0<x/6 := by omega
  by_cases hj : y/6=0
  · simpa only [gridSpernerRoutingInterior,gridSpernerRoutingTileColor,Nat.ne_of_gt his,
      hj,ite_false,ite_true] using sourceBottomTileColor_ne_zero (x%6) (y%6)
  · have h := gridSpernerRoutingTileColor_background (P:=P) (S:=S) (i:=x/6) (j:=y/6) his (by omega)
      (Or.inl hi) (Nat.mod_lt x (by omega)) (Nat.mod_lt y (by omega))
    rw [gridSpernerRoutingInterior,h]
    decide

/-- The far-top padding and left collar never use color one. -/
theorem gridSpernerRoutingInterior_ne_one_of_large_y {n : ℕ} {P S : ℕ → ℕ} {x y : ℕ}
    (hy : 6*(6*n+2)≤y) : gridSpernerRoutingInterior n P S x y≠1 := by
  have hj : 6*n+2≤y/6 := by omega
  have hjs : 0<y/6 := by omega
  by_cases hi : x/6=0
  · have hj1 : y/6≠1 := by omega
    simpa only [gridSpernerRoutingInterior,gridSpernerRoutingTileColor,hi,Nat.ne_of_gt hjs,
      hj1,ite_true,ite_false] using sourceLeftTileColor_ne_one (x%6) (y%6)
  · have h := gridSpernerRoutingTileColor_background (P:=P) (S:=S) (i:=x/6) (j:=y/6) (by omega) hjs
      (Or.inr hj) (Nat.mod_lt x (by omega)) (Nat.mod_lt y (by omega))
    rw [gridSpernerRoutingInterior,h]
    decide

end GameTheory.Math.GridWire








