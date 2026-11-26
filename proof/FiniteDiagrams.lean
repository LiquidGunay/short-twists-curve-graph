import Lean

/-! Independent executable check of the signed diagrams. Lean 4.8.0, core only.
    A decision at budget m means "distance at most m" under the combinatorial
    interpretation justified in the paper. No tables of neighbors or of
    terminal answers are supplied as input. -/
namespace FiniteDiagrams

abbrev Code := Array Int
abbrev Side := Nat
abbrev Faces := Array (Array Nat)
abbrev Route := Array (Side × Nat × Nat)

def p12 : Code := #[1,-8,-3,-10,5,6,7,-2,-9,-4,11,12]
def p13 : Code := #[1,-8,-3,-9,-4,11,13,2,7,6,5,10,12]
def p14 : Code := #[1,-9,-3,-11,-5,-6,-7,-8,-2,-10,-4,12,13,14]
def fourSquares : Code := #[1,2,4,3]

def flip (d : Nat) := if d % 2 = 0 then d + 1 else d - 1

def cycles (perm : Array Nat) : Faces := Id.run do
  let mut seen := Array.mkArray perm.size false
  let mut out := #[]
  for start in [:perm.size] do
    if seen[start]! then continue
    let mut d := start
    let mut face := #[]
    for _ in [:perm.size] do
      if seen[d]! then break
      seen := seen.set! d true
      face := face.push d
      d := perm[d]!
    out := out.push face
  return out

/-- Boundary cycles in the original four-valent graph. -/
def originalFaces (code : Code) : Faces := Id.run do
  let n := code.size
  let mut edges := Array.mkArray (4*n) 0
  let mut rot := edges
  for j in [:n] do
    let s := code[j]!
    let i := s.natAbs-1
    let k := code[(j+1)%n]!.natAbs-1
    let a := 4*i
    let nextA := 4*((i+1)%n)+2
    edges := ((edges.set! a nextA).set! nextA a)
    edges := ((edges.set! (a+1) (4*k+3)).set! (4*k+3) (a+1))
    for u in [:4] do
      rot := rot.set! (a+u) (a+(u+(if s>0 then 1 else 3))%4)
  return cycles (edges.map (fun d => rot[d]!))

/-- Collapse the two boundary circles after cutting along the first curve. -/
def cutFaces (code : Code) : Faces := Id.run do
  let n := code.size
  let mut pos := Array.mkArray n 0
  let mut neg := pos
  for j in [:n] do
    let s := code[j]!
    let i := s.natAbs-1
    let prev := (2*j+2*n-1)%(2*n)
    pos := pos.set! i (if s>0 then 2*j else prev)
    neg := neg.set! i (if s>0 then prev else 2*j)
  let mut perm := Array.mkArray (2*n) 0
  for j in [:n] do
    perm := perm.set! (flip pos[j]!) pos[(j+1)%n]!
    perm := perm.set! (flip neg[j]!) neg[(j+n-1)%n]!
  return cycles perm

structure Triangulation where
  opp : Array Side
  bands : Array (Array Nat)
  deriving Inhabited

def triangulate (fs : Faces) (n : Nat) : Triangulation := Id.run do
  let base := 2*n
  let mut fresh := base
  let mut paired := Array.mkArray base base
  let mut tri := #[]
  for f in fs do
    if f.size == 2 then
      paired := (paired.set! f[0]! f[1]!).set! f[1]! f[0]!
    else
      let mut first := f[0]!
      for j in [1:f.size-2] do
        tri := ((tri.push first).push f[j]!).push fresh
        first := fresh+1
        fresh := fresh+2
      tri := ((tri.push first).push f[f.size-2]!).push f[f.size-1]!
  let mut index := Array.mkArray fresh 0
  for i in [:tri.size] do index := index.set! tri[i]! i
  let mut o := #[]
  let mut bands := #[]
  for d in tri do
    if d ≥ base then
      o := o.push index[base + flip (d-base)]!
      bands := bands.push #[]
    else
      let mut e := d
      let mut band := #[]
      for _ in [:base] do
        band := band.push e
        let back := flip e
        if paired[back]! == base then
          o := o.push index[back]!
          break
        e := paired[back]!
      bands := bands.push band
  return ⟨o,bands⟩

/-- List signed diagrams for a positive twist by tracing through the collar.
    The fixed-side and moving-side linear orders independently label the events. -/
def twist (s : Code) (power : Nat) : Code := Id.run do
  let n := s.size
  let mut col := Array.mkArray n 0
  let mut positive := Array.mkArray n false
  for j in [:n] do
    let i := s[j]!.natAbs-1
    col := col.set! i j
    positive := positive.set! i (s[j]!>0)
  let mut fixed : Array (Array (Nat × Nat)) := Array.mkArray n #[]
  let mut moving := fixed
  for i in [:n] do
    for f in [:n] do
      for k in [:power] do
        let beginCol := 4*col[i]! + (if positive[i]! then 1 else 4*n-1)
        let h := (8*n+4*col[f]!-beginCol)%(4*n) + k*(4*n)
        let key := (i*n+f)*power+k
        let u := if positive[f]! then h else 4*n*power-h
        let v := if positive[i]! then h else 4*n*power-h
        fixed := fixed.modify f (fun xs => xs.push (u,key))
        moving := moving.modify i (fun xs => xs.push (v,key))
  let mut label := Array.mkArray (n*n*power) 0
  let mut count := 0
  for block in fixed do
    for (_,key) in block.qsort (fun a b => a.1<b.1) do
      count := count+1
      label := label.set! key count
  let mut result := #[]
  for block in moving do
    for (_,key) in block.qsort (fun a b => a.1<b.1) do
      let x : Int := label[key]!
      result := result.push (if positive[key/power/n]! == positive[key/power%n]! then x else -x)
  return result

def sideEdges (opp : Array Nat) : Array Nat := Id.run do
  let mut edges := Array.mkArray opp.size 0
  let mut i := 0
  for d in [:opp.size] do
    if d < opp[d]! then
      edges := (edges.set! d i).set! opp[d]! i
      i := i+1
  return edges

/-- Recover a connected normal curve directly from six edge weights.
    Within a triangle use the corner counts to compute the next slot. -/
def normalRoute (opp edges weights : Array Nat) : Option Route := Id.run do
  let w := edges.map (fun i => weights[i]!)
  let total := weights.foldl (·+·) 0
  if total == 0 then return none
  for tr in [:opp.size/3] do
    let x := w[3*tr]!; let y := w[3*tr+1]!; let z := w[3*tr+2]!
    if (x+y+z)%2 != 0 || x+y<z || y+z<x || z+x<y then return none
  let start := (List.range opp.size).find? (fun d => w[d]!>0) |>.getD 0
  let mut d := start
  let mut t := 0
  let mut path := #[]
  for i in [:total] do
    let rev := w[d]!-1-t
    path := path.push (d,t,rev)
    let p := opp[d]!
    let base := 3*(p/3)
    let prev := base+(p%3+2)%3
    let next := base+(p%3+1)%3
    let leftCorner := (w[p]!+w[prev]!-w[next]!)/2
    if rev<leftCorner then
      d := prev
      t := w[prev]!-1-rev
    else
      d := next
      t := w[p]!-1-rev
    if d==start && t==0 then return (if i+1==total then some path else none)
  return none

def routes (opp : Array Nat) (bound : Nat) : Array Route := Id.run do
  let edges := sideEdges opp
  let base := bound+1
  let mut out := #[]
  for rank in [:base^(opp.size/2)] do
    let mut number := rank
    let mut ws := #[]
    for _ in [:opp.size/2] do
      ws := ws.push (number%base)
      number := number/base
    if let some route := normalRoute opp edges ws then out := out.push route
  return out.qsort (fun x y => x.size<y.size)

def neighbor (tr : Triangulation) (route : Route) : Code := Id.run do
  let mut hits : Array (Nat × Nat × Int) := #[]
  for (side,t,r) in route do
    for dart in tr.bands[side]! do
      let idx : Int := (hits.size+1 : Nat)
      let hit := if dart%2==0 then (dart/2,t,idx) else (dart/2,r,-idx)
      hits := hits.push hit
  let ordered := hits.qsort (fun a b => a.1<b.1 || (a.1==b.1 && a.2.1<b.2.1))
  return ordered.map (fun a => a.2.2)

/-- A cached row records its input and a proof of its value. Proofs are erased
    by the evaluator. Even an arbitrary initial cache is safe to use. -/
structure CachedRoutes where
  opp : Array Nat
  bound : Nat
  value : Array Route
  correct : value = routes opp bound

abbrev RouteCache := Lean.HashMap (List Nat × Nat) CachedRoutes

def getRoutes (opp : Array Nat) (bound : Nat) (cache : RouteCache) :
    {rs : Array Route // rs = routes opp bound} × RouteCache := Id.run do
  let key := (opp.toList,bound)
  if let some row := cache.find? key then
    if same : row.opp = opp ∧ row.bound = bound then
      return (⟨row.value, by rw [row.correct,same.1,same.2]⟩,cache)
  let rs := routes opp bound
  return (⟨rs,rfl⟩, cache.insert key ⟨opp,bound,rs,rfl⟩)

def terminal (s : Code) : Bool :=
  s.isEmpty || decide (2+s.size < (originalFaces s).size+4)

def coordinateBound (tr : Triangulation) (k : Nat) : Nat :=
  k+1+(if tr.bands.any Array.isEmpty then 1 else 0)

def visit {α σ : Type} (test : α → σ → Bool × σ) : List α → σ → Bool × σ
  | [], cache => (false,cache)
  | r :: rs, cache =>
    let (found,next) := test r cache
    if found then (true,next) else visit test rs next

/-- Test distance at most extra+2. Every cache hit returns the actual row
    computed by routes; no cache stores answers for curve pairs. -/
def reachable : Nat → Code → StateM RouteCache Bool
  | 0, s => fun cache => (terminal s,cache)
  | k+1, s => fun cache =>
    if terminal s then (true,cache) else
      let tr := triangulate (cutFaces s) s.size
      let (row,next) := getRoutes tr.opp (coordinateBound tr k) cache
      visit (fun r => reachable k (neighbor tr r)) row.val.toList next

def exactTest (s : Code) (d : Nat) : Bool :=
  let (shorter,cache) := (reachable (d-3) s).run {}
  if shorter then false else ((reachable (d-2) s).run cache).1

def faceProfile (s : Code) : Nat × Nat × Nat :=
  let faces := originalFaces s
  (faces.size,(faces.filter (fun f => f.size==4)).size,(faces.filter (fun f => f.size==6)).size)

-- The finite equalities use Lean's native evaluator, as reported by #print axioms.
theorem thirteen_seed_faces : faceProfile p13 = (11,7,4) := by native_decide
theorem twelve_seed_distance_test : exactTest p12 4 = true := by native_decide
theorem thirteen_seed_distance_test : exactTest p13 4 = true := by native_decide
theorem fourteen_seed_distance_test : exactTest p14 4 = true := by native_decide
theorem twelve_unit_distance_test : exactTest (twist p12 1) 5 = true := by native_decide
theorem thirteen_twist_distance_test : exactTest (twist p13 1) 5 = true := by native_decide
theorem twelve_double_distance_test : exactTest (twist p12 2) 6 = true := by native_decide
theorem twelve_triple_distance_test : exactTest (twist p12 3) 6 = true := by native_decide
theorem fourteen_twist_distance_test : exactTest (twist p14 1) 6 = true := by native_decide
theorem nested_unit_distance_test : exactTest (twist (twist fourSquares 1) 1) 5 = true := by
  native_decide

#print axioms thirteen_seed_faces
#print axioms thirteen_twist_distance_test
#print axioms fourteen_twist_distance_test
#print axioms nested_unit_distance_test

/-- Ordered representatives of all distance-four seeds at 12 and 13 crossings.
    The companion census enumerates the inputs; this theorem checks their distances. -/
def smallSeeds : Array Code := #[
  #[1,-8,-9,-10,5,12,7,-2,-3,-4,11,6],
  #[1,-8,-9,-10,5,12,7,2,3,4,11,6],
  #[1,-8,-5,-10,-3,-12,7,-2,-11,-4,-9,-6],
  #[1,-8,-3,-10,-5,-12,7,-2,-9,-4,-11,-6],
  #[1,2,3,10,5,12,7,8,9,4,11,6],
  #[1,-9,-11,-4,-3,-2,-8,-10,5,12,6,13,7],
  #[1,-9,-11,4,3,2,-8,-10,5,12,6,13,7],
  #[1,-9,-10,-11,6,4,2,-8,-13,-7,-12,5,3],
  #[1,-9,-10,-11,6,13,8,-2,-3,-4,-5,12,7],
  #[1,-9,-10,-11,6,13,8,2,3,4,5,12,7],
  #[1,-9,-3,-11,-5,-13,7,8,-2,-10,-4,-12,-6],
  #[1,-8,-10,-12,-4,-3,-2,-7,-9,-11,5,13,6],
  #[1,-8,-9,-10,-11,5,13,7,2,3,4,12,6],
  #[1,-8,-9,-10,4,2,13,7,12,6,11,5,3],
  #[1,2,3,4,11,6,13,8,9,10,5,12,7],
  #[1,2,3,10,8,6,13,5,12,4,11,9,7]
]

theorem small_seed_unit_tests :
    smallSeeds.all (fun s => exactTest s 4 && exactTest (twist s 1) 5) = true := by
  native_decide

#print axioms small_seed_unit_tests
end FiniteDiagrams
