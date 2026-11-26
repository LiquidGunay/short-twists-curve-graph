import FiniteDiagrams

/-! Exhaustive finite input generation for the twelve- and thirteen-crossing census.
The coverage of *surface curves* by these gluings is a separate topological assertion. -/
namespace ShortTwists.Census
open FiniteDiagrams

def pairings : Nat → List Nat → List (List (Nat × Nat))
  | 0, xs => if xs.isEmpty then [[]] else []
  | _+1, [] => []
  | k+1, a::rest => rest.bind fun b =>
    (pairings k (rest.erase b)).map (fun tail => (a,b)::tail)

def mateOf (ps : List (Nat × Nat)) : Array Nat :=
  ps.foldl (fun m (a,b) => (m.set! a b).set! b a) (Array.mkArray 12 0)

def rotate (d : Nat) := 3*(d/3) + (d+1)%3
def circles (m : Array Nat) := cycles (m.map rotate)

def shapes : List (Array Nat) := [
  #[1,0,3,2,6,9,4,10,11,5,7,8], #[3,4,5,0,1,2,9,10,11,6,7,8],
  #[3,4,6,0,1,9,2,10,11,5,7,8], #[3,4,6,0,1,9,2,11,10,5,8,7],
  #[3,6,9,0,7,10,1,4,11,2,5,8], #[3,6,9,0,7,11,1,4,10,2,8,5]]

/-- Every labeling permutes the four triangles and rotates the sides of each. -/
def relabelings : Array (Array Nat) := Id.run do
  let mut all := #[]
  for a in [:4] do
    for b in [:4] do
      if b==a then continue
      for c in [:4] do
        if c==a || c==b then continue
        let order := #[a,b,c,6-(a+b+c)]
        for spin in [:81] do
          all := all.push ((Array.range 12).map (fun d =>
            3*order[d/3]! + (d%3+(spin/3^(d/3))%3)%3))
  return all

def relabel (m labels : Array Nat) : Array Nat := Id.run do
  let mut out := Array.mkArray 12 0
  for d in [:12] do out := out.set! labels[d]! labels[m[d]!]!
  return out

def shapeAudit : Nat × Nat × Nat × Bool := Id.run do
  let all := (pairings 6 (List.range 12)).map mateOf
  let eligible := all.filter (fun m => (circles m).size == 2)
  let mut covered : Lean.HashSet (List Nat) := {}
  let mut separate := true
  for m in shapes do
    let mut orbit : Lean.HashSet (List Nat) := {}
    for labels in relabelings do orbit := orbit.insert (relabel m labels).toList
    separate := separate && orbit.toList.all (fun p => !covered.contains p)
    covered := covered.insertMany orbit.toList
  return (all.length,eligible.length,covered.size,
    separate && eligible.all (fun m => covered.contains m.toList))

def widths : Nat → Nat → List (List Nat)
  | 0, n => if n=0 then [[]] else []
  | k+1, n => (List.range (n+1)).bind (fun w =>
    (widths k (n-w)).map (w :: ·))

def ends (m : Array Nat) (ws : List Nat) : Array (Array Nat) := Id.run do
  let mut bundle := Array.mkArray 12 #[]
  let mut first := 0
  let mut edge := 0
  for d in [:12] do
    if d < m[d]! then
      let w := ws[edge]!
      let upper := (Array.range w).map (fun i => 2*(first+i))
      let lower := upper.reverse.map (·+1)
      bundle := (bundle.set! d upper).set! m[d]! lower
      first := first+w
      edge := edge+1
  return bundle

/-- Read one circuit after identifying the two boundary circles with the given offset. -/
def circuit (n shift : Nat) (top bottom : Array Nat) : Option Code := Id.run do
  let mut mate := Array.mkArray (2*n) 0
  let mut signed := Array.mkArray (2*n) (0 : Int)
  for j in [:n] do
    let a := top[j]!
    let b := bottom[(j+shift)%n]!
    mate := (mate.set! a b).set! b a
    signed := (signed.set! a (j+1 : Nat)).set! b (-(j+1 : Int))
  let mut d := top[0]!
  let mut word := #[]
  for _ in [:n] do
    word := word.push signed[d]!
    d := mate[flip d]!
    if d==top[0]! then return if word.size==n then some word else none
  return none

/-- Move the origin and reverse direction independently on both marked loops.
Normalization of the first sign accounts for the two surface orientations. -/
def canonical (s : Code) : List Int := Id.run do
  let n := s.size
  let mut best : Option (List Int) := none
  for order in #[s,s.reverse] do
    for j in [:n] do
      let initial := order[j]!
      for forward in #[true,false] do
        let mut code := #[]
        for t in [:n] do
          let v := order[(j+t)%n]!
          let displacement := if forward then n+v.natAbs-initial.natAbs else n+initial.natAbs-v.natAbs
          let label : Int := 1+displacement%n
          code := code.push (if (0<v) == (0<initial) then label else -label)
        let candidate := code.toList
        if best.all (fun old => decide (candidate < old)) then best := some candidate
  return best.getD []

def sortWords (words : List (List Int)) : List (List Int) :=
  (words.toArray.qsort (fun x y => decide (x < y))).toList

def census (n : Nat) : Nat × List (List Int) := Id.run do
  let mut seen : Lean.HashSet (List Int) := {}
  let mut kept := []
  for m in shapes do
    let cs := circles m
    for ws in widths 6 n do
      let bundles := ends m ws
      let top := cs[0]!.foldl (fun (a : Array Nat) d => a ++ bundles[d]!) #[]
      if top.size != n then continue
      let bottom := (cs[1]!.foldl (fun (a : Array Nat) d => a ++ bundles[d]!) #[]).reverse
      for shift in [:n] do
        if let some w := circuit n shift top bottom then
          let fs := cutFaces w
          if fs.size+2 != n || fs.any (fun face => face.size<2) then continue
          let key := canonical w
          if seen.contains key then continue
          seen := seen.insert key
          if exactTest key.toArray 4 then kept := key :: kept
  return (seen.size,sortWords kept)

def listed (n : Nat) := sortWords ((smallSeeds.filter (fun w => w.size==n)).toList.map Array.toList)

theorem all_six_shapes : shapeAudit = (10395,4563,4563,true) := by native_decide
theorem all_twelve : census 12 = (348,listed 12) := by native_decide
theorem all_thirteen : census 13 = (499,listed 13) := by native_decide

#print axioms all_twelve
#print axioms all_thirteen
end ShortTwists.Census
