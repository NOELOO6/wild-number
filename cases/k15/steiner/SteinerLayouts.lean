import SteinerSearch

namespace Wild15.Steiner
open WildExact.Rotation.CutTest

/-- One digit per point specifies which of the five triples contains it. -/
private def decode (digits : String) : Blocks 14 :=
  let labels := digits.toList.toArray
  (List.range 5).map fun k => points.filter fun x =>
    (labels[x.val]!).toNat == '0'.toNat+k

def layouts : List (Blocks 14) := ([
  "342320011341420", "204041212343130", "312340204304121", "103423140032241", "324132441203010",
  "434120014233210", "210344042332110", "131020234044123", "410312130244203", "213330142410042",
  "314302404223110", "334032044121021", "002413423341120", "241343031120420", "121302414430203",
  "224411200130343", "301404032121423", "022013423113044", "331231044210042", "001042443233112",
  "120443312032401", "422013420101343", "133240140214032", "004022213331414", "020303244141213",
  "120323401401324", "013240124042133", "242144301233100", "310322023440141", "400213412243031",
  "402031441013322", "003223241131440", "221013044241033", "402323211310404", "134212034002413",
  "242340311241030", "304240201342113", "421013401334202", "234031120340421", "210404110232334",
  "233140123241400", "403224011234031", "330131441202240", "412001334104223", "041320421041332",
  "201024123140343", "443330142201012", "130314140420223", "314422124130003", "014032301234124",
  "403200324214131", "440201142231303", "031210413022434", "233402401130214", "440421132301032",
  "321402342130041", "311234003421042", "024121013443302", "230024034141213", "002033424112341",
  "121004331320442", "043322121030414", "132412420401303", "442431332100021", "044311430201322",
  "421403001243321"] : List String).map decode

def entry (bs : Blocks 14) : Nat × Array Nat :=
  let ss := cuts bs
  (2^ss.length-1,translated ss 0)

/-- The four possible alternating decompositions of two disjoint perfect
matchings on twelve vertices, in units of matching edges. -/
def lengths : List (List Nat) := [[6],[2,4],[3,3],[2,2,2]]

def nextOf (cs : List Nat) (i : Fin 6) : Fin 6 :=
  let rec shift : List Nat → Nat → Nat
    | [],j => j
    | k::ks,j => if j<k then (j+1)%k else k+shift ks (j-k)
  ⟨shift cs i.val%6,Nat.mod_lt _ (by decide)⟩

/-- All orientations of the certified opposite edges of a seed. -/
def oriented (ts : List Block) (i : V) : List Pair :=
  let es := edgesOf ts i
  es ++ es.map Prod.swap

/-- Each cut has a point whose two named incident edges both cross it. -/
def robust (cs : List Nat) (bs : Blocks 14) : Bool :=
  let ts := seeds (nextOf cs)
  (cuts bs).all fun side => (oriented ts 0).any fun a => (oriented ts 1).any fun b =>
    a.1==b.1 && a.2!=b.2 && side.contains a.1 != side.contains a.2 &&
      side.contains b.1 != side.contains b.2

def tables (cs : List Nat) := ((layouts.filter (robust cs)).map entry)

def works (bank : List (Nat × Array Nat)) (ts : List Block) : Bool :=
  let rows := points.map (edgesOf ts)
  bank.any fun t => rows.all fun es => crossed t.2 es==t.1

def exhaust (cs : List Nat) :=
  let ts := seeds (nextOf cs)
  search (works (tables cs)) 22 (bankOf ts) ts

end Wild15.Steiner
