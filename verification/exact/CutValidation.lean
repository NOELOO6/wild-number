import CutData
namespace WildExact.Seventeen

def validateCuts : Bool :=
  let layouts := List.finRange 15400
  let localRange := layouts.all fun p => (localCuts p).all (fun k => allKeys.contains k)
  let flags := allKeys.all fun k =>
    let bits := partFlags k
    k<16384 && layouts.all (fun p => bits.testBit p.val == (localCuts p).contains k)
  let bounds := (List.finRange 6188).all (fun b => allKeys.all (fun k => embed b k<262144))
  localRange && flags && bounds

end WildExact.Seventeen
